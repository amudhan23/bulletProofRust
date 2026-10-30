use ark_bls12_381::Fr;
use ark_crypto_primitives::crh::bowe_hopwood::constraints;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
    SynthesisError,
};

use crate::{hadamard, inner_product, powers_of};

pub type SparseRow<F> = Vec<(usize, F)>;

pub struct ArithCircuit<F: PrimeField> {
    pub num_constraints: usize,
    pub num_instance_variables: usize, // instance variables
    pub num_witness_variables: usize,  // witness variables
    pub w_l: Vec<SparseRow<F>>,
    pub w_r: Vec<SparseRow<F>>,
    pub w_o: Vec<SparseRow<F>>,
    pub w_v: Vec<SparseRow<F>>,
    pub c_pub: Vec<F>,
}

pub fn delta<F: PrimeField>(y: F, f_l: &[F], f_r: &[F]) -> F {
    let y_inv = y.inverse().unwrap();
    let y_inv_pows = powers_of(y_inv, f_l.len());

    let had_product = hadamard(&y_inv_pows, f_r);
    inner_product(&had_product, f_l)
}

pub fn assign<G: CurveGroup>(
    mats: &ConstraintMatrices<G::ScalarField>,
    z: &[G::ScalarField],
) -> (
    Vec<G::ScalarField>,
    Vec<G::ScalarField>,
    Vec<G::ScalarField>,
) {
    let mv = |m: &Vec<Vec<(G::ScalarField, usize)>>| -> Vec<G::ScalarField> {
        m.iter()
            .map(|row| row.iter().map(|(c, j)| *c * z[*j]).sum())
            .collect()
    };
    let (mut a_l, mut a_r, mut a_o) = (mv(&mats.a), mv(&mats.b), mv(&mats.c));
    for j in mats.num_instance_variables..z.len() {
        a_l.push(z[j]);
        a_r.push(G::ScalarField::one());
        a_o.push(z[j]);
    }
    (a_l, a_r, a_o)
}

impl<F: PrimeField> ArithCircuit<F> {
    pub fn convert_to_f_vectors(&self, z_pows: &[F]) -> (Vec<F>, Vec<F>, Vec<F>, Vec<F>, F) {
        let n = (self.num_constraints + self.num_witness_variables).next_power_of_two();
        let mut f_l: Vec<F> = vec![F::zero(); n];
        let mut f_r: Vec<F> = vec![F::zero(); n];
        let mut f_o: Vec<F> = vec![F::zero(); n];
        let mut f_v: Vec<F> = vec![F::zero(); n];
        let mut f_c: F = F::zero();

        for q in 0..z_pows.len() {
            for &(gate, coeff) in &self.w_l[q] {
                f_l[gate] += coeff * z_pows[q];
            }
            for &(gate, coeff) in &self.w_r[q] {
                f_r[gate] += coeff * z_pows[q];
            }
            for &(gate, coeff) in &self.w_o[q] {
                f_o[gate] += coeff * z_pows[q];
            }
            for &(gate, coeff) in &self.w_v[q] {
                f_v[gate] += coeff * z_pows[q];
            }

            f_c += self.c_pub[q] * z_pows[q];
        }

        (f_l, f_r, f_o, f_v, f_c)
    }

    pub fn convert_to_wiring_constraint(mats: &ConstraintMatrices<F>, instance: &[F]) -> Self {
        let num_constraints = mats.num_constraints;
        let num_witness_variables = mats.num_witness_variables;
        let num_instance_variables = mats.num_instance_variables;
        let total_rows = 3 * num_constraints + num_witness_variables;

        let mut w_l: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_r: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_o: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let w_v: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut c_pub: Vec<F> = vec![F::zero(); total_rows];

        for i in 0..num_constraints {
            let rows = [3 * i, 3 * i + 1, 3 * i + 2];
            w_l[rows[0]].push((i, F::one()));
            w_r[rows[1]].push((i, F::one()));
            w_o[rows[2]].push((i, F::one()));

            for (k, mat) in [&mats.a, &mats.b, &mats.c].into_iter().enumerate() {
                for &(coeff, col) in &mat[i] {
                    if col < num_instance_variables {
                        c_pub[rows[k]] += coeff * instance[col];
                    } else {
                        w_l[rows[k]]
                            .push((num_constraints + (col - num_instance_variables), -coeff));
                    }
                }
            }
        }

        for j in 0..num_witness_variables {
            let row = 3 * num_constraints + j;
            w_r[row].push((num_constraints + j, F::one()));
            c_pub[row] = F::one();
        }

        Self {
            num_constraints,
            num_instance_variables,
            num_witness_variables,
            w_l,
            w_r,
            w_o,
            w_v,
            c_pub,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::CubicCircuit;
    use ark_bls12_381::Fr;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, Matrix};

    fn matvec(m: &Matrix<Fr>, z: &[Fr]) -> Vec<Fr> {
        m.iter()
            .map(|row| row.iter().map(|(c, j)| *c * z[*j]).sum())
            .collect()
    }
    fn sparse_dot(rows: &[SparseRow<Fr>], x: &[Fr]) -> Vec<Fr> {
        rows.iter()
            .map(|r| r.iter().map(|(j, c)| *c * x[*j]).sum())
            .collect()
    }

    fn setup() -> (ConstraintMatrices<Fr>, Vec<Fr>, Vec<Fr>) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        CubicCircuit {
            x: Some(Fr::from(3u32)),
            out: Fr::from(35u32),
        }
        .generate_constraints(cs.clone())
        .unwrap();
        cs.finalize();
        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        (
            mats,
            b.instance_assignment.clone(),
            b.witness_assignment.clone(),
        )
    }

    fn residuals(ac: &ArithCircuit<Fr>, a_l: &[Fr], a_r: &[Fr], a_o: &[Fr], v: &[Fr]) -> Vec<Fr> {
        let (l, r, o) = (
            sparse_dot(&ac.w_l, a_l),
            sparse_dot(&ac.w_r, a_r),
            sparse_dot(&ac.w_o, a_o),
        );
        let wv = sparse_dot(&ac.w_v, v);
        (0..ac.c_pub.len())
            .map(|k| l[k] + r[k] + o[k] - wv[k] - ac.c_pub[k])
            .collect()
    }

    #[test]
    fn wiring_holds_for_cubic() {
        let (mats, instance, witness) = setup();
        let mut z = instance.clone();
        z.extend(witness.iter().cloned());
        let ac = ArithCircuit::convert_to_wiring_constraint(&mats, &instance);
        let (a_l, a_r, a_o) = (
            matvec(&mats.a, &z),
            matvec(&mats.b, &z),
            matvec(&mats.c, &z),
        );
        for i in 0..ac.num_constraints {
            assert_eq!(a_l[i] * a_r[i], a_o[i]);
        }
        assert!(
            residuals(&ac, &a_l, &a_r, &a_o, &witness)
                .iter()
                .all(|r| *r == Fr::from(0u32))
        );
        println!(
            "rows={} n={} W_V row sizes={:?}",
            ac.c_pub.len(),
            ac.num_constraints,
            ac.w_v.iter().map(|r| r.len()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn wrong_witness_breaks_wiring() {
        let (mats, instance, mut witness) = setup();
        let mut z = instance.clone();
        z.extend(witness.iter().cloned());
        let ac = ArithCircuit::convert_to_wiring_constraint(&mats, &instance);
        let (a_l, a_r, a_o) = (
            matvec(&mats.a, &z),
            matvec(&mats.b, &z),
            matvec(&mats.c, &z),
        );
        witness[0] += Fr::from(1u32); // lie about v[0]
        assert!(
            residuals(&ac, &a_l, &a_r, &a_o, &witness)
                .iter()
                .any(|r| *r != Fr::from(0u32))
        );
    }
}

#[cfg(test)]
mod more_tests {
    use super::*;
    use crate::circuit::CubicCircuit;
    use ark_bls12_381::Fr;
    use ark_relations::lc;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, Variable};

    fn sparse_dot(rows: &[SparseRow<Fr>], x: &[Fr]) -> Vec<Fr> {
        rows.iter()
            .map(|r| r.iter().map(|(j, c)| *c * x[*j]).sum())
            .collect()
    }

    /// (2x + 3y) * 1 = out, with x = 1, y = 2, out = 8
    fn linear_cs() -> ark_relations::r1cs::ConstraintSystemRef<Fr> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let out = cs.new_input_variable(|| Ok(Fr::from(8u32))).unwrap();
        let x = cs.new_witness_variable(|| Ok(Fr::from(1u32))).unwrap();
        let y = cs.new_witness_variable(|| Ok(Fr::from(2u32))).unwrap();
        cs.enforce_constraint(
            lc!() + (Fr::from(2u32), x) + (Fr::from(3u32), y),
            lc!() + Variable::One,
            lc!() + out,
        )
        .unwrap();
        cs.finalize();
        cs
    }

    #[test]
    fn coefficients_are_kept_in_w_v() {
        let cs = linear_cs();
        let mats = cs.to_matrices().unwrap();
        let instance = cs.borrow().unwrap().instance_assignment.clone();
        let ac = ArithCircuit::convert_to_wiring_constraint(&mats, &instance);
        // row 0 is the A-row: a_L = 2*x + 3*y
        assert_eq!(ac.w_v[0], vec![(0, Fr::from(2u32)), (1, Fr::from(3u32))]);
    }

    #[test]
    fn wrong_public_output_breaks_wiring() {
        let (mats, instance, witness) = {
            let cs = ConstraintSystem::<Fr>::new_ref();
            CubicCircuit {
                x: Some(Fr::from(3u32)),
                out: Fr::from(35u32),
            }
            .generate_constraints(cs.clone())
            .unwrap();
            cs.finalize();
            let b = cs.borrow().unwrap();
            (
                cs.to_matrices().unwrap(),
                b.instance_assignment.clone(),
                b.witness_assignment.clone(),
            )
        };
        let mut z = instance.clone();
        z.extend(witness.iter().cloned());
        let honest = |inst: &[Fr]| {
            let ac = ArithCircuit::convert_to_wiring_constraint(&mats, inst);
            let mv = |m: &ark_relations::r1cs::Matrix<Fr>| -> Vec<Fr> {
                m.iter()
                    .map(|row| row.iter().map(|(c, j)| *c * z[*j]).sum())
                    .collect()
            };
            let (a_l, a_r, a_o) = (mv(&mats.a), mv(&mats.b), mv(&mats.c));
            let (l, r, o) = (
                sparse_dot(&ac.w_l, &a_l),
                sparse_dot(&ac.w_r, &a_r),
                sparse_dot(&ac.w_o, &a_o),
            );
            let wv = sparse_dot(&ac.w_v, &witness);
            (0..ac.c_pub.len()).all(|k| l[k] + r[k] + o[k] == wv[k] + ac.c_pub[k])
        };
        assert!(honest(&instance));
        let mut wrong = instance.clone();
        wrong[1] = Fr::from(36u32); // claim out = 36
        assert!(!honest(&wrong));
    }
}

#[cfg(test)]
mod sha_tests {
    use super::*;
    use crate::circuit_sha256::Sha256Circuit;
    use ark_bls12_381::Fr;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, Matrix};
    use sha2::{Digest, Sha256};

    fn sparse_dot(rows: &[SparseRow<Fr>], x: &[Fr]) -> Vec<Fr> {
        rows.iter()
            .map(|r| r.iter().map(|(j, c)| *c * x[*j]).sum())
            .collect()
    }
    fn matvec(m: &Matrix<Fr>, z: &[Fr]) -> Vec<Fr> {
        m.iter()
            .map(|row| row.iter().map(|(c, j)| *c * z[*j]).sum())
            .collect()
    }

    #[test]
    fn wiring_holds_for_sha256() {
        let preimage = b"hello".to_vec();
        let expected_hash = Sha256::digest(&preimage).to_vec();
        let cs = ConstraintSystem::<Fr>::new_ref();
        Sha256Circuit::<Fr> {
            preimage,
            expected_hash,
            _phantom: std::marker::PhantomData,
        }
        .generate_constraints(cs.clone())
        .unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let mats = cs.to_matrices().unwrap();
        let (instance, witness) = {
            let b = cs.borrow().unwrap();
            (b.instance_assignment.clone(), b.witness_assignment.clone())
        };
        let mut z = instance.clone();
        z.extend(witness.iter().cloned());

        let t = std::time::Instant::now();
        let ac = ArithCircuit::convert_to_wiring_constraint(&mats, &instance);
        println!("convert: {:?}", t.elapsed());
        println!(
            "n={} rows={} instance={} witness(m)={} nnz(W_V)={}",
            ac.num_constraints,
            ac.c_pub.len(),
            ac.num_instance_variables,
            ac.num_witness_variables,
            ac.w_v.iter().map(|r| r.len()).sum::<usize>()
        );

        let (a_l, a_r, a_o) = (
            matvec(&mats.a, &z),
            matvec(&mats.b, &z),
            matvec(&mats.c, &z),
        );
        for i in 0..ac.num_constraints {
            assert_eq!(a_l[i] * a_r[i], a_o[i], "gate {i}");
        }

        let resid = |inst_c: &[Fr], v: &[Fr]| -> bool {
            let (l, r, o) = (
                sparse_dot(&ac.w_l, &a_l),
                sparse_dot(&ac.w_r, &a_r),
                sparse_dot(&ac.w_o, &a_o),
            );
            let wv = sparse_dot(&ac.w_v, v);
            (0..inst_c.len()).all(|k| l[k] + r[k] + o[k] == wv[k] + inst_c[k])
        };
        assert!(resid(&ac.c_pub, &witness));

        // tampered witness value
        let mut bad = witness.clone();
        bad[0] += Fr::from(1u32);
        assert!(!resid(&ac.c_pub, &bad));

        // wrong claimed hash: flip one public hash bit
        let mut inst2 = instance.clone();
        let last = inst2.len() - 1;
        inst2[last] = Fr::from(1u32) - inst2[last];
        let ac2 = ArithCircuit::convert_to_wiring_constraint(&mats, &inst2);
        assert!(!resid(&ac2.c_pub, &witness));
    }
}

#[cfg(test)]
mod t2_tests {
    use super::*;
    use crate::circuit::CubicCircuit;
    use crate::{hadamard, inner_product, powers_of};
    use ark_bls12_381::Fr;
    use ark_ff::Field;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, Matrix};

    fn matvec(m: &Matrix<Fr>, z: &[Fr]) -> Vec<Fr> {
        m.iter()
            .map(|row| row.iter().map(|(c, j)| *c * z[*j]).sum())
            .collect()
    }

    /// Pad a vector to length n with zeros
    fn pad(v: &mut Vec<Fr>, n: usize) {
        v.resize(n, Fr::from(0u32));
    }

    #[test]
    fn t2_two_ways_cubic() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        CubicCircuit {
            x: Some(Fr::from(3u32)),
            out: Fr::from(35u32),
        }
        .generate_constraints(cs.clone())
        .unwrap();
        cs.finalize();
        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let (instance, witness) = (b.instance_assignment.clone(), b.witness_assignment.clone());
        drop(b);
        let mut z = instance.clone();
        z.extend(witness.iter().cloned());

        let ac = ArithCircuit::convert_to_wiring_constraint(&mats, &instance);
        let n = (ac.num_constraints + ac.num_witness_variables).next_power_of_two();
        let q = ac.c_pub.len();

        // random y and z (use deterministic "random" for reproducibility)
        let y = Fr::from(123u32);
        let zz = Fr::from(456u32);

        // z_pows = [zz, zz^2, ..., zz^Q]
        let z_pows: Vec<Fr> = {
            let mut v = Vec::with_capacity(q);
            let mut cur = zz;
            for _ in 0..q {
                v.push(cur);
                cur *= zz;
            }
            v
        };

        // fold
        let (f_l, f_r, f_o, _f_v, k_c) = ac.convert_to_f_vectors(&z_pows);

        // --- Way 1: t2 = k_c + delta ---
        let d = delta(y, &f_l, &f_r);
        let t2_way1 = k_c + d;

        // --- Way 2: t2 = <l1, r1> + <l2, r0> ---
        // build a_L, a_R, a_O (with home gates), padded to n
        let (mut a_l, mut a_r, mut a_o) = (
            matvec(&mats.a, &z),
            matvec(&mats.b, &z),
            matvec(&mats.c, &z),
        );
        for j in mats.num_instance_variables..z.len() {
            a_l.push(z[j]);
            a_r.push(Fr::from(1u32));
            a_o.push(z[j]);
        }
        pad(&mut a_l, n);
        pad(&mut a_r, n);
        pad(&mut a_o, n);

        let y_n = powers_of(y, n); // [1, y, y^2, ..., y^(n-1)]  -- check your powers_of
        let y_inv = y.inverse().unwrap();
        let y_inv_n = powers_of(y_inv, n); // [1, y^-1, y^-2, ...]

        // l₁ = a_L + y^{-n} ∘ f_R   (coefficient of X in l(X))
        let l1: Vec<Fr> = a_l
            .iter()
            .zip(y_inv_n.iter().zip(f_r.iter()))
            .map(|(al, (yi, fr))| *al + *yi * *fr)
            .collect();

        // r₁ = y^n ∘ a_R + f_L       (coefficient of X in r(X))
        let r1: Vec<Fr> = y_n
            .iter()
            .zip(a_r.iter())
            .zip(f_l.iter())
            .map(|((yn, ar), fl)| *yn * *ar + *fl)
            .collect();

        // l₂ = a_O                    (coefficient of X² in l(X))
        let l2 = a_o.clone();

        // r₀ = f_O - y^n              (constant term of r(X))
        let r0: Vec<Fr> = f_o
            .iter()
            .zip(y_n.iter())
            .map(|(fo, yn)| *fo - *yn)
            .collect();

        let t2_way2 = inner_product(&l1, &r1) + inner_product(&l2, &r0);

        assert_eq!(t2_way1, t2_way2, "honest cubic: t2 must match both ways");

        // --- Tampered: change a witness value, way2 should differ ---
        let mut a_l_bad = a_l.clone();
        a_l_bad[ac.num_constraints] += Fr::from(1u32); // corrupt first home gate
        let l1_bad: Vec<Fr> = a_l_bad
            .iter()
            .zip(y_inv_n.iter().zip(f_r.iter()))
            .map(|(al, (yi, fr))| *al + *yi * *fr)
            .collect();
        let t2_bad = inner_product(&l1_bad, &r1) + inner_product(&l2, &r0);

        assert_ne!(t2_way1, t2_bad, "tampered cubic: t2 must NOT match");
    }
}
