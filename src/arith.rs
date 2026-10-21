use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
    SynthesisError,
};

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

impl<F: PrimeField> ArithCircuit<F> {
    fn convert_to_wiring_constraint(mats: &ConstraintMatrices<F>, instance: &[F]) -> Self {
        let num_constraints = mats.num_constraints;
        let num_witness_variables = mats.num_witness_variables;
        let num_instance_variables = mats.num_instance_variables;
        let total_rows = 3 * num_constraints;

        let mut w_l: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_r: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_o: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_v: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut c_pub: Vec<F> = vec![F::zero(); total_rows];

        for i in 0..num_constraints {
            let rows = [3 * i, 3 * i + 1, 3 * i + 2];
            w_l[rows[0]].push((i, F::one()));
            w_r[rows[1]].push((i, F::one()));
            w_o[rows[2]].push((i, F::one()));

            for (k, mat) in [&mats.a, &mats.b, &mats.c].into_iter().enumerate() {
                for &(coeff, col) in &mat[i] {
                    if (col < num_instance_variables) {
                        c_pub[rows[k]] += coeff * instance[col];
                    } else {
                        w_v[rows[k]].push((col - num_instance_variables, coeff));
                    }
                }
            }
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
