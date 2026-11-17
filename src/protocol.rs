use std::vec;

use ark_bls12_381::Fr;
use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::ConstraintMatrices;
use ark_std::rand::Rng;
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;

use crate::{IpaProof, inner_product_scalar_generator, prove_ipa, verify_ipa};
use crate::{
    ProofParams, TranscriptProtocol,
    arith::{ArithCircuit, assign, delta},
    hadamard, inner_product, pedersen_vec, powers_of,
};

fn pedersen_vectors<G: CurveGroup>(a: &[G::ScalarField], g_vec: &[G]) -> G {
    debug_assert_eq!(a.len(), g_vec.len());
    a.iter().zip(g_vec).map(|(s, p)| *p * *s).sum()
}

pub fn commit_two_vectors<G: CurveGroup>(
    a: &Vec<G::ScalarField>,
    b: &Vec<G::ScalarField>,
    g: &Vec<G>,
    h: &Vec<G>,
    alpha: G::ScalarField,
    h_blind: G,
) -> G {
    pedersen_vectors(a, g) + pedersen_vectors(b, h) + h_blind * alpha
}

pub fn commit_vector<G: CurveGroup>(
    a: &Vec<G::ScalarField>,
    g: &Vec<G>,
    alpha: G::ScalarField,
    h_blind: G,
) -> G {
    pedersen_vectors(a, g) + h_blind * alpha
}

pub fn commit_scalar<G: CurveGroup>(a: G::ScalarField, g: G, b: G::ScalarField, h_blind: G) -> G {
    g * a + h_blind * b
}

fn powers_of_starts_base<F: PrimeField>(base: F, n: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(n);
    let mut cur = base;
    for _ in 0..n {
        out.push(cur);
        cur *= base;
    }
    out
}

fn vec_add<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    a.iter().zip(b).map(|(x, y)| *x + *y).collect()
}

fn vec_sub<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    a.iter().zip(b).map(|(x, y)| *x - *y).collect()
}

fn vecs_hadamard_prod<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    a.iter().zip(b).map(|(x, y)| *x * *y).collect()
}

fn vec_gen_prod<G: CurveGroup>(a: &[G::ScalarField], g: &Vec<G>) -> G {
    a.iter().zip(g).map(|(x, y)| *y * *x).sum()
}

fn scalar_vector_mul<G: CurveGroup>(
    x: G::ScalarField,
    v: &[G::ScalarField],
) -> Vec<G::ScalarField> {
    v.iter().map(|y| x * *y).collect()
}

pub struct Proof<G: CurveGroup> {
    A_I: G,
    A_O: G,
    S: G,
    tau_x: G::ScalarField,
    myu: G::ScalarField,
    T1: G,
    T3: G,
    T4: G,
    T5: G,
    T6: G,
    t_x: G::ScalarField,
    ipa_proof: IpaProof<G>,
}

pub fn prove<G: CurveGroup>(
    mats: &ConstraintMatrices<G::ScalarField>,
    instance: &[G::ScalarField],
    witness: &[G::ScalarField],
    params: &ProofParams<G>,
    rng: &mut impl Rng,
    commited: &[usize],
    v_gammas: &[G::ScalarField],
    transcript: &mut Transcript,
) -> Proof<G> {
    let ac = ArithCircuit::convert_to_wiring_constraint(mats, instance, &commited);

    let mut v_vals: Vec<G::ScalarField> = Vec::new();
    let mut V = Vec::new();

    for j in 0..commited.len() {
        v_vals.push(witness[commited[j]]);
        let v_commit = params.u * v_vals[j] + params.h_b * v_gammas[j];
        transcript.append_point(b"V", &v_commit);
        V.push(v_commit);
    }

    let mut z = instance.to_vec();
    z.extend_from_slice(witness);
    let (mut a_l, mut a_r, mut a_o) = assign::<G>(mats, &z);
    a_l.resize(params.n, G::ScalarField::zero());
    a_r.resize(params.n, G::ScalarField::zero());
    a_o.resize(params.n, G::ScalarField::zero());

    let alpha = G::ScalarField::rand(rng);
    let beta = G::ScalarField::rand(rng);
    let gamma = G::ScalarField::rand(rng);
    let A_I = commit_two_vectors(&a_l, &a_r, &params.g, &params.h, alpha, params.h_b);
    let A_O = commit_vector(&a_o, &params.g, beta, params.h_b);

    let s_l: Vec<G::ScalarField> = (0..params.n).map(|_| G::ScalarField::rand(rng)).collect();
    let s_r: Vec<G::ScalarField> = (0..params.n).map(|_| G::ScalarField::rand(rng)).collect();
    let S = commit_two_vectors(&s_l, &s_r, &params.g, &params.h, gamma, params.h_b);
    transcript.append_point(b"Com_A_I", &A_I);
    transcript.append_point(b"Com_A_O", &A_O);
    transcript.append_point(b"Com_S", &S);

    let y: G::ScalarField = transcript.get_challenge(b"y");
    let z_chal: G::ScalarField = transcript.get_challenge(b"z");

    let q = ac.w_l.len();

    let z_chal_powers = powers_of_starts_base(z_chal, q);

    let (f_l, f_r, f_o, f_v, k_c) = ac.convert_to_f_vectors(&z_chal_powers);

    let y_inv = y.inverse().unwrap();
    let y_pow = powers_of(y, params.n);
    let y_pow_inv = powers_of(y_inv, params.n);

    let l1 = vec_add(&a_l, &hadamard::<G>(&y_pow_inv, &f_r));
    let l2 = a_o.clone();
    let l3 = s_l.clone();

    let r1 = vec_sub(&f_o, &y_pow);
    let r2 = vec_add(&hadamard::<G>(&y_pow, &a_r), &f_l);
    let r3 = hadamard::<G>(&y_pow, &s_r);

    let t1 = inner_product::<G>(&l1, &r1);
    let t3 = inner_product::<G>(&l2, &r2) + inner_product::<G>(&l3, &r1);
    let t4 = inner_product::<G>(&l3, &r2) + inner_product::<G>(&l1, &r3);
    let t5 = inner_product::<G>(&l2, &r3);
    let t6 = inner_product::<G>(&l3, &r3);

    let delta_1 = G::ScalarField::rand(rng);
    let delta_3 = G::ScalarField::rand(rng);
    let delta_4 = G::ScalarField::rand(rng);
    let delta_5 = G::ScalarField::rand(rng);
    let delta_6 = G::ScalarField::rand(rng);

    let T1 = commit_scalar(t1, params.u, delta_1, params.h_b);
    let T3 = commit_scalar(t3, params.u, delta_3, params.h_b);
    let T4 = commit_scalar(t4, params.u, delta_4, params.h_b);
    let T5 = commit_scalar(t5, params.u, delta_5, params.h_b);
    let T6 = commit_scalar(t6, params.u, delta_6, params.h_b);

    transcript.append_point(b"T1", &T1);
    transcript.append_point(b"T3", &T3);
    transcript.append_point(b"T4", &T4);
    transcript.append_point(b"T5", &T5);
    transcript.append_point(b"T6", &T6);

    let fv_v = inner_product::<G>(&f_v, &v_vals);
    let fv_gamma = inner_product::<G>(&f_v, &v_gammas);

    let x: G::ScalarField = transcript.get_challenge(b"x");

    let delta = delta(y, &f_l, &f_r);

    let x2 = x * x;
    let x3 = x2 * x;
    let x4 = x3 * x;
    let x5 = x4 * x;
    let x6 = x5 * x;

    let t_x = x * t1 + x2 * (k_c + delta + fv_v) + x3 * t3 + x4 * t4 + x5 * t5 + x6 * t6;
    let tau_x =
        x * delta_1 + x3 * delta_3 + x4 * delta_4 + x5 * delta_5 + x6 * delta_6 + x2 * fv_gamma;

    let myu = x * alpha + x2 * beta + x3 * gamma;

    let l_x: Vec<G::ScalarField> = vec_add(
        &vec_add(
            &scalar_vector_mul::<G>(x, &l1),
            &scalar_vector_mul::<G>(x2, &l2),
        ),
        &scalar_vector_mul::<G>(x3, &l3),
    );
    // let r_x = r1 + scalar_vector_mul(x, &r2) + scalar_vector_mul(x3, &r3);

    let r_x: Vec<G::ScalarField> = vec_add(
        &vec_add(&r1, &scalar_vector_mul::<G>(x, &r2)),
        &scalar_vector_mul::<G>(x3, &r3),
    );

    let h_prime: Vec<G> = params
        .h
        .iter()
        .zip(y_pow_inv.iter())
        .map(|(h, y)| *h * *y)
        .collect();

    transcript.append_scalar(b"t_x", t_x);
    transcript.append_scalar(b"tau_x", tau_x);
    transcript.append_scalar(b"myu", myu);

    let w: G::ScalarField = transcript.get_challenge(b"w");
    let u_prime = params.u * w;

    let ipa_proof = prove_ipa(transcript, l_x, r_x, params.g.clone(), h_prime, u_prime);

    Proof {
        A_I,
        A_O,
        S,
        tau_x,
        myu,
        T1,
        T3,
        T4,
        T5,
        T6,
        t_x,
        ipa_proof,
    }
}

pub fn verify<G: CurveGroup>(
    mats: &ConstraintMatrices<G::ScalarField>,
    instance: &[G::ScalarField],
    params: &ProofParams<G>,
    commited: &[usize],
    v_commitments: &[G],
    proof: &Proof<G>,
    transcript: &mut Transcript,
) -> bool {
    let ac = ArithCircuit::convert_to_wiring_constraint(mats, instance, &commited);

    for V in v_commitments {
        transcript.append_point(b"V", V);
    }

    transcript.append_point(b"Com_A_I", &proof.A_I);
    transcript.append_point(b"Com_A_O", &proof.A_O);
    transcript.append_point(b"Com_S", &proof.S);

    let y: G::ScalarField = transcript.get_challenge(b"y");
    let z_chal: G::ScalarField = transcript.get_challenge(b"z");

    let q = ac.w_l.len();

    let z_chal_powers = powers_of_starts_base(z_chal, q);

    let (f_l, f_r, f_o, f_v, k_c) = ac.convert_to_f_vectors(&z_chal_powers);

    let y_inv = y.inverse().unwrap();
    let y_pow = powers_of(y, params.n);
    let y_pow_inv = powers_of(y_inv, params.n);

    transcript.append_point(b"T1", &proof.T1);
    transcript.append_point(b"T3", &proof.T3);
    transcript.append_point(b"T4", &proof.T4);
    transcript.append_point(b"T5", &proof.T5);
    transcript.append_point(b"T6", &proof.T6);

    let x: G::ScalarField = transcript.get_challenge(b"x");

    let delta = delta(y, &f_l, &f_r);

    let x2 = x * x;
    let x3 = x2 * x;
    let x4 = x3 * x;
    let x5 = x4 * x;
    let x6 = x5 * x;
    let fv_v_commitment = inner_product_scalar_generator(&f_v, v_commitments);

    //check 1
    let t_lhs = params.u * proof.t_x + params.h_b * proof.tau_x;
    let t_rhs = proof.T1 * x
        + params.u * x2 * (delta + k_c)
        + (fv_v_commitment) * x2
        + proof.T3 * x3
        + proof.T4 * x4
        + proof.T5 * x5
        + proof.T6 * x6;

    if t_lhs != t_rhs {
        return false;
    }

    let h_prime: Vec<G> = params
        .h
        .iter()
        .zip(y_pow_inv.iter())
        .map(|(h, y)| *h * *y)
        .collect();

    let x_public_term = (vec_gen_prod(&vecs_hadamard_prod(&y_pow_inv, &f_r), &params.g) * x
        + vec_gen_prod(&f_l, &h_prime) * x);
    let constant_term = vec_gen_prod(&vec_sub(&f_o, &y_pow), &h_prime);

    transcript.append_scalar(b"t_x", proof.t_x);
    transcript.append_scalar(b"tau_x", proof.tau_x);
    transcript.append_scalar(b"myu", proof.myu);

    let w: G::ScalarField = transcript.get_challenge(b"w");
    let u_prime = params.u * w;

    let P = proof.A_I * x + proof.A_O * x2 + proof.S * x3 - params.h_b * proof.myu
        + x_public_term
        + constant_term
        + u_prime * proof.t_x;

    verify_ipa(
        transcript,
        &proof.ipa_proof,
        P,
        params.g.clone(),
        h_prime,
        u_prime,
    )
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fr, G1Projective};
    use ark_relations::r1cs::{ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem};
    use ark_std::UniformRand;
    use merlin::Transcript;

    use crate::ProofParams;
    use crate::circuit::CubicCircuit;
    use crate::protocol::{prove, verify};

    /// Build the cubic circuit x^3 + x + 5 = out, return (mats, instance, witness, n)
    fn cubic_setup() -> (ConstraintMatrices<Fr>, Vec<Fr>, Vec<Fr>, usize) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        CubicCircuit {
            x: Some(Fr::from(3u32)),
            out: Fr::from(35u32),
        }
        .generate_constraints(cs.clone())
        .unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let instance = b.instance_assignment.clone();
        let witness = b.witness_assignment.clone();

        // n = next power of two of (num_constraints + num_witness_variables)
        let n = (mats.num_constraints + mats.num_witness_variables).next_power_of_two();

        (mats, instance, witness, n)
    }

    /// Build ProofParams with deterministic generators
    fn make_params(n: usize) -> ProofParams<G1Projective> {
        let mut rng = ark_std::test_rng();
        let g: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let h: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let u = G1Projective::rand(&mut rng);
        let h_b = G1Projective::rand(&mut rng);

        ProofParams { g, h, u, h_b, n }
    }

    #[test]
    fn honest_proof_verifies() {
        let (mats, instance, witness, n) = cubic_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        // Prove
        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        // Verify with fresh transcript (same label)
        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        let ok = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut transcript_v);

        assert!(ok, "honest proof should verify");
    }

    #[test]
    fn wrong_public_input_fails() {
        let (mats, instance, witness, n) = cubic_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        // Prove with correct instance
        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        // Verify with wrong instance: claim out = 36 instead of 35
        let mut wrong_instance = instance.clone();
        wrong_instance[1] = Fr::from(36u32);

        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        let ok = verify::<G1Projective>(&mats, &wrong_instance, &params, &proof, &mut transcript_v);

        assert!(!ok, "wrong public input should fail verification");
    }

    #[test]
    fn wrong_witness_fails() {
        let (mats, instance, _, n) = cubic_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        // Prove with wrong witness: x = 4 instead of 3
        // x^3 + x + 5 = 69, but we still claim out = 35
        let bad_witness = vec![Fr::from(4u32), Fr::from(16u32), Fr::from(64u32)];

        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &bad_witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        let ok = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut transcript_v);

        assert!(!ok, "wrong witness should fail verification");
    }

    fn honest_proof() -> (
        ConstraintMatrices<Fr>,
        Vec<Fr>,
        ProofParams<G1Projective>,
        super::Proof<G1Projective>,
    ) {
        let (mats, instance, witness, n) = cubic_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();
        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );
        // sanity: the untampered proof verifies
        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        assert!(verify::<G1Projective>(
            &mats,
            &instance,
            &params,
            &proof,
            &mut transcript_v
        ));
        (mats, instance, params, proof)
    }

    // ── Negative tests: tamper individual proof fields ─────────────────

    #[test]
    fn tampered_a_i_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            A_I: proof.A_I + proof.S,
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered A_I must be rejected"
        );
    }

    #[test]
    fn tampered_a_o_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            A_O: proof.A_O + proof.S,
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered A_O must be rejected"
        );
    }

    #[test]
    fn tampered_s_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            S: proof.S + proof.A_I,
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered S must be rejected"
        );
    }

    #[test]
    fn tampered_t_x_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            t_x: proof.t_x + Fr::from(1u32),
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered t_x must be rejected"
        );
    }

    #[test]
    fn tampered_tau_x_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            tau_x: proof.tau_x + Fr::from(1u32),
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered tau_x must be rejected"
        );
    }

    #[test]
    fn tampered_myu_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            myu: proof.myu + Fr::from(1u32),
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered myu must be rejected"
        );
    }

    #[test]
    fn tampered_t1_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad = super::Proof {
            T1: proof.T1 + proof.A_I,
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered T1 must be rejected"
        );
    }

    #[test]
    fn tampered_ipa_a_final_fails() {
        let (mats, instance, params, proof) = honest_proof();
        let bad_ipa = crate::IpaProof {
            l_vec: proof.ipa_proof.l_vec.clone(),
            r_vec: proof.ipa_proof.r_vec.clone(),
            a_final: proof.ipa_proof.a_final + Fr::from(1u32),
            b_final: proof.ipa_proof.b_final,
        };
        let bad = super::Proof {
            ipa_proof: bad_ipa,
            ..proof
        };
        let mut t = Transcript::new(b"r1cs_bp_test");
        assert!(
            !verify::<G1Projective>(&mats, &instance, &params, &bad, &mut t),
            "tampered IPA a_final must be rejected"
        );
    }

    #[test]
    fn wrong_transcript_label_fails() {
        let (mats, instance, witness, n) = cubic_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        // Verifier uses a different transcript label
        let mut transcript_v = Transcript::new(b"WRONG_LABEL");
        let ok = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut transcript_v);
        assert!(!ok, "mismatched transcript label must fail");
    }

    // ── Bigger circuit test: PowerCircuit with ~63 constraints ─────────

    #[test]
    fn power_circuit_63_constraints() {
        use crate::circuit_bench::PowerCircuit;

        let num_mults = 63;
        let x_val = Fr::from(2u32);
        let mut y_val = x_val;
        for _ in 0..num_mults {
            y_val *= x_val;
        }

        let cs = ConstraintSystem::<Fr>::new_ref();
        let circuit = PowerCircuit {
            x: Some(x_val),
            y: y_val,
            num_mults,
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let instance = b.instance_assignment.clone();
        let witness = b.witness_assignment.clone();
        drop(b);

        let n = (mats.num_constraints + mats.num_witness_variables).next_power_of_two();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        let ok = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut transcript_v);
        assert!(ok, "PowerCircuit(63) honest proof must verify");
    }

    #[test]
    fn power_circuit_255_constraints() {
        use crate::circuit_bench::PowerCircuit;

        let num_mults = 255;
        let x_val = Fr::from(2u32);
        let mut y_val = x_val;
        for _ in 0..num_mults {
            y_val *= x_val;
        }

        let cs = ConstraintSystem::<Fr>::new_ref();
        let circuit = PowerCircuit {
            x: Some(x_val),
            y: y_val,
            num_mults,
        };
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let instance = b.instance_assignment.clone();
        let witness = b.witness_assignment.clone();
        drop(b);

        let n = (mats.num_constraints + mats.num_witness_variables).next_power_of_two();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();

        let mut transcript_p = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(
            &mats,
            &instance,
            &witness,
            &params,
            &mut rng,
            &mut transcript_p,
        );

        let mut transcript_v = Transcript::new(b"r1cs_bp_test");
        let ok = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut transcript_v);
        assert!(ok, "PowerCircuit(255) honest proof must verify");
    }

    // ── Soundness: planting a U-component in A_O must not forge a proof ──
    //
    // A prover with an invalid witness can know its gate-0 error Δ before any
    // challenge (gate 0 has weight y^0 = 1). Before the w-randomization of u in
    // the IPA, adding Δ·U to A_O cancelled the x²·Δ gap and the forgery verified.
    // `malicious_prove` is the real prover plus that single extra line.

    use super::*;

    fn malicious_prove<G: CurveGroup>(
        gate0_violation: G::ScalarField,
        mats: &ConstraintMatrices<G::ScalarField>,
        instance: &[G::ScalarField],
        witness: &[G::ScalarField],
        params: &ProofParams<G>,
        rng: &mut impl Rng,
        transcript: &mut Transcript,
    ) -> Proof<G> {
        let ac = ArithCircuit::convert_to_wiring_constraint(mats, instance);
        let mut z = instance.to_vec();
        z.extend_from_slice(witness);
        let (mut a_l, mut a_r, mut a_o) = assign::<G>(mats, &z);
        a_l.resize(params.n, G::ScalarField::zero());
        a_r.resize(params.n, G::ScalarField::zero());
        a_o.resize(params.n, G::ScalarField::zero());

        let alpha = G::ScalarField::rand(rng);
        let beta = G::ScalarField::rand(rng);
        let gamma = G::ScalarField::rand(rng);
        let A_I = commit_two_vectors(&a_l, &a_r, &params.g, &params.h, alpha, params.h_b);
        let A_O = commit_vector(&a_o, &params.g, beta, params.h_b);
        // ATTACK: smuggle a U-component into A_O to cancel the gate-0 violation
        let A_O = A_O + params.u * gate0_violation;

        let s_l: Vec<G::ScalarField> = (0..params.n).map(|_| G::ScalarField::rand(rng)).collect();
        let s_r: Vec<G::ScalarField> = (0..params.n).map(|_| G::ScalarField::rand(rng)).collect();
        let S = commit_two_vectors(&s_l, &s_r, &params.g, &params.h, gamma, params.h_b);
        transcript.append_point(b"Com_A_I", &A_I);
        transcript.append_point(b"Com_A_O", &A_O);
        transcript.append_point(b"Com_S", &S);

        let y: G::ScalarField = transcript.get_challenge(b"y");
        let z_chal: G::ScalarField = transcript.get_challenge(b"z");

        let q = 3 * ac.num_constraints + ac.num_witness_variables;

        let z_chal_powers = powers_of_starts_base(z_chal, q);

        let (f_l, f_r, f_o, _, k_c) = ac.convert_to_f_vectors(&z_chal_powers);

        let y_inv = y.inverse().unwrap();
        let y_pow = powers_of(y, params.n);
        let y_pow_inv = powers_of(y_inv, params.n);

        let l1 = vec_add(&a_l, &hadamard::<G>(&y_pow_inv, &f_r));
        let l2 = a_o.clone();
        let l3 = s_l.clone();

        let r1 = vec_sub(&f_o, &y_pow);
        let r2 = vec_add(&hadamard::<G>(&y_pow, &a_r), &f_l);
        let r3 = hadamard::<G>(&y_pow, &s_r);

        let t1 = inner_product::<G>(&l1, &r1);
        let t3 = inner_product::<G>(&l2, &r2) + inner_product::<G>(&l3, &r1);
        let t4 = inner_product::<G>(&l3, &r2) + inner_product::<G>(&l1, &r3);
        let t5 = inner_product::<G>(&l2, &r3);
        let t6 = inner_product::<G>(&l3, &r3);

        let delta_1 = G::ScalarField::rand(rng);
        let delta_3 = G::ScalarField::rand(rng);
        let delta_4 = G::ScalarField::rand(rng);
        let delta_5 = G::ScalarField::rand(rng);
        let delta_6 = G::ScalarField::rand(rng);

        let T1 = commit_scalar(t1, params.u, delta_1, params.h_b);
        let T3 = commit_scalar(t3, params.u, delta_3, params.h_b);
        let T4 = commit_scalar(t4, params.u, delta_4, params.h_b);
        let T5 = commit_scalar(t5, params.u, delta_5, params.h_b);
        let T6 = commit_scalar(t6, params.u, delta_6, params.h_b);

        transcript.append_point(b"T1", &T1);
        transcript.append_point(b"T3", &T3);
        transcript.append_point(b"T4", &T4);
        transcript.append_point(b"T5", &T5);
        transcript.append_point(b"T6", &T6);

        let x: G::ScalarField = transcript.get_challenge(b"x");

        let delta = delta(y, &f_l, &f_r);

        let x2 = x * x;
        let x3 = x2 * x;
        let x4 = x3 * x;
        let x5 = x4 * x;
        let x6 = x5 * x;

        let t_x = x * t1 + x2 * (k_c + delta) + x3 * t3 + x4 * t4 + x5 * t5 + x6 * t6;
        let tau_x = x * delta_1 + x3 * delta_3 + x4 * delta_4 + x5 * delta_5 + x6 * delta_6;

        let myu = x * alpha + x2 * beta + x3 * gamma;

        let l_x: Vec<G::ScalarField> = vec_add(
            &vec_add(
                &scalar_vector_mul::<G>(x, &l1),
                &scalar_vector_mul::<G>(x2, &l2),
            ),
            &scalar_vector_mul::<G>(x3, &l3),
        );
        // let r_x = r1 + scalar_vector_mul(x, &r2) + scalar_vector_mul(x3, &r3);

        let r_x: Vec<G::ScalarField> = vec_add(
            &vec_add(&r1, &scalar_vector_mul::<G>(x, &r2)),
            &scalar_vector_mul::<G>(x3, &r3),
        );

        let h_prime: Vec<G> = params
            .h
            .iter()
            .zip(y_pow_inv.iter())
            .map(|(h, y)| *h * *y)
            .collect();

        transcript.append_scalar(b"t_x", t_x);
        transcript.append_scalar(b"tau_x", tau_x);
        transcript.append_scalar(b"myu", myu);

        let w: G::ScalarField = transcript.get_challenge(b"w");
        let u_prime = params.u * w;

        let ipa_proof = prove_ipa(transcript, l_x, r_x, params.g.clone(), h_prime, u_prime);

        Proof {
            A_I,
            A_O,
            S,
            tau_x,
            myu,
            T1,
            T3,
            T4,
            T5,
            T6,
            t_x,
            ipa_proof,
        }
    }

    /// Circuit x*x = y with y = 9 public, but witness x = 2: constraint 0 is FALSE.
    fn false_square_setup() -> (ConstraintMatrices<Fr>, Vec<Fr>, Vec<Fr>, usize) {
        use ark_relations::lc;
        let cs = ConstraintSystem::<Fr>::new_ref();
        let y = cs.new_input_variable(|| Ok(Fr::from(9u64))).unwrap();
        let x = cs.new_witness_variable(|| Ok(Fr::from(2u64))).unwrap();
        cs.enforce_constraint(lc!() + x, lc!() + x, lc!() + y)
            .unwrap();
        cs.finalize();
        assert!(!cs.is_satisfied().unwrap(), "witness should be invalid");
        let mats = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let n = (mats.num_constraints + mats.num_witness_variables).next_power_of_two();
        (
            mats,
            b.instance_assignment.clone(),
            b.witness_assignment.clone(),
            n,
        )
    }

    #[test]
    fn honest_prover_with_false_witness_is_rejected() {
        let (mats, instance, witness, n) = false_square_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();
        let mut tp = Transcript::new(b"r1cs_bp_test");
        let proof = prove::<G1Projective>(&mats, &instance, &witness, &params, &mut rng, &mut tp);
        let mut tv = Transcript::new(b"r1cs_bp_test");
        assert!(!verify::<G1Projective>(
            &mats, &instance, &params, &proof, &mut tv
        ));
    }

    #[test]
    fn planted_u_component_in_a_o_is_rejected() {
        let (mats, instance, witness, n) = false_square_setup();
        let params = make_params(n);
        let mut rng = ark_std::test_rng();
        // gate 0: a_L*a_R - a_O = 2*2 - 9 = -5, independent of all challenges
        let violation = Fr::from(4u64) - Fr::from(9u64);
        let mut tp = Transcript::new(b"r1cs_bp_test");
        let proof = malicious_prove::<G1Projective>(
            violation, &mats, &instance, &witness, &params, &mut rng, &mut tp,
        );
        let mut tv = Transcript::new(b"r1cs_bp_test");
        let accepted = verify::<G1Projective>(&mats, &instance, &params, &proof, &mut tv);
        assert!(
            !accepted,
            "FORGERY: verifier accepted a proof for x*x = 9 with x = 2"
        );
    }
}
