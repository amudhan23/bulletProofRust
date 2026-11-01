use std::vec;

use ark_bls12_381::Fr;
use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::ConstraintMatrices;
use ark_std::rand::Rng;
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;

use crate::{IpaProof, prove_ipa, verify_ipa};
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

struct Proof<G: CurveGroup> {
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
    transcript: &mut Transcript,
) -> Proof<G> {
    let ac = ArithCircuit::convert_to_wiring_constraint(mats, instance);
    let mut z = instance.to_vec();
    z.extend_from_slice(witness);
    let (a_l, a_r, a_o) = assign::<G>(mats, &z);
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
        .zip(y_pow.iter())
        .map(|(h, y)| *h * *y)
        .collect();

    let ipa_proof = prove_ipa(transcript, l_x, r_x, params.g.clone(), h_prime, params.u);

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
    proof: &Proof<G>,
    transcript: &mut Transcript,
) -> bool {
    let ac = ArithCircuit::convert_to_wiring_constraint(mats, instance);

    transcript.append_point(b"Com_A_I", &proof.A_I);
    transcript.append_point(b"Com_A_O", &proof.A_O);
    transcript.append_point(b"Com_S", &proof.S);

    let y: G::ScalarField = transcript.get_challenge(b"y");
    let z_chal: G::ScalarField = transcript.get_challenge(b"z");

    let q = 3 * ac.num_constraints + ac.num_witness_variables;

    let z_chal_powers = powers_of_starts_base(z_chal, q);

    let (f_l, f_r, f_o, _, k_c) = ac.convert_to_f_vectors(&z_chal_powers);

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

    let t_lhs = params.u * proof.t_x + params.h_b * proof.tau_x;
    let t_rhs = proof.T1 * x
        + params.u * x2 * (delta + k_c)
        + proof.T3 * x3
        + proof.T4 * x4
        + proof.T5 * x5
        + proof.T6 * x6;

    if (t_lhs != t_rhs) {
        return false;
    }

    let h_prime: Vec<G> = params
        .h
        .iter()
        .zip(y_pow.iter())
        .map(|(h, y)| *h * *y)
        .collect();

    let x_public_term = (vec_gen_prod(&vecs_hadamard_prod(&y_pow_inv, &f_r), &params.g) * x
        + vec_gen_prod(&f_l, &h_prime));
    let constant_term = vec_gen_prod(&vec_sub(&f_o, &y_pow), &h_prime);

    let P = proof.A_I * x + proof.A_O * x2 + proof.S * x3 - params.h_b * proof.myu
        + x_public_term
        + constant_term
        + params.u * proof.t_x;

    verify_ipa(
        transcript,
        &proof.ipa_proof,
        P,
        params.g.clone(),
        h_prime,
        params.u,
    )
}
