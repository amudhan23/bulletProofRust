use ark_bls12_381::Fr;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintMatrices;
use ark_std::rand::Rng;
use merlin::Transcript;

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
    pedersen_vectors(a, g) + pedersen_vectors(b, h) + alpha * h_blind
}

pub fn commit_vector<G: CurveGroup>(
    a: &Vec<G::ScalarField>,
    g: &Vec<G>,
    alpha: G::ScalarField,
    h_blind: G,
) -> G {
    pedersen_vectors(a, g) + alpha * h_blind
}

pub fn commit_scalar<G: CurveGroup>(a: G::ScalarField, g: G, b: G::ScalarField, h_blind: G) -> G {
    a * g + b * h_blind
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

fn vec_sub<G: CurveGroup>(a: &[G::ScalarField], b: &[G::ScalarField]) -> Vec<G::ScalarField> {
    a.iter().zip(b).map(|(x, y)| *x - *y).collect()
}

pub fn prove<G: CurveGroup>(
    mats: &ConstraintMatrices<Fr>,
    instance: &[G::ScalarField],
    witness: &[G::ScalarField],
    params: &ProofParams<G>,
    rng: &mut impl Rng,
    transcript: &mut Transcript,
) -> Proof<G> {
    let mut ac = ArithCircuit::convert_to_wiring_constraint(mats, instance);
    let mut z = instance.to_vec();
    z.extend_from_slice(witness);
    let (a_l, a_r, a_o) = assign(mats, &z);
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

    let y = transcript.get_challenge(b"y");
    let z_chal: G::ScalarField = transcript.get_challenge(b"z");

    let q = 3 * ac.num_constraints + ac.num_witness_variables;

    let z_chal_powers = powers_of_starts_base(z_chal, q);

    let (f_l, f_r, f_o, _, k_c) = ac.convert_to_f_vectors(&z_chal_powers);

    let y_inv = y.inverse().unwrap();
    let y_pow = powers_of(y, params.n);
    let y_pow_inv = powers_of(y_inv, params.n);

    let l1 = vec_add(&a_l, &hadamard(&y_pow_inv, &f_r));
    let l2 = a_o.clone();
    let l3 = s_l.clone();

    let r1 = vec_sub(&f_o, &y_pow);
    let r2 = vec_add(&hadamard(&y_pow, &a_r), &f_l);
    let r3 = hadamard(&y_pow, &s_r);

    let t1 = inner_product(&l1, &r1);
    let t3 = inner_product(&l2, &r2) + inner_product(&l3, &r1);
    let t4 = inner_product(&l3, &r2) + inner_product(&l1, &r3);
    let t5 = inner_product(&l2, &r3);
    let t6 = inner_product(&l3, &r3);

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
    let delta_X = x * delta_1 + x3 * delta_3 + x4 * delta_4 + x5 * delta_5 + x6 * delta_6;

    let myu = x * alpha + x2 * beta + x3 * gamma;
}
