use ark_bls12_381::{Fr, G1Projective};
use ark_std::{UniformRand, Zero, One};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;
use ark_ff::Field;
use circuit::CubicCircuit;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer, ConstraintMatrices, Matrix};
use ark_relations::r1cs::ConstraintSystemRef;
mod circuit;

pub trait TranscriptProtocol{
    fn dom_sep(&mut self, n: u64);
    fn append_point<G: CurveGroup>(&mut self, label: &'static [u8], point: &G);
    fn get_challenge<F: PrimeField>(&mut self, label: &'static [u8]) -> F;
}



impl TranscriptProtocol for Transcript{

    fn dom_sep(&mut self, n:u64){
        self.append_message(b"dom-sep", b"NYU_Courant_IPA_v1");
        self.append_u64(b"n", n);
    }

    fn append_point<G:CurveGroup>(&mut self, label: &'static[u8], point : &G){
        let mut bytes = Vec::new();
        point.serialize_compressed(&mut bytes).expect("Serialization failed");
        self.append_message(label, &bytes);
    }

    fn get_challenge<F:PrimeField>(&mut self, label:&'static [u8]) -> F{
        let mut buf = [0u8; 32];
        self.challenge_bytes(label, &mut buf);
        F::from_le_bytes_mod_order(&buf)
    }

}

fn inner_product<F: PrimeField>(a:&[F], b:&[F]) -> F{
    a.iter()
     .zip(b.iter())
     .map(|(a_i, b_i)| *a_i * *b_i)
     .sum()
}



fn hadamard<F: Field>(a: &[F], b:&[F]) -> Vec<F> {
    a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect()
}

fn powers_of<F: Field>(base: F, n: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(n);
    let mut cur = F::one();
    for _ in 0..n {out.push(cur); cur*=base;}
    out
}

fn sparse_matvec<F: Field>(m: &Matrix<F>, z:&[F], num_rows: usize) -> Vec<F> {
    let mut out = vec![F::zero(); num_rows];

    for (i, row) in m.iter().enumerate().take(num_rows) {
        let mut acc = F::zero();
        for(coeff, col) in row {
            acc += *coeff * z[*col];
        }
        out[i] = acc;
    }

    out
}

fn pad_zero<F: Field>(mut v: Vec<F>, new_len: usize) -> Vec<F> {
    v.resize(new_len, F::zero());
    v
}

fn pedersen_vec<G: CurveGroup>(a: &[G::ScalarField], g_vec:&[G])->G {
    debug_assert_eq!(a.len(), g_vec.len());
    a.iter().zip(g_vec).map(|(s, p)| *p * *s).sum()
}

fn pedersen_with_ip<G: CurveGroup>(
    a: &[G::ScalarField],
    b: &[G::ScalarField],
    g_vec: &[G],
    h_vec: &[G],
    u: G,
) -> G {
    let c = inner_product(a, b);
    pedersen_vec(a, g_vec) + pedersen_vec(b, h_vec) + u * c
}


pub struct IpaProof<G: CurveGroup> {
    pub l_vec: Vec<G>,
    pub r_vec: Vec<G>,
    pub a_final: G::ScalarField,
    pub b_final: G::ScalarField,
}


pub fn prove_ipa<G: CurveGroup> (
    transcript: &mut Transcript,
    mut a: Vec<G:: ScalarField>,
    mut b: Vec<G:: ScalarField>,
    mut g_vec: Vec<G>,
    mut h_vec: Vec<G>,
    u: G
 ) ->IpaProof<G> {
    let mut n = a.len();

    let mut l_vec = Vec::new();
    let mut r_vec = Vec::new();


    while n> 1{
        let half = n/2;
        let (a_l, a_r) = a.split_at(half);
        let (b_l, b_r) = b.split_at(half);
        let (g_l, g_r) = g_vec.split_at(half);
        let (h_l, h_r) = h_vec.split_at(half);

        let l = pedersen_with_ip(a_l, b_r, g_r, h_l, u);
        let r = pedersen_with_ip(a_r, b_l, g_l, h_r, u);


        transcript.append_point(b"L", &l);
        transcript.append_point(b"R", &r);

        let x:G::ScalarField = transcript.get_challenge(b"x");
        let x_inv = x.inverse().expect("challenge must be invertible");

        let a_prime: Vec<_> = a_l.iter().zip(a_r.iter()).map(|(al, ar)| *al * x + *ar * x_inv).collect();
        let b_prime: Vec<_> = b_l.iter().zip(b_r.iter()).map(|(bl, br)| *bl * x_inv + *br * x).collect();
        let g_prime: Vec<_> = g_l.iter().zip(g_r.iter()).map(|(gl, gr)| *gl * x_inv + *gr * x).collect();
        let h_prime: Vec<_> = h_l.iter().zip(h_r.iter()).map(|(hl, hr)| *hl * x + *hr * x_inv).collect();

        l_vec.push(l);
        r_vec.push(r);
        a = a_prime;
        b = b_prime;
        g_vec = g_prime;
        h_vec = h_prime;
        n = half;
    }

    IpaProof {
        l_vec,
        r_vec,
        a_final : a[0],
        b_final : b[0],
    }

}

pub fn verify_ipa<G: CurveGroup>(
    transcript: &mut Transcript,
    proof: &IpaProof<G>,
    mut commitment: G,
    mut g_vec: Vec<G>,
    mut h_vec: Vec<G>,
    u: G,
) -> bool{
    let mut n = g_vec.len();

    for(l, r) in proof.l_vec.iter().zip(proof.r_vec.iter()) {

        transcript.append_point(b"L", l);
        transcript.append_point(b"R", r);
        let x = transcript.get_challenge::<G::ScalarField>(b"x");
        let x_inv = x.inverse().unwrap();
        let x_sq = x * x;
        let x_sq_inv = x_inv * x_inv;

        commitment = *l * x_sq + commitment + *r * x_sq_inv;

        let half = n/2;
        let (g_l, g_r) = g_vec.split_at(half);
        let (h_l, h_r) = h_vec.split_at(half);

        g_vec = g_l.iter().zip(g_r).map(|(gl, gr)| *gl * x_inv + *gr * x).collect();
        h_vec = h_l.iter().zip(h_r).map(|(hl, hr)| *hl * x + *hr * x_inv).collect();

        n=half;

    }

    let a = proof.a_final;
    let b = proof.b_final;
    let c = a * b;

    let expected_c = g_vec[0] * a + h_vec[0] * b + u * c;

    commitment == expected_c
}


// fn pederson_commitment<G: CurveGroup>(a:&[G::ScalarField], b:&[G::ScalarField], g_vec: &[G], h_vec: &[G], u:G) -> G{

//     let c = inner_product(a,b);

//     let a_g : G = a.iter()
//                         .zip(g_vec.iter())
//                         .map(|(a_i, g_i)| *g_i * *a_i)
//                         .sum();
    
//     let b_h : G = b.iter()
//                         .zip(h_vec.iter())
//                         .map(|(b_i, h_i)| *h_i * *b_i)
//                         .sum();

//     a_g + b_h + (u*c)                        
// }

pub struct R1csIpaParams<G: CurveGroup> {
    pub g_vec: Vec<G>,
    pub h_vec: Vec<G>,
    pub u:G,
    pub n_pad: usize,
}

pub struct R1csIpaProof<G: CurveGroup> {
    pub v_a: G,
    pub v_b: G,
    pub v_c: G,
    pub ipa: IpaProof<G>,
}

pub fn setup<G: CurveGroup, R: ark_std::rand::Rng> (
    n_pad: usize,
    rng: &mut R
) -> R1csIpaParams<G> {
    assert!(n_pad.is_power_of_two());
    let two_n = 2 * n_pad;
    let g_vec:Vec<G> = (0..two_n).map(|_| G::rand(rng)).collect();
    let h_vec:Vec<G> = (0..two_n).map(|_| G::rand(rng)).collect();
    let u = G::rand(rng);
    R1csIpaParams {g_vec, h_vec, u, n_pad}
}


pub fn prove_r1cs<G: CurveGroup> (
    cs: ConstraintSystemRef<G::ScalarField>,
    params: &R1csIpaParams<G>,
) -> R1csIpaProof<G> {
    
    cs.finalize();
    let matrices: ConstraintMatrices<G::ScalarField> = cs.to_matrices().expect("constraint matrices not available");
    let num_constraints = matrices.num_constraints;

    let cs_borrow = cs.borrow().expect("cs is borrowed");
    let mut z: Vec<G::ScalarField> = cs_borrow.instance_assignment.clone();
    z.extend_from_slice(&cs_borrow.witness_assignment);
    drop(cs_borrow);

    let n_pad = params.n_pad;
    assert!(num_constraints <= n_pad, "n_pad too small");

    let az = pad_zero(sparse_matvec(&matrices.a, &z, num_constraints), n_pad);
    let bz = pad_zero(sparse_matvec(&matrices.b, &z, num_constraints), n_pad);
    let cz = pad_zero(sparse_matvec(&matrices.c, &z, num_constraints), n_pad);

    debug_assert_eq!(hadamard(&az, &bz), cz, "R1CS violated by witness");

    let (g_lo, g_hi) = params.g_vec.split_at(n_pad);
    let (h_lo, _h_hi) = params.h_vec.split_at(n_pad);

    let v_a:G = pedersen_vec(&az, g_lo);
    let v_c:G = pedersen_vec(&cz, g_hi);
    let v_b:G = pedersen_vec(&bz, h_lo);

    let mut transcript = Transcript::new(b"R1CS-IPA");
    transcript.dom_sep((2 * n_pad) as u64);
    transcript.append_point(b"V_A", &v_a);
    transcript.append_point(b"V_B", &v_b);
    transcript.append_point(b"V_C", &v_c);
    let y: G::ScalarField = transcript.get_challenge(b"y");

    let y_pow = powers_of(y,n_pad);
    let y_inv = y.inverse().unwrap();
    let y_pow_inv = powers_of(y_inv, n_pad);

    let mut a_full = az.clone();
    a_full.extend_from_slice(&cz);

    let b_lo: Vec<G::ScalarField> = hadamard(&y_pow, &bz);
    let b_hi: Vec<G::ScalarField> = y_pow.iter().map(|y_i| -*y_i).collect();
    let mut b_full = b_lo;
    b_full.extend_from_slice(&b_hi);

    let (h_lo, h_hi) = params.h_vec.split_at(n_pad);
    let h_lo_rebased: Vec<G> = h_lo
        .iter()
        .zip(&y_pow_inv)
        .map(|(h, y_inv_i)| *h * *y_inv_i)
        .collect();

    let mut h_prime: Vec<G> = h_lo_rebased;
    h_prime.extend_from_slice(h_hi);

    let ipa = prove_ipa::<G>(
        &mut transcript,
        a_full,
        b_full,
        params.g_vec.clone(),
        h_prime,
        params.u,
    );

    R1csIpaProof{v_a, v_b, v_c, ipa}
}

pub fn verify_r1cs<G:CurveGroup>(
    params: &R1csIpaParams<G>,
    proof: &R1csIpaProof<G>,
) -> bool{
    let n_pad = params.n_pad;

    let mut transcript = Transcript::new(b"R1CS-IPA");
    transcript.dom_sep((2 * n_pad) as u64);
    transcript.append_point(b"V_A", &proof.v_a);
    transcript.append_point(b"V_B", &proof.v_b);
    transcript.append_point(b"V_C", &proof.v_c);
    let y: G::ScalarField = transcript.get_challenge(b"y");

    let y_pow = powers_of(y, n_pad);
    let y_inv = y.inverse().unwrap();
    let y_pow_inv = powers_of(y_inv, n_pad);

    let (h_lo, h_hi) = params.h_vec.split_at(n_pad);
    let h_lo_rebased: Vec<G> = h_lo
        .iter()
        .zip(&y_pow_inv)
        .map(|(h, y_inv_i)| *h * *y_inv_i)
        .collect();

    let mut h_prime:Vec<G> = h_lo_rebased;
    h_prime.extend_from_slice(h_hi);

    let h_hi_neg_y_pow:G = h_hi
        .iter()
        .zip(&y_pow)
        .map(|(h, y_i)| *h * (-*y_i))
        .sum();

    let p_initial:G = proof.v_a + proof.v_c + proof.v_b + h_hi_neg_y_pow;

    verify_ipa::<G>(
        &mut transcript,
        &proof.ipa,
        p_initial,
        params.g_vec.clone(),
        h_prime,
        params.u,
    )
}


fn main(){
    let mut rng = ark_std::test_rng();

    {
    let n = 4;
    let mut rng = ark_std::test_rng();
    let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
    let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
    let g_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
    let h_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
    let u: G1Projective = G1Projective::rand(&mut rng);

    let initial = pedersen_with_ip(&a, &b, &g_vec, &h_vec, u);

    let mut t_p = Transcript::new(b"unit-ipa");
    t_p.dom_sep(n as u64);
    let proof = prove_ipa::<G1Projective>(&mut t_p, a, b, g_vec.clone(), h_vec.clone(), u);

    let mut t_v = Transcript::new(b"unit-ipa");
    t_v.dom_sep(n as u64);
    let ok = verify_ipa::<G1Projective>(&mut t_v, &proof, initial, g_vec, h_vec, u);
    println!("[unit IPA] valid = {}", ok);
}

    println!("R1CS");

    let circuit = CubicCircuit {
        x: Some(Fr::from(3u32)),
        out: Fr::from(35u32),
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    println!(" R1CS satisfied : {}", cs.is_satisfied().unwrap());
    println!(" num_constraints : {}", cs.num_constraints());
    println!(" num_instance : {}", cs.num_instance_variables());
    println!(" num_witness: {}", cs.num_witness_variables());


    let n_pad = cs.num_constraints().next_power_of_two().max(2);
    println!(" n_pad :          {} ", n_pad);

    let params = setup::<G1Projective, _>(n_pad, &mut rng);

    let proof = prove_r1cs::<G1Projective>(cs.clone(), &params);
    println!("  IPA recusrion : {} rounds", proof.ipa.l_vec.len());

    let ok = verify_r1cs::<G1Projective>(&params, &proof);
    println!(" verification : {}", ok);
    assert!(ok, "honest proof must verify");

    let mut bad = R1csIpaProof{
        v_a: proof.v_a,
        v_b: proof.v_b,
        v_c: proof.v_c,
        ipa: IpaProof {
            l_vec: proof.ipa.l_vec.clone(),
            r_vec: proof.ipa.r_vec.clone(),
            a_final: proof.ipa.a_final + Fr::one(),
            b_final: proof.ipa.b_final,
        },
    };

    let bad_ok = verify_r1cs::<G1Projective>(&params, &bad);
    println!(" tampered rejected : {}", !bad_ok);
    assert!(!bad_ok, "tampered proof must be rejected");

    let bad_circuit = CubicCircuit {
        x: Some(Fr::from(4u32)),
        out: Fr::from(35u32),
    };

    let cs2 = ConstraintSystem::<Fr>::new_ref();
    bad_circuit.generate_constraints(cs2.clone()).unwrap();
    cs2.finalize();
    println!(" bad-witness sat? :{} ", cs2.is_satisfied().unwrap());

    if cfg!(not(debug_assertions)) {
        let bad_proof = prove_r1cs::<G1Projective>(cs2, &params);
        let bad_ok = verify_r1cs::<G1Projective>(&params, &bad_proof);
        println!(" bad-witness valid: {} (expected false)", bad_ok);
        assert!(!bad_ok);
    }   else {
        println!(" (skipping bad-witness verify run in debug mode - debug_assert would panic!)");
    }

    let _ = bad.ipa.a_final;
}

