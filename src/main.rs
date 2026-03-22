use ark_bls12_381::{Fr, G1Projective};
use ark_std::UniformRand;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;

fn inner_product<F: PrimeField>(a:&[F], b:&[F]) -> F{
    a.iter()
     .zip(b.iter())
     .map(|(a_i, b_i)| *a_i * *b_i)
     .sum()
}

fn pederson_commitment<G: CurveGroup>(a:&[G::ScalarField], b:&[G::ScalarField], g_vec: &[G], h_vec: &[G], u:G) -> G{

    let c = inner_product(a,b);

    let a_g : G = a.iter()
                        .zip(g_vec.iter())
                        .map(|(a_i, g_i)| *g_i * *a_i)
                        .sum();
    
    let b_h : G = b.iter()
                        .zip(h_vec.iter())
                        .map(|(b_i, h_i)| *h_i * *b_i)
                        .sum();

    a_g + b_h + (u*c)                        
}

fn main(){
    let mut rng = ark_std::test_rng();

    let n=4;

    let a:Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
    let b:Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

    let g_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
    let h_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();

    let u:G1Projective = G1Projective::rand(&mut rng);

    println!("Pedersen commitment: {}", pederson_commitment(&a, &b, &g_vec, &h_vec, u));
}