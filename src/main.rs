use ark_bls12_381::{Fr, G1Projective};
use ark_ec::Group;
use ark_std::UniformRand;

fn inner_product(a:&[Fr], b:&[Fr]) -> Fr{
    a.iter()
     .zip(b.iter())
     .map(|(a_i, b_i)| *a_i * *b_i)
     .sum()
}

fn pederson_commitment(a:&[Fr], b:&[Fr], g_vec: &[G1Projective], h_vec: &[G1Projective], u:G1Projective) -> G1Projective{

    let c = inner_product(a,b);

    let a_g : G1Projective = a.iter()
                                .zip(g_vec.iter())
                                .map(|(a_i, g_i)| *g_i * *a_i)
                                .sum();
    
    let b_h : G1Projective = b.iter()
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