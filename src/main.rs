use ark_bls12_381::{Fr, G1Projective};
use ark_ec::Group;
use ark_std::UniformRand;

fn pederson_commitment(v:Fr, r:Fr, g:G1Projective, h:G1Projective) -> G1Projective{
    (g*v) + (h*r)
}

fn main(){
    let mut rng = ark_std::test_rng();

    let g = G1Projective::generator();

    let h = G1Projective::rand(&mut rng);

    let v = Fr::from(5u32);
    let r = Fr::rand(&mut rng);

    // let commitment = pederson_commitment(v,r,g,h);

    println!("Successfully commited {}", pederson_commitment(v,r,g,h));
}