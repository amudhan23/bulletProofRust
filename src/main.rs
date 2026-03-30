use ark_bls12_381::{Fr, G1Projective};
use ark_std::UniformRand;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;


pub trait TranscriptProtocol{
    fn ipa_sep_domain(&mut self, n: u64);
    fn append_point<G: CurveGroup>(&mut self, label: &'static [u8], point: &G);
    fn get_challenge<F: PrimeField>(&mut self, label: &'static [u8]) -> F;
}

impl TranscriptProtocol for Transcript{

    fn ipa_sep_domain(&mut self, n:u64){
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

    let commitment = pederson_commitment(&a, &b, &g_vec, &h_vec, u);

    let mut transcript = Transcript::new(b"Independent_Study_IPA");
    transcript.ipa_sep_domain(n as u64);

    transcript.append_point(b"C", &commitment);

    let x:Fr = transcript.get_challenge(b"x");

    println!("Successfully generated Challenge x: {}", x);

}