use ark_ff::PrimeField;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::uint8::UInt8;
use ark_crypto_primitives::crh::{
    sha256::{constraints::{Sha256Gadget, UnitVar}, Sha256},
    CRHSchemeGadget,
};

#[derive(Clone)]
pub struct Sha256Circuit<F: PrimeField> {
    pub preimage: Vec<u8>,           
    pub expected_hash: Vec<u8>,      
    pub _phantom: std::marker::PhantomData<F>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256Circuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {

        let preimage_var: Vec<UInt8<F>> =
            UInt8::new_witness_vec(ark_relations::ns!(cs, "preimage"), &self.preimage)?;

        let expected_hash_var: Vec<UInt8<F>> =
            UInt8::new_input_vec(ark_relations::ns!(cs, "expected_hash"), &self.expected_hash)?;


        let unit_var = UnitVar::default();
        let computed_hash_var =
            <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unit_var, &preimage_var)?;

        computed_hash_var.0.enforce_equal(&expected_hash_var)?;

        Ok(())
    }
}