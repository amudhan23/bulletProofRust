use ark_ff::PrimeField;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

#[derive(Clone)]
pub struct SquareCircuit<F: PrimeField> {
    pub x: Option<F>,
    pub out: F,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for SquareCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let out_var = cs.new_input_variable(|| Ok(self.out))?;

        let x_val = self.x.unwrap_or_else(F::zero);
        let x_var = cs.new_witness_variable(|| Ok(x_val))?;

        let x_sq_val = x_val * x_val;
        let x_sq_var = cs.new_witness_variable(|| Ok(x_sq_val))?;
        cs.enforce_constraint(lc!() + x_var, lc!() + x_var, lc!() + x_sq_var)?;

        let six = F::from(6u32);
        cs.enforce_constraint(
            lc!() + Variable::One,
            lc!() + x_sq_var + x_var + (six, Variable::One),
            lc!() + out_var,
        )?;

        Ok(())
    }
}
