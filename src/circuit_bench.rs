use ark_ff::PrimeField;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};

#[derive(Clone)]
pub struct PowerCircuit<F: PrimeField> {
    pub x: Option<F>,
    pub y: F,               
    pub num_mults: usize,   
}

impl<F: PrimeField> ConstraintSynthesizer<F> for PowerCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let y_var = cs.new_input_variable(|| Ok(self.y))?;

        let x_val = self.x.unwrap_or_else(F::zero);
        let x_var = cs.new_witness_variable(|| Ok(x_val))?;

        let mut prev_var = x_var;
        let mut prev_val = x_val;

        for i in 1..=self.num_mults {
            let new_val = prev_val * x_val;

            let new_var = if i == self.num_mults {
                y_var
            } else {
                cs.new_witness_variable(|| Ok(new_val))?
            };

            cs.enforce_constraint(
                lc!() + prev_var,
                lc!() + x_var,
                lc!() + new_var,
            )?;

            prev_var = new_var;
            prev_val = new_val;
        }

        Ok(())
    }
}