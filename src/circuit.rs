use ark_ff::PrimeField;
use ark_relations::{
    lc,
r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

#[derive(Clone)]
pub struct CubicCircuit<F: PrimeField>{
    pub x: Option<F>,
    pub out: F,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for CubicCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {

        let out_var = cs.new_input_variable(|| Ok(self.out))?;

        let x_val = self.x.unwrap_or_else(F::zero);
        let x_var = cs.new_witness_variable(|| Ok(x_val))?;

        let x_sq_val = x_val * x_val;
        let x_sq_var = cs.new_witness_variable(|| Ok(x_sq_val))?;
        cs.enforce_constraint(
            lc!() + x_var,
            lc!() + x_var,
            lc!() + x_sq_var
        )?;

        let x_cu_val = x_sq_val * x_val;
        let x_cu_var = cs.new_witness_variable(|| Ok(x_cu_val))?;
        cs.enforce_constraint(
            lc!() + x_sq_var,
            lc!() + x_var,
            lc!() + x_cu_var
        )?;

        let five = F::from(5u32);
        cs.enforce_constraint(
            lc!() + Variable::One,
            lc!() + x_cu_var + x_var + (five, Variable::One),
            lc!() + out_var
        )?;

        Ok(())
    }
}

