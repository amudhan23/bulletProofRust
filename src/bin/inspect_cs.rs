use std::println;

use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_relations::{
    lc,
    r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError, Variable,
    },
};
use ark_std::{One, Zero};

pub struct CubicCircuit<F: PrimeField> {
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
        cs.enforce_constraint(lc!() + x_var, lc!() + x_var, lc!() + x_sq_var)?;

        let x_cu_val = x_sq_val * x_val;
        let x_cu_var = cs.new_witness_variable(|| Ok(x_cu_val))?;
        cs.enforce_constraint(lc!() + x_sq_var, lc!() + x_var, lc!() + x_cu_var)?;

        let five = F::from(5u32);
        cs.enforce_constraint(
            lc!() + Variable::One,
            lc!() + x_cu_var + x_var + (five, Variable::One),
            lc!() + out_var,
        )?;

        Ok(())
    }
}

fn main() {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let circuit = CubicCircuit {
        x: Some(Fr::from(3u32)),
        out: Fr::from(35u32),
    };
    circuit.generate_constraints(cs.clone()).unwrap();

    println!("num_constraints : {}", cs.num_constraints());
    println!("num_instance_variables: {}", cs.num_instance_variables());
    println!("num_witness_variables: {}", cs.num_witness_variables());

    let matrices = cs.to_matrices().unwrap();

    println!("matrics : {:?}", matrices);

    for (name, mat) in [("A", &matrices.a), ("B", &matrices.b), ("C", &matrices.c)] {
        println!("\n{}:", name);
        for (i, row) in mat.iter().enumerate() {
            println!("  row {}: {:?}", i, row);
        }
    }
}
