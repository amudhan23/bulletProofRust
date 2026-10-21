use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
    SynthesisError,
};

pub type SparseRow<F> = Vec<(usize, F)>;

pub struct ArithCircuit<F: PrimeField> {
    pub num_constraints: usize,
    pub num_instance_variables: usize, // instance variables
    pub num_witness_variables: usize,  // witness variables
    pub w_l: Vec<SparseRow<F>>,
    pub w_r: Vec<SparseRow<F>>,
    pub w_o: Vec<SparseRow<F>>,
    pub w_v: Vec<SparseRow<F>>,
    pub c_pub: Vec<F>,
}

impl<F: PrimeField> ArithCircuit<F> {
    fn convert_to_wiring_constraint(mats: &ConstraintMatrices<F>, instance: &[F]) -> Self {
        let num_constraints = mats.num_constraints;
        let num_witness_variables = mats.num_witness_variables;
        let num_instance_variables = mats.num_instance_variables;
        let total_rows = 3 * num_constraints;

        let mut w_l: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_r: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_o: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut w_v: Vec<SparseRow<F>> = vec![Vec::new(); total_rows];
        let mut c_pub: Vec<F> = vec![F::zero(); total_rows];

        for i in 0..num_constraints {
            let rows = [3 * i, 3 * i + 1, 3 * i + 2];
            w_l[rows[0]].push((i, F::one()));
            w_r[rows[1]].push((i, F::one()));
            w_o[rows[2]].push((i, F::one()));

            for (k, mat) in [&mats.a, &mats.b, &mats.c].into_iter().enumerate() {
                for &(coeff, col) in &mat[i] {
                    if (col < num_instance_variables) {
                        c_pub[rows[k]] += coeff * instance[col];
                    } else {
                        w_v[rows[k]].push((col - num_instance_variables, F::one()));
                    }
                }
            }
        }

        Self {
            num_constraints,
            num_instance_variables,
            num_witness_variables,
            w_l,
            w_r,
            w_o,
            w_v,
            c_pub,
        }
    }
}
