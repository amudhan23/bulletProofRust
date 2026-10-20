use crate::square_circuit::SquareCircuit;

use super::*;

fn cubic_cs(x: u32, out: u32) -> ConstraintSystemRef<Fr> {
    let circuit = CubicCircuit {
        x: Some(Fr::from(x)),
        out: Fr::from(out),
    };
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    cs
}

fn square_cs(x: u32, out: u32) -> ConstraintSystemRef<Fr> {
    let circuit = SquareCircuit {
        x: Some(Fr::from(x)),
        out: Fr::from(out),
    };
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    cs
}

#[test]
fn forgery_wrong_statement_accepted() {
    let mut rng = ark_std::test_rng();
    let cs = cubic_cs(4, 73);
    assert!(cs.is_satisfied().unwrap());
    let n_pad = cubic_cs(3, 35).num_constraints().next_power_of_two().max(2);
    let params = setup::<G1Projective, _>(n_pad, &mut rng);
    let proof = prove_r1cs::<G1Projective, _>(cs, &params, &mut rng);
    assert!(verify_r1cs::<G1Projective>(&params, &proof));
}

#[test]
fn forgery_wrong_circuit_accepted() {
    let mut rng = ark_std::test_rng();
    let n_pad = cubic_cs(3, 35).num_constraints().next_power_of_two().max(2);
    let params = setup::<G1Projective, _>(n_pad, &mut rng);

    let cs = square_cs(4, 26);
    assert!(cs.is_satisfied().unwrap());
    let proof = prove_r1cs::<G1Projective, _>(cs, &params, &mut rng);
    assert!(verify_r1cs::<G1Projective>(&params, &proof));
}
