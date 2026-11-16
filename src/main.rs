use bulletproofs_ipa::circuit::CubicCircuit;
use bulletproofs_ipa::circuit_bench::PowerCircuit;
use bulletproofs_ipa::circuit_sha256::Sha256Circuit;
use bulletproofs_ipa::*;

use ark_bls12_381::{Fr, G1Projective};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, Matrix};
use ark_serialize::CanonicalSerialize;
use ark_std::{One, UniformRand, Zero};
use merlin::Transcript;
use sha2::Sha256;
use sha2::{Digest, Sha256 as Sha256Hasher};
use std::time::Instant;

fn test_sha256() {
    println!("\n=== SHA256 single-proof test ===");
    let mut rng = ark_std::test_rng();

    // Small fixed preimage for testing
    let preimage = b"hello".to_vec();

    // Compute reference SHA256 using the sha2 crate (outside the circuit)
    let expected_hash: Vec<u8> = {
        let mut h = Sha256Hasher::new();
        h.update(&preimage);
        h.finalize().to_vec()
    };
    println!(" preimage: {:?}", String::from_utf8_lossy(&preimage));
    println!(
        " expected hash (hex): {}",
        expected_hash
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<String>()
    );

    let circuit = Sha256Circuit::<Fr> {
        preimage,
        expected_hash,
        _phantom: std::marker::PhantomData,
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let num_constraints = cs.num_constraints();
    println!(" R1CS constraints: {}", num_constraints);
    assert!(cs.is_satisfied().unwrap(), "SHA256 circuit not satisfied");

    let n_pad = num_constraints.next_power_of_two().max(2);
    println!(" n_pad: {}", n_pad);

    println!(" Generating parameters...");
    let setup_start = Instant::now();
    let params = setup::<G1Projective>(n_pad);
    println!(" Setup: {:.2} s", setup_start.elapsed().as_secs_f64());

    println!(" Proving...");
    let prove_start = Instant::now();
    let proof = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    let prove_elapsed = prove_start.elapsed();
    println!(" Prove: {:.2} s", prove_elapsed.as_secs_f64());

    println!(" Verifying...");
    let verify_start = Instant::now();
    let ok = verify_r1cs::<G1Projective>(&params, &proof);
    let verify_elapsed = verify_start.elapsed();
    println!(" Verify: {:.2} s", verify_elapsed.as_secs_f64());

    assert!(ok, "SHA256 proof must verify");

    let rounds = proof.ipa.l_vec.len();
    let proof_bytes = 6 * 48 + 3 * 32 + 2 * rounds * 48 + 2 * 32;
    println!(" Proof size: {} bytes ({} IPA rounds)", proof_bytes, rounds);
    println!(" Verification: {}", ok);
}

fn benchmark() {
    println!("\n=== Benchmark: ZK Bulletproofs over R1CS ===");
    println!(
        "{:>10} {:>8} {:>14} {:>14} {:>14} {:>8}",
        "constraints", "n_pad", "prove (ms)", "verify (ms)", "proof (bytes)", "rounds"
    );
    println!("{}", "-".repeat(78));

    let sizes = [3, 15, 63, 255, 1023];

    for &num_mults in &sizes {
        let mut rng = ark_std::test_rng();

        let x_val = Fr::from(2u32);
        let mut y_val = x_val;
        for _ in 0..num_mults {
            y_val *= x_val;
        }

        let circuit = PowerCircuit {
            x: Some(x_val),
            y: y_val,
            num_mults,
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();

        assert!(
            cs.is_satisfied().unwrap(),
            "circuit not satisfied at num_mults={}",
            num_mults
        );

        let actual_constraints = cs.num_constraints();
        let n_pad = actual_constraints.next_power_of_two().max(2);
        let params = setup::<G1Projective>(n_pad);

        let _ = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);

        let prove_start = Instant::now();
        let proof = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
        let prove_elapsed = prove_start.elapsed();

        let verify_start = Instant::now();
        let ok = verify_r1cs::<G1Projective>(&params, &proof);
        let verify_elapsed = verify_start.elapsed();

        assert!(ok, "honest proof must verify at num_mults={}", num_mults);

        let rounds = proof.ipa.l_vec.len();
        let proof_bytes = 6 * 48 + 3 * 32 + 2 * rounds * 48 + 2 * 32;

        println!(
            "{:>10} {:>8} {:>14.2} {:>14.2} {:>14} {:>8}",
            actual_constraints,
            n_pad,
            prove_elapsed.as_secs_f64() * 1000.0,
            verify_elapsed.as_secs_f64() * 1000.0,
            proof_bytes,
            rounds
        );
    }
    println!("{}", "-".repeat(78));
    println!("Notes:");
    println!("  - Run with `cargo run --release` for representative timings.");
    println!("  - Proof size grows as O(log n) — Bulletproofs' headline feature.");
    println!("  - Prover/verifier scale linearly with circuit size.");
}

fn main() {
    let mut rng = ark_std::test_rng();

    {
        let n = 4;
        let mut rng = ark_std::test_rng();
        let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let g_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let h_vec: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let u: G1Projective = G1Projective::rand(&mut rng);

        let initial = pedersen_with_ip(&a, &b, &g_vec, &h_vec, u);

        let mut t_p = Transcript::new(b"unit-ipa");
        t_p.dom_sep(n as u64);
        let proof = prove_ipa::<G1Projective>(&mut t_p, a, b, g_vec.clone(), h_vec.clone(), u);

        let mut t_v = Transcript::new(b"unit-ipa");
        t_v.dom_sep(n as u64);
        let ok = verify_ipa::<G1Projective>(&mut t_v, &proof, initial, g_vec, h_vec, u);
        println!("[unit IPA] valid = {}", ok);
    }

    println!("R1CS");

    let circuit = CubicCircuit {
        x: Some(Fr::from(3u32)),
        out: Fr::from(35u32),
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    println!(" R1CS satisfied : {}", cs.is_satisfied().unwrap());
    println!(" num_constraints : {}", cs.num_constraints());
    println!(" num_instance : {}", cs.num_instance_variables());
    println!(" num_witness: {}", cs.num_witness_variables());

    let n_pad = cs.num_constraints().next_power_of_two().max(2);
    println!(" n_pad :          {} ", n_pad);

    let params = setup::<G1Projective>(n_pad);

    let proof = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    println!("  IPA recusrion : {} rounds", proof.ipa.l_vec.len());

    let ok = verify_r1cs::<G1Projective>(&params, &proof);
    println!(" verification : {}", ok);
    assert!(ok, "honest proof must verify");

    let proof1 = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    let proof2 = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    println!(
        " V_A different across runs (hiding works): {}",
        proof1.v_a != proof2.v_a
    );

    let proof_a = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    let proof_b = prove_r1cs::<G1Projective, _>(cs.clone(), &params, &mut rng);
    println!(
        " t_hat varies across runs (full ZK works): {}",
        proof_a.t_hat != proof_b.t_hat
    );
    println!(
        " S varies across runs:                      {}",
        proof_a.s != proof_b.s
    );
    println!(
        " T_1 varies across runs:                    {}",
        proof_a.t1_commit != proof_b.t1_commit
    );

    let mut bad = R1csIpaProof {
        v_a: proof.v_a,
        v_b: proof.v_b,
        v_c: proof.v_c,
        s: proof.s,
        t1_commit: proof.t1_commit,
        t2_commit: proof.t2_commit,
        t_hat: proof.t_hat,
        tau_x: proof.tau_x,
        mu: proof.mu,
        ipa: IpaProof {
            l_vec: proof.ipa.l_vec.clone(),
            r_vec: proof.ipa.r_vec.clone(),
            a_final: proof.ipa.a_final + Fr::one(),
            b_final: proof.ipa.b_final,
        },
    };

    let bad_ok = verify_r1cs::<G1Projective>(&params, &bad);
    println!(" tampered rejected : {}", !bad_ok);
    assert!(!bad_ok, "tampered proof must be rejected");

    let bad_circuit = CubicCircuit {
        x: Some(Fr::from(4u32)),
        out: Fr::from(35u32),
    };

    let cs2 = ConstraintSystem::<Fr>::new_ref();
    bad_circuit.generate_constraints(cs2.clone()).unwrap();
    cs2.finalize();
    println!(" bad-witness sat? :{} ", cs2.is_satisfied().unwrap());

    if cfg!(not(debug_assertions)) {
        let bad_proof = prove_r1cs::<G1Projective, _>(cs2, &params, &mut rng);
        let bad_ok = verify_r1cs::<G1Projective>(&params, &bad_proof);
        println!(" bad-witness valid: {} (expected false)", bad_ok);
        assert!(!bad_ok);
    } else {
        println!(" (skipping bad-witness verify run in debug mode - debug_assert would panic!)");
    }

    let _ = bad.ipa.a_final;

    test_sha256();
    benchmark();
}
