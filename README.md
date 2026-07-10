# Bulletproofs over R1CS in Rust

A from-scratch implementation of the [Bulletproofs](https://eprint.iacr.org/2017/1066) zero-knowledge argument system over Rank-1 Constraint Systems (R1CS), built in Rust using the [arkworks](https://arkworks.rs) ecosystem on the BLS12-381 elliptic curve.

This implementation was developed as an independent research project under the supervision of **Prof. Benedikt Bünz** (NYU Courant), one of the original authors of the Bulletproofs paper.

---

## What this proves

Given an arkworks `ConstraintSystem`, the prover produces a zero-knowledge proof of the statement:

```
∃ z : Az ∘ Bz = Cz
```

where `A, B, C` are public R1CS constraint matrices, `z = [instance | witness]` is the extended witness vector, and `∘` is the Hadamard (entrywise) product. The proof reveals nothing about `z` beyond the fact that a satisfying witness exists.

---

## Architecture

The implementation is built in three stages, each a self-contained checkpoint:

### Stage 1 — Inner-Product Argument (IPA)
The recursive halving engine at the core of Bulletproofs. Given a Pedersen commitment to two vectors **a**, **b** and their inner product ⟨**a**, **b**⟩, the IPA proves knowledge of **a**, **b** in O(log n) proof size without sending the vectors directly.

Each round halves the vector length by folding with a Fiat-Shamir challenge `x`:
- `a' = x·a_l + x⁻¹·a_r`
- Generators fold in lockstep: `g' = x⁻¹·g_l + x·g_r`

After log₂(n) rounds, two scalars remain and the verifier checks the final equation directly.

### Stage 2 — R1CS Reduction (sound, non-ZK)
Bridges from arkworks' `ConstraintMatrices` to the inner-product form. The prover commits separately to `Az`, `Bz`, `Cz` on disjoint generator slots (`V_A`, `V_B`, `V_C`). After a Fiat-Shamir challenge `y`, both parties build length-2n vectors:

```
a_full = (Az ‖ Cz)
b_full = (yⁿ ∘ Bz ‖ -yⁿ)
```

so that `⟨a_full, b_full⟩ = ⟨Az ∘ Bz − Cz, yⁿ⟩`, which equals zero iff R1CS is satisfied (with overwhelming probability over `y`, by Schwartz-Zippel). The verifier homomorphically reconstructs the IPA's starting commitment from `V_A`, `V_B`, `V_C` using a rebased generator vector that absorbs the `yⁱ` factors.

### Stage 3 — Zero-Knowledge Layer
Patches the two leaks in Stage 2:

1. **Blind the commitments**: each of `V_A`, `V_B`, `V_C` receives a fresh random blinding scalar on an independent generator `h_b`, making them perfectly hiding.

2. **Blind the IPA inputs**: sample random vectors `s_L`, `s_R` and commit to them in `S`. The IPA runs on `l(x) = a_full + x·s_L` and `r(x) = b_full + x·s_R` — uniformly random vectors, regardless of the witness.

3. **Polynomial identity check**: the inner product `⟨l(x), r(x)⟩ = t₀ + t₁x + t₂x²`. The prover commits to `t₁`, `t₂` in `T_1`, `T_2` before challenge `x` is drawn, then reveals `t̂ = t(x)` and blinding scalars `τ_x`, `μ`. The verifier runs two checks that together force `t₀ = 0`:
   - **Check A**: `t̂·u + τ_x·h_b =? x·T_1 + x²·T_2` — pins `t̂` to "polynomial value with `t₀ = 0`" via DL independence of `u` and `h_b`
   - **Check B**: the IPA, which pins `t̂` to the actual inner product

Both checks pass simultaneously only when `t₀ = 0`, i.e., R1CS is satisfied.

---

## Complexity

From the original Bulletproofs paper (Bünz et al., IEEE S&P 2018):

| Quantity | Complexity |
|---|---|
| Proof size | O(log n) |
| Prover time | O(n) |
| Verifier time | O(n) |

Although the IPA runs log₂(n) rounds, the active vector length halves each round, so total prover work telescopes as `n + n/2 + n/4 + ... ≈ 2n`, which is O(n). The proof size adds 2 group elements per round — 96 bytes per doubling of n_pad on BLS12-381.

---

## Benchmark Results

Measured with `cargo run --release` on a single laptop CPU (single-threaded, no MSM optimization). Each row uses a warm-up run before the measured run.

### PowerCircuit scaling (`x^(k+1) = y`, k constraints)

| Constraints | n\_pad | Prove (ms) | Verify (ms) | Proof (bytes) | IPA rounds |
|---:|---:|---:|---:|---:|---:|
| 3 | 4 | 29.31 | 17.13 | 736 | 3 |
| 15 | 16 | 135.88 | 49.83 | 928 | 5 |
| 63 | 64 | 332.10 | 153.42 | 1120 | 7 |
| 255 | 256 | 1253.53 | 574.75 | 1312 | 9 |
| 1023 | 1024 | 5854.18 | 2490.60 | 1504 | 11 |

### SHA256 preimage (standard ZK benchmark)

| Constraints | n\_pad | Prove (s) | Verify (s) | Proof (bytes) | IPA rounds |
|---:|---:|---:|---:|---:|---:|
| 40,619 | 65,536 | 345.4 | 162.9 | 2,080 | 17 |

SHA256 preimage `"hello"` verified against the standard `sha2` crate output: `2cf24dba...b9824` ✓

Proof size grows by exactly 96 bytes per doubling of n\_pad — one extra IPA round = 2 compressed G1 points. The proof is under 2.1 KB even for a 40,000-constraint circuit.

---

## Project Structure

```
src/
├── main.rs           # Protocol implementation + tests
│   ├── TranscriptProtocol   # Fiat-Shamir helpers (Merlin)
│   ├── prove_ipa / verify_ipa   # Inner-Product Argument
│   ├── prove_r1cs / verify_r1cs # Full ZK R1CS protocol
│   └── setup                    # Public parameter generation
├── circuit.rs        # CubicCircuit: proves x³ + x + 5 = 35
├── circuit_bench.rs  # PowerCircuit: parametric benchmark circuit
└── circuit_sha256.rs # SHA256 preimage circuit (Sha256Gadget)
```

---

## Dependencies

```toml
ark-ff = "0.4.0"
ark-ec = "0.4.0"
ark-std = "0.4.0"
ark-bls12-381 = "0.4.0"
ark-serialize = "0.4.0"
ark-relations = "0.4.0"
ark-crypto-primitives = { version = "0.4", features = ["crh", "r1cs", "sponge"] }
ark-r1cs-std = "0.4"
merlin = "3.0.0"
sha2 = "0.10"
```

| Crate | Role |
|---|---|
| `ark-bls12-381` | BLS12-381 curve — G1 group operations, Fr scalar field |
| `ark-ff`, `ark-ec` | Generic field and curve-group traits (`PrimeField`, `CurveGroup`) |
| `ark-relations` | R1CS constraint system, matrices, synthesizer trait |
| `ark-std` | RNG abstractions, `UniformRand` |
| `ark-serialize` | Compressed serialization of G1 points for the transcript |
| `ark-r1cs-std` | R1CS gadgets — `UInt8`, `Boolean`, equality enforcement |
| `ark-crypto-primitives` | `Sha256Gadget` for the SHA256 benchmark circuit |
| `merlin` | Fiat-Shamir transcript with domain separation |
| `sha2` | Reference SHA256 for cross-validating the in-circuit computation |

---

## Running

```bash
# Full test suite (cubic circuit + ZK checks + soundness checks)
cargo run --release

# Benchmarks (PowerCircuit scaling + SHA256)
# benchmark() is called at the end of main()
cargo run --release
```

> Always use `--release`. Debug mode is 20-50× slower for BLS12-381 arithmetic.

Expected output:

```
[unit IPA] valid = true
R1CS satisfied : true
verification : true
V_A different across runs (hiding works): true
t_hat varies across runs (full ZK works): true
S varies across runs: true
T_1 varies across runs: true
tampered rejected : true

=== Benchmark: ZK Bulletproofs over R1CS ===
constraints    n_pad    prove (ms)    verify (ms)  proof (bytes)   rounds
...
```

---

## Tests

The `main()` function exercises four properties:

| Test | What it checks |
|---|---|
| **Unit IPA** | IPA engine in isolation on random vectors |
| **Honest proof verifies** | Full ZK R1CS protocol end-to-end on a cubic circuit |
| **Hiding** | `V_A`, `S`, `T_1`, `t̂` all differ across runs on the same witness — confirms the ZK layer randomizes the proof |
| **Soundness** | Tampered `a_final` is rejected; unsatisfied witness fails in release mode |

---

## Limitations

This is a research prototype, not a production library:

- **Naive MSM**: multi-scalar multiplications are computed term-by-term. Production implementations use Pippenger's algorithm for ~5-10× speedup.
- **No verifier batching**: the verifier folds generators round-by-round. Deferring to a single end-of-protocol MSM (as in dalek's implementation) would significantly reduce verifier time.
- **Single-threaded**: both prover and verifier are unparallelized.
- **Test RNG**: generators are sampled from `ark_std::test_rng()`. Production deployment requires hash-to-curve generator derivation so no party knows discrete-log relations.
- **No audit**: the implementation has not been reviewed for production security.

---

## References

- Bünz, Bootle, Boneh, Poelstra, Wuille, Maxwell. [Bulletproofs: Short Proofs for Confidential Transactions and More](https://eprint.iacr.org/2017/1066). IEEE S&P 2018.
- Segev. [Bulletproofs for R1CS: Bridging the Completeness-Soundness Gap and a ZK Extension](https://eprint.iacr.org/2025/039). ePrint 2025.
- [arkworks zkSNARK ecosystem](https://arkworks.rs)

---

## Author

Amudhan Muthaiah — Independent research under Prof. Benedikt Bünz, NYU Courant Institute of Mathematical Sciences.
