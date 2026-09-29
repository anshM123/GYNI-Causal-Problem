import GYNIProof.LowerBound

/-! Axiom check for the conditional build (see `check.sh`). -/

-- general lemmas
#print axioms GYNIProof.trace_formW_of_tp
#print axioms GYNIProof.posSemidef_of_blocks
#print axioms GYNIProof.posSemidef_of_diagDom
#print axioms GYNIProof.posSemidef_of_cert
#print axioms GYNIProof.posSemidef_of_chk
-- the strategy: validity (normalization), instruments, exact value (unconditional)
#print axioms GYNIProof.Wc_normalized
#print axioms GYNIProof.Mc_instrument
#print axioms GYNIProof.gyniValue_eq
-- a kernel-checked block certificate, the block assembly, W ≥ 0 (hypothesis `BigBlocksPSD`)
#print axioms GYNIProof.cert_1_1
#print axioms GYNIProof.cert_0_1
#print axioms GYNIProof.blockPSD_le
#print axioms GYNIProof.Wc_posSemidef
#print axioms GYNIProof.Wc_isProcess
-- main theorems with the hypothesis `BigBlocksPSD`
#print axioms GYNIProof.gyni_lower_bound_exact_of_bigBlocks
#print axioms GYNIProof.gyni_lower_bound_of_bigBlocks
#print axioms GYNIProof.gyni_beats_previous_of_bigBlocks
