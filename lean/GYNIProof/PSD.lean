import GYNIProof.BlockCerts

/-!
# `W` is a valid process matrix

Every block `(cA, cB)` (Alice's class `cA`, Bob's class `cB`) of `W` is `2^{-71}` times a
submatrix of the integer block `blockA cA cB` (`cA ≤ cB`, `BlockCerts.lean`), or the party swap of
such a block (`WintF_swap`). Together with block diagonality (`WintF_zero`) this gives `W ≥ 0`
(`posSemidef_of_blocks`); the normalization is `Wc_normalized` (unconditional).
All blocks except the three `256 × 256` blocks in `BigBlocksPSD` are kernel-checked.
-/

namespace GYNIProof

open Matrix
open scoped ComplexOrder

/-- Row-major index of `(p₁, p₂)` in the block `(cA, cB)`. -/
def lin (cA cB : Fin 26) (p : Fin (sz cA) × Fin (sz cB)) : Fin (szN cA.val * szN cB.val) :=
  ⟨p.2.val + szN cB.val * p.1.val, by
    obtain ⟨⟨p1, h1⟩, ⟨p2, h2⟩⟩ := p
    simp only [sz] at h1 h2 ⊢
    calc p2 + szN cB.val * p1 < szN cB.val + szN cB.val * p1 := by omega
      _ = szN cB.val * (p1 + 1) := by ring
      _ ≤ szN cB.val * szN cA.val := Nat.mul_le_mul_left _ h1
      _ = szN cA.val * szN cB.val := Nat.mul_comm _ _⟩

lemma lin_div (cA cB : Fin 26) (p : Fin (sz cA) × Fin (sz cB)) :
    (lin cA cB p).val / szN cB.val = p.1.val := by
  have h2 := p.2.2
  simp only [sz] at h2
  simp only [lin]
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h2, zero_add]

lemma lin_mod (cA cB : Fin 26) (p : Fin (sz cA) × Fin (sz cB)) :
    (lin cA cB p).val % szN cB.val = p.2.val := by
  have h2 := p.2.2
  simp only [sz] at h2
  simp only [lin]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- The block of `W` in the classes `(cA, cB)`. -/
noncomputable def blkW (cA cB : Fin 26) :
    Matrix (Fin (sz cA) × Fin (sz cB)) (Fin (sz cA) × Fin (sz cB)) ℂ :=
  Matrix.of fun p q => Wc (ePt ⟨cA, p.1⟩, ePt ⟨cB, p.2⟩) (ePt ⟨cA, q.1⟩, ePt ⟨cB, q.2⟩)

theorem blkW_psd_le (hbig : BigBlocksPSD) (cA cB : Fin 26) (h : cA.val ≤ cB.val) :
    (blkW cA cB).PosSemidef := by
  have hB := blockPSD_le hbig cA.val cB.val h cB.2
  unfold BlockPSD at hB
  have hS := (hB.submatrix (lin cA cB)).smul (show (0 : ℝ) ≤ ((2 : ℝ) ^ 71)⁻¹ by positivity)
  convert hS using 1
  ext p q
  simp only [blkW, Matrix.of_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Wc_apply, blockA, lin_div, lin_mod, ePt_apply, Complex.real_smul]
  push_cast
  ring

theorem blkW_psd (hbig : BigBlocksPSD) (cA cB : Fin 26) : (blkW cA cB).PosSemidef := by
  by_cases h : cA.val ≤ cB.val
  · exact blkW_psd_le hbig cA cB h
  · have h' := (blkW_psd_le hbig cB cA (by omega)).submatrix
      (Prod.swap : Fin (sz cA) × Fin (sz cB) → Fin (sz cB) × Fin (sz cA))
    convert h' using 1
    ext p q
    simp only [blkW, Matrix.of_apply, Matrix.submatrix_apply, Prod.fst_swap, Prod.snd_swap,
      Wc_apply, WintF_swap]

/-- `W ≥ 0`, given the three `256 × 256` blocks. -/
theorem Wc_posSemidef (hbig : BigBlocksPSD) : Wc.PosSemidef := by
  refine posSemidef_of_blocks ePt Wc Wc_isHermitian (fun s t s' t' h => ?_) (blkW_psd hbig)
  rw [Wc_apply, WintF_zero]
  · simp
  · simp only [clsN_ePt]
    rcases h with h | h
    · exact Or.inl fun e => h (Fin.ext e)
    · exact Or.inr fun e => h (Fin.ext e)

/-- `W` is a valid process matrix, given the three `256 × 256` blocks. -/
theorem Wc_isProcess (hbig : BigBlocksPSD) : IsProcess Wc :=
  ⟨Wc_posSemidef hbig, fun M N hM hN => Wc_normalized M N hM.2 hN.2⟩

end GYNIProof
