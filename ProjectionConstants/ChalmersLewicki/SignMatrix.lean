/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Absolute
import ProjectionConstants.Matrix.SignMatrix

/-!
# The formula of Chalmers and Lewicki in terms of sign matrices

For a real matrix `P` and weights `tᵢ ≥ 0`, the sum `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` is the maximum of
`Tr(√D S √D P) = ∑ᵢⱼ tᵢ tⱼ Sᵢⱼ Pᵢⱼ` over the sign matrices `S`, where `D = diag(tᵢ²)`; the
maximum is attained at the sign pattern of `P`. Together with the formula of Chalmers and Lewicki
[CL] (`maxRelProjConst_eq_clConst`), this gives the formulation of [JFA, Theorem 2.1]:

`λ_ℝ(n, d) = max { kyFanSum n (√D S √D) : S ∈ 𝒮_d, D ∈ 𝒟_d }`,

where `𝒮_d` is the set of `d × d` sign matrices (`IsSignMatrix`), `𝒟_d` is the set of diagonal
matrices `D = diag(w)` with `w ≥ 0` and `Tr D = 1` (`IsWeight w`), `√D S √D = weightedSign S w`,
and `kyFanSum n A` is the supremum of `Tr(AP)` over the orthogonal projections `P` of rank `n`
(for symmetric `A`, the sum of the `n` largest eigenvalues of `A`). Taking the supremum over `d`
gives `λ_ℝ(n)`. In the notation of [JFA], `λ_ℝ(n, d) = Π(n, d)` and `λ_ℝ(n) = Π_n`.

## Main definitions

* `signPattern P`: the matrix of the signs of the entries of `P`, with the convention `sgn 0 = 1`.
* `signMatrixValues n`: the values `kyFanSum n (√D S √D)` over all dimensions `d`, all
  `S ∈ 𝒮_d` and all `D ∈ 𝒟_d`.

## Main statements

* `kyFanSum_weightedSign_le_maxRelProjConst`, `maxRelProjConst_real_le`: the formula for
  `λ_ℝ(n, d)`.
* `maxProjConst_real_eq_sSup`: the formula `λ_ℝ(n) = sup (signMatrixValues n)`.
* `kyFanSum_weightedSign_le_maxProjConst`, `exists_lt_kyFanSum_weightedSign`: the two halves of
  this formula, in the form in which they are used.

## References

* [CL] B. L. Chalmers, G. Lewicki, *A proof of the Grünbaum conjecture*.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
-/

open Finset Matrix

namespace ProjectionConstants

variable {ι : Type*}

/-- The sign pattern of a real matrix, with the convention `sgn 0 = 1`. -/
noncomputable def signPattern (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  of fun i j ↦ if 0 ≤ P i j then 1 else -1

lemma signPattern_mul_self (P : Matrix ι ι ℝ) (i j : ι) : signPattern P i j * P i j = |P i j| := by
  simp only [signPattern, of_apply]
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.1 h)]

variable [Fintype ι]

/-- The sign pattern of an orthogonal projection is a sign matrix: it is symmetric, and its
diagonal entries are `1` since `Pᵢᵢ ≥ 0`. -/
lemma isSignMatrix_signPattern {P : Matrix ι ι ℝ} (hP : IsStarProjection P) :
    IsSignMatrix (signPattern P) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i ↦ ?_⟩
  · simp [signPattern, hP.apply_comm i j]
  · simp only [signPattern, of_apply]
    split_ifs <;> simp
  · simp [signPattern, hP.diag_nonneg i]

lemma IsWeight.isUnitWeight_sqrt {w : ι → ℝ} (hw : IsWeight w) : IsUnitWeight fun i ↦ √(w i) :=
  ⟨fun _ ↦ Real.sqrt_nonneg _, by simp [Real.sq_sqrt (hw.nonneg _), hw.sum_eq]⟩

lemma IsUnitWeight.isWeight_sq {t : ι → ℝ} (ht : IsUnitWeight t) : IsWeight fun i ↦ t i ^ 2 :=
  ⟨fun _ ↦ sq_nonneg _, ht.sum_sq⟩

/-- `Tr(√D S √D P) ≤ ∑ᵢⱼ √wᵢ √wⱼ |Pᵢⱼ|` for a sign matrix `S` and `D = diag(w)`. -/
lemma frobeniusInner_weightedSign_le_weightedAbsSum {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (w : ι → ℝ) (P : Matrix ι ι ℝ) :
    frobeniusInner (weightedSign S w) P ≤ weightedAbsSum (fun i ↦ √(w i)) P := by
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
  rw [weightedSign_apply, Real.norm_eq_abs]
  have h : S i j * P i j ≤ |P i j| := by
    rcases hS.pm i j with h | h
    · rw [h, one_mul]
      exact le_abs_self _
    · rw [h, neg_one_mul]
      exact neg_le_abs _
  calc √(w i) * S i j * √(w j) * P i j = √(w i) * √(w j) * (S i j * P i j) := by ring
    _ ≤ √(w i) * √(w j) * |P i j| := by gcongr

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = Tr(√D S √D P)` for `D = diag(tᵢ²)` and the sign pattern `S` of `P`. -/
lemma weightedAbsSum_eq_frobeniusInner {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (P : Matrix ι ι ℝ) :
    weightedAbsSum t P = frobeniusInner (weightedSign (signPattern P) fun i ↦ t i ^ 2) P := by
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [weightedSign_apply, Real.sqrt_sq (ht i), Real.sqrt_sq (ht j), Real.norm_eq_abs,
    ← signPattern_mul_self]
  ring

/-! ### The maximal relative projection constants -/

section MaxRelProjConst

variable {n : ℕ}

/-- `kyFanSum n (√D S √D) ≤ clConst ℝ ι n` for every sign matrix `S` and every weight `w`. -/
lemma kyFanSum_weightedSign_le_clConst {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {w : ι → ℝ}
    (hw : IsWeight w) : kyFanSum n (weightedSign S w) ≤ clConst ℝ ι n :=
  kyFanSum_le clConst_nonneg fun P hP ↦ (frobeniusInner_weightedSign_le_weightedAbsSum hS w P).trans
    (le_clConst hw.isUnitWeight_sqrt hP)

/-- **The formula of Chalmers and Lewicki**, lower bound ([JFA, Theorem 2.1]):
`kyFanSum n (√D S √D) ≤ λ_ℝ(n, d)` for every sign matrix `S` and every weight `w`. -/
theorem kyFanSum_weightedSign_le_maxRelProjConst {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : IsSignMatrix S) {w : Fin d → ℝ} (hw : IsWeight w) :
    kyFanSum n (weightedSign S w) ≤ maxRelProjConst ℝ n d := by
  rw [maxRelProjConst_eq_clConst]
  exact kyFanSum_weightedSign_le_clConst hS hw

/-- **The formula of Chalmers and Lewicki**, upper bound ([JFA, Theorem 2.1]): if
`kyFanSum n (√D S √D) ≤ c` for every sign matrix `S` and every weight `w`, then
`λ_ℝ(n, d) ≤ c`. -/
theorem maxRelProjConst_real_le {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (S : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ), IsSignMatrix S → IsWeight w →
      kyFanSum n (weightedSign S w) ≤ c) :
    maxRelProjConst ℝ n d ≤ c := by
  rw [maxRelProjConst_eq_clConst]
  refine clConst_le hc fun t P ht hP ↦ ?_
  rw [weightedAbsSum_eq_frobeniusInner ht.nonneg]
  exact (frobeniusInner_le_kyFanSum _ hP).trans
    (h _ _ (isSignMatrix_signPattern hP.1) ht.isWeight_sq)

end MaxRelProjConst

/-! ### The maximal projection constants -/

section MaxProjConst

variable {n : ℕ}

/-- `kyFanSum n (√D S √D) ≤ λ_ℝ(n)` for every sign matrix `S` and every weight `w`. -/
theorem kyFanSum_weightedSign_le_maxProjConst {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    {w : ι → ℝ} (hw : IsWeight w) : kyFanSum n (weightedSign S w) ≤ maxProjConst ℝ n :=
  kyFanSum_le (maxProjConst_nonneg n) fun P hP ↦
    (frobeniusInner_weightedSign_le_weightedAbsSum hS w P).trans
      (weightedAbsSum_le_maxProjConst hw.isUnitWeight_sqrt hP)

variable (n) in
/-- The values `kyFanSum n (√D S √D)` over all dimensions `d`, all `d × d` sign matrices `S`
and all weights `w ∈ ℝ^d`, where `D = diag(w)`. -/
def signMatrixValues : Set ℝ :=
  {x | ∃ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ),
    IsSignMatrix S ∧ IsWeight w ∧ kyFanSum n (weightedSign S w) = x}

lemma bddAbove_signMatrixValues : BddAbove (signMatrixValues n) :=
  ⟨maxProjConst ℝ n, by
    rintro _ ⟨d, S, w, hS, hw, rfl⟩
    exact kyFanSum_weightedSign_le_maxProjConst hS hw⟩

lemma signMatrixValues_nonempty : (signMatrixValues n).Nonempty :=
  ⟨_, 1, of fun _ _ ↦ 1, fun _ ↦ 1, isSignMatrix_ones, ⟨fun _ ↦ zero_le_one, by simp⟩, rfl⟩

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ sup (signMatrixValues n)` for every unit weight `t` and every
`P ∈ orthProjs ℝ ι n`. -/
lemma weightedAbsSum_le_sSup_signMatrixValues {t : ι → ℝ} (ht : IsUnitWeight t)
    {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι n) :
    weightedAbsSum t P ≤ sSup (signMatrixValues n) := by
  let e := (Fintype.equivFin ι).symm
  have hle : kyFanSum n (weightedSign (signPattern P) fun i ↦ t i ^ 2) ≤
      sSup (signMatrixValues n) := by
    rw [← kyFanSum_submatrix n e, ← weightedSign_submatrix]
    exact le_csSup bddAbove_signMatrixValues ⟨_, _, _,
      (isSignMatrix_signPattern hP.1).submatrix e, ht.isWeight_sq.comp_equiv e, rfl⟩
  rw [weightedAbsSum_eq_frobeniusInner ht.nonneg]
  exact (frobeniusInner_le_kyFanSum _ hP).trans hle

/-- **The formula of Chalmers and Lewicki** for the maximal projection constant
([JFA, Theorem 2.1]): `λ_ℝ(n) = sup { kyFanSum n (√D S √D) : S ∈ 𝒮_d, D ∈ 𝒟_d, d ∈ ℕ }`. -/
theorem maxProjConst_real_eq_sSup (hn : 1 ≤ n) :
    maxProjConst ℝ n = sSup (signMatrixValues n) := by
  have h0 : 0 ≤ sSup (signMatrixValues n) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hP : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ orthProjs ℝ (Fin n) n :=
      ⟨IsStarProjection.one _, by simp⟩
    exact (weightedAbsSum_nonneg isUnitWeight_uniform.nonneg _).trans
      (weightedAbsSum_le_sSup_signMatrixValues isUnitWeight_uniform hP)
  apply le_antisymm
  · rw [maxProjConst_eq_iSup_clConst]
    exact ciSup_le fun d ↦
      clConst_le h0 fun t P ht hP ↦ weightedAbsSum_le_sSup_signMatrixValues ht hP
  · refine csSup_le signMatrixValues_nonempty ?_
    rintro _ ⟨d, S, w, hS, hw, rfl⟩
    exact kyFanSum_weightedSign_le_maxProjConst hS hw

/-- `λ_ℝ(n)` is approximated by the values `kyFanSum n (√D S √D)`. -/
theorem exists_lt_kyFanSum_weightedSign (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ), IsSignMatrix S ∧ IsWeight w ∧
      maxProjConst ℝ n - δ < kyFanSum n (weightedSign S w) := by
  have h : maxProjConst ℝ n - δ < sSup (signMatrixValues n) := by
    rw [← maxProjConst_real_eq_sSup hn]
    linarith
  obtain ⟨_, ⟨d, S, w, hS, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup signMatrixValues_nonempty h
  exact ⟨d, S, w, hS, hw, hlt⟩

end MaxProjConst

end ProjectionConstants
