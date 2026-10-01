/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Stationary
import ProjectionConstants.ForMathlib.BigOperators

/-!
# Maximizing configurations `(S, w)`

A *configuration* on a finite index type `ι` is a pair `(S, w)` of a sign matrix `S`
(`IsSignMatrix S`) and a weight vector `w` (`IsWeight w`). Its value is
`kyFanSumLe n (weightedSign S w)`: the supremum of `Tr(√D S √D P)`, where `D = diag(w)`, over the
orthogonal projections `P` of rank at most `n`. In the notation of [AMOP] (for `ι = Fin d`), `S`
ranges over the set `𝒮_d` of sign matrices and `D` over the set `𝒟_d` of nonnegative diagonal
matrices of trace one.

This file collects the properties of maximizing configurations that enter the proof of
[AMOP, Theorem 1.2] in `ProjectionConstants.AlmostMinimal.Main`.

## Main definitions

* `IsGlobalMax n S w`: `(S, w)` has the largest value among all configurations on `ι`.
* `flipSign S i j`: the matrix `S` with the signs of the entries `(i, j)` and `(j, i)` flipped.

## Main statements

* `exists_isGlobalMax`: the value attains its maximum over all configurations on `ι`.
* `exists_forall_kyFanSumLe_weightedSign_le`: for fixed weights, the value attains its maximum
  over the sign matrices.
* `sign_mul_nonneg_of_isMax`: [AMOP, Lemma 3.2], the part that we need. If the weights are
  positive, `S` maximizes the value for these weights, and `Q` is an optimal projection, then
  `Sᵢⱼ Qᵢⱼ ≥ 0` for all `i, j`, that is `S ∘ Q = |Q|`.
* `kyFanSumLe_weightedSign_le_restrict`: an index of weight zero can be removed without
  decreasing the value.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

variable {ι : Type*} [Fintype ι]

/-! ### Existence of maximizers -/

/-- `(S, w)` maximizes `kyFanSumLe n (weightedSign S w)` over all sign matrices `S` and weights `w`
on `ι`. -/
structure IsGlobalMax (n : ℕ) (S : Matrix ι ι ℝ) (w : ι → ℝ) : Prop where
  sign : IsSignMatrix S
  weight : IsWeight w
  max : ∀ (S' : Matrix ι ι ℝ) (w' : ι → ℝ), IsSignMatrix S' → IsWeight w' →
    kyFanSumLe n (weightedSign S' w') ≤ kyFanSumLe n (weightedSign S w)

/-- **Existence of maximizers.** If `ι` is nonempty, then `kyFanSumLe n (weightedSign S w)` attains
its maximum over all sign matrices `S` and weights `w` on `ι`. -/
theorem exists_isGlobalMax [Nonempty ι] (n : ℕ) :
    ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsGlobalMax n S w := by
  have hmaxw : ∀ S : Matrix ι ι ℝ, ∃ w, IsWeight w ∧
      ∀ w', IsWeight w' → kyFanSumLe n (weightedSign S w') ≤ kyFanSumLe n (weightedSign S w) := by
    intro S
    obtain ⟨w, hw, hmax⟩ := isCompact_setOf_isWeight.exists_isMaxOn nonempty_setOf_isWeight
      (continuous_kyFanSumLe_weightedSign n S).continuousOn
    exact ⟨w, hw, fun w' hw' ↦ hmax hw'⟩
  choose W hW hWmax using hmaxw
  have hne : {S : Matrix ι ι ℝ | IsSignMatrix S}.Nonempty := ⟨_, isSignMatrix_ones⟩
  obtain ⟨S, hS, hSmax⟩ := Set.exists_max_image _
    (fun S ↦ kyFanSumLe n (weightedSign S (W S))) finite_setOf_isSignMatrix hne
  exact ⟨S, W S, hS, hW S, fun S' w' hS' hw' ↦ (hWmax S' w' hw').trans (hSmax S' hS')⟩

/-- For fixed weights `w`, `kyFanSumLe n (weightedSign S w)` attains its maximum over the sign
matrices `S`. -/
theorem exists_forall_kyFanSumLe_weightedSign_le (n : ℕ) (w : ι → ℝ) :
    ∃ S : Matrix ι ι ℝ, IsSignMatrix S ∧ ∀ S', IsSignMatrix S' →
      kyFanSumLe n (weightedSign S' w) ≤ kyFanSumLe n (weightedSign S w) := by
  have hne : {S : Matrix ι ι ℝ | IsSignMatrix S}.Nonempty := ⟨_, isSignMatrix_ones⟩
  obtain ⟨S, hS, hSmax⟩ := Set.exists_max_image _ (fun S ↦ kyFanSumLe n (weightedSign S w))
    finite_setOf_isSignMatrix hne
  exact ⟨S, hS, hSmax⟩

/-! ### The sign pattern of optimal projections -/

/-- The matrix `S` with the signs of the entries `(i, j)` and `(j, i)` flipped. -/
def flipSign [DecidableEq ι] (S : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℝ :=
  Matrix.of fun a b ↦ if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then -S a b else S a b

omit [Fintype ι] in
/-- Flipping the signs of an off-diagonal pair of entries of a sign matrix gives a sign matrix. -/
lemma isSignMatrix_flipSign [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι}
    (hij : i ≠ j) : IsSignMatrix (flipSign S i j) := by
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a ↦ ?_⟩
  · simp only [flipSign, Matrix.of_apply, hS.symm a b]
    by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
    · have h' : (b = i ∧ a = j) ∨ (b = j ∧ a = i) := by tauto
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ ((b = i ∧ a = j) ∨ (b = j ∧ a = i)) := by tauto
      rw [ite_eq_right h, ite_eq_right h']
  · simp only [flipSign, Matrix.of_apply]
    split_ifs
    · rcases hS.pm a b with h | h <;> simp [h]
    · exact hS.pm a b
  · simp only [flipSign, Matrix.of_apply]
    have h : ¬ ((a = i ∧ a = j) ∨ (a = j ∧ a = i)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hij rfl
    rw [ite_eq_right h, hS.diag]

private lemma sum_sum_ite_ite [DecidableEq ι] (i j : ι) (c : ℝ) :
    ∑ a : ι, ∑ b : ι, (if a = i then (if b = j then c else 0) else 0) = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (mem_univ i) h

/-- For symmetric `Q`, flipping the signs of `(i, j)` and `(j, i)` changes `Tr(√D S √D Q)` by
`-4 √wᵢ √wⱼ Sᵢⱼ Qᵢⱼ`. -/
lemma frobeniusInner_weightedSign_flipSign [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (w : ι → ℝ) {Q : Matrix ι ι ℝ} (hQ : ∀ a b, Q b a = Q a b) {i j : ι} (hij : i ≠ j) :
    frobeniusInner (weightedSign (flipSign S i j) w) Q =
      frobeniusInner (weightedSign S w) Q - 4 * (√(w i) * √(w j) * (S i j * Q i j)) := by
  have hdiff : ∀ a b, weightedSign (flipSign S i j) w a b * Q a b =
      weightedSign S w a b * Q a b -
        ((if a = i then (if b = j then 2 * (√(w i) * √(w j) * (S i j * Q i j)) else 0) else 0) +
          (if a = j then (if b = i then 2 * (√(w i) * √(w j) * (S i j * Q i j)) else 0)
            else 0)) := by
    intro a b
    simp only [weightedSign, flipSign, Matrix.of_apply]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [true_and, true_or, ite_true, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
      ring
    · by_cases h2 : a = j ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij), ite_true, and_self, or_true]
        rw [hS.symm a b, hQ a b]
        ring
      · have h3 : ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) := by tauto
        rw [ite_eq_right h3]
        by_cases ha : a = i
        · have hb : b ≠ j := fun hb ↦ h1 ⟨ha, hb⟩
          have ha' : a ≠ j := ha ▸ hij
          simp [ha, hb, hij]
        · by_cases ha' : a = j
          · have hb : b ≠ i := fun hb ↦ h2 ⟨ha', hb⟩
            simp [ha', hb, Ne.symm hij]
          · simp [ha, ha']
  have hsum : frobeniusInner (weightedSign (flipSign S i j) w) Q =
      ∑ a, ∑ b, (weightedSign S w a b * Q a b -
        ((if a = i then (if b = j then 2 * (√(w i) * √(w j) * (S i j * Q i j)) else 0) else 0) +
          (if a = j then (if b = i then 2 * (√(w i) * √(w j) * (S i j * Q i j)) else 0)
            else 0))) := by
    unfold frobeniusInner
    exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ hdiff a b
  rw [hsum]
  simp only [sum_sub_distrib, sum_add_distrib, sum_sum_ite_ite]
  unfold frobeniusInner
  ring

/-- **The sign pattern of an optimal projection** ([AMOP, Lemma 3.2], the part that we need). Let
the weights `q` be positive, let `S` maximize `kyFanSumLe n (weightedSign S q)` among the sign
matrices, and let `Q ∈ orthProjsLe ι n` attain this supremum. Then `Sᵢⱼ Qᵢⱼ ≥ 0`, that is
`S ∘ Q = |Q|`. -/
theorem sign_mul_nonneg_of_isMax {n : ℕ} {S Q : Matrix ι ι ℝ} {q : ι → ℝ} (hS : IsSignMatrix S)
    (hq : ∀ i, 0 < q i)
    (hSmax : ∀ S', IsSignMatrix S' →
      kyFanSumLe n (weightedSign S' q) ≤ kyFanSumLe n (weightedSign S q))
    (hQ : Q ∈ orthProjsLe _ n)
    (hQopt : frobeniusInner (weightedSign S q) Q = kyFanSumLe n (weightedSign S q)) (i j : ι) :
    0 ≤ S i j * Q i j := by
  classical
  by_contra hneg
  push Not at hneg
  have hij : i ≠ j := by
    rintro rfl
    rw [hS.diag, one_mul] at hneg
    linarith [hQ.1.diag_nonneg i]
  have h1 := frobeniusInner_weightedSign_flipSign hS q hQ.1.apply_comm hij
  have h2 := frobeniusInner_le_kyFanSumLe (weightedSign (flipSign S i j) q) hQ
  have h3 := hSmax _ (isSignMatrix_flipSign hS hij)
  have hpos : 0 < √(q i) * √(q j) := mul_pos (Real.sqrt_pos.2 (hq i)) (Real.sqrt_pos.2 (hq j))
  have h4 : 0 < √(q i) * √(q j) * -(S i j * Q i j) := mul_pos hpos (by linarith)
  linarith

/-! ### Removing an index of weight zero -/

/-- If column `j` of the symmetric matrix `M` vanishes, then `kyFanSumLe n M` is attained by an
orthogonal projection whose column `j` vanishes. -/
lemma exists_frobeniusInner_eq_kyFanSumLe_of_apply_eq_zero {n : ℕ} {M : Matrix ι ι ℝ}
    (hM : ∀ a b, M b a = M a b) {j : ι} (hMj : ∀ i, M i j = 0) :
    ∃ P₁ ∈ orthProjsLe ι n, (∀ i, P₁ i j = 0) ∧ frobeniusInner M P₁ = kyFanSumLe n M := by
  obtain ⟨P, hP, hPopt⟩ := exists_frobeniusInner_eq_kyFanSumLe n M
  have hmax : ∀ P' ∈ orthProjsLe ι n, frobeniusInner M P' ≤ frobeniusInner M P :=
    fun P' hP' ↦ hPopt ▸ frobeniusInner_le_kyFanSumLe M hP'
  have hcomm := sum_mul_eq_sum_mul_of_isMaxOn (.ext hM) hP hmax
  have hy : ∀ i, ∑ k, P i k * P k j = P i j := fun i ↦ hP.1.sum_mul_apply i j
  have hMy : ∀ i, ∑ k, M i k * P k j = 0 := by
    intro i
    rw [hcomm i j]
    simp [hMj]
  have hyj : P j j = (fun k ↦ P k j) ⬝ᵥ (fun k ↦ P k j) := by
    simp only [dotProduct]
    rw [hP.1.diag_eq_sum_sq j]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hP.1.apply_comm k j, sq]
  by_cases ha : (fun k ↦ P k j) ⬝ᵥ (fun k ↦ P k j) = 0
  · exact ⟨P, hP, fun i ↦ eq_zero_of_dotProduct_self_eq_zero ha i, hPopt⟩
  set D := (fun k ↦ P k j) ⬝ᵥ (fun k ↦ P k j) with hD
  refine ⟨Matrix.of fun a b ↦ P a b - P a j * P b j / D,
    ⟨isStarProjection_sub_rankOne (u := fun k ↦ P k j) hP.1 hy ha, ?_⟩, fun i ↦ ?_, ?_⟩
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, sum_sub_distrib, ← sum_div]
    have h1 : ∑ i, P i j * P i j = D := rfl
    rw [h1, div_self ha]
    linarith [show ∑ i, P i i ≤ n from hP.2]
  · simp only [Matrix.of_apply]
    rw [← hyj, mul_div_assoc, hyj, div_self ha, mul_one, sub_self]
  · have htv : frobeniusInner M (Matrix.of fun a b ↦ P a b - P a j * P b j / D) =
        frobeniusInner M P - ((fun k ↦ P k j) ⬝ᵥ M *ᵥ (fun k ↦ P k j)) / D := by
      simp only [frobeniusInner, dotProduct_mulVec_self_eq_sum, Matrix.of_apply, sum_div,
        ← sum_sub_distrib]
      refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
      ring
    have hq : (fun k ↦ P k j) ⬝ᵥ M *ᵥ (fun k ↦ P k j) = 0 := by
      simp only [dotProduct, mulVec_apply_eq_sum, hMy, mul_zero, sum_const_zero]
    rw [htv, hq, zero_div, sub_zero, hPopt]

/-- **Restriction.** If `wⱼ = 0`, then removing the index `j` does not decrease
`kyFanSumLe n (weightedSign S w)`. -/
theorem kyFanSumLe_weightedSign_le_restrict [DecidableEq ι] {n : ℕ} {S : Matrix ι ι ℝ}
    {w : ι → ℝ} (hS : IsSignMatrix S) {j : ι} (hj : w j = 0) :
    kyFanSumLe n (weightedSign S w) ≤
      kyFanSumLe n (weightedSign (Matrix.of fun a b : {k // k ≠ j} ↦ S a b) fun a ↦ w a) := by
  have hMj : ∀ i, weightedSign S w i j = 0 := fun i ↦ by simp [weightedSign, hj]
  have hMj' : ∀ i, weightedSign S w j i = 0 := fun i ↦ by
    rw [IsSignMatrix.weightedSign_comm hS w i j]
    exact hMj i
  obtain ⟨P₁, hP₁, hP₁j, hval⟩ := exists_frobeniusInner_eq_kyFanSumLe_of_apply_eq_zero (n := n)
    (IsSignMatrix.weightedSign_comm hS w) hMj
  have hP₁j' : ∀ i, P₁ j i = 0 := fun i ↦ by rw [hP₁.1.apply_comm i j]; exact hP₁j i
  rw [← hval]
  refine le_trans (le_of_eq ?_) (frobeniusInner_le_kyFanSumLe _
    (P := Matrix.of fun a b : {k // k ≠ j} ↦ P₁ a b)
    ⟨IsStarProjection.of_apply (fun a b ↦ hP₁.1.apply_comm a b) (fun a b ↦ ?_), ?_⟩)
  · simp only [frobeniusInner, Matrix.of_apply]
    have e1 : ∀ a : {k // k ≠ j}, ∑ b : {k // k ≠ j},
        weightedSign (Matrix.of fun a b : {k // k ≠ j} ↦ S a b) (fun a ↦ w a) a b * P₁ a b =
          ∑ b, weightedSign S w a b * P₁ a b := by
      intro a
      change ∑ b : {k // k ≠ j}, weightedSign S w a b * P₁ a b = _
      rw [Fintype.sum_subtype_ne_eq_sub j (fun b ↦ weightedSign S w a b * P₁ a b), hP₁j, mul_zero,
        sub_zero]
    simp only [e1]
    rw [Fintype.sum_subtype_ne_eq_sub j (fun a ↦ ∑ b, weightedSign S w a b * P₁ a b)]
    simp only [hMj', zero_mul, sum_const_zero, sub_zero]
  · simp only [Matrix.of_apply]
    rw [Fintype.sum_subtype_ne_eq_sub j (fun k ↦ P₁ a k * P₁ k b), hP₁j, zero_mul, sub_zero,
      hP₁.1.sum_mul_apply]
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    rw [Fintype.sum_subtype_ne_eq_sub j (fun k ↦ P₁ k k), hP₁j, sub_zero]
    exact hP₁.2

end ProjectionConstants.AlmostMinimal
