/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Stabilization.Maximizer

/-!
# Reweighting a maximizer

This is [KMMP, Claim 2.4]. Let `(t, U)` be a maximizer of the Chalmers–Lewicki quantity in
Parseval form (`IsMaximizer`), with columns `uᵢ` and maximum `λ = clConst ℝ ι r`, and let `C` be
a set of indices with `⟨uᵢ, uⱼ⟩ ≥ 0` for `i, j ∈ C`. If `cᵢ ≥ 0`, `cᵢ = 1` for `i ∉ C` and
`∑ᵢ cᵢ uᵢ uᵢᵀ = ∑ᵢ uᵢ uᵢᵀ`, then `(√cᵢ tᵢ, √cᵢ uᵢ)` is again a maximizer (`IsMaximizer.reweight`).

The proof uses the two first-order conditions of `ProjectionConstants.Stabilization.Maximizer`.
With `dᵢ = cᵢ - 1` and `bᵢⱼ = tᵢ tⱼ |⟨uᵢ, uⱼ⟩|`:

* `U' U'ᵀ = ∑ᵢ cᵢ uᵢ uᵢᵀ = I`;
* `λ ∑ᵢ dᵢ tᵢ² = ∑ᵢ dᵢ ⟨uᵢ, H uᵢ⟩ = 0` by the quadratic form `H`, so `‖t'‖ = 1`;
* the new value is `∑ᵢⱼ cᵢ cⱼ bᵢⱼ = λ + 2 ∑ᵢ dᵢ (∑ⱼ bᵢⱼ) + ∑ᵢⱼ dᵢ dⱼ bᵢⱼ`. The middle term is
  `2λ ∑ᵢ dᵢ tᵢ² = 0` by the weight condition, and the last is `‖∑_{i ∈ C} dᵢ tᵢ uᵢ‖² ≥ 0`, since
  `bᵢⱼ = tᵢ tⱼ ⟨uᵢ, uⱼ⟩` on `C`. So the value is at least, hence equal to, the maximum `λ`.

## Main statements

* `IsMaximizer.reweight`: reweighting a maximizer by `√cᵢ` gives a maximizer.

## References

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.
-/

open Matrix Finset

namespace ProjectionConstants.Stabilization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} {t : ι → ℝ} {U : Matrix (Fin r) ι ℝ}

namespace IsMaximizer

/-- Rescaling the columns `uᵢ` by `aᵢ` rescales the Gram matrix to `(aᵢ aⱼ ⟨uᵢ, uⱼ⟩)`. -/
lemma gram_mul_diagonal (U : Matrix (Fin r) ι ℝ) (a : ι → ℝ) (i j : ι) :
    ((U * diagonal a)ᴴ * (U * diagonal a)) i j = a i * a j * (Uᴴ * U) i j := by
  rw [gram_apply, gram_apply, Finset.mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [Matrix.mul_diagonal]
  ring

/-- **Reweighting** ([KMMP, Claim 2.4]). Let `(t, U)` be a maximizer and let `⟨uᵢ, uⱼ⟩ ≥ 0` for
`i, j ∈ C`. If `cᵢ ≥ 0`, `cᵢ = 1` for `i ∉ C` and `∑ᵢ cᵢ uᵢ uᵢᵀ = ∑ᵢ uᵢ uᵢᵀ`, then
`(√cᵢ tᵢ, √cᵢ uᵢ)` is again a maximizer. -/
theorem reweight (h : IsMaximizer r t U) (hL0 : 0 < clConst ℝ ι r) (C : Finset ι)
    (hC : ∀ i ∈ C, ∀ j ∈ C, 0 ≤ (Uᴴ * U) i j) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i ∉ C, c i = 1) (hcU : ∀ k l, ∑ i, c i * (U k i * U l i) = ∑ i, U k i * U l i) :
    IsMaximizer r (fun i ↦ √(c i) * t i) (U * diagonal fun i ↦ √(c i)) := by
  have hw := h.weight_eq
  have hL'' := h.eq
  obtain ⟨H, hH⟩ := h.exists_quadratic
  set a : ι → ℝ := fun i ↦ √(c i) with ha_def
  have ha0 : ∀ i, 0 ≤ a i := fun i ↦ Real.sqrt_nonneg _
  have haa : ∀ i, a i * a i = c i := fun i ↦ Real.mul_self_sqrt (hc i)
  set L := clConst ℝ ι r with hL
  set P := Uᴴ * U with hP
  have hPabs : ∀ i j, |P j i| = |P i j| := fun i j ↦ by rw [hP, gram_symm]
  set d : ι → ℝ := fun i ↦ c i - 1 with hd_def
  -- `∑ᵢ dᵢ uᵢ uᵢᵀ = 0`
  have hd0 : ∀ k l, ∑ i, d i * (U k i * U l i) = 0 := by
    intro k l
    simp only [hd_def, sub_mul, one_mul, sum_sub_distrib, hcU, sub_self]
  -- `∑ᵢ dᵢ tᵢ² = 0`
  have hdt : ∑ i, d i * t i ^ 2 = 0 := by
    have hHi : ∀ i, (Uᴴ * H * U) i i = ∑ k, ∑ l, H k l * (U k i * U l i) := by
      intro i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun l _ ↦ sum_congr rfl fun k _ ↦ by ring
    have e : L * ∑ i, d i * t i ^ 2 = 0 := by
      calc L * ∑ i, d i * t i ^ 2 = ∑ i, d i * (Uᴴ * H * U) i i := by
            rw [Finset.mul_sum]
            exact sum_congr rfl fun i _ ↦ by rw [hH]; ring
        _ = ∑ k, ∑ l, H k l * ∑ i, d i * (U k i * U l i) := by
            simp_rw [hHi, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine sum_congr rfl fun k _ ↦ ?_
            rw [Finset.sum_comm]
            exact sum_congr rfl fun l _ ↦ sum_congr rfl fun i _ ↦ by ring
        _ = 0 := by simp [hd0]
    exact (mul_eq_zero.mp e).resolve_left hL0.ne'
  -- the new weights
  have hunit : IsUnitWeight fun i ↦ a i * t i := by
    refine ⟨fun i ↦ mul_nonneg (ha0 i) (h.unit.nonneg i), ?_⟩
    have e : ∀ i, (a i * t i) ^ 2 = t i ^ 2 + d i * t i ^ 2 := fun i ↦ by
      rw [mul_pow, sq (a i), haa, hd_def]
      ring
    simp only [e, sum_add_distrib, hdt, add_zero, h.unit.sum_sq]
  -- the new frame
  have hpars : (U * diagonal a) * (U * diagonal a)ᴴ = 1 := by
    rw [← h.parseval]
    ext k l
    have e1 : ((U * diagonal a) * (U * diagonal a)ᴴ) k l = ∑ i, c i * (U k i * U l i) := by
      rw [Matrix.mul_apply]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [Matrix.conjTranspose_apply, star_trivial, Matrix.mul_diagonal, Matrix.mul_diagonal,
        ← haa i]
      ring
    have e2 : (U * Uᴴ) k l = ∑ i, U k i * U l i := by
      rw [Matrix.mul_apply]
      exact sum_congr rfl fun i _ ↦ by rw [Matrix.conjTranspose_apply, star_trivial]
    rw [e1, e2, hcU]
  refine ⟨hunit, hpars,
    le_antisymm (le_clConst hunit (conjTranspose_mul_self_mem_orthProjs hpars)) ?_⟩
  -- the value does not decrease
  set b : ι → ι → ℝ := fun i j ↦ t i * t j * |P i j| with hb
  have hval : weightedAbsSum (fun i ↦ a i * t i) ((U * diagonal a)ᴴ * (U * diagonal a)) =
      ∑ i, ∑ j, c i * c j * b i j := by
    unfold weightedAbsSum
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [gram_mul_diagonal, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (ha0 i),
      abs_of_nonneg (ha0 j), ← haa i, ← haa j, hb]
    ring
  have hL' : ∑ i, ∑ j, b i j = L := by
    rw [← hL'']
    unfold weightedAbsSum
    simp only [hb, Real.norm_eq_abs]
  have hrow : ∀ i, ∑ j, b i j = L * t i ^ 2 := fun i ↦ by
    rw [← hw i, Finset.mul_sum]
    exact sum_congr rfl fun j _ ↦ by simp only [hb]; ring
  have hcol : ∀ j, ∑ i, b i j = L * t j ^ 2 := fun j ↦ by
    rw [← hrow j]
    exact sum_congr rfl fun i _ ↦ by simp only [hb, hPabs]; ring
  have hquad : 0 ≤ ∑ i, ∑ j, d i * d j * b i j := by
    have e : ∀ i j, d i * d j * b i j = ∑ k, (d i * t i * U k i) * (d j * t j * U k j) := by
      intro i j
      have e2 : d i * d j * b i j = d i * d j * (t i * t j * P i j) := by
        by_cases hij : i ∈ C ∧ j ∈ C
        · simp only [hb]
          rw [abs_of_nonneg (hC i hij.1 j hij.2)]
        · have hz : d i * d j = 0 := by
            rcases not_and_or.mp hij with hi | hj
            · simp [hd_def, hc1 i hi]
            · simp [hd_def, hc1 j hj]
          rw [hz, zero_mul, zero_mul]
      rw [e2, hP, gram_apply, Finset.mul_sum, Finset.mul_sum]
      exact sum_congr rfl fun k _ ↦ by ring
    calc 0 ≤ ∑ k, (∑ i, d i * t i * U k i) ^ 2 := sum_nonneg fun k _ ↦ sq_nonneg _
      _ = ∑ i, ∑ j, d i * d j * b i j := by
        simp_rw [e, sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        exact sum_congr rfl fun i _ ↦ Finset.sum_comm
  have hexp : ∑ i, ∑ j, c i * c j * b i j = ∑ i, ∑ j, b i j + ∑ i, d i * ∑ j, b i j +
      ∑ j, d j * ∑ i, b i j + ∑ i, ∑ j, d i * d j * b i j := by
    have e : ∀ i j, c i * c j * b i j = b i j + d i * b i j + d j * b i j + d i * d j * b i j := by
      intro i j
      simp only [hd_def]
      ring
    simp_rw [e, sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j ↦ d j * b i j)]
  have hz1 : ∑ i, d i * ∑ j, b i j = 0 := by
    simp_rw [hrow]
    rw [← mul_zero L, ← hdt, Finset.mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  have hz2 : ∑ j, d j * ∑ i, b i j = 0 := by
    simp_rw [hcol]
    rw [← mul_zero L, ← hdt, Finset.mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hval, hexp, hL', hz1, hz2]
  linarith

end IsMaximizer

end ProjectionConstants.Stabilization
