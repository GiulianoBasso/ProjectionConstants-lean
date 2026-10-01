/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The characteristic polynomial of `√D R₅ √D`

This file contains the algebraic part of [JFA-E, Proposition F], `Π(2, R₅) = 4/3`, where
`Π(2, R₅)` is the maximum of `kyFanSum 2 (√D R₅ √D)` over all weights. The sign matrix
`R₅ = J - 2E` of [JFA-E], where `E` is the adjacency matrix of a `5`-cycle, is indexed here by
`Fin 5 = {0, …, 4}` ([JFA-E] uses `1, …, 5`). For a vector `s` we write
`scaledR5 s = diag(s) R₅ diag(s)`; for `sᵢ = √dᵢ` this is `√D R₅ √D` with `D = diag(d)`.

The characteristic polynomial of `scaledR5 s` is `X⁵ - (∑ sᵢ²) X⁴ + 4τ X² - 16δ`, where `τ` is
the sum of `dᵢdⱼdₖ` over the coherent triples `{i, j, k}` of `R₅` and `δ = d₀d₁d₂d₃d₄`
([JFA-E, Lemma E]). If `∑ sᵢ² = 1`, the Vieta relations for its roots `μᵢ` give
`μᵢ + μⱼ ≤ 4/3` for `i ≠ j`, with strict inequality if `δ > 0`. The link with the eigenvalues of
the symmetric matrix `scaledR5 s` is made in
`ProjectionConstants.GrunbaumConjecture.R5.Eigenvalues`.

## Main definitions

* `R5`: the matrix `R₅`.
* `scaledR5 s`: the matrix `diag(s) R₅ diag(s)`.
* `tripleSum s`, `prodSq s`: the numbers `τ` and `δ` of [JFA-E, Lemma E], for `dᵢ = sᵢ²`.

## Main statements

* `charpoly_scaledR5`: the characteristic polynomial of `scaledR5 s` ([JFA-E, Lemma E]).
* `root_add_root_le_of_charpoly`: if the characteristic polynomial splits as `∏ (X - μᵢ)` and
  `∑ sᵢ² = 1`, then `μᵢ + μⱼ ≤ 4/3` for all `i ≠ j`, strictly if all `sᵢ ≠ 0`.
* `exists_root_add_root_eq_of_charpoly`: for `s² = (1/3, 1/3, 0, 1/3, 0)`, two of the `μᵢ` sum
  to `4/3`, as in the proof of [JFA-E, Proposition F]
  (`ProjectionConstants.GrunbaumConjecture.Main` gets this lower bound from `R₃` instead).

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Matrix
open Polynomial (X C)

namespace ProjectionConstants.GrunbaumConjecture

/-- `R₅ = J − 2E`, where `E` is the adjacency matrix of the 5-cycle `0–1–2–3–4–0`. -/
def R5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ 1, -1,  1,  1, -1;
     -1,  1, -1,  1,  1;
      1, -1,  1, -1,  1;
      1,  1, -1,  1, -1;
     -1,  1,  1, -1,  1]

/-- `scaledR5 s = diag(s) R₅ diag(s)`; for `s = (√d₀, …, √d₄)` this is `√D R₅ √D`. -/
def scaledR5 (s : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun i j ↦ s i * R5 i j * s j

/-- `tripleSum s = ∑ dᵢdⱼdₖ` with `dᵢ = sᵢ²`, summed over the coherent triples
`{0, 1, 3}, {1, 2, 4}, {0, 2, 3}, {1, 3, 4}, {0, 2, 4}` of `R₅`; this is the `τ` of
[JFA-E, Lemma E]. -/
def tripleSum (s : Fin 5 → ℝ) : ℝ :=
  s 0 ^ 2 * s 1 ^ 2 * s 3 ^ 2 + s 1 ^ 2 * s 2 ^ 2 * s 4 ^ 2 + s 2 ^ 2 * s 3 ^ 2 * s 0 ^ 2 +
    s 3 ^ 2 * s 4 ^ 2 * s 1 ^ 2 + s 4 ^ 2 * s 0 ^ 2 * s 2 ^ 2

/-- `prodSq s = d₀d₁d₂d₃d₄` with `dᵢ = sᵢ²`; this is the `δ` of [JFA-E, Lemma E]. -/
def prodSq (s : Fin 5 → ℝ) : ℝ := (s 0 * s 1 * s 2 * s 3 * s 4) ^ 2

/-! ### The characteristic polynomial ([JFA-E, Lemma E]) -/

/-- The matrix `x·1 − scaledR5 s`, written out explicitly. -/
theorem scalar_sub_scaledR5 (s : Fin 5 → ℝ) (x : ℝ) :
    Matrix.scalar (Fin 5) x - scaledR5 s =
      !![x - s 0 * s 0, s 0 * s 1, -(s 0 * s 2), -(s 0 * s 3), s 0 * s 4;
         s 1 * s 0, x - s 1 * s 1, s 1 * s 2, -(s 1 * s 3), -(s 1 * s 4);
         -(s 2 * s 0), s 2 * s 1, x - s 2 * s 2, s 2 * s 3, -(s 2 * s 4);
         -(s 3 * s 0), -(s 3 * s 1), s 3 * s 2, x - s 3 * s 3, s 3 * s 4;
         s 4 * s 0, -(s 4 * s 1), -(s 4 * s 2), s 4 * s 3, x - s 4 * s 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scaledR5, R5, Matrix.scalar_apply]

/-- `det(x·1 − scaledR5 s) = x⁵ − (∑ sᵢ²) x⁴ + 4τ x² − 16δ`, where `τ = tripleSum s` and
`δ = prodSq s`. -/
theorem det_scalar_sub_scaledR5 (s : Fin 5 → ℝ) (x : ℝ) :
    (Matrix.scalar (Fin 5) x - scaledR5 s).det =
      x ^ 5 - (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 + s 4 ^ 2) * x ^ 4 +
        4 * tripleSum s * x ^ 2 - 16 * prodSq s := by
  rw [scalar_sub_scaledR5]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, tripleSum, prodSq]
  ring

/-- **[JFA-E, Lemma E].** The characteristic polynomial of `scaledR5 s`. -/
theorem charpoly_scaledR5 (s : Fin 5 → ℝ) :
    (scaledR5 s).charpoly = X ^ 5 - C (s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 + s 4 ^ 2) * X ^ 4 +
      C (4 * tripleSum s) * X ^ 2 - C (16 * prodSq s) := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, det_scalar_sub_scaledR5]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

/-! ### The Vieta argument -/

/-- The Vieta argument for one pair `a, b` of roots of `x⁵ − x⁴ + 4τx² − 16δ`
with remaining roots `c, d, e`: then `a + b ≤ 4/3`, strictly if `δ > 0`. -/
theorem add_le_four_thirds_of_vieta (a b c d e δ : ℝ) (hδ : 0 ≤ δ)
    (H1 : a + b + c + d + e = 1)
    (H2 : a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d + c * e + d * e = 0)
    (H4 : a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e = 0)
    (H5 : a * b * c * d * e = 16 * δ) :
    a + b ≤ 4/3 ∧ (0 < δ → a + b < 4/3) := by
  -- the squares of the roots sum to `1`, so each root is at most `1`
  have hsq : a^2 + b^2 + c^2 + d^2 + e^2 = 1 := by
    linear_combination (a + b + c + d + e + 1) * H1 - 2 * H2
  have ha1 : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg (a - 1)]
  have hb1 : b ≤ 1 := by
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg (b - 1)]
  rcases le_or_gt a 0 with ha | ha
  · exact ⟨by linarith, fun _ ↦ by linarith⟩
  rcases le_or_gt b 0 with hb | hb
  · exact ⟨by linarith, fun _ ↦ by linarith⟩
  -- now `s = a + b > 0` and `q = a b > 0`; write `B = cd + ce + de`
  have hs : 0 < a + b := by linarith
  have hq2 : 0 < (a * b) ^ 2 := pow_pos (mul_pos ha hb) 2
  have hB : c*d + c*e + d*e = -(a*b) - (a + b) * (1 - (a + b)) := by
    linear_combination H2 - (a + b) * H1
  have key : (a*b)^2 * (c*d + c*e + d*e) = -16 * (a + b) * δ := by
    linear_combination (a*b) * H4 - (a + b) * H5
  have hamgm : 4 * (a * b) ≤ (a + b)^2 := by nlinarith [sq_nonneg (a - b)]
  refine ⟨?_, fun hδpos ↦ ?_⟩
  · -- `q² B = −16 s δ ≤ 0`, hence `B ≤ 0`, hence `s(s−1) ≤ q ≤ s²/4`
    have hBle : c*d + c*e + d*e ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have h1 : 0 < (a*b)^2 * (c*d + c*e + d*e) := mul_pos hq2 hcon
      nlinarith [mul_nonneg hs.le hδ]
    have h34 : (a + b) * (3 * (a + b) - 4) ≤ 0 := by nlinarith [hB, hBle, hamgm]
    by_contra hcon
    push Not at hcon
    have : 0 < (a + b) * (3 * (a + b) - 4) := mul_pos hs (by linarith)
    linarith
  · -- if `δ > 0`, then `B < 0` and all inequalities are strict
    have hBlt : c*d + c*e + d*e < 0 := by
      by_contra hcon
      push Not at hcon
      have h1 : 0 ≤ (a*b)^2 * (c*d + c*e + d*e) := mul_nonneg hq2.le hcon
      nlinarith [mul_pos hs hδpos]
    have h34 : (a + b) * (3 * (a + b) - 4) < 0 := by nlinarith [hB, hBlt, hamgm]
    by_contra hcon
    push Not at hcon
    have : 0 ≤ (a + b) * (3 * (a + b) - 4) := mul_nonneg hs.le (by linarith)
    linarith

/-- Vieta for the pair `μ 0, μ 1`: coefficients are read off by evaluating at `0, ±1, ±2`. -/
theorem root_zero_add_root_one_le (μ : Fin 5 → ℝ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x : ℝ, ∏ i, (x - μ i) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ) :
    μ 0 + μ 1 ≤ 4/3 ∧ (0 < δ → μ 0 + μ 1 < 4/3) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  have h4 := h (-2)
  simp only [Fin.prod_univ_five] at h0 h1 h2 h3 h4
  apply add_le_four_thirds_of_vieta (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) δ hδ
  · linear_combination (-1/24 : ℝ) * (h3 + h4 - 4 * h1 - 4 * h2 + 6 * h0)
  · linear_combination (h3 - h4 - 2 * (h1 - h2)) / 12
  · linear_combination (8 * (h1 - h2) - (h3 - h4)) / 12
  · linear_combination (-1 : ℝ) * h0

/-- Any two distinct indices can be moved to `0, 1` by a permutation. -/
private theorem exists_perm_zero_one (i j : Fin 5) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = i ∧ σ 1 = j := by
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have hj : Equiv.swap 0 i j ≠ 0 := by
    intro h
    apply hij
    have := congrArg (Equiv.swap 0 i) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h01 hj.symm, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Vieta for an arbitrary pair of roots. -/
theorem root_add_root_le (μ : Fin 5 → ℝ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x : ℝ, ∏ i, (x - μ i) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ)
    (i j : Fin 5) (hij : i ≠ j) :
    μ i + μ j ≤ 4/3 ∧ (0 < δ → μ i + μ j < 4/3) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one i j hij
  have h' : ∀ x : ℝ, ∏ k, (x - (μ ∘ σ) k) = x ^ 5 - x ^ 4 + 4 * t * x ^ 2 - 16 * δ := by
    intro x
    rw [← h x]
    exact Equiv.prod_comp σ (fun k ↦ x - μ k)
  have := root_zero_add_root_one_le (μ ∘ σ) t δ hδ h'
  simp only [Function.comp_apply, hσ0, hσ1] at this
  exact this

/-! ### [JFA-E, Proposition F], assuming that the characteristic polynomial splits -/

/-- If `∑ sᵢ² = 1` and `charpoly (scaledR5 s) = ∏ (X − μᵢ)`, then `μᵢ + μⱼ ≤ 4/3` for `i ≠ j`,
with strict inequality if all `sᵢ ≠ 0`. -/
theorem root_add_root_le_of_charpoly (s μ : Fin 5 → ℝ) (hs : ∑ i, s i ^ 2 = 1)
    (hμ : (scaledR5 s).charpoly = ∏ i, (X - C (μ i))) (i j : Fin 5) (hij : i ≠ j) :
    μ i + μ j ≤ 4/3 ∧ ((∀ k, s k ≠ 0) → μ i + μ j < 4/3) := by
  have hs' : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 + s 4 ^ 2 = 1 := by
    simpa [Fin.sum_univ_five] using hs
  have h : ∀ x : ℝ, ∏ i, (x - μ i) = x ^ 5 - x ^ 4 + 4 * tripleSum s * x ^ 2 - 16 * prodSq s := by
    intro x
    have := congrArg (Polynomial.eval x) hμ
    rw [Matrix.eval_charpoly, det_scalar_sub_scaledR5, hs', Polynomial.eval_prod] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    linear_combination -this
  have hδ : 0 ≤ prodSq s := by unfold prodSq; positivity
  have H := root_add_root_le μ (tripleSum s) (prodSq s) hδ h i j hij
  refine ⟨H.1, fun hk ↦ H.2 ?_⟩
  have hne : s 0 * s 1 * s 2 * s 3 * s 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hk 0) (hk 1)) (hk 2)) (hk 3)) (hk 4)
  unfold prodSq
  exact sq_pos_iff.mpr hne

/-- For `s² = (1/3, 1/3, 0, 1/3, 0)`, i.e. `D = ⅓ Diag(1,1,0,1,0)`, the characteristic
polynomial is `X² (X − 2/3)² (X + 1/3)`, so two of the roots sum to `4/3`. -/
theorem exists_root_add_root_eq_of_charpoly (s μ : Fin 5 → ℝ)
    (h0 : s 0 ^ 2 = 1 / 3) (h1 : s 1 ^ 2 = 1 / 3) (h2 : s 2 = 0) (h3 : s 3 ^ 2 = 1 / 3)
    (h4 : s 4 = 0)
    (hμ : (scaledR5 s).charpoly = ∏ i, (X - C (μ i))) :
    ∃ i j, i ≠ j ∧ μ i + μ j = 4/3 := by
  have hchar : (scaledR5 s).charpoly = X ^ 2 * (X - C (2/3)) ^ 2 * (X - C (-1/3)) := by
    apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly, det_scalar_sub_scaledR5]
    simp only [tripleSum, prodSq, h2, h4, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [h0, h1, h3]
    ring
  have hne1 : (X ^ 2 * (X - C (2/3)) ^ 2 : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
  have hne2 : (X ^ 2 * (X - C (2/3)) ^ 2 * (X - C (-1/3)) : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero hne1 (Polynomial.X_sub_C_ne_zero _)
  -- the roots of `∏ (X − μᵢ)` are the `μᵢ`
  have hroots : (scaledR5 s).charpoly.roots = Finset.univ.val.map μ := by
    rw [hμ, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  -- `2/3` is a double root
  have hcount : Multiset.count (2/3 : ℝ) (Finset.univ.val.map μ) = 2 := by
    rw [← hroots, hchar, Polynomial.roots_mul hne2, Polynomial.roots_mul hne1]
    norm_num [Polynomial.roots_pow, Polynomial.roots_X, Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val] at hcount
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hcount]; norm_num)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact ⟨a, b, hab, by rw [← ha, ← hb]; norm_num⟩

end ProjectionConstants.GrunbaumConjecture
