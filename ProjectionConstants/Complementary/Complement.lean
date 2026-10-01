/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Formula

/-!
# Complementary projections and the `k`-fold repetition of a frame

This file proves the lower bound in the formula for maximal relative projection constants in
complementary dimensions [DL26, Theorem 3.1] (`ProjectionConstants.Complementary.Main`). If `Q`
is an orthogonal projection of rank `m` on `𝕜^N`, then `1 - Q` is an orthogonal projection of
rank `N - m` with `∑ᵢⱼ |(1 - Q)ᵢⱼ| = N - 2m + ∑ᵢⱼ |Qᵢⱼ|`. We apply this to the `k`-fold
repetition of an optimal equal-weight frame of `M` vectors in `𝕜^m` and obtain
`μ_𝕜(m, M) + 1 - 2m/(kM) ≤ μ_𝕜(kM - m, kM)`.

## Main definitions

* `repeatProj k P₀`: the `k`-fold repetition `(1/k) Jₖ ⊗ P₀` of a matrix `P₀`, the Gram matrix of
  the frame `k^{-1/2} [U | ⋯ | U]` if `P₀ = Uᴴ U`.

## Main statements

* `one_sub_mem_orthProjs`: if `P` is an orthogonal projection of rank `n` on `𝕜^N`, then `1 - P`
  is one of rank `N - n`.
* `weightedAbsSum_one_sub`: `∑ᵢⱼ tᵢ tⱼ |(1 - Q)ᵢⱼ| = ∑ tᵢ² - 2 ∑ tᵢ² Qᵢᵢ + ∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|`.
* `absSum_one_sub`: `∑ᵢⱼ |(1 - Q)ᵢⱼ| = N - 2m + ∑ᵢⱼ |Qᵢⱼ|`.
* `repeatProj_mem_orthProjs`, `absSum_repeatProj`: `repeatProj k P₀` is an orthogonal
  projection of the same rank as `P₀`, and `∑ᵢⱼ |(repeatProj k P₀)ᵢⱼ| = k ∑ᵢⱼ |(P₀)ᵢⱼ|`.
* `quasiRelConst_add_le_quasiRelConst`: the lower bound of [DL26, Theorem 3.1],
  `μ_𝕜(m, M) + 1 - 2m/(kM) ≤ μ_𝕜(kM - m, kM)`.
* `quasiRelConst_add_le_clConst`: the same lower bound for `λ_𝕜(kM - m, kM)`.

## References

* [DL26] B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection constants*,
  arXiv:2609.29422.
-/

open Finset Matrix

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complementary projection `1 - P` of an orthogonal projection of rank `n` has rank
`N - n`. -/
lemma one_sub_mem_orthProjs {n : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι n) :
    1 - P ∈ orthProjs 𝕜 ι (Fintype.card ι - n) := by
  refine ⟨hP.1.one_sub, ?_⟩
  rw [trace_sub, trace_one, hP.2, Nat.cast_sub (le_card_of_mem_orthProjs hP)]

/-- `∑ᵢⱼ tᵢ tⱼ |(1 - Q)ᵢⱼ| = ∑ᵢ tᵢ² - 2 ∑ᵢ tᵢ² Qᵢᵢ + ∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` for an orthogonal projection
`Q`. -/
lemma weightedAbsSum_one_sub (t : ι → ℝ) {Q : Matrix ι ι 𝕜} (hQ : IsStarProjection Q) :
    weightedAbsSum t (1 - Q) =
      ∑ i, t i ^ 2 - 2 * ∑ i, t i ^ 2 * RCLike.re (Q i i) + weightedAbsSum t Q := by
  have hentry : ∀ i j, ‖(1 - Q) i j‖ =
      ‖Q i j‖ + if i = j then 1 - 2 * RCLike.re (Q i i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := hQ.re_diag_le_one i
      have hn1 : ‖(1 : 𝕜) - Q i i‖ = 1 - RCLike.re (Q i i) := by
        conv_lhs => rw [hQ.diag_eq_re i, ← RCLike.ofReal_one, ← RCLike.ofReal_sub,
          RCLike.norm_ofReal]
        exact abs_of_nonneg (by linarith)
      rw [Matrix.sub_apply, one_apply_eq, hn1, hQ.norm_diag_eq]
      simp only [↓reduceIte]
      ring
    · rw [Matrix.sub_apply, one_apply_ne hij, zero_sub, norm_neg]
      simp [hij]
  unfold weightedAbsSum
  simp only [hentry, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, mem_univ,
    ite_true]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ ↦ by ring

omit [DecidableEq ι] in
/-- `∑ᵢⱼ |Pᵢⱼ|` is the weighted sum with all weights equal to `1`. -/
lemma absSum_eq_weightedAbsSum_one (P : Matrix ι ι 𝕜) :
    absSum P = weightedAbsSum (fun _ ↦ (1 : ℝ)) P := by
  simp [absSum, weightedAbsSum]

/-- `∑ᵢⱼ |(1 - Q)ᵢⱼ| = N - 2m + ∑ᵢⱼ |Qᵢⱼ|` for an orthogonal projection `Q` of rank `m`. -/
lemma absSum_one_sub {m : ℕ} {Q : Matrix ι ι 𝕜} (hQ : Q ∈ orthProjs 𝕜 ι m) :
    absSum (1 - Q) = Fintype.card ι - 2 * m + absSum Q := by
  rw [absSum_eq_weightedAbsSum_one, weightedAbsSum_one_sub _ hQ.1, ← absSum_eq_weightedAbsSum_one]
  simp [sum_re_diag hQ]

/-! ### Repeating a frame `k` times -/

/-- The `k`-fold repetition `(1/k) Jₖ ⊗ P₀` of a matrix `P₀`: the Gram matrix of the frame
`k^{-1/2} [U | ⋯ | U]` if `P₀ = Uᴴ U`. -/
def repeatProj (k : ℕ) {κ : Type*} (P₀ : Matrix κ κ 𝕜) : Matrix (Fin k × κ) (Fin k × κ) 𝕜 :=
  Matrix.of fun p q ↦ (k : 𝕜)⁻¹ * P₀ p.2 q.2

omit [Fintype ι] [DecidableEq ι] in
/-- For `k ≠ 0`, the `k`-fold repetition of an orthogonal projection of rank `m` is an orthogonal
projection of rank `m`. -/
lemma repeatProj_mem_orthProjs {k : ℕ} (hk : k ≠ 0) {κ : Type*} [Fintype κ] {m : ℕ}
    {P₀ : Matrix κ κ 𝕜} (hP₀ : P₀ ∈ orthProjs 𝕜 κ m) :
    repeatProj k P₀ ∈ orthProjs 𝕜 (Fin k × κ) m := by
  have hk' : (k : 𝕜) ≠ 0 := by exact_mod_cast hk
  refine ⟨.of_conjTranspose_eq ?_ ?_, ?_⟩
  · ext p q
    simp only [repeatProj, conjTranspose_apply, of_apply, star_mul', star_inv₀, star_natCast]
    rw [← hP₀.1.apply_symm]
  · ext p q
    simp only [repeatProj, mul_apply, of_apply, Fintype.sum_prod_type, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have h := congrFun (congrFun hP₀.1.mul_self p.2) q.2
    rw [mul_apply] at h
    rw [← h, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    field_simp
  · have h := hP₀.2
    simp only [trace, diag_apply] at h ⊢
    simp only [repeatProj, of_apply, Fintype.sum_prod_type, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, h]
    field_simp

omit [Fintype ι] [DecidableEq ι] in
/-- `∑ᵢⱼ |(repeatProj k P₀)ᵢⱼ| = k ∑ᵢⱼ |(P₀)ᵢⱼ|`. -/
lemma absSum_repeatProj (k : ℕ) {κ : Type*} [Fintype κ] (P₀ : Matrix κ κ 𝕜) :
    absSum (repeatProj k P₀) = k * absSum P₀ := by
  simp only [absSum, repeatProj, of_apply, Fintype.sum_prod_type, norm_mul, norm_inv,
    RCLike.norm_natCast, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · field_simp

/-- **The lower bound of [DL26, Theorem 3.1].** Repeating a frame `k` times and passing to the
complement gives an equal-norm frame with `μ_𝕜(m, M) + 1 - 2m/(kM) ≤ μ_𝕜(kM - m, kM)`. -/
theorem quasiRelConst_add_le_quasiRelConst {m M k : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (hmM : m ≤ M) :
    quasiRelConst 𝕜 (Fin M) m + 1 - 2 * m / (k * M) ≤
      quasiRelConst 𝕜 (Fin (k * M)) (k * M - m) := by
  classical
  obtain ⟨P₀, hP₀, hval⟩ := exists_quasiRelConst_eq (𝕜 := 𝕜) (ι := Fin M) (by simpa using hmM)
  have hQ := repeatProj_mem_orthProjs (by omega : k ≠ 0) hP₀
  have hP := one_sub_mem_orthProjs hQ
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hP
  have hP' := submatrix_mem_orthProjs (finProdFinEquiv (m := k) (n := M)).symm hP
  have h1 := le_quasiRelConst hP'
  rw [absSum_submatrix, Fintype.card_fin, absSum_one_sub hQ, absSum_repeatProj,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
  refine le_trans (le_of_eq ?_) h1
  rw [← hval, Fintype.card_fin]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  field_simp
  ring

/-- `μ_𝕜(m, M) + 1 - 2m/(kM) ≤ λ_𝕜(kM - m, kM)`, with `λ_𝕜(kM - m, kM)` written as `clConst`
(see `maxRelProjConst_eq_clConst`). -/
theorem quasiRelConst_add_le_clConst {m M k : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (hmM : m ≤ M) :
    quasiRelConst 𝕜 (Fin M) m + 1 - 2 * m / (k * M) ≤ clConst 𝕜 (Fin (k * M)) (k * M - m) :=
  (quasiRelConst_add_le_quasiRelConst hk hM hmM).trans quasiRelConst_le_clConst

end ProjectionConstants
