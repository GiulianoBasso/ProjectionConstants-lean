/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ForMathlib.Matrix.DotProduct
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Star projections of matrices

A matrix `P ∈ 𝕜^{ι×ι}` over `𝕜 = ℝ` or `ℂ` is an orthogonal projection if and only if it is a star
projection in the sense of Mathlib (`IsStarProjection P`), that is, `Pᴴ = P` and `P * P = P`.
This is the notion of orthogonal projection used throughout the library. This file collects
elementary facts about the entries and the quadratic form of such matrices; the orthogonal
projections of a given rank are studied in `ProjectionConstants.Matrix.OrthProj`.

## Main statements

* `IsStarProjection.of_conjTranspose_eq`: a constructor from `Pᴴ = P` and `P * P = P`.
* `IsStarProjection.diag_eq`, `IsStarProjection.norm_apply_le_one`,
  `IsStarProjection.norm_apply_sq_le_mul`: `Pᵢᵢ = ∑ₖ |Pₖᵢ|²`, `|Pᵢⱼ| ≤ 1`, `|Pᵢⱼ|² ≤ Pᵢᵢ Pⱼⱼ`.
* `IsStarProjection.submatrix`: relabelling the index set preserves star projections.
* `IsStarProjection.apply_comm`, `IsStarProjection.diag_eq_sum_sq`,
  `IsStarProjection.sq_apply_le_mul`: a real star projection is symmetric, `Pᵢᵢ = ∑ₖ Pᵢₖ²` and
  `Pᵢⱼ² ≤ Pᵢᵢ Pⱼⱼ`.
* `IsStarProjection.of_apply`: a real matrix that is entrywise symmetric and idempotent is a star
  projection.
* `IsStarProjection.dotProduct_mulVec_eq_sum_sq`, `IsStarProjection.dotProduct_mulVec_nonneg`,
  `IsStarProjection.dotProduct_mulVec_le`: `0 ≤ xᵀ P x = ‖P x‖² ≤ ‖x‖²` for a real star
  projection `P`.
-/

open Finset Matrix

namespace IsStarProjection

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-! ### Entries of star projections over `ℝ` or `ℂ` -/

section RCLike

/-- A matrix `P` with `Pᴴ = P` and `P * P = P` is a star projection. -/
lemma of_conjTranspose_eq {P : Matrix ι ι 𝕜} (h₁ : Pᴴ = P) (h₂ : P * P = P) :
    IsStarProjection P :=
  ⟨h₂, h₁⟩

variable {P : Matrix ι ι 𝕜} (hP : IsStarProjection P)
include hP

/-- A star projection is Hermitian: `Pᴴ = P`. -/
lemma conjTranspose_eq : Pᴴ = P := hP.isSelfAdjoint

/-- A star projection is idempotent: `P * P = P`. -/
lemma mul_self : P * P = P := hP.isIdempotentElem

/-- `Pⱼᵢ = conj(Pᵢⱼ)`. -/
lemma apply_symm (i j : ι) : P j i = star (P i j) := by
  conv_lhs => rw [← hP.conjTranspose_eq]
  rfl

/-- `|Pⱼᵢ| = |Pᵢⱼ|`. -/
lemma norm_apply_symm (i j : ι) : ‖P j i‖ = ‖P i j‖ := by
  rw [hP.apply_symm, norm_star]

/-- `Pᴴ P = P`. -/
lemma conjTranspose_mul_self : Pᴴ * P = P := by rw [hP.conjTranspose_eq, hP.mul_self]

/-- The diagonal entries: `Pᵢᵢ = ∑ₖ |Pₖᵢ|²`. -/
lemma diag_eq (i : ι) : P i i = ((∑ k, ‖P k i‖ ^ 2 : ℝ) : 𝕜) := by
  conv_lhs => rw [← hP.conjTranspose_mul_self]
  simp only [mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  push_cast
  rfl

/-- `Re Pᵢᵢ = ∑ₖ |Pₖᵢ|²` (sum over the `i`-th column). -/
lemma re_diag (i : ι) : RCLike.re (P i i) = ∑ k, ‖P k i‖ ^ 2 := by
  rw [hP.diag_eq i, RCLike.ofReal_re]

/-- The diagonal entries of a star projection are real. -/
lemma diag_eq_re (i : ι) : P i i = (RCLike.re (P i i) : 𝕜) := by
  rw [hP.re_diag, hP.diag_eq]

/-- `Re Pᵢᵢ = ∑ₖ |Pᵢₖ|²` (sum over the `i`-th row). -/
lemma re_diag_eq_sum_row (i : ι) : RCLike.re (P i i) = ∑ k, ‖P i k‖ ^ 2 := by
  rw [hP.re_diag]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hP.norm_apply_symm]

/-- `0 ≤ Re Pᵢᵢ`. -/
lemma re_diag_nonneg (i : ι) : 0 ≤ RCLike.re (P i i) := by
  rw [hP.re_diag]
  exact Finset.sum_nonneg fun k _ ↦ by positivity

/-- `|Pᵢⱼ|² ≤ Re Pⱼⱼ`. -/
lemma norm_apply_sq_le (i j : ι) : ‖P i j‖ ^ 2 ≤ RCLike.re (P j j) := by
  rw [hP.re_diag]
  exact Finset.single_le_sum (f := fun k ↦ ‖P k j‖ ^ 2) (fun k _ ↦ by positivity)
    (Finset.mem_univ i)

/-- `|Pᵢᵢ| = Re Pᵢᵢ`. -/
lemma norm_diag_eq (i : ι) : ‖P i i‖ = RCLike.re (P i i) := by
  rw [hP.diag_eq_re i, RCLike.norm_ofReal, abs_of_nonneg (by simpa using hP.re_diag_nonneg i)]
  simp

/-- `Re Pᵢᵢ ≤ 1`. -/
lemma re_diag_le_one (i : ι) : RCLike.re (P i i) ≤ 1 := by
  have h := hP.norm_apply_sq_le i i
  rw [hP.norm_diag_eq] at h
  nlinarith [hP.re_diag_nonneg i]

/-- The entries of a star projection satisfy `|Pᵢⱼ| ≤ 1`. -/
lemma norm_apply_le_one (i j : ι) : ‖P i j‖ ≤ 1 := by
  have h := (hP.norm_apply_sq_le i j).trans (hP.re_diag_le_one j)
  nlinarith [norm_nonneg (P i j)]

/-- `|Pᵢⱼ|² ≤ Pᵢᵢ Pⱼⱼ` (Cauchy–Schwarz for the Gram matrix `P = Pᴴ P`). -/
lemma norm_apply_sq_le_mul (i j : ι) :
    ‖P i j‖ ^ 2 ≤ RCLike.re (P i i) * RCLike.re (P j j) := by
  -- `Pᵢⱼ = ∑ₖ conj(Pₖᵢ) Pₖⱼ`, then Cauchy–Schwarz
  have hij : P i j = ∑ k, star (P k i) * P k j := by
    conv_lhs => rw [← hP.conjTranspose_mul_self]
    simp [mul_apply]
  have h1 : ‖P i j‖ ≤ ∑ k, ‖P k i‖ * ‖P k j‖ := by
    rw [hij]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 : (∑ k, ‖P k i‖ * ‖P k j‖) ^ 2 ≤ (∑ k, ‖P k i‖ ^ 2) * ∑ k, ‖P k j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hP.re_diag, hP.re_diag]
  calc ‖P i j‖ ^ 2 ≤ (∑ k, ‖P k i‖ * ‖P k j‖) ^ 2 := by gcongr
    _ ≤ _ := h2

/-- `∑ₖ Pᵢₖ Pₖⱼ = Pᵢⱼ`. -/
lemma sum_mul_apply (i j : ι) : ∑ k, P i k * P k j = P i j := by
  have := congrFun (congrFun hP.mul_self i) j
  rwa [Matrix.mul_apply] at this

/-- Relabelling the index set along an equivalence `e` preserves star projections. -/
lemma submatrix {κ : Type*} [Fintype κ] (e : κ ≃ ι) : IsStarProjection (P.submatrix e e) :=
  ⟨(submatrix_mul_equiv P P e e e).trans (by rw [hP.mul_self]),
    (conjTranspose_submatrix P e e).trans (by rw [hP.conjTranspose_eq])⟩

end RCLike

/-! ### Real star projections -/

section Real

variable {P : Matrix ι ι ℝ} (hP : IsStarProjection P)
include hP

/-- A real star projection is symmetric: `Pⱼᵢ = Pᵢⱼ`. -/
lemma apply_comm (i j : ι) : P j i = P i j := by
  rw [hP.apply_symm, star_trivial]

/-- A real star projection is a symmetric matrix. -/
lemma isSymm : P.IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ hP.apply_comm i j

/-- `Pᵢᵢ = ∑ₖ Pᵢₖ²`. -/
lemma diag_eq_sum_sq (i : ι) : P i i = ∑ k, P i k ^ 2 := by
  rw [← hP.sum_mul_apply i i]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hP.apply_comm i k, sq]

/-- `Pᵢⱼ² ≤ Pᵢᵢ`. -/
lemma sq_apply_le_diag (i j : ι) : P i j ^ 2 ≤ P i i := by
  rw [hP.diag_eq_sum_sq i]
  exact Finset.single_le_sum (f := fun k ↦ P i k ^ 2) (fun k _ ↦ sq_nonneg (P i k))
    (Finset.mem_univ j)

/-- `0 ≤ Pᵢᵢ`. -/
lemma diag_nonneg (i : ι) : 0 ≤ P i i := by
  rw [hP.diag_eq_sum_sq i]
  exact Finset.sum_nonneg fun k _ ↦ sq_nonneg _

/-- `Pᵢᵢ ≤ 1`. -/
lemma diag_le_one (i : ι) : P i i ≤ 1 := by
  have h1 := hP.sq_apply_le_diag i i
  have h2 := hP.diag_nonneg i
  nlinarith

/-- `|Pᵢⱼ| ≤ 1`. -/
lemma abs_apply_le_one (i j : ι) : |P i j| ≤ 1 := by
  simpa using hP.norm_apply_le_one i j

/-- `Pᵢⱼ² ≤ Pᵢᵢ Pⱼⱼ`. -/
lemma sq_apply_le_mul (i j : ι) : P i j ^ 2 ≤ P i i * P j j := by
  simpa using hP.norm_apply_sq_le_mul i j

end Real

/-- A real matrix that is entrywise symmetric and idempotent is a star projection. -/
lemma of_apply {P : Matrix ι ι ℝ} (hsymm : ∀ i j, P j i = P i j)
    (hidem : ∀ i j, ∑ k, P i k * P k j = P i j) : IsStarProjection P :=
  ⟨show P * P = P by ext i j; simp [mul_apply, hidem],
    show Pᴴ = P by ext i j; simp [conjTranspose_apply, hsymm]⟩

/-! ### The quadratic form of a real star projection -/

section Quadratic

variable {P : Matrix ι ι ℝ} (hP : IsStarProjection P)
include hP

/-- `xᵀPx = ‖Px‖² = ∑ₗ (∑ᵢ Pₗᵢ xᵢ)²` for a real star projection `P`. -/
lemma dotProduct_mulVec_eq_sum_sq (x : ι → ℝ) :
    x ⬝ᵥ P *ᵥ x = ∑ l, (∑ i, P l i * x i) ^ 2 := by
  have e : ∀ i j, P i j * x i * x j = ∑ l, (P l i * x i) * (P l j * x j) := fun i j ↦ by
    rw [← hP.sum_mul_apply i j, sum_mul, sum_mul]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [hP.apply_comm l i]
    ring
  rw [dotProduct_mulVec_self_eq_sum]
  rw [sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ e i j]
  simp only [sq, sum_mul_sum]
  calc ∑ i, ∑ j, ∑ l, P l i * x i * (P l j * x j)
      = ∑ i, ∑ l, ∑ j, P l i * x i * (P l j * x j) := sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ l, ∑ i, ∑ j, P l i * x i * (P l j * x j) := sum_comm

/-- `0 ≤ xᵀPx` for a real star projection `P`. -/
lemma dotProduct_mulVec_nonneg (x : ι → ℝ) : 0 ≤ x ⬝ᵥ P *ᵥ x := by
  rw [hP.dotProduct_mulVec_eq_sum_sq]
  exact sum_nonneg fun l _ ↦ sq_nonneg _

/-- `xᵀPx ≤ xᵀx` for a real star projection `P`. -/
lemma dotProduct_mulVec_le (x : ι → ℝ) : x ⬝ᵥ P *ᵥ x ≤ x ⬝ᵥ x := by
  classical
  have h := hP.one_sub.dotProduct_mulVec_nonneg x
  have e : x ⬝ᵥ (1 - P) *ᵥ x = x ⬝ᵥ x - x ⬝ᵥ P *ᵥ x := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
  linarith

end Quadratic

end IsStarProjection
