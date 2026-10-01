/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Real dot products and quadratic forms

Elementary facts about the dot product `x ⬝ᵥ y` of real vectors and about quadratic forms
`x ⬝ᵥ A *ᵥ x`. Linear combinations `a x + b y` are written pointwise, as
`fun i ↦ a * x i + b * y i`.

## Main statements

* `dotProduct_self_nonneg`, `eq_zero_of_dotProduct_self_eq_zero`: `u ⬝ᵥ u ≥ 0`, with equality
  only for `u = 0`.
* `sq_le_one_of_dotProduct_self`, `abs_le_one_of_dotProduct_self`: the coordinates of a unit
  vector are at most one in absolute value.
* `linearComb_dotProduct`, `dotProduct_linearComb`: the dot product is bilinear.
* `Matrix.dotProduct_mulVec_self_eq_sum`: `u ⬝ᵥ A *ᵥ u = ∑ᵢⱼ Aᵢⱼ uᵢ uⱼ`.
* `Matrix.linearComb_dotProduct_mulVec_linearComb`: the quadratic form of a symmetric matrix at a
  linear combination `a x + b z`.
-/

open Finset

variable {ι : Type*} [Fintype ι]

/-- `u ⬝ᵥ u ≥ 0` for a real vector `u`. -/
lemma dotProduct_self_nonneg (u : ι → ℝ) : 0 ≤ u ⬝ᵥ u :=
  sum_nonneg fun i _ ↦ mul_self_nonneg (u i)

/-- If `u ⬝ᵥ u = 0`, then every coordinate of the real vector `u` vanishes. -/
lemma eq_zero_of_dotProduct_self_eq_zero {u : ι → ℝ} (h : u ⬝ᵥ u = 0) (i : ι) : u i = 0 :=
  congrFun (dotProduct_self_eq_zero.1 h) i

/-- The coordinates of a unit vector satisfy `uᵢ² ≤ 1`. -/
lemma sq_le_one_of_dotProduct_self {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (i : ι) : u i ^ 2 ≤ 1 := by
  rw [← hu, dotProduct, sq]
  exact single_le_sum (f := fun k ↦ u k * u k) (fun k _ ↦ mul_self_nonneg (u k)) (mem_univ i)

/-- The coordinates of a unit vector are at most one in absolute value. -/
lemma abs_le_one_of_dotProduct_self {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (i : ι) : |u i| ≤ 1 :=
  abs_le_of_sq_le_sq (by simpa using sq_le_one_of_dotProduct_self hu i) zero_le_one

/-- `(a x + b y) ⬝ᵥ z = a (x ⬝ᵥ z) + b (y ⬝ᵥ z)`. -/
lemma linearComb_dotProduct (x y z : ι → ℝ) (a b : ℝ) :
    (fun i ↦ a * x i + b * y i) ⬝ᵥ z = a * (x ⬝ᵥ z) + b * (y ⬝ᵥ z) := by
  simp only [dotProduct, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- `z ⬝ᵥ (a x + b y) = a (z ⬝ᵥ x) + b (z ⬝ᵥ y)`. -/
lemma dotProduct_linearComb (x y z : ι → ℝ) (a b : ℝ) :
    z ⬝ᵥ (fun i ↦ a * x i + b * y i) = a * (z ⬝ᵥ x) + b * (z ⬝ᵥ y) := by
  rw [dotProduct_comm, linearComb_dotProduct, dotProduct_comm x, dotProduct_comm y]

namespace Matrix

/-- The quadratic form of a matrix as a double sum: `u ⬝ᵥ A *ᵥ u = ∑ᵢⱼ Aᵢⱼ uᵢ uⱼ`. -/
lemma dotProduct_mulVec_self_eq_sum (A : Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ A *ᵥ u = ∑ i, ∑ j, A i j * u i * u j := by
  simp only [dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- The quadratic form of a symmetric matrix `A` at a linear combination `a x + b z` is
`a² xᵀAx + 2ab zᵀAx + b² zᵀAz`. -/
lemma linearComb_dotProduct_mulVec_linearComb {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x z : ι → ℝ)
    (a b : ℝ) :
    (fun i ↦ a * x i + b * z i) ⬝ᵥ A *ᵥ (fun i ↦ a * x i + b * z i) =
      a ^ 2 * (x ⬝ᵥ A *ᵥ x) + 2 * a * b * (z ⬝ᵥ A *ᵥ x) + b ^ 2 * (z ⬝ᵥ A *ᵥ z) := by
  have h1 : (fun i ↦ a * x i + b * z i) ⬝ᵥ A *ᵥ (fun i ↦ a * x i + b * z i) =
      a ^ 2 * (x ⬝ᵥ A *ᵥ x) + a * b * (x ⬝ᵥ A *ᵥ z + z ⬝ᵥ A *ᵥ x) + b ^ 2 * (z ⬝ᵥ A *ᵥ z) := by
    simp only [↓dotProduct_mulVec_self_eq_sum, dotProduct, mulVec, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    ring
  rw [h1, hA.dotProduct_mulVec_comm (x := x) (y := z)]
  ring

end Matrix
