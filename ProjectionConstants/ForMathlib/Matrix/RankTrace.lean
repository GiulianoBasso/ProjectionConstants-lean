/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Chebyshev

/-!
# Trace, rank and Frobenius norm

For a real symmetric matrix `A`, `(tr A)² ≤ rank(A) · ∑ᵢⱼ Aᵢⱼ²` (see [Bernstein, *Matrix
Mathematics*, Fact 7.12.13]). This is the Cauchy–Schwarz inequality for the nonzero eigenvalues
of `A`: `tr A = ∑ λᵢ`, `∑ᵢⱼ Aᵢⱼ² = ∑ λᵢ²`, and exactly `rank A` eigenvalues are nonzero. The
inequality is used in the proof of the Bukh–Cox bound (`ProjectionConstants.Bounds.BukhCox`).

## Main statements

* `Matrix.IsHermitian.sum_sq_eq_sum_eigenvalues_sq`: `∑ᵢⱼ Aᵢⱼ² = ∑ᵢ λᵢ²`.
* `Matrix.IsHermitian.sq_trace_le_rank_mul`: `(tr A)² ≤ rank(A) · ∑ᵢⱼ Aᵢⱼ²`.
-/

open Matrix Finset

namespace Matrix.IsHermitian

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a real symmetric matrix, `∑ᵢⱼ Aᵢⱼ²` is the sum of the squared eigenvalues. -/
theorem sum_sq_eq_sum_eigenvalues_sq {A : Matrix κ κ ℝ} (hA : A.IsHermitian) :
    ∑ i, ∑ j, A i j ^ 2 = ∑ i, hA.eigenvalues i ^ 2 := by
  have hsymm : ∀ i j, A j i = A i j := fun i j ↦ by
    have := congrFun (congrFun hA i) j
    simpa using this
  have h1 : ∑ i, ∑ j, A i j ^ 2 = (A * A).trace := by
    simp only [Matrix.trace, diag_apply, mul_apply]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hsymm, sq]
  set U := hA.eigenvectorUnitary
  set D : Matrix κ κ ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = (U : Matrix κ κ ℝ) * D * (star U : Matrix κ κ ℝ) := hA.spectral_theorem
  have hUU : (star U : Matrix κ κ ℝ) * (U : Matrix κ κ ℝ) = 1 := Unitary.coe_star_mul_self U
  have h2 : (A * A).trace = (D * D).trace := by
    rw [hspec]
    calc ((U : Matrix κ κ ℝ) * D * (star U : Matrix κ κ ℝ) * ((U : Matrix κ κ ℝ) * D *
          (star U : Matrix κ κ ℝ))).trace
        = ((U : Matrix κ κ ℝ) * (D * ((star U : Matrix κ κ ℝ) * (U : Matrix κ κ ℝ)) * D) *
            (star U : Matrix κ κ ℝ)).trace := by simp only [Matrix.mul_assoc]
      _ = ((U : Matrix κ κ ℝ) * (D * D) * (star U : Matrix κ κ ℝ)).trace := by
          rw [hUU, Matrix.mul_one]
      _ = ((D * D) * ((star U : Matrix κ κ ℝ) * (U : Matrix κ κ ℝ))).trace := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = (D * D).trace := by rw [hUU, Matrix.mul_one]
  rw [h1, h2, diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

omit [DecidableEq κ] in
/-- **`(tr A)² ≤ rank(A) · ∑ᵢⱼ Aᵢⱼ²`** for real symmetric matrices. -/
theorem sq_trace_le_rank_mul {A : Matrix κ κ ℝ} (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ A.rank * ∑ i, ∑ j, A i j ^ 2 := by
  classical
  rw [hA.sum_sq_eq_sum_eigenvalues_sq, hA.rank_eq_card_non_zero_eigs]
  have htr : A.trace = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  set S := (Finset.univ : Finset κ).filter fun i ↦ hA.eigenvalues i ≠ 0
  have hS : Fintype.card {i // hA.eigenvalues i ≠ 0} = S.card := by
    rw [Fintype.card_subtype]
  have h1 : ∑ i, hA.eigenvalues i = ∑ i ∈ S, hA.eigenvalues i := by
    rw [Finset.sum_filter_ne_zero]
  have h2 : ∑ i ∈ S, hA.eigenvalues i ^ 2 ≤ ∑ i, hA.eigenvalues i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ ↦ sq_nonneg _)
  rw [htr, h1, hS]
  calc (∑ i ∈ S, hA.eigenvalues i) ^ 2 ≤ S.card * ∑ i ∈ S, hA.eigenvalues i ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ S.card * ∑ i, hA.eigenvalues i ^ 2 := by gcongr

end Matrix.IsHermitian
