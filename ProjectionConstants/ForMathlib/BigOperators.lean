/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over finite types

Elementary identities for sums `∑ i, f i` over a `Fintype`: removing one summand, reindexing along
an injective map, permuting three nested sums, and splitting a sum over `ι × ι` into its diagonal
and its off-diagonal part.

## Main statements

* `Fintype.sum_subtype_ne_eq_sub`: `∑_{k ≠ a} f k = ∑ₖ f k - f a`.
* `Fintype.sum_eq_sum_comp_of_injective`: a sum of a function vanishing outside the range of an
  injective map `e` is a sum over the domain of `e`.
* `Fintype.sum_comm_cycle`: `∑ₐ ∑_b ∑_c F a b c = ∑_b ∑_c ∑ₐ F a b c`.
* `Fintype.sum_prod_eq_sum_diag_add_sum_offDiag`: `∑_{p ∈ ι × ι} F p` is the sum of the diagonal
  terms `F (i, i)` and of the off-diagonal terms.
-/

open Finset

namespace Fintype

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]

/-- `∑_{k ≠ a} f k = ∑ₖ f k - f a`. -/
theorem sum_subtype_ne_eq_sub [DecidableEq ι] [AddCommGroup M] (a : ι) (f : ι → M) :
    ∑ k : {k // k ≠ a}, f k = ∑ k, f k - f a := by
  rw [sum_eq_add_sum_subtype_ne f a, add_sub_cancel_left]

/-- A sum of a function that vanishes outside the range of an injective map `e` is a sum over
the domain of `e`: `∑ₖ f k = ∑ᵢ f (e i)`. -/
theorem sum_eq_sum_comp_of_injective [AddCommMonoid M] {e : ι → κ} (he : Function.Injective e)
    (f : κ → M) (h : ∀ k, (¬ ∃ i, e i = k) → f k = 0) : ∑ k, f k = ∑ i, f (e i) :=
  (sum_of_injective e he (fun i ↦ f (e i)) f h fun _ ↦ rfl).symm

/-- `∑ₐ ∑_b ∑_c F a b c = ∑_b ∑_c ∑ₐ F a b c`. -/
theorem sum_comm_cycle {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (F : α → β → γ → M) : ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ c, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm

/-- Splitting a sum over `ι × ι` into its diagonal and its off-diagonal part:
`∑ p, F p = ∑ᵢ F (i, i) + ∑_{p.1 ≠ p.2} F p`. -/
theorem sum_prod_eq_sum_diag_add_sum_offDiag [DecidableEq ι] [AddCommMonoid M] (F : ι × ι → M) :
    ∑ p, F p = ∑ i, F (i, i) + ∑ p ∈ univ.filter (fun p : ι × ι ↦ p.1 ≠ p.2), F p := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun p : ι × ι ↦ p.1 = p.2)]
  congr 1
  refine Finset.sum_nbij' (fun p ↦ p.1) (fun i ↦ (i, i)) ?_ ?_ ?_ ?_ ?_
  · intro p _; simp
  · intro i _; simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Prod.ext rfl hp
  · intro i _; rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [show p = (p.1, p.1) from Prod.ext rfl hp.symm]

end Fintype
