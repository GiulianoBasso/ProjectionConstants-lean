/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Carathéodory's theorem for cones

If `x = ∑_{i ∈ s} aᵢ vᵢ` with `aᵢ ≥ 0` in a real vector space `V` of dimension `d`, then
`x = ∑_{i ∈ s} bᵢ vᵢ` with `bᵢ ≥ 0` and at most `d` of the `bᵢ` nonzero
(`exists_sparse_conic_combination`). In `ProjectionConstants.Stabilization.Main` this is applied
in the space of symmetric `r × r` matrices, to make a maximizer of the Chalmers–Lewicki quantity
sparse ([KMMP, Claim 2.5]).

Proof: if the `vᵢ` with `aᵢ ≠ 0` are linearly dependent, move along a relation until the first
coefficient vanishes (`exists_smaller_support`), and repeat.

## Main statements

* `exists_smaller_support`: one reduction step.
* `exists_sparse_conic_combination`: Carathéodory's theorem for cones.

## References

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.

## Tags

Carathéodory's theorem, conic combination
-/

open Finset

namespace ProjectionConstants.Stabilization

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*}

/-- **One reduction step.** If the vectors `vᵢ` with `aᵢ ≠ 0` are linearly dependent, one more
coefficient can be made zero. -/
lemma exists_smaller_support (s : Finset ι) (v : ι → V) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hdep : ¬LinearIndependent ℝ (fun i : s.filter (a · ≠ 0) ↦ v i)) :
    ∃ b : ι → ℝ, (∀ i ∈ s, 0 ≤ b i) ∧ ∑ i ∈ s, b i • v i = ∑ i ∈ s, a i • v i ∧
      (s.filter (b · ≠ 0)).card < (s.filter (a · ≠ 0)).card := by
  classical
  set S := s.filter (a · ≠ 0) with hS
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- a relation with a positive coefficient
  obtain ⟨h, hh, j₀, hj₀⟩ : ∃ h : S → ℝ, ∑ i, h i • v i = 0 ∧ ∃ j, 0 < h j := by
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · refine ⟨-g, ?_, i₀, by simpa using hneg⟩
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
    · exact ⟨g, hg, i₀, hpos⟩
  -- the relation, extended by zero
  set β : ι → ℝ := fun i ↦ if hi : i ∈ S then h ⟨i, hi⟩ else 0 with hβ
  have hβS : ∀ i (hi : i ∈ S), β i = h ⟨i, hi⟩ := fun i hi ↦ by simp [hβ, hi]
  have hβ0 : ∀ i ∉ S, β i = 0 := fun i hi ↦ by simp [hβ, hi]
  have hSs : S ⊆ s := filter_subset _ _
  have hβsum : ∑ i ∈ s, β i • v i = 0 := by
    rw [← sum_subset hSs fun i _ hi ↦ by rw [hβ0 i hi, zero_smul]]
    rw [← hh, ← sum_coe_sort S]
    exact sum_congr rfl fun i _ ↦ by rw [hβS i i.2]
  -- the first coefficient to vanish
  set Q := S.filter (0 < β ·) with hQ
  have hQne : Q.Nonempty := ⟨j₀, mem_filter.2 ⟨j₀.2, by rw [hβS _ j₀.2]; exact hj₀⟩⟩
  obtain ⟨j, hjQ, hjmin⟩ := exists_min_image Q (fun i ↦ a i / β i) hQne
  obtain ⟨hjS, hβj⟩ := mem_filter.1 hjQ
  set τ := a j / β j with hτ
  refine ⟨fun i ↦ a i - τ * β i, fun i hi ↦ ?_, ?_, ?_⟩
  · -- nonnegativity
    by_cases hb : 0 < β i
    · have hiS : i ∈ S := by
        by_contra hiS
        rw [hβ0 i hiS] at hb
        exact lt_irrefl 0 hb
      have := hjmin i (mem_filter.2 ⟨hiS, hb⟩)
      rw [le_div_iff₀ hb] at this
      simp only
      linarith
    · replace hb : β i ≤ 0 := not_lt.mp hb
      have hτ0 : 0 ≤ τ := div_nonneg (ha j (hSs hjS)) hβj.le
      simp only
      nlinarith [ha i hi]
  · -- the combination is unchanged
    simp only [sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hβsum, smul_zero, sub_zero]
  · -- the support shrinks
    refine card_lt_card ⟨fun i hi ↦ ?_, fun hsub ↦ ?_⟩
    · obtain ⟨his, hne⟩ := mem_filter.1 hi
      refine mem_filter.2 ⟨his, fun ha0 ↦ hne ?_⟩
      have hiS : i ∉ S := fun h' ↦ (mem_filter.1 h').2 ha0
      simp only [ha0, hβ0 i hiS, mul_zero, sub_zero]
    · have hj := hsub hjS
      obtain ⟨-, hne⟩ := mem_filter.1 hj
      apply hne
      simp only [hτ]
      field_simp
      ring

/-- **Carathéodory's theorem for cones.** A nonnegative combination `∑_{i ∈ s} aᵢ vᵢ` in a real
vector space of dimension `d` is a nonnegative combination `∑_{i ∈ s} bᵢ vᵢ` with at most `d`
nonzero coefficients. -/
theorem exists_sparse_conic_combination [FiniteDimensional ℝ V] (s : Finset ι) (v : ι → V)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∃ b : ι → ℝ, (∀ i ∈ s, 0 ≤ b i) ∧ ∑ i ∈ s, b i • v i = ∑ i ∈ s, a i • v i ∧
      (s.filter (b · ≠ 0)).card ≤ Module.finrank ℝ V := by
  induction hk : (s.filter (a · ≠ 0)).card using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    by_cases hli : LinearIndependent ℝ (fun i : s.filter (a · ≠ 0) ↦ v i)
    · refine ⟨a, ha, rfl, ?_⟩
      have := hli.fintype_card_le_finrank
      rwa [Fintype.card_coe] at this
    · obtain ⟨b, hb, hsum, hlt⟩ := exists_smaller_support s v a ha hli
      obtain ⟨b', hb', hsum', hcard⟩ := ih _ (hk ▸ hlt) b hb rfl
      exact ⟨b', hb', hsum'.trans hsum, hcard⟩

end ProjectionConstants.Stabilization
