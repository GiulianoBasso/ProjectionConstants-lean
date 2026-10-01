/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.KyFan.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Sign matrices and weights

In the formulation of Chalmers and Lewicki used in [JFA] and [AMOP], the maximal relative
projection constant `λ_ℝ(n, d)` is the maximum of the Ky Fan sum `kyFanSum n (√D S √D)` over the
sign matrices `S ∈ 𝒮_d` and the diagonal weight matrices `D = diag(w) ∈ 𝒟_d`, that is, `w ≥ 0`
and `∑ wᵢ = 1` (see `ProjectionConstants.ChalmersLewicki.SignMatrix`). This file provides the
basic facts about sign matrices, weights and the matrices `√D S √D` that this formulation needs.

## Main definitions

* `IsSignMatrix S`: `S` is a symmetric `(±1)`-matrix with ones on the diagonal.
* `IsWeight w`: `w ≥ 0` and `∑ᵢ wᵢ = 1`.
* `weightedSign S w`: the matrix `√D S √D` with entries `√wᵢ Sᵢⱼ √wⱼ`, for `D = diag(w)`.

## Main statements

* `dotProduct_mulVec_weightedSign_le`: the Rayleigh bound `uᵀ(√D S √D)u ≤ ‖u‖²`.
* `frobeniusInner_weightedSign_le_trace`, `kyFanSumLe_weightedSign_le`: `Tr(√D S √D P) ≤ Tr P`
  for an orthogonal projection `P`, hence `kyFanSumLe n (√D S √D) ≤ n`.
* `Matrix.PosSemidef.frobeniusInner_le_trace`: `Tr(MP) ≤ Tr M` for `M ⪰ 0` and an orthogonal
  projection `P`.
* `finite_setOf_isSignMatrix`, `isCompact_setOf_isWeight`: there are finitely many sign matrices,
  and the weights form a compact set.
* `continuous_kyFanSumLe_weightedSign`, `continuous_kyFanSum_weightedSign`: continuity in `w`.

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants

variable {ι : Type*}

/-- `S` is a **sign matrix**: a symmetric `(±1)`-matrix with ones on the diagonal. (The sign
matrices of size `d` form the set `𝒮_d` of [JFA].) -/
structure IsSignMatrix (S : Matrix ι ι ℝ) : Prop where
  /-- `S` is symmetric. -/
  symm : ∀ i j, S j i = S i j
  /-- The entries of `S` are `±1`. -/
  pm : ∀ i j, S i j = 1 ∨ S i j = -1
  /-- The diagonal entries of `S` are `1`. -/
  diag : ∀ i, S i i = 1

/-- `w` is a **weight**: `w ≥ 0` and `∑ᵢ wᵢ = 1`. (The corresponding diagonal matrices `diag(w)`
form the set `𝒟_d` of [JFA].) -/
structure IsWeight [Fintype ι] (w : ι → ℝ) : Prop where
  /-- The weights are nonnegative. -/
  nonneg : ∀ i, 0 ≤ w i
  /-- The weights sum to `1`. -/
  sum_eq : ∑ i, w i = 1

/-- The matrix `√D S √D` for `D = diag(w)`, with entries `√wᵢ Sᵢⱼ √wⱼ`. -/
noncomputable def weightedSign (S : Matrix ι ι ℝ) (w : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ √(w i) * S i j * √(w j)

/-- The entries `√wᵢ Sᵢⱼ √wⱼ` of `√D S √D`. -/
@[simp]
lemma weightedSign_apply (S : Matrix ι ι ℝ) (w : ι → ℝ) (i j : ι) :
    weightedSign S w i j = √(w i) * S i j * √(w j) :=
  rfl

namespace IsSignMatrix

variable {S : Matrix ι ι ℝ} (hS : IsSignMatrix S)
include hS

/-- `|Sᵢⱼ| = 1`. -/
lemma abs_eq (i j : ι) : |S i j| = 1 := by
  rcases hS.pm i j with h | h <;> simp [h]

/-- `Sᵢⱼ² = 1`. -/
lemma mul_self_eq (i j : ι) : S i j * S i j = 1 := by
  rcases hS.pm i j with h | h <;> simp [h]

/-- Relabelling the index set along an equivalence preserves sign matrices. -/
lemma submatrix {κ : Type*} (e : κ ≃ ι) : IsSignMatrix (S.submatrix e e) :=
  ⟨fun a b ↦ hS.symm (e a) (e b), fun a b ↦ hS.pm (e a) (e b), fun a ↦ hS.diag (e a)⟩

/-- `√D S √D` is symmetric: `(√D S √D)ⱼᵢ = (√D S √D)ᵢⱼ`. -/
lemma weightedSign_comm (w : ι → ℝ) (i j : ι) : weightedSign S w j i = weightedSign S w i j := by
  simp only [weightedSign_apply, hS.symm]
  ring

/-- `√D S √D` is Hermitian, that is, symmetric. -/
lemma isHermitian_weightedSign (w : ι → ℝ) : (weightedSign S w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [weightedSign_apply, star_trivial, hS.symm]
  ring

end IsSignMatrix

/-- The all-ones matrix is a sign matrix. -/
lemma isSignMatrix_ones : IsSignMatrix (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix ι ι ℝ) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ Or.inl rfl, fun _ ↦ rfl⟩

/-- `√D (S + C) √D = √D S √D + √D C √D`. -/
lemma weightedSign_add (S C : Matrix ι ι ℝ) (w : ι → ℝ) :
    weightedSign (S + C) w = weightedSign S w + weightedSign C w := by
  ext i j
  simp only [weightedSign_apply, Matrix.add_apply]
  ring

/-- `weightedSign` commutes with relabelling the index set. -/
lemma weightedSign_submatrix {κ : Type*} (e : κ ≃ ι) (S : Matrix ι ι ℝ) (w : ι → ℝ) :
    weightedSign (S.submatrix e e) (w ∘ e) = (weightedSign S w).submatrix e e := by
  ext a b
  simp

/-- Relabelling the index set along an equivalence preserves weights. -/
lemma IsWeight.comp_equiv [Fintype ι] {κ : Type*} [Fintype κ] (e : κ ≃ ι) {w : ι → ℝ}
    (hw : IsWeight w) : IsWeight (w ∘ e) :=
  ⟨fun a ↦ hw.nonneg (e a), by rw [← hw.sum_eq]; exact Equiv.sum_comp e w⟩

variable [Fintype ι]

/-- `xᵀ(√D S √D)x = (√D x)ᵀ S (√D x)`. -/
lemma dotProduct_mulVec_weightedSign (S : Matrix ι ι ℝ) (w x : ι → ℝ) :
    x ⬝ᵥ weightedSign S w *ᵥ x = (fun k ↦ √(w k) * x k) ⬝ᵥ S *ᵥ fun k ↦ √(w k) * x k := by
  simp only [dotProduct_mulVec_self_eq_sum, weightedSign_apply]
  exact sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring

/-- `(√D S √D x)ₖ = √wₖ ∑ₗ Sₖₗ √wₗ xₗ`. -/
lemma mulVec_weightedSign (S : Matrix ι ι ℝ) (w x : ι → ℝ) (k : ι) :
    (weightedSign S w *ᵥ x) k = √(w k) * ∑ l, S k l * (√(w l) * x l) := by
  simp only [mulVec, dotProduct, weightedSign_apply, mul_sum]
  exact sum_congr rfl fun l _ ↦ by ring

/-- The **Rayleigh bound** `uᵀ(√D S √D)u ≤ ‖u‖²`. -/
lemma dotProduct_mulVec_weightedSign_le {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) (u : ι → ℝ) : u ⬝ᵥ weightedSign S w *ᵥ u ≤ u ⬝ᵥ u := by
  have hsq : ∀ i, √(w i) ^ 2 = w i := fun i ↦ Real.sq_sqrt (hw.nonneg i)
  calc u ⬝ᵥ weightedSign S w *ᵥ u
      = ∑ i, ∑ j, (√(w i) * S i j * √(w j)) * u i * u j := by
        simp [dotProduct_mulVec_self_eq_sum]
    _ ≤ ∑ i, ∑ j, (√(w i) * |u i|) * (√(w j) * |u j|) := by
        refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
        calc (√(w i) * S i j * √(w j)) * u i * u j
            ≤ |(√(w i) * S i j * √(w j)) * u i * u j| := le_abs_self _
          _ = (√(w i) * |u i|) * (√(w j) * |u j|) := by
              simp only [abs_mul, hS.abs_eq, abs_of_nonneg (Real.sqrt_nonneg _)]
              ring
    _ = (∑ i, √(w i) * |u i|) ^ 2 := by rw [sq, sum_mul_sum]
    _ ≤ (∑ i, √(w i) ^ 2) * ∑ i, |u i| ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
    _ = u ⬝ᵥ u := by
        simp only [hsq, hw.sum_eq, one_mul, dotProduct, sq, abs_mul_abs_self]

/-- `uᵀ(√D S √D)u ≤ 1` for a unit vector `u`. -/
lemma dotProduct_mulVec_weightedSign_le_one {S : Matrix ι ι ℝ} {w : ι → ℝ}
    (hS : IsSignMatrix S) (hw : IsWeight w) {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) :
    u ⬝ᵥ weightedSign S w *ᵥ u ≤ 1 :=
  hu ▸ dotProduct_mulVec_weightedSign_le hS hw u

/-- `Tr(MP) = ∑ᵢ (Peᵢ)ᵀ M (Peᵢ)` for an orthogonal projection `P`. -/
lemma frobeniusInner_eq_sum_dotProduct_mulVec (M : Matrix ι ι ℝ) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) :
    frobeniusInner M P = ∑ i, (fun a ↦ P a i) ⬝ᵥ M *ᵥ fun a ↦ P a i := by
  have h1 : ∀ a b, M a b * P a b = ∑ i, M a b * P a i * P b i := by
    intro a b
    rw [← hP.sum_mul_apply a b, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hP.apply_comm i b]
    ring
  simp only [frobeniusInner, dotProduct_mulVec_self_eq_sum, h1]
  calc ∑ a, ∑ b, ∑ i, M a b * P a i * P b i
      = ∑ a, ∑ i, ∑ b, M a b * P a i * P b i := sum_congr rfl fun a _ ↦ sum_comm
    _ = ∑ i, ∑ a, ∑ b, M a b * P a i * P b i := sum_comm

/-- `Tr(√D S √D P) ≤ Tr P` for an orthogonal projection `P`. -/
lemma frobeniusInner_weightedSign_le_trace {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) {P : Matrix ι ι ℝ} (hP : IsStarProjection P) :
    frobeniusInner (weightedSign S w) P ≤ P.trace := by
  rw [frobeniusInner_eq_sum_dotProduct_mulVec _ hP]
  refine sum_le_sum fun i _ ↦ (dotProduct_mulVec_weightedSign_le hS hw _).trans (le_of_eq ?_)
  rw [Matrix.diag_apply, hP.diag_eq_sum_sq i]
  simp only [dotProduct, sq]
  exact sum_congr rfl fun a _ ↦ by rw [hP.apply_comm i a]

/-! ### Positive semidefinite matrices -/

/-- A real symmetric matrix with `xᵀMx ≥ 0` for all `x` is positive semidefinite. -/
lemma posSemidef_of_isSymm {M : Matrix ι ι ℝ} (hM : M.IsSymm) (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) :
    M.PosSemidef :=
  .of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.2 hM) fun x ↦ by simpa using h x

omit [Fintype ι] in
/-- If `C ⪰ 0`, then `√D C √D ⪰ 0`. -/
lemma _root_.Matrix.PosSemidef.weightedSign [Finite ι] {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (w : ι → ℝ) : (weightedSign C w).PosSemidef := by
  have := Fintype.ofFinite ι
  refine posSemidef_of_isSymm (.ext fun i j ↦ ?_) fun x ↦ ?_
  · have h : C j i = C i j := by simpa using hC.1.apply i j
    simp only [weightedSign_apply, h]
    ring
  · rw [dotProduct_mulVec_weightedSign]
    simpa using hC.dotProduct_mulVec_nonneg _

/-- `0 ≤ Tr(MP)` for `M ⪰ 0` and an orthogonal projection `P`. -/
lemma _root_.Matrix.PosSemidef.frobeniusInner_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {P : Matrix ι ι ℝ} (hP : IsStarProjection P) : 0 ≤ frobeniusInner M P := by
  rw [frobeniusInner_eq_sum_dotProduct_mulVec M hP]
  exact sum_nonneg fun i _ ↦ by simpa using hM.dotProduct_mulVec_nonneg _

/-- `Tr(MP) ≤ Tr M` for `M ⪰ 0` and an orthogonal projection `P`. -/
lemma _root_.Matrix.PosSemidef.frobeniusInner_le_trace {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {P : Matrix ι ι ℝ} (hP : IsStarProjection P) : frobeniusInner M P ≤ M.trace := by
  classical
  have h1 := hM.frobeniusInner_nonneg hP.one_sub
  have h2 : frobeniusInner M (1 - P) = M.trace - frobeniusInner M P := by
    simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.sub_apply,
      Matrix.one_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ite_true]
  linarith

/-- `kyFanSumLe n (√D S √D) ≤ n`. -/
lemma kyFanSumLe_weightedSign_le {n : ℕ} {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : kyFanSumLe n (weightedSign S w) ≤ n :=
  kyFanSumLe_le fun _ hP ↦ (frobeniusInner_weightedSign_le_trace hS hw hP.1).trans hP.2

/-- `kyFanSum n A ≤ kyFanSumLe n A`. -/
lemma kyFanSum_le_kyFanSumLe (n : ℕ) (A : Matrix ι ι ℝ) : kyFanSum n A ≤ kyFanSumLe n A := by
  by_cases h : (frobeniusInner A '' orthProjs ℝ ι n).Nonempty
  · exact csSup_le h (by
      rintro _ ⟨P, hP, rfl⟩
      exact frobeniusInner_le_kyFanSumLe A (orthProjs_subset_orthProjsLe n hP))
  · rw [Set.not_nonempty_iff_eq_empty] at h
    simp only [kyFanSum, h, Real.sSup_empty]
    exact kyFanSumLe_nonneg n A

/-! ### The sets of sign matrices and of weights -/

omit [Fintype ι] in
/-- The sign matrices form a finite set. -/
lemma finite_setOf_isSignMatrix [Finite ι] : Set.Finite {S : Matrix ι ι ℝ | IsSignMatrix S} := by
  apply (Set.finite_range fun b : ι → ι → Bool ↦
    (Matrix.of fun i j ↦ if b i j then (1 : ℝ) else -1)).subset
  intro S hS
  refine ⟨fun i j ↦ decide (S i j = 1), ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rcases (hS : IsSignMatrix S).pm i j with h | h
  · simp [h]
  · simp [h]; norm_num

/-- The weights form a compact set. -/
lemma isCompact_setOf_isWeight : IsCompact {w : ι → ℝ | IsWeight w} := by
  have hset : {w : ι → ℝ | IsWeight w} = (⋂ i, {w : ι → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h ↦ ⟨h.nonneg, h.sum_eq⟩, fun h ↦ ⟨h.1, h.2⟩⟩
  have hclosed : IsClosed {w : ι → ℝ | IsWeight w} := by
    rw [hset]
    apply IsClosed.inter
    · exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (by fun_prop) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)) hclosed ?_
  intro w hw
  refine ⟨fun i ↦ (hw : IsWeight w).nonneg i, fun i ↦ ?_⟩
  change w i ≤ 1
  rw [← hw.sum_eq]
  exact single_le_sum (f := w) (fun j _ ↦ hw.nonneg j) (mem_univ i)

/-- There are weights on every nonempty index set. -/
lemma nonempty_setOf_isWeight [Nonempty ι] : {w : ι → ℝ | IsWeight w}.Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨fun k ↦ if k = i then 1 else 0, fun k ↦ by split_ifs <;> norm_num, ?_⟩
  simp

/-! ### Continuity in the weights -/

/-- `kyFanSum` is Lipschitz in the entries: `kyFanSum n A ≤ kyFanSum n B + ∑ᵢⱼ |Aᵢⱼ - Bᵢⱼ|`. -/
lemma kyFanSum_le_add (n : ℕ) (A B : Matrix ι ι ℝ) :
    kyFanSum n A ≤ kyFanSum n B + ∑ i, ∑ j, |A i j - B i j| := by
  by_cases hne : (frobeniusInner A '' orthProjs ℝ ι n).Nonempty
  · refine csSup_le hne ?_
    rintro _ ⟨P, hP, rfl⟩
    have h1 := frobeniusInner_le_kyFanSum B hP
    have h2 := frobeniusInner_le_sum_abs (A - B) hP.1
    have h3 := frobeniusInner_sub A B P
    simp only [Matrix.sub_apply] at h2
    linarith
  · have hne' : ¬ (frobeniusInner B '' orthProjs ℝ ι n).Nonempty := by
      simpa [Set.image_nonempty] using hne
    rw [Set.not_nonempty_iff_eq_empty] at hne hne'
    simp only [kyFanSum, hne, hne', Real.sSup_empty, zero_add]
    positivity

/-- A function of the matrix `√D S √D` that is Lipschitz in its entries is continuous in `w`. -/
lemma continuous_comp_weightedSign {F : Matrix ι ι ℝ → ℝ}
    (hF : ∀ A B, F A ≤ F B + ∑ i, ∑ j, |A i j - B i j|) (S : Matrix ι ι ℝ) :
    Continuous fun w : ι → ℝ ↦ F (weightedSign S w) := by
  rw [Metric.continuous_iff]
  intro w₀ ε hε
  set R : (ι → ℝ) → ℝ :=
    fun w ↦ ∑ k, ∑ l, |weightedSign S w k l - weightedSign S w₀ k l| with hRdef
  have hR : Continuous R := by
    simp only [hRdef, weightedSign_apply]
    fun_prop
  have hR0 : R w₀ = 0 := by simp [hRdef]
  obtain ⟨δ, hδ, hδR⟩ := Metric.continuous_iff.mp hR w₀ ε hε
  refine ⟨δ, hδ, fun w hw ↦ ?_⟩
  have hRw : R w < ε := by
    have := hδR w hw
    rw [hR0, Real.dist_eq, sub_zero] at this
    exact lt_of_abs_lt this
  have h1 := hF (weightedSign S w) (weightedSign S w₀)
  have h2 := hF (weightedSign S w₀) (weightedSign S w)
  have hsymm : ∑ k, ∑ l, |weightedSign S w₀ k l - weightedSign S w k l| =
      ∑ k, ∑ l, |weightedSign S w k l - weightedSign S w₀ k l| :=
    sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ abs_sub_comm _ _
  rw [hsymm] at h2
  rw [Real.dist_eq, abs_lt]
  simp only [hRdef] at hRw
  constructor <;> linarith

/-- `w ↦ kyFanSumLe n (√D S √D)` is continuous. -/
lemma continuous_kyFanSumLe_weightedSign (n : ℕ) (S : Matrix ι ι ℝ) :
    Continuous fun w : ι → ℝ ↦ kyFanSumLe n (weightedSign S w) :=
  continuous_comp_weightedSign (kyFanSumLe_le_add n) S

/-- `w ↦ kyFanSum n (√D S √D)` is continuous. -/
lemma continuous_kyFanSum_weightedSign (n : ℕ) (S : Matrix ι ι ℝ) :
    Continuous fun w : ι → ℝ ↦ kyFanSum n (weightedSign S w) :=
  continuous_comp_weightedSign (kyFanSum_le_add n) S

end ProjectionConstants
