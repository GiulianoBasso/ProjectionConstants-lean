/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Estimates
import ProjectionConstants.L1
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Trace duality in `ℓ₁`

For a subspace `E ⊆ ℓ₁^ι`, the relative projection constant `λ(E, ℓ₁^ι) = relProjConst (l1Sub E)`
is the infimum of the operator norms `colSumNorm R` of the matrix projections `R` onto `E`
(`relProjConst_l1Sub`). Trace duality bounds it from below: let `P² = P`, `AP = PA` and
`ν₁(A) = ∑ₐ maxᵦ |Aₐᵦ| ≤ 1`. Then `Tr(AP) = Tr(AR) ≤ colSumNorm R` for every projection `R` onto
the range of `P`.

## Main statements

* `trace_mul_le_relProjConst`: **trace duality** ([AMOP, Lemma 2.1], the inequality that we
  need), `Tr(AP) ≤ λ(range P, ℓ₁^ι)`.
* `exists_orthProj_of_colSum_le`: the last step of the proof of [AMOP, Theorem 1.2]. Let `P` be a
  symmetric idempotent matrix of trace at most `n` that commutes with `A`, and whose column sums
  `∑ₐ |Pₐᵦ|` are at most `Tr(AP) + ε`. Then some `n`-dimensional subspace `E ⊆ ℓ₁^d` has an
  orthogonal projection `P'` with `‖P'‖ ≤ λ(E, ℓ₁^d) + ε`, and `‖P'‖` is at least the largest
  column sum of `P`. To reach dimension `n`, the matrix `P` is padded by an identity block
  (`E ↦ E × ℝᵏ`); then the indices are relabelled by `Fin d`.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Trace duality** ([AMOP, Lemma 2.1], the inequality that we need). If `P² = P`, `AP = PA`
and `|Aₐᵦ| ≤ αₐ` with `∑ₐ αₐ ≤ 1`, then `Tr(AP) ≤ λ(range P, ℓ₁^ι)`. -/
theorem trace_mul_le_relProjConst {P A : Matrix ι ι ℝ} (hP : P * P = P) (hAP : A * P = P * A)
    {α : ι → ℝ} (hα : ∀ a b, |A a b| ≤ α a) (hsum : ∑ a, α a ≤ 1) :
    (A * P).trace ≤ relProjConst (l1Sub (LinearMap.range (Matrix.toLin' P))) := by
  set E := LinearMap.range (Matrix.toLin' P) with hE
  have hmemE : ∀ y, P *ᵥ y ∈ E := fun y ↦ ⟨y, Matrix.toLin'_apply P y⟩
  have hfix : ∀ x ∈ E, P *ᵥ x = x := by
    rintro x ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hP]
  rw [relProjConst_l1Sub]
  refine le_csInf ⟨_, P, ⟨hmemE, hfix⟩, rfl⟩ ?_
  rintro _ ⟨R, ⟨hR1, hR2⟩, rfl⟩
  have hRP : R * P = P := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec]
    exact hR2 _ (hmemE v)
  have hPR : P * R = R := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hR1 v)
  have htr : (A * P).trace = (A * R).trace := by
    calc (A * P).trace = (A * (R * P)).trace := by rw [hRP]
      _ = (P * (A * R)).trace := by rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = ((A * P) * R).trace := by rw [← Matrix.mul_assoc, hAP]
      _ = (A * R).trace := by rw [Matrix.mul_assoc, hPR]
  rw [htr]
  have hα0 : ∀ a, 0 ≤ α a := fun a ↦ (abs_nonneg _).trans (hα a a)
  have hop := colSumNorm_nonneg R
  calc (A * R).trace = ∑ a, ∑ b, A a b * R b a := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    _ ≤ ∑ a, α a * ∑ b, |R b a| := by
        refine sum_le_sum fun a _ ↦ ?_
        rw [mul_sum]
        refine sum_le_sum fun b _ ↦ ?_
        calc A a b * R b a ≤ |A a b * R b a| := le_abs_self _
          _ = |A a b| * |R b a| := abs_mul _ _
          _ ≤ α a * |R b a| := mul_le_mul_of_nonneg_right (hα a b) (abs_nonneg _)
    _ ≤ ∑ a, α a * colSumNorm R := by
        refine sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ (hα0 a)
        simpa only [Real.norm_eq_abs] using col_le_colSumNorm R a
    _ = (∑ a, α a) * colSumNorm R := by rw [sum_mul]
    _ ≤ 1 * colSumNorm R := mul_le_mul_of_nonneg_right hsum hop
    _ = colSumNorm R := one_mul _

/-! ### Padding and relabelling -/

/-- **Conclusion.** Let `P` be a symmetric idempotent `κ × κ` matrix of trace at most `n`, and
let `A` commute with `P`, with `|Aₐᵦ| ≤ αₐ` and `∑ₐ αₐ ≤ 1`. If every column of `P` has
`ℓ₁`-norm at most `hi ≤ Tr(AP) + ε`, with `hi ≥ 1`, and some column has norm at least `lo`, then
there is an `n`-dimensional subspace `E = range P' ⊆ ℓ₁^d` such that the orthogonal projection
`P'` onto `E` satisfies `lo ≤ ‖P'‖ ≤ λ(E, ℓ₁^d) + ε`. Here `‖P'‖ = colSumNorm P'` is the operator
norm on `ℓ₁^d`. We pad `P` by an identity block and relabel by `Fin d`. -/
theorem exists_orthProj_of_colSum_le {κ : Type*} [Fintype κ] {n : ℕ} {P A : Matrix κ κ ℝ}
    (hPs : ∀ a b, P b a = P a b) (hP : P * P = P) (htr : P.trace ≤ n) (hAP : A * P = P * A)
    {α : κ → ℝ} (hα : ∀ a b, |A a b| ≤ α a) (hsum : ∑ a, α a ≤ 1) {lo hi ε : ℝ}
    (hcol : ∀ b, ∑ a, |P a b| ≤ hi) (hhi1 : 1 ≤ hi) (hhi : hi ≤ (A * P).trace + ε)
    (hlo : ∃ b, lo ≤ ∑ a, |P a b|) :
    ∃ (d : ℕ) (P' : Matrix (Fin d) (Fin d) ℝ), P'.IsSymm ∧ P' * P' = P' ∧
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' P')) = n ∧
      lo ≤ colSumNorm P' ∧
        colSumNorm P' ≤ relProjConst (l1Sub (LinearMap.range (Matrix.toLin' P'))) + ε := by
  classical
  -- the rank of `P`
  set r := Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) with hr
  have hrP : (r : ℝ) = P.trace := finrank_range_eq_trace hP
  have hrn : r ≤ n := by
    have : (r : ℝ) ≤ n := hrP ▸ htr
    exact_mod_cast this
  set k := n - r with hk
  -- padding by an identity block
  set Q : Matrix (κ ⊕ Fin k) (κ ⊕ Fin k) ℝ := Matrix.fromBlocks P 0 0 1 with hQ
  set B : Matrix (κ ⊕ Fin k) (κ ⊕ Fin k) ℝ := Matrix.fromBlocks A 0 0 0 with hB
  have hQQ : Q * Q = Q := by
    simp only [hQ, Matrix.fromBlocks_multiply, hP]
    simp
  have hBQ : B * Q = Q * B := by
    simp only [hB, hQ, Matrix.fromBlocks_multiply, hAP]
    simp
  have hQs : ∀ x y, Q y x = Q x y := by
    rintro (a | a) (b | b) <;> simp [hQ, hPs, Matrix.one_apply, eq_comm]
  have hQtr : Q.trace = P.trace + k := by
    simp [hQ, Matrix.trace, Fintype.sum_sum_type]
  have hBQtr : (B * Q).trace = (A * P).trace := by
    simp only [hB, hQ, Matrix.fromBlocks_multiply]
    simp [Matrix.trace, Fintype.sum_sum_type]
  have hQcol : ∀ y, ∑ x, |Q x y| ≤ hi := by
    rintro (b | j)
    · simp only [Fintype.sum_sum_type, hQ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, abs_zero, sum_const_zero, add_zero]
      exact hcol b
    · simp only [Fintype.sum_sum_type, hQ, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, abs_zero, sum_const_zero, zero_add, Matrix.one_apply]
      rw [sum_eq_single j]
      · simpa using hhi1
      · intro i _ hij
        simp [hij]
      · simp
  set α' : κ ⊕ Fin k → ℝ := Sum.elim α (fun _ ↦ 0) with hα'
  have hBα : ∀ x y, |B x y| ≤ α' x := by
    have hα0 : ∀ a, 0 ≤ α a := fun a ↦ (abs_nonneg _).trans (hα a a)
    rintro (a | a) (b | b) <;> simp [hB, hα', hα, hα0]
  have hα'sum : ∑ x, α' x ≤ 1 := by
    simp only [hα', Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_const_zero, add_zero]
    exact hsum
  -- relabelling by `Fin d`
  set e := Fintype.equivFin (κ ⊕ Fin k) with he
  set P' := Q.submatrix e.symm e.symm with hP'
  set A' := B.submatrix e.symm e.symm with hA'
  have hPP' : P' * P' = P' := by
    rw [hP', Matrix.submatrix_mul_equiv, hQQ]
  have hAP' : A' * P' = P' * A' := by
    rw [hA', hP', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hBQ]
  have hcol' : ∀ i, ∑ x, |P' x i| = ∑ y, |Q y (e.symm i)| := by
    intro i
    simp only [hP', Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun y ↦ |Q y (e.symm i)|)
  refine ⟨Fintype.card (κ ⊕ Fin k), P', ?_, hPP', ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, hP', Matrix.submatrix_apply]
    exact hQs _ _
  · have h1 := finrank_range_eq_trace hPP'
    rw [hP', trace_submatrix_equiv, hQtr, ← hrP] at h1
    have h2 : ((r : ℝ) + (k : ℝ)) = (n : ℝ) := by
      rw [hk]
      push_cast [hrn]
      ring
    rw [h2] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hlo
    refine hb.trans (le_trans (le_of_eq ?_) (col_le_colSumNorm P' (e (Sum.inl b))))
    simp only [Real.norm_eq_abs]
    rw [hcol', Equiv.symm_apply_apply]
    simp [hQ, Fintype.sum_sum_type]
  · have h1 : colSumNorm P' ≤ hi := by
      refine colSumNorm_le (by linarith) fun i ↦ ?_
      simp only [Real.norm_eq_abs]
      rw [hcol']
      exact hQcol _
    have h2 := trace_mul_le_relProjConst hPP' hAP' (α := α' ∘ e.symm)
      (fun i j ↦ by simp only [hA', Matrix.submatrix_apply, Function.comp_apply]; exact hBα _ _)
      (by change ∑ i, α' (e.symm i) ≤ 1; rw [Equiv.sum_comp e.symm α']; exact hα'sum)
    have h3 : (A' * P').trace = (A * P).trace := by
      rw [hA', hP', Matrix.submatrix_mul_equiv, trace_submatrix_equiv, hBQtr]
    rw [h3] at h2
    linarith

end ProjectionConstants.AlmostMinimal
