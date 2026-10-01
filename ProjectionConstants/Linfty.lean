/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# Projections in `ℓ∞^N` as matrices

In Mathlib the space `ι → 𝕜` carries the sup norm, so it is the space `ℓ∞^ι`. A linear operator
on `ℓ∞^ι` is given by a matrix `P`, and its operator norm is the maximal row sum
`rowSumNorm P = maxᵢ ∑ⱼ |Pᵢⱼ|`. Hence the relative projection constant `λ(Y, ℓ∞^ι)` of a
subspace `Y ⊆ 𝕜^ι` is the infimum of `rowSumNorm P` over the matrices `P` that project onto `Y`.

Basic properties of `maxRelProjConst` (boundedness, nonnegativity) are proved in
`ProjectionConstants.Matrix.OrthProj`.

## Main definitions

* `rowSumNorm P`: the maximal row sum `maxᵢ ∑ⱼ |Pᵢⱼ|` of a matrix `P`.
* `IsMatrixProjOnto Y P`: the matrix `P` is a projection of `𝕜^ι` onto the subspace `Y`.
* `maxRelProjConst 𝕜 m N`: the **maximal relative projection constant**
  `λ_𝕜(m, N) = sup { λ(Y, ℓ∞^N) : Y ⊆ ℓ∞^N, dim Y = m }`.

## Main statements

* `rowSumNorm_eq_opNorm`: the operator norm of `P` on `ℓ∞` is `rowSumNorm P`.
* `relProjConst_le_rowSumNorm`, `le_relProjConst_of_rowSumNorm`: `λ(Y, ℓ∞^ι)` is the infimum of
  `rowSumNorm P` over the matrix projections `P` onto `Y`.
* `exists_isMatrixProjOnto_lt`: there are matrix projections onto `Y` whose maximal row sum is
  arbitrarily close to `λ(Y, ℓ∞^ι)`.
-/

open scoped NNReal Matrix

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜]

section RowSum

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The maximal row sum `maxᵢ ∑ⱼ |Pᵢⱼ|`, the operator norm of `P` on `ℓ∞`. -/
noncomputable def rowSumNorm (P : Matrix m n 𝕜) : ℝ :=
  ((Finset.univ.sup fun i ↦ ∑ j, ‖P i j‖₊ : ℝ≥0) : ℝ)

/-- `0 ≤ rowSumNorm P`. -/
lemma rowSumNorm_nonneg (P : Matrix m n 𝕜) : 0 ≤ rowSumNorm P := NNReal.coe_nonneg _

/-- Every row sum `∑ⱼ |Pᵢⱼ|` is at most `rowSumNorm P`. -/
lemma row_le_rowSumNorm (P : Matrix m n 𝕜) (i : m) : ∑ j, ‖P i j‖ ≤ rowSumNorm P := by
  have h : ∑ j, ‖P i j‖₊ ≤ Finset.univ.sup fun i ↦ ∑ j, ‖P i j‖₊ :=
    Finset.le_sup (f := fun i ↦ ∑ j, ‖P i j‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.2 h
  simpa [rowSumNorm] using h'

/-- If all row sums are at most `c ≥ 0`, then `rowSumNorm P ≤ c`. -/
lemma rowSumNorm_le {P : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, ‖P i j‖ ≤ c) :
    rowSumNorm P ≤ c := by
  rw [rowSumNorm, ← NNReal.coe_mk c hc, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ ↦ ?_
  rw [← NNReal.coe_le_coe]
  simpa using h i

/-- For every matrix some row realizes the maximal row sum. -/
lemma exists_row_eq_rowSumNorm [Nonempty m] (P : Matrix m n 𝕜) :
    ∃ i, ∑ j, ‖P i j‖ = rowSumNorm P := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset m) Finset.univ_nonempty
    (fun i ↦ ∑ j, ‖P i j‖₊)
  refine ⟨i, ?_⟩
  simp only [rowSumNorm, hi, NNReal.coe_sum, coe_nnnorm]

open Matrix.Norms.Operator in
/-- The operator norm of a matrix acting on `ℓ∞` is its maximal row sum. -/
theorem rowSumNorm_eq_opNorm [DecidableEq n] (P : Matrix m n 𝕜) :
    rowSumNorm P = ‖LinearMap.toContinuousLinearMap (Matrix.toLin' P)‖ := by
  have h := Matrix.linfty_opNorm_toMatrix (LinearMap.toContinuousLinearMap (Matrix.toLin' P))
  rw [← h, Matrix.linfty_opNorm_def]
  simp [rowSumNorm]

end RowSum

section Projections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix `P` is a projection of `𝕜^ι` onto the subspace `Y`. -/
structure IsMatrixProjOnto (Y : Submodule 𝕜 (ι → 𝕜)) (P : Matrix ι ι 𝕜) : Prop where
  /-- `P` maps `𝕜^ι` into `Y`. -/
  mem : ∀ x, P *ᵥ x ∈ Y
  /-- `P` is the identity on `Y`. -/
  map_id : ∀ y ∈ Y, P *ᵥ y = y

variable (Y : Submodule 𝕜 (ι → 𝕜))

/-- A matrix projection onto `Y` is a projection onto `Y` as a bounded operator. -/
lemma IsMatrixProjOnto.toCLM {P : Matrix ι ι 𝕜} (hP : IsMatrixProjOnto Y P) :
    IsProjectionOnto Y (LinearMap.toContinuousLinearMap (Matrix.toLin' P)) :=
  ⟨fun x ↦ by simpa using hP.mem x, fun y hy ↦ by simpa using hP.map_id y hy⟩

omit [Fintype ι] [DecidableEq ι] in
/-- `LinearMap.toContinuousLinearMap` undoes the coercion of a bounded operator on `𝕜^ι` to a
linear map. -/
lemma toContinuousLinearMap_coe [Finite ι] (f : (ι → 𝕜) →L[𝕜] (ι → 𝕜)) :
    LinearMap.toContinuousLinearMap (f : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜)) = f :=
  (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl

/-- The matrix of a projection onto `Y` is a matrix projection onto `Y`. -/
lemma isMatrixProjOnto_toMatrix {f : (ι → 𝕜) →L[𝕜] (ι → 𝕜)} (hf : IsProjectionOnto Y f) :
    IsMatrixProjOnto Y (LinearMap.toMatrix' (f : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))) :=
  ⟨fun x ↦ by simpa [Matrix.toLin'_toMatrix'] using hf.mem x,
    fun y hy ↦ by simpa [Matrix.toLin'_toMatrix'] using hf.map_id y hy⟩

omit [DecidableEq ι] in
/-- `λ(Y, ℓ∞^ι) ≤ rowSumNorm P` for every matrix projection `P` onto `Y`. -/
lemma relProjConst_le_rowSumNorm {P : Matrix ι ι 𝕜} (hP : IsMatrixProjOnto Y P) :
    relProjConst Y ≤ rowSumNorm P := by
  classical
  rw [rowSumNorm_eq_opNorm]
  exact relProjConst_le Y (hP.toCLM Y)

omit [DecidableEq ι] in
/-- Lower bounds for `λ(Y, ℓ∞^ι)` can be checked on matrices. -/
lemma le_relProjConst_of_rowSumNorm {c : ℝ}
    (h : ∀ P : Matrix ι ι 𝕜, IsMatrixProjOnto Y P → c ≤ rowSumNorm P) :
    c ≤ relProjConst Y := by
  classical
  refine le_relProjConst Y fun f hf ↦ ?_
  have h1 := h _ (isMatrixProjOnto_toMatrix Y hf)
  rwa [rowSumNorm_eq_opNorm, Matrix.toLin'_toMatrix', toContinuousLinearMap_coe] at h1

omit [DecidableEq ι] in
/-- For every `ε > 0` there is a matrix projection onto `Y` with maximal row sum less than
`λ(Y, ℓ∞^ι) + ε`. -/
lemma exists_isMatrixProjOnto_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Matrix ι ι 𝕜, IsMatrixProjOnto Y P ∧ rowSumNorm P < relProjConst Y + ε := by
  classical
  obtain ⟨f, hf, hlt⟩ := exists_isProjectionOnto_norm_lt Y hε
  refine ⟨_, isMatrixProjOnto_toMatrix Y hf, ?_⟩
  rwa [rowSumNorm_eq_opNorm, Matrix.toLin'_toMatrix', toContinuousLinearMap_coe]

omit [DecidableEq ι] in
/-- Every subspace `Y ⊆ 𝕜^ι` admits a matrix projection onto it. -/
lemma exists_isMatrixProjOnto : ∃ P : Matrix ι ι 𝕜, IsMatrixProjOnto Y P := by
  obtain ⟨P, hP, -⟩ := exists_isMatrixProjOnto_lt Y one_pos
  exact ⟨P, hP⟩

end Projections

variable (𝕜) in
/-- The **maximal relative projection constant**
`λ_𝕜(m, N) = sup { λ(Y, ℓ∞^N) : Y ⊆ ℓ∞^N, dim Y = m }` (it is `0` if `N < m`). -/
noncomputable def maxRelProjConst (m N : ℕ) : ℝ :=
  ⨆ Y : {Y : Submodule 𝕜 (Fin N → 𝕜) // Module.finrank 𝕜 Y = m}, relProjConst Y.1

end ProjectionConstants
