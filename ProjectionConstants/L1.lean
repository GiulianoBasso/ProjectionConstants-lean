/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Linfty
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Projections in `ℓ₁^N` as matrices

The space `ℓ₁^ι` is `WithLp 1 (ι → 𝕜)`, that is `PiLp 1 (fun _ : ι ↦ 𝕜)`, with the norm
`‖x‖ = ∑ᵢ ‖xᵢ‖`. A linear operator on `ℓ₁^ι` is given by a matrix `P` (`Matrix.toLpLin 1 1 P`),
and its operator norm is the maximal column sum `colSumNorm P = maxⱼ ∑ᵢ ‖Pᵢⱼ‖`. Hence the
relative projection constant `λ(Y, ℓ₁^ι)` of a subspace `Y ⊆ 𝕜^ι` is the infimum of
`colSumNorm P` over the matrices `P` that project onto `Y`.

This is the dual picture of `ProjectionConstants.Linfty`, where the operator norm is the maximal
row sum.

## Main definitions

* `colSumNorm P`: the maximal column sum `maxⱼ ∑ᵢ ‖Pᵢⱼ‖` of a matrix `P`.
* `l1Op P`: the matrix `P` as a bounded operator on `ℓ₁`.
* `l1Sub Y`: a subspace `Y ⊆ 𝕜^ι`, regarded as a subspace of `ℓ₁^ι`.

## Main statements

* `norm_l1Op`: `‖l1Op P‖ = colSumNorm P`.
* `dotProduct_l1Op_comm`: for a symmetric real matrix `P`, the operator `l1Op P` is self-adjoint
  for the dot product.
* `relProjConst_l1Sub`: `λ(Y, ℓ₁^ι)` is the infimum of `colSumNorm P` over the matrix
  projections `P` onto `Y`.
-/

open scoped Matrix
open WithLp (toLp ofLp)

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜]

section ColSum

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The maximal column sum `maxⱼ ∑ᵢ ‖Pᵢⱼ‖`, the operator norm of `P` on `ℓ₁`. -/
noncomputable def colSumNorm (P : Matrix m n 𝕜) : ℝ := rowSumNorm Pᵀ

/-- `0 ≤ colSumNorm P`. -/
lemma colSumNorm_nonneg (P : Matrix m n 𝕜) : 0 ≤ colSumNorm P := rowSumNorm_nonneg _

/-- Every column sum `∑ᵢ ‖Pᵢⱼ‖` is at most `colSumNorm P`. -/
lemma col_le_colSumNorm (P : Matrix m n 𝕜) (j : n) : ∑ i, ‖P i j‖ ≤ colSumNorm P :=
  row_le_rowSumNorm Pᵀ j

/-- If all column sums are at most `c ≥ 0`, then `colSumNorm P ≤ c`. -/
lemma colSumNorm_le {P : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ∑ i, ‖P i j‖ ≤ c) :
    colSumNorm P ≤ c :=
  rowSumNorm_le hc h

variable [DecidableEq n]

/-- The matrix `P` as a bounded operator `ℓ₁^n → ℓ₁^m`. -/
noncomputable def l1Op (P : Matrix m n 𝕜) : WithLp 1 (n → 𝕜) →L[𝕜] WithLp 1 (m → 𝕜) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 1 1 P)

/-- `l1Op P` acts on the underlying vectors by `x ↦ P *ᵥ x`. -/
@[simp] lemma ofLp_l1Op (P : Matrix m n 𝕜) (x : WithLp 1 (n → 𝕜)) :
    ofLp (l1Op P x) = P *ᵥ ofLp x := rfl

/-- `‖P x‖₁ ≤ colSumNorm P * ‖x‖₁`. -/
lemma norm_l1Op_apply_le (P : Matrix m n 𝕜) (x : WithLp 1 (n → 𝕜)) :
    ‖l1Op P x‖ ≤ colSumNorm P * ‖x‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  calc ∑ i, ‖(l1Op P x) i‖ = ∑ i, ‖∑ j, P i j * x j‖ := rfl
    _ ≤ ∑ i, ∑ j, ‖P i j‖ * ‖x j‖ := by
        gcongr with i
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ norm_mul _ _))
    _ = ∑ j, (∑ i, ‖P i j‖) * ‖x j‖ := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, colSumNorm P * ‖x j‖ := by
        gcongr with j
        exact col_le_colSumNorm P j
    _ = colSumNorm P * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]

/-- **The operator norm of a matrix acting on `ℓ₁` is its maximal column sum.** -/
theorem norm_l1Op (P : Matrix m n 𝕜) : ‖l1Op P‖ = colSumNorm P := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (colSumNorm_nonneg P) (norm_l1Op_apply_le P)) ?_
  refine colSumNorm_le (norm_nonneg _) fun j ↦ ?_
  have h := (l1Op P).le_opNorm (toLp 1 (Pi.single j (1 : 𝕜) : n → 𝕜))
  have h1 : ‖toLp 1 (Pi.single j (1 : 𝕜) : n → 𝕜)‖ = 1 := by
    rw [PiLp.norm_eq_of_L1, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have h2 : ‖l1Op P (toLp 1 (Pi.single j (1 : 𝕜) : n → 𝕜))‖ = ∑ i, ‖P i j‖ := by
    rw [PiLp.norm_eq_of_L1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ‖(P *ᵥ (Pi.single j (1 : 𝕜) : n → 𝕜)) i‖ = _
    simp
  rwa [h1, mul_one, h2] at h

omit [Fintype m] in
/-- For a symmetric real matrix `P`, `l1Op P` is self-adjoint for the dot product:
`(P x) ⬝ᵥ y = x ⬝ᵥ (P y)`. -/
lemma dotProduct_l1Op_comm {P : Matrix n n ℝ} (hP : P.IsSymm) (x y : WithLp 1 (n → ℝ)) :
    ofLp (l1Op P x) ⬝ᵥ ofLp y = ofLp x ⬝ᵥ ofLp (l1Op P y) := by
  simp only [ofLp_l1Op]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP.eq, dotProduct_comm]

end ColSum

section Projections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A subspace `Y ⊆ 𝕜^ι`, regarded as a subspace of `ℓ₁^ι = WithLp 1 (ι → 𝕜)`. -/
def l1Sub (Y : Submodule 𝕜 (ι → 𝕜)) : Submodule 𝕜 (WithLp 1 (ι → 𝕜)) :=
  Y.comap (WithLp.linearEquiv 1 𝕜 (ι → 𝕜)).toLinearMap

omit [Fintype ι] [DecidableEq ι] in
/-- `x ∈ l1Sub Y` if and only if the underlying vector of `x` lies in `Y`. -/
@[simp] lemma mem_l1Sub {Y : Submodule 𝕜 (ι → 𝕜)} {x : WithLp 1 (ι → 𝕜)} :
    x ∈ l1Sub Y ↔ ofLp x ∈ Y := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `l1Sub Y` has the same dimension as `Y`. -/
lemma finrank_l1Sub (Y : Submodule 𝕜 (ι → 𝕜)) :
    Module.finrank 𝕜 (l1Sub Y) = Module.finrank 𝕜 Y := by
  rw [l1Sub, Submodule.comap_equiv_eq_map_symm]
  exact ((WithLp.linearEquiv 1 𝕜 (ι → 𝕜)).symm.submoduleMap Y).finrank_eq.symm

variable (Y : Submodule 𝕜 (ι → 𝕜))

/-- A matrix projection onto `Y` is a projection of `ℓ₁^ι` onto `l1Sub Y`. -/
lemma IsMatrixProjOnto.l1Op {P : Matrix ι ι 𝕜} (hP : IsMatrixProjOnto Y P) :
    IsProjectionOnto (l1Sub Y) (l1Op P) :=
  ⟨fun x ↦ hP.mem (ofLp x), fun y hy ↦ by
    have h : P *ᵥ ofLp y = ofLp y := hP.map_id _ hy
    change toLp 1 (P *ᵥ ofLp y) = y
    rw [h, WithLp.toLp_ofLp]⟩

/-- If `l1Op P` is a projection onto `l1Sub Y`, then `P` is a matrix projection onto `Y`. -/
lemma isMatrixProjOnto_of_l1Op {P : Matrix ι ι 𝕜} (h : IsProjectionOnto (l1Sub Y) (l1Op P)) :
    IsMatrixProjOnto Y P :=
  ⟨fun x ↦ h.mem (toLp 1 x), fun y hy ↦ congrArg ofLp (h.map_id (toLp 1 y) hy)⟩

/-- Every bounded operator on `ℓ₁^ι` is given by a matrix. -/
lemma l1Op_toLpLin_symm (T : WithLp 1 (ι → 𝕜) →L[𝕜] WithLp 1 (ι → 𝕜)) :
    l1Op ((Matrix.toLpLin 1 1).symm (T : WithLp 1 (ι → 𝕜) →ₗ[𝕜] WithLp 1 (ι → 𝕜))) = T := by
  ext1 x
  simp [l1Op]

omit [DecidableEq ι] in
/-- **`λ(Y, ℓ₁^ι)` via matrices**: the relative projection constant of `Y ⊆ ℓ₁^ι` is the
infimum of the maximal column sums of the matrix projections onto `Y`. -/
theorem relProjConst_l1Sub :
    relProjConst (l1Sub Y) = sInf (colSumNorm '' {P : Matrix ι ι 𝕜 | IsMatrixProjOnto Y P}) := by
  classical
  unfold relProjConst
  congr 1
  ext c
  constructor
  · rintro ⟨T, hT, rfl⟩
    set P := (Matrix.toLpLin 1 1).symm (T : WithLp 1 (ι → 𝕜) →ₗ[𝕜] WithLp 1 (ι → 𝕜))
    have hPT : l1Op P = T := l1Op_toLpLin_symm T
    refine ⟨P, isMatrixProjOnto_of_l1Op Y (hPT ▸ hT), ?_⟩
    simp only
    rw [← norm_l1Op, hPT]
  · rintro ⟨P, hP, rfl⟩
    exact ⟨l1Op P, hP.l1Op Y, norm_l1Op P⟩

end Projections

end ProjectionConstants
