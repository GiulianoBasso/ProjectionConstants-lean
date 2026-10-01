/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Formula
import ProjectionConstants.Reduction

/-!
# The maximal absolute projection constant via the formula of Chalmers and Lewicki

We combine the formula of Chalmers and Lewicki [DL, Theorem 1.1]
(`ProjectionConstants.ChalmersLewicki.Formula`) with the reduction of maximal projection constants
to subspaces of `ℓ∞^N` (`ProjectionConstants.Reduction`). Since `λ_𝕜(m, N) ≤ √m` for all `N`,
this gives the theorem of Kadec and Snobar [KS], `λ(Y) ≤ √m` for every `m`-dimensional normed
space `Y`, and the formula `λ_𝕜(m) = sup_N λ_𝕜(m, N)`.

## Main statements

* `relProjConst_le_sqrt`, `absProjConst_le_sqrt`, `maxProjConst_le_sqrt`: the theorem of Kadec
  and Snobar, `λ(Y, X) ≤ √m`, `λ(Y) ≤ √m` and `λ_𝕜(m) ≤ √m` for `m`-dimensional `Y`.
* `Superspace.relProjConst_le_absProjConst`: `λ(Y, X) ≤ λ(Y)` for every superspace `X` of `Y`.
* `absProjConst_le_maxProjConst`: `λ(Y) ≤ λ_𝕜(m)` for every `m`-dimensional space `Y`.
* `maxProjConst_eq_iSup_maxRelProjConst`: `λ_𝕜(m) = sup_N λ_𝕜(m, N)`.
* `maxProjConst_eq_iSup_clConst`: `λ_𝕜(m) = sup_N clConst 𝕜 (Fin N) m`, that is, `λ_𝕜(m)` is the
  supremum of `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` over all `N`, all unit weights `t ∈ ℝ^N` and all orthogonal
  projections `P` of rank `m`.
* `weightedAbsSum_le_maxProjConst`, `exists_lt_weightedAbsSum`: the two halves of this formula,
  in the form in which they are used.
* `quasiMaxConst_le_maxProjConst`: `μ_𝕜(m) ≤ λ_𝕜(m)`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [KS] M. I. Kadec, M. G. Snobar, *Some functionals over a compact Minkowski space*,
  Math. Notes 10 (1971).
-/

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `λ_𝕜(m, N) ≤ √m` for all `N`, in the form used by the reduction to `ℓ∞^N`. -/
lemma maxRelProjConst_le_sqrt' (m : ℕ) : ∀ N, maxRelProjConst 𝕜 m N ≤ √m :=
  fun N ↦ maxRelProjConst_le_sqrt m N

/-- **Kadec–Snobar.** `λ(Y, X) ≤ √m` for every `m`-dimensional subspace of a normed space. -/
theorem relProjConst_le_sqrt {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Y : Submodule 𝕜 X) [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) :
    relProjConst Y ≤ √m :=
  relProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ(Y) ≤ √m` for every `m`-dimensional normed space `Y`. -/
theorem absProjConst_le_sqrt (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) : absProjConst 𝕜 Y ≤ √m :=
  absProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m) Y hY

/-- **Kadec–Snobar.** `λ_𝕜(m) ≤ √m`. -/
theorem maxProjConst_le_sqrt (m : ℕ) : maxProjConst 𝕜 m ≤ √m :=
  maxProjConst_le_of_maxRelProjConst_le (maxRelProjConst_le_sqrt' m)

/-- `λ(Y, X) ≤ λ(Y)` for every superspace `X` of a finite-dimensional normed space `Y`. -/
theorem Superspace.relProjConst_le_absProjConst {Y : Type u} [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [FiniteDimensional 𝕜 Y] (X : Superspace 𝕜 Y) :
    relProjConst (LinearMap.range X.emb.toLinearMap) ≤ absProjConst 𝕜 Y := by
  have hdim : ∀ X' : Superspace 𝕜 Y,
      Module.finrank 𝕜 (LinearMap.range X'.emb.toLinearMap) = Module.finrank 𝕜 Y :=
    fun X' ↦ LinearMap.finrank_range_of_inj X'.emb.injective
  refine le_ciSup
    (f := fun X' : Superspace 𝕜 Y ↦ relProjConst (LinearMap.range X'.emb.toLinearMap))
    ⟨√(Module.finrank 𝕜 Y), ?_⟩ X
  rintro _ ⟨X', rfl⟩
  exact relProjConst_le_sqrt _ (hdim X')

/-- `λ(Y) ≤ λ_𝕜(m)` for every `m`-dimensional normed space `Y : Type`. -/
theorem absProjConst_le_maxProjConst (Y : Type) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) :
    absProjConst 𝕜 Y ≤ maxProjConst 𝕜 m :=
  le_ciSup (f := fun Y' : FinDimNormedSpace 𝕜 m ↦ absProjConst 𝕜 Y'.carrier)
    ⟨√m, by rintro _ ⟨Y', rfl⟩; exact absProjConst_le_sqrt _ Y'.finrank_eq⟩ ⟨Y, hY⟩

section Type0

variable {𝕜 : Type} [RCLike 𝕜]

/-- `λ_𝕜(m) = sup_N λ_𝕜(m, N)`. -/
theorem maxProjConst_eq_iSup_maxRelProjConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, maxRelProjConst 𝕜 m N :=
  maxProjConst_eq_iSup_of_le (maxRelProjConst_le_sqrt' m)

/-- `λ_𝕜(m) = sup_N clConst 𝕜 (Fin N) m`, the supremum of `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` over all `N`, all
`t ∈ ℝ^N` with `t ≥ 0`, `‖t‖₂ = 1` and all `P ∈ orthProjs 𝕜 (Fin N) m`. -/
theorem maxProjConst_eq_iSup_clConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, clConst 𝕜 (Fin N) m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  simp_rw [maxRelProjConst_eq_clConst]

/-- `λ_𝕜(m, N) ≤ λ_𝕜(m)`. -/
lemma maxRelProjConst_le_maxProjConst (m N : ℕ) : maxRelProjConst 𝕜 m N ≤ maxProjConst 𝕜 m := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  exact le_ciSup ⟨√m, by rintro _ ⟨N, rfl⟩; exact maxRelProjConst_le_sqrt m N⟩ N

/-- `clConst 𝕜 (Fin N) m ≤ λ_𝕜(m)`. -/
lemma clConst_le_maxProjConst (m N : ℕ) : clConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m := by
  rw [← maxRelProjConst_eq_clConst]; exact maxRelProjConst_le_maxProjConst m N

/-- Every `m`-dimensional `Y ⊆ ℓ∞^N` gives a lower bound `λ(Y, ℓ∞^N) ≤ λ_𝕜(m)`. -/
lemma relProjConst_le_maxProjConst' {m N : ℕ} (Y : Submodule 𝕜 (Fin N → 𝕜))
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ maxProjConst 𝕜 m :=
  relProjConst_le_maxProjConst (maxRelProjConst_le_sqrt' m) Y hY

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ_𝕜(m)` for every unit weight `t` and every `P ∈ orthProjs 𝕜 ι m`. -/
lemma weightedAbsSum_le_maxProjConst {m : ℕ} {ι : Type*} [Fintype ι]
    {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    weightedAbsSum t P ≤ maxProjConst 𝕜 m := by
  -- relabel `ι` as `Fin N`
  let e := (Fintype.equivFin ι).symm
  have hP' := submatrix_mem_orthProjs e hP
  have ht' : IsUnitWeight (t ∘ e) :=
    ⟨fun i ↦ ht.nonneg _, by rw [← ht.sum_sq]; exact e.sum_comp (fun i ↦ t i ^ 2)⟩
  have h1 : weightedAbsSum (t ∘ e) (P.submatrix e e) = weightedAbsSum t P := by
    simp only [weightedAbsSum, Function.comp_apply, Matrix.submatrix_apply]
    rw [e.sum_comp (fun i ↦ ∑ j, t i * t (e j) * ‖P i (e j)‖)]
    exact Finset.sum_congr rfl fun i _ ↦ e.sum_comp (fun j ↦ t i * t j * ‖P i j‖)
  rw [← h1]
  exact (le_clConst ht' hP').trans (clConst_le_maxProjConst m _)

/-- `λ_𝕜(m)` is approximated by the values `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` for unit weights `t ∈ ℝ^N` and
`P ∈ orthProjs 𝕜 (Fin N) m`. -/
theorem exists_lt_weightedAbsSum {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (t : Fin N → ℝ) (P : Matrix (Fin N) (Fin N) 𝕜), IsUnitWeight t ∧
      P ∈ orthProjs 𝕜 (Fin N) m ∧ maxProjConst 𝕜 m - δ < weightedAbsSum t P := by
  by_contra! h
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h1 : (1 : Matrix (Fin m) (Fin m) 𝕜) ∈ orthProjs 𝕜 (Fin m) m :=
    ⟨IsStarProjection.one _, by simp⟩
  have h0 : 0 ≤ maxProjConst 𝕜 m - δ := (weightedAbsSum_nonneg isUnitWeight_uniform.nonneg _).trans
    (h _ _ _ isUnitWeight_uniform h1)
  have hle : maxProjConst 𝕜 m ≤ maxProjConst 𝕜 m - δ := by
    conv_lhs => rw [maxProjConst_eq_iSup_clConst]
    exact ciSup_le fun N ↦ clConst_le h0 fun t P ht hP ↦ h N t P ht hP
  linarith

/-- `μ_𝕜(m, N) ≤ λ_𝕜(m)`. -/
lemma quasiRelConst_le_maxProjConst {m : ℕ} (N : ℕ) :
    quasiRelConst 𝕜 (Fin N) m ≤ maxProjConst 𝕜 m :=
  (quasiRelConst_le_maxRelProjConst m N).trans (maxRelProjConst_le_maxProjConst m N)

/-- `μ_𝕜(m) ≤ λ_𝕜(m)`; equality holds by `maxProjConst_eq_quasiMaxConst`. -/
lemma quasiMaxConst_le_maxProjConst (m : ℕ) : quasiMaxConst 𝕜 m ≤ maxProjConst 𝕜 m :=
  quasiMaxConst_le (maxProjConst_nonneg m) fun N ↦ quasiRelConst_le_maxProjConst N

end Type0

end ProjectionConstants
