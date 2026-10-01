/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.RCLike.Basic

/-!
# Projection constants

Let `X` be a normed space over `𝕜 = ℝ` or `ℂ` and let `Y ⊆ X` be a finite-dimensional subspace.
A projection of `X` onto `Y` is a bounded linear operator `P : X → X` with `P(X) ⊆ Y` and `P y = y`
for `y ∈ Y`; such projections exist because `Y` is complemented. This file defines the relative,
the absolute and the maximal absolute projection constants, following [DL, §1].

The reduction of the suprema to subspaces of the finite-dimensional spaces `ℓ∞^N` is proved in
`ProjectionConstants.Reduction`, and the Kadec–Snobar bound `λ_𝕜(m) ≤ √m`, which shows that the
suprema are finite, in `ProjectionConstants.ChalmersLewicki.Absolute`. The invariance of `λ(Y)`
under isometries and its computation in superspaces with the extension property (such as `ℓ∞^N`)
are in `ProjectionConstants.Injective`.

## Main definitions

* `IsProjectionOnto Y P`: the bounded operator `P : X → X` is a projection onto `Y`, i.e.
  `P(X) ⊆ Y` and `P|_Y = id`.
* `relProjConst Y`: the **relative projection constant** `λ(Y, X) = inf ‖P‖`, the infimum over
  all projections of `X` onto `Y`.
* `Superspace 𝕜 Y`: a normed space `X` together with a linear isometric embedding `Y → X`;
  `Superspace.ofSubmodule Y` is the superspace `X` of a subspace `Y ⊆ X`.
* `absProjConst 𝕜 Y`: the **absolute projection constant** `λ(Y) = sup λ(Y, X)`, the supremum
  over all superspaces `X` of `Y`.
* `FinDimNormedSpace 𝕜 m`: a bundled normed space of dimension `m`.
* `maxProjConst 𝕜 m`: the **maximal absolute projection constant**
  `λ_𝕜(m) = sup { λ(Y) : dim Y = m }`, the supremum over all `m`-dimensional normed spaces.

## Main statements

* `exists_isProjectionOnto`: every finite-dimensional subspace admits a projection onto it.
* `exists_isProjectionOnto_norm_lt`: there are projections onto `Y` of norm arbitrarily close to
  `λ(Y, X)`.
* `one_le_relProjConst`: `1 ≤ λ(Y, X)` if `Y ≠ ⊥`.
* `absProjConst_nonneg`, `maxProjConst_nonneg`: `0 ≤ λ(Y)` and `0 ≤ λ_𝕜(m)`.

## Implementation notes

The infimum and the suprema are taken in `ℝ`, where the supremum of an empty or unbounded set is
`0` by convention; `absProjConst` and `maxProjConst` are therefore only meaningful together with
the bounds mentioned above. The superspaces of a space `Y : Type u` in `absProjConst` range over
`Type u`, and the spaces in `maxProjConst` range over `Type`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

open scoped NNReal

namespace ProjectionConstants

universe u

section Relative

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- `P` is a (bounded linear) **projection of `X` onto `Y`**: `P(X) ⊆ Y` and `P y = y` for
`y ∈ Y`. -/
structure IsProjectionOnto (Y : Submodule 𝕜 X) (P : X →L[𝕜] X) : Prop where
  /-- `P` maps `X` into `Y`. -/
  mem : ∀ x, P x ∈ Y
  /-- `P` is the identity on `Y`. -/
  map_id : ∀ y ∈ Y, P y = y

/-- The **relative projection constant** `λ(Y, X) = inf { ‖P‖ : P projection of X onto Y }`. -/
noncomputable def relProjConst (Y : Submodule 𝕜 X) : ℝ :=
  sInf ((fun P : X →L[𝕜] X ↦ ‖P‖) '' {P | IsProjectionOnto Y P})

variable (Y : Submodule 𝕜 X)

/-- Finite-dimensional subspaces are complemented: there is a projection onto `Y`. -/
theorem exists_isProjectionOnto [FiniteDimensional 𝕜 Y] :
    ∃ P : X →L[𝕜] X, IsProjectionOnto Y P := by
  obtain ⟨f, hf⟩ := Submodule.ClosedComplemented.of_finiteDimensional Y
  refine ⟨Y.subtypeL.comp f, ⟨fun x ↦ (f x).2, fun y hy ↦ ?_⟩⟩
  simpa using congrArg Subtype.val (hf ⟨y, hy⟩)

/-- `0 ≤ λ(Y, X)`. -/
lemma relProjConst_nonneg : 0 ≤ relProjConst Y :=
  Real.sInf_nonneg (by rintro _ ⟨P, -, rfl⟩; exact norm_nonneg _)

/-- `λ(Y, X) ≤ ‖P‖` for every projection `P` of `X` onto `Y`. -/
lemma relProjConst_le {P : X →L[𝕜] X} (hP : IsProjectionOnto Y P) : relProjConst Y ≤ ‖P‖ :=
  csInf_le ⟨0, by rintro _ ⟨Q, -, rfl⟩; exact norm_nonneg _⟩ ⟨P, hP, rfl⟩

/-- Lower bounds for `λ(Y, X)` can be checked on the projections of `X` onto `Y`. -/
lemma le_relProjConst [FiniteDimensional 𝕜 Y] {c : ℝ}
    (h : ∀ P : X →L[𝕜] X, IsProjectionOnto Y P → c ≤ ‖P‖) : c ≤ relProjConst Y := by
  obtain ⟨P, hP⟩ := exists_isProjectionOnto Y
  exact le_csInf ⟨_, P, hP, rfl⟩ (by rintro _ ⟨Q, hQ, rfl⟩; exact h Q hQ)

/-- For every `ε > 0` there is a projection onto `Y` of norm less than `λ(Y, X) + ε`. -/
lemma exists_isProjectionOnto_norm_lt [FiniteDimensional 𝕜 Y] {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, IsProjectionOnto Y P ∧ ‖P‖ < relProjConst Y + ε := by
  obtain ⟨P, hP⟩ := exists_isProjectionOnto Y
  have hne : ((fun P : X →L[𝕜] X ↦ ‖P‖) '' {P | IsProjectionOnto Y P}).Nonempty :=
    ⟨_, P, hP, rfl⟩
  obtain ⟨_, ⟨Q, hQ, rfl⟩, h⟩ := exists_lt_of_csInf_lt hne
    (lt_add_of_pos_right (relProjConst Y) hε)
  exact ⟨Q, hQ, h⟩

/-- A nonzero subspace has relative projection constant at least `1`. -/
lemma one_le_relProjConst [FiniteDimensional 𝕜 Y] (hY : Y ≠ ⊥) : 1 ≤ relProjConst Y := by
  refine le_relProjConst Y fun P hP ↦ ?_
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have h := P.le_opNorm y
  rw [hP.map_id y hyY] at h
  exact le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hy0)

end Relative

section Absolute

/-- A **superspace** of a normed space `Y`: a normed space `X` together with a linear isometric
embedding `Y → X`. -/
structure Superspace (𝕜 : Type*) [RCLike 𝕜] (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] where
  /-- The ambient space. -/
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace 𝕜 carrier]
  /-- The isometric embedding of `Y` into the ambient space. -/
  emb : Y →ₗᵢ[𝕜] carrier

attribute [instance] Superspace.normedAddCommGroup Superspace.normedSpace

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The **absolute projection constant** `λ(Y) = sup { λ(Y, X) : Y ⊆ X }`, the supremum over all
normed spaces `X` containing `Y` isometrically. -/
noncomputable def absProjConst (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] : ℝ :=
  ⨆ X : Superspace 𝕜 Y, relProjConst (LinearMap.range X.emb.toLinearMap)

/-- A finite-dimensional normed space of dimension `m` (bundled). -/
structure FinDimNormedSpace (m : ℕ) where
  /-- The underlying type. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace 𝕜 carrier]
  [finiteDimensional : FiniteDimensional 𝕜 carrier]
  /-- The dimension of the space is `m`. -/
  finrank_eq : Module.finrank 𝕜 carrier = m

attribute [instance] FinDimNormedSpace.normedAddCommGroup FinDimNormedSpace.normedSpace
  FinDimNormedSpace.finiteDimensional

/-- The **maximal absolute projection constant** `λ_𝕜(m) = sup { λ(Y) : dim Y = m }`. -/
noncomputable def maxProjConst (m : ℕ) : ℝ :=
  ⨆ Y : FinDimNormedSpace 𝕜 m, absProjConst 𝕜 Y.carrier

variable {𝕜}

/-- The normed space `X`, regarded as a superspace of its subspace `Y` (via the inclusion). -/
def Superspace.ofSubmodule {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Y : Submodule 𝕜 X) : Superspace 𝕜 Y :=
  ⟨X, Y.subtypeₗᵢ⟩

/-- The image of `Y` in the superspace `Superspace.ofSubmodule Y` is `Y` itself. -/
@[simp] lemma Superspace.range_ofSubmodule {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (Y : Submodule 𝕜 X) :
    LinearMap.range (Superspace.ofSubmodule Y).emb.toLinearMap = Y :=
  Submodule.range_subtype Y

/-- `0 ≤ λ(Y)`. -/
lemma absProjConst_nonneg (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    0 ≤ absProjConst 𝕜 Y :=
  Real.iSup_nonneg fun _ ↦ relProjConst_nonneg _

/-- `0 ≤ λ_𝕜(m)`. -/
lemma maxProjConst_nonneg (m : ℕ) : 0 ≤ maxProjConst 𝕜 m :=
  Real.iSup_nonneg fun Y ↦ absProjConst_nonneg Y.carrier

end Absolute

end ProjectionConstants
