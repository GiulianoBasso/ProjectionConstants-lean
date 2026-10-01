/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The extension property and the invariance of projection constants

A normed space `E` has the **extension property** (it is `1`-injective) if every bounded operator
from a subspace `W` of a normed space `Z` to `E` extends to `Z` without increasing its norm. By
the Hahn–Banach theorem, applied to each coordinate, the spaces `ℓ∞^ι = (ι → 𝕜)` (`ι` finite)
and `ℓ∞(Γ)` (`Γ` arbitrary) have the extension property. The projection constant of a
finite-dimensional space `Y` can be computed in any superspace with the extension property:
`λ(Y) = λ(Y, E)` [G, §1]. This is how `λ(Y)` is computed for subspaces `Y ⊆ ℓ∞^N`.

We also show that `λ` is an isometric invariant, and that it is Lipschitz with respect to the
Banach–Mazur distance: `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)` for every isomorphism `T : X → Y`. This is the
lemma in [G, §3], by which Grünbaum deduces `λ(ℓ₂²) = 4/π` from the projection constants of the
regular `2ⁿ`-gons.

## Main definitions

* `HasExtensionProperty 𝕜 E`: every bounded operator into `E` defined on a subspace of a normed
  space extends to the whole space with the same bound.

## Main statements

* `hasExtensionProperty_pi`, `hasExtensionProperty_lp`: `ℓ∞^ι` and `ℓ∞(Γ)` have the extension
  property.
* `HasExtensionProperty.absProjConst_eq`: `λ(Y) = λ(Y, E)` if `E` has the extension property.
* `LinearIsometryEquiv.absProjConst_eq`: isometric spaces have the same projection constant.
* `absProjConst_eq_relProjConst_pi`: `λ(Y) = λ(Y, ℓ∞^ι)` for every subspace `Y ⊆ ℓ∞^ι`.
* `absProjConst_of_subsingleton`: the projection constant of the zero space is `0`.
* `ContinuousLinearEquiv.absProjConst_le`: `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)` [G, §3, Lemma].
* `absProjConst_le_mul_of_le_of_le`: Grünbaum's formulation: if `‖x‖ ≤ ‖T x‖ ≤ μ ‖x‖`, then
  `λ(Y) ≤ μ λ(X)` and `λ(X) ≤ μ λ(Y)`.

## Implementation notes

The extension property quantifies over normed spaces `Z` in the universe of `E`, which is the
universe of the superspaces in the definition of `absProjConst`. The Banach–Mazur estimate uses
the isometric embedding of `X` into `ℓ∞(X)` by norming functionals; this is why it is stated for
a field `𝕜 : Type`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.

## Tags

projection constant, extension property, injective Banach space, Banach–Mazur distance
-/

open scoped ENNReal

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The extension property -/

section Extension

variable (𝕜) in
/-- A normed space `E` has the **extension property** if every bounded operator from a subspace
`W` of a normed space `Z` (in the universe of `E`) to `E` extends to `Z` without increasing its
norm. -/
def HasExtensionProperty (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (W : Submodule 𝕜 Z) (S : W →L[𝕜] E),
    ∃ S' : Z →L[𝕜] E, (∀ w : W, S' w = S w) ∧ ‖S'‖ ≤ ‖S‖

/-- **`ℓ∞^ι` has the extension property**: extend each coordinate by Hahn–Banach. -/
theorem hasExtensionProperty_pi (ι : Type*) [Fintype ι] : HasExtensionProperty 𝕜 (ι → 𝕜) := by
  intro Z _ _ W S
  choose Φ hΦ hΦn using fun i ↦ exists_extension_norm_eq W ((ContinuousLinearMap.proj i).comp S)
  refine ⟨ContinuousLinearMap.pi Φ, fun w ↦ funext fun i ↦ hΦ i w, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z ↦ ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  have hi : ‖(ContinuousLinearMap.proj i).comp S‖ ≤ ‖S‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w ↦
      (norm_le_pi_norm (S w) i).trans (S.le_opNorm w)
  calc ‖Φ i z‖ ≤ ‖Φ i‖ * ‖z‖ := (Φ i).le_opNorm z
    _ ≤ ‖S‖ * ‖z‖ := by rw [hΦn]; gcongr

/-- **`ℓ∞(Γ)` has the extension property**: extend each coordinate by Hahn–Banach. -/
theorem hasExtensionProperty_lp (Γ : Type*) :
    HasExtensionProperty 𝕜 (lp (fun _ : Γ ↦ 𝕜) ∞) := by
  intro Z _ _ W S
  choose Φ hΦ hΦn using fun γ ↦ exists_extension_norm_eq W
    ((lp.evalCLM 𝕜 (fun _ : Γ ↦ 𝕜) ∞ γ).comp S)
  have hΦle : ∀ γ, ‖Φ γ‖ ≤ ‖S‖ := fun γ ↦ by
    rw [hΦn]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w ↦
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (S w) γ).trans (S.le_opNorm w)
  have hle : ∀ z γ, ‖Φ γ z‖ ≤ ‖S‖ * ‖z‖ := fun z γ ↦
    ((Φ γ).le_opNorm z).trans (by gcongr; exact hΦle γ)
  let T : Z →ₗ[𝕜] lp (fun _ : Γ ↦ 𝕜) ∞ :=
    { toFun := fun z ↦ ⟨fun γ ↦ Φ γ z, memℓp_infty ⟨‖S‖ * ‖z‖, by
        rintro _ ⟨γ, rfl⟩; exact hle z γ⟩⟩
      map_add' := fun z z' ↦ lp.ext (funext fun γ ↦ map_add (Φ γ) z z')
      map_smul' := fun c z ↦ lp.ext (funext fun γ ↦ map_smul (Φ γ) c z) }
  refine ⟨T.mkContinuous ‖S‖ fun z ↦ lp.norm_le_of_forall_le (by positivity) (hle z), fun w ↦ ?_,
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _⟩
  exact lp.ext (funext fun γ ↦ hΦ γ w)

end Extension

/-! ### Invariance under isometries -/

section Invariance

/-- Isometric spaces have the same absolute projection constant. -/
theorem _root_.LinearIsometryEquiv.absProjConst_eq {X Y : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (e : X ≃ₗᵢ[𝕜] Y) :
    absProjConst 𝕜 X = absProjConst 𝕜 Y := by
  -- composing the embedding with `e` identifies the superspaces of `Y` with those of `X`
  have key : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
      [NormedSpace 𝕜 Y] (e : X ≃ₗᵢ[𝕜] Y),
      Set.range (fun Z : Superspace 𝕜 Y ↦ relProjConst (LinearMap.range Z.emb.toLinearMap)) ⊆
        Set.range (fun Z : Superspace 𝕜 X ↦ relProjConst (LinearMap.range Z.emb.toLinearMap)) := by
    intro X Y _ _ _ _ e
    rintro _ ⟨Z, rfl⟩
    refine ⟨⟨Z.carrier, Z.emb.comp e.toLinearIsometry⟩, ?_⟩
    have h : LinearMap.range (Z.emb.comp e.toLinearIsometry).toLinearMap =
        LinearMap.range Z.emb.toLinearMap := by
      ext z
      simp only [LinearMap.mem_range, LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp,
        Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨e x, hx⟩, fun ⟨y, hy⟩ ↦ ⟨e.symm y, by simpa using hy⟩⟩
    exact congrArg relProjConst h
  exact congrArg sSup (Set.Subset.antisymm (key e.symm) (key e))

/-- The projection constant of the zero space is `0`. -/
theorem absProjConst_of_subsingleton (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [Subsingleton X] : absProjConst 𝕜 X = 0 := by
  refine le_antisymm (Real.iSup_le (fun Z ↦ ?_) le_rfl)
    (Real.iSup_nonneg fun _ ↦ relProjConst_nonneg _)
  have h0 : ∀ z ∈ LinearMap.range Z.emb.toLinearMap, z = 0 := by
    rintro _ ⟨x, rfl⟩
    simp [Subsingleton.elim x 0]
  have hP : IsProjectionOnto (LinearMap.range Z.emb.toLinearMap) 0 :=
    ⟨fun _ ↦ Submodule.zero_mem _, fun y hy ↦ (h0 y hy).symm ▸ rfl⟩
  exact (relProjConst_le _ hP).trans norm_zero.le

end Invariance

/-! ### Computing projection constants in spaces with the extension property -/

section Computation

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The projection constant can be computed in a superspace with the extension property**:
`λ(Y) = λ(Y, E)` [G, §1]. Given a superspace `Z ⊇ Y` and a projection `P` of `E` onto `Y`, extend
the inclusion `Y → E` to `S : Z → E` with `‖S‖ ≤ 1`; then `P S` is a projection of `Z` onto `Y`
with `‖P S‖ ≤ ‖P‖`. -/
theorem HasExtensionProperty.absProjConst_eq (hE : HasExtensionProperty 𝕜 E) (Y : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 Y] : absProjConst 𝕜 Y = relProjConst Y := by
  have key : ∀ Z : Superspace 𝕜 Y,
      relProjConst (LinearMap.range Z.emb.toLinearMap) ≤ relProjConst Y := by
    intro Z
    refine le_relProjConst Y fun P hP ↦ ?_
    -- the inverse of the embedding, as an operator into `E`
    let S : LinearMap.range Z.emb.toLinearMap →L[𝕜] E :=
      Y.subtypeL.comp (Z.emb.equivRange.symm.toContinuousLinearEquiv :
        LinearMap.range Z.emb.toLinearMap →L[𝕜] Y)
    have hS : ∀ y : Y, S ⟨Z.emb y, y, rfl⟩ = y := fun y ↦ by
      have h : Z.emb.equivRange.symm ⟨Z.emb y, y, rfl⟩ = y := by
        rw [LinearIsometryEquiv.symm_apply_eq]; rfl
      simp [S, h]
    have hSn : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p ↦ by
      simp only [S, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, one_mul]
      exact (Z.emb.equivRange.symm.norm_map p).le
    obtain ⟨S', hS', hS'n⟩ := hE Z.carrier _ S
    -- the projection `Q = J P S'` of `Z` onto `J(Y)`
    let Q : Z.carrier →L[𝕜] Z.carrier :=
      Z.emb.toContinuousLinearMap.comp ((P.codRestrict Y hP.mem).comp S')
    have hQ : IsProjectionOnto (LinearMap.range Z.emb.toLinearMap) Q := by
      refine ⟨fun z ↦ ⟨_, rfl⟩, ?_⟩
      rintro _ ⟨y, rfl⟩
      have h1 : S' (Z.emb y) = y := (hS' ⟨Z.emb y, y, rfl⟩).trans (hS y)
      have h2 : P.codRestrict Y hP.mem (y : E) = y := Subtype.ext (hP.map_id _ y.2)
      simp [Q, h1, h2]
    refine (relProjConst_le _ hQ).trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      fun z ↦ ?_)
    calc ‖Q z‖ = ‖P (S' z)‖ := by simp [Q]
      _ ≤ ‖P‖ * ‖S' z‖ := P.le_opNorm _
      _ ≤ ‖P‖ * ‖z‖ := by
          gcongr
          exact (S'.le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg z) (hS'n.trans hSn))
  refine le_antisymm (Real.iSup_le key (relProjConst_nonneg Y)) ?_
  have h := le_ciSup ⟨relProjConst Y, by rintro _ ⟨Z, rfl⟩; exact key Z⟩
    (Superspace.ofSubmodule Y)
  rwa [Superspace.range_ofSubmodule] at h

/-- If `E` has the extension property and `f : X → E` is an isometric embedding, then
`λ(X) = λ(f(X), E)`. -/
theorem HasExtensionProperty.absProjConst_eq_of_linearIsometry (hE : HasExtensionProperty 𝕜 E)
    {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    (f : X →ₗᵢ[𝕜] E) : absProjConst 𝕜 X = relProjConst (LinearMap.range f.toLinearMap) := by
  rw [f.equivRange.absProjConst_eq, hE.absProjConst_eq]

/-- `λ(Y) = λ(Y, ℓ∞^ι)` for every subspace `Y ⊆ ℓ∞^ι`. -/
theorem absProjConst_eq_relProjConst_pi {ι : Type*} [Fintype ι] (Y : Submodule 𝕜 (ι → 𝕜)) :
    absProjConst 𝕜 Y = relProjConst Y :=
  (hasExtensionProperty_pi ι).absProjConst_eq Y

end Computation

/-! ### The Banach–Mazur estimate -/

section BanachMazur

variable {𝕜 : Type} [RCLike 𝕜] {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

variable (𝕜 X) in
/-- Every normed space `X` embeds isometrically into `ℓ∞(X)`, by `x ↦ (φ_y x)_y` for norming
functionals `φ_y` (`‖φ_y‖ ≤ 1`, `φ_y y = ‖y‖`). -/
theorem exists_linearIsometry_lp : Nonempty (X →ₗᵢ[𝕜] lp (fun _ : X ↦ 𝕜) ∞) := by
  choose φ hφ1 hφy using fun y : X ↦ exists_dual_vector'' 𝕜 y
  have hle : ∀ x y, ‖φ y x‖ ≤ ‖x‖ := fun x y ↦
    ((φ y).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) (hφ1 y))
  let T : X →ₗ[𝕜] lp (fun _ : X ↦ 𝕜) ∞ :=
    { toFun := fun x ↦ ⟨fun y ↦ φ y x, memℓp_infty ⟨‖x‖, by rintro _ ⟨y, rfl⟩; exact hle x y⟩⟩
      map_add' := fun x x' ↦ lp.ext (funext fun y ↦ map_add (φ y) x x')
      map_smul' := fun c x ↦ lp.ext (funext fun y ↦ map_smul (φ y) c x) }
  refine ⟨⟨T, fun x ↦ le_antisymm (lp.norm_le_of_forall_le (norm_nonneg x) (hle x)) ?_⟩⟩
  calc ‖x‖ = ‖φ x x‖ := by rw [hφy]; simp
    _ ≤ ‖T x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero (T x) x

/-- **Grünbaum's lemma** [G, §3]: the projection constant is Lipschitz with respect to the
Banach–Mazur distance, `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)` for every isomorphism `T : X → Y`.

Embed `X` isometrically into `ℓ∞(X)` and let `P` be a projection onto its image. Given a
superspace `Z ⊇ Y`, extend `T⁻¹ : Y → X ⊆ ℓ∞(X)` to `S : Z → ℓ∞(X)` with `‖S‖ ≤ ‖T⁻¹‖`; then
`T P S` is a projection of `Z` onto `Y`. -/
theorem _root_.ContinuousLinearEquiv.absProjConst_le [FiniteDimensional 𝕜 X] (T : X ≃L[𝕜] Y) :
    absProjConst 𝕜 Y ≤ ‖(T : X →L[𝕜] Y)‖ * ‖(T.symm : Y →L[𝕜] X)‖ * absProjConst 𝕜 X := by
  obtain ⟨ι⟩ := exists_linearIsometry_lp 𝕜 X
  have hL : HasExtensionProperty 𝕜 (lp (fun _ : X ↦ 𝕜) ∞) := hasExtensionProperty_lp X
  rw [hL.absProjConst_eq_of_linearIsometry ι]
  set R := LinearMap.range ι.toLinearMap
  set K := ‖(T : X →L[𝕜] Y)‖ * ‖(T.symm : Y →L[𝕜] X)‖ with hK_def
  have hK : 0 ≤ K := by positivity
  refine Real.iSup_le (fun Z ↦ ?_) (mul_nonneg hK (relProjConst_nonneg R))
  set J := LinearMap.range Z.emb.toLinearMap
  -- every projection of `ℓ∞(X)` onto `ι(X)` gives a projection of `Z` onto `J(Y)`
  have key : ∀ P : lp (fun _ : X ↦ 𝕜) ∞ →L[𝕜] lp (fun _ : X ↦ 𝕜) ∞, IsProjectionOnto R P →
      relProjConst J ≤ K * ‖P‖ := by
    intro P hP
    let S : J →L[𝕜] lp (fun _ : X ↦ 𝕜) ∞ :=
      ι.toContinuousLinearMap.comp ((T.symm : Y →L[𝕜] X).comp
        (Z.emb.equivRange.symm.toContinuousLinearEquiv : J →L[𝕜] Y))
    have hS : ∀ y : Y, S ⟨Z.emb y, y, rfl⟩ = ι (T.symm y) := fun y ↦ by
      have h : Z.emb.equivRange.symm ⟨Z.emb y, y, rfl⟩ = y := by
        rw [LinearIsometryEquiv.symm_apply_eq]; rfl
      simp [S, h]
    have hSn : ‖S‖ ≤ ‖(T.symm : Y →L[𝕜] X)‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p ↦ by
        simpa [S] using (T.symm : Y →L[𝕜] X).le_opNorm (Z.emb.equivRange.symm p)
    obtain ⟨S', hS', hS'n⟩ := hL Z.carrier J S
    let ιinv : R →L[𝕜] X := (ι.equivRange.symm.toContinuousLinearEquiv : R →L[𝕜] X)
    have hιinv : ∀ x : X, ιinv ⟨ι x, x, rfl⟩ = x := fun x ↦ by
      simp only [ιinv, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [LinearIsometryEquiv.symm_apply_eq]; rfl
    let Q : Z.carrier →L[𝕜] Z.carrier := Z.emb.toContinuousLinearMap.comp
      ((T : X →L[𝕜] Y).comp (ιinv.comp ((P.codRestrict R hP.mem).comp S')))
    have hQ : IsProjectionOnto J Q := by
      refine ⟨fun z ↦ ⟨_, rfl⟩, ?_⟩
      rintro _ ⟨y, rfl⟩
      have h1 : S' (Z.emb y) = ι (T.symm y) := (hS' ⟨Z.emb y, y, rfl⟩).trans (hS y)
      have h2 : P.codRestrict R hP.mem (ι (T.symm y)) = ⟨ι (T.symm y), T.symm y, rfl⟩ :=
        Subtype.ext (hP.map_id _ ⟨T.symm y, rfl⟩)
      simp [Q, h1, h2, hιinv]
    refine (relProjConst_le _ hQ).trans (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      fun z ↦ ?_)
    have hιn : ∀ r : R, ‖ιinv r‖ = ‖r‖ := fun r ↦ by simp [ιinv]
    calc ‖Q z‖ = ‖(T : X →L[𝕜] Y) (ιinv (P.codRestrict R hP.mem (S' z)))‖ := by simp [Q]
      _ ≤ ‖(T : X →L[𝕜] Y)‖ * ‖ιinv (P.codRestrict R hP.mem (S' z))‖ :=
          T.toContinuousLinearMap.le_opNorm _
      _ = ‖(T : X →L[𝕜] Y)‖ * ‖P (S' z)‖ := by rw [hιn]; rfl
      _ ≤ ‖(T : X →L[𝕜] Y)‖ * (‖P‖ * (‖(T.symm : Y →L[𝕜] X)‖ * ‖z‖)) := by
          gcongr
          refine (P.le_opNorm _).trans ?_
          gcongr
          exact (S'.le_opNorm z).trans (by gcongr; exact hS'n.trans hSn)
      _ = K * ‖P‖ * ‖z‖ := by rw [hK_def]; ring
  -- optimize over `P`
  rcases hK.eq_or_lt with hK0 | hKpos
  · obtain ⟨P, hP⟩ := exists_isProjectionOnto R
    simpa [← hK0] using key P hP
  · have h : relProjConst J / K ≤ relProjConst R :=
      le_relProjConst R fun P hP ↦ (div_le_iff₀' hKpos).2 (key P hP)
    calc relProjConst J = K * (relProjConst J / K) := by field_simp
      _ ≤ K * relProjConst R := by gcongr

/-- **Grünbaum's lemma** [G, §3] in its original form, for two norms `‖·‖₁ ≤ ‖·‖₂ ≤ μ ‖·‖₁` on
the same space: if `T : X → Y` is a linear bijection with `‖x‖ ≤ ‖T x‖ ≤ μ ‖x‖`, then
`λ(Y) ≤ μ λ(X)` and `λ(X) ≤ μ λ(Y)`. -/
theorem absProjConst_le_mul_of_le_of_le [FiniteDimensional 𝕜 X] (T : X ≃ₗ[𝕜] Y) {μ : ℝ}
    (h₁ : ∀ x, ‖x‖ ≤ ‖T x‖) (h₂ : ∀ x, ‖T x‖ ≤ μ * ‖x‖) :
    absProjConst 𝕜 Y ≤ μ * absProjConst 𝕜 X ∧ absProjConst 𝕜 X ≤ μ * absProjConst 𝕜 Y := by
  have : FiniteDimensional 𝕜 Y := T.finiteDimensional
  rcases le_or_gt 0 μ with hμ | hμ
  · let T' : X ≃L[𝕜] Y := T.toContinuousLinearEquiv
    have hT : ‖(T' : X →L[𝕜] Y)‖ ≤ μ :=
      ContinuousLinearMap.opNorm_le_bound _ hμ fun x ↦ h₂ x
    have hT' : ‖(T'.symm : Y →L[𝕜] X)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
        change ‖T.symm y‖ ≤ 1 * ‖y‖
        simpa using h₁ (T.symm y)
    have hX := absProjConst_nonneg (𝕜 := 𝕜) X
    have hY := absProjConst_nonneg (𝕜 := 𝕜) Y
    constructor
    · calc absProjConst 𝕜 Y ≤ ‖(T' : X →L[𝕜] Y)‖ * ‖(T'.symm : Y →L[𝕜] X)‖ * absProjConst 𝕜 X :=
            T'.absProjConst_le
        _ ≤ μ * 1 * absProjConst 𝕜 X := by gcongr
        _ = μ * absProjConst 𝕜 X := by ring
    · calc absProjConst 𝕜 X ≤ ‖(T'.symm : Y →L[𝕜] X)‖ * ‖(T'.symm.symm : X →L[𝕜] Y)‖ *
            absProjConst 𝕜 Y := T'.symm.absProjConst_le
        _ ≤ 1 * μ * absProjConst 𝕜 Y := by gcongr; exact hT
        _ = μ * absProjConst 𝕜 Y := by ring
  · -- for `μ < 0` both spaces are zero
    have hX : Subsingleton X := ⟨fun x x' ↦ by
      have h : ∀ x : X, x = 0 := fun x ↦ norm_le_zero_iff.1 (by
        nlinarith [h₁ x, h₂ x, norm_nonneg x, norm_nonneg (T x)])
      rw [h x, h x']⟩
    have hY : Subsingleton Y := T.symm.toEquiv.subsingleton
    simp [absProjConst_of_subsingleton]

end BanachMazur

end ProjectionConstants
