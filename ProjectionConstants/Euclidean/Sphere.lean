/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Invariant measures on the unit sphere

Let `E` be a finite-dimensional inner product space over `𝕜 = ℝ` or `ℂ` and let `S` be its unit
sphere. The linear isometries of `E` act transitively on `S`, and a finite measure `ν` on `S` is
*invariant* if every linear isometry preserves it.

The key fact for the projection constant of `E` (`ProjectionConstants.Euclidean.LowerBound`) is
the following symmetry lemma: for `φ : 𝕜 → 𝕜` continuous and `y ∈ S`,
`∫ φ(⟪y, u⟫) u dν(u) = a · y`, where `a = ∫ φ(⟪e, u⟫) ⟪e, u⟫ dν(u)` does not depend on `y`.
Indeed the vector on the left is fixed by every reflection that fixes `y`, so it is a multiple of
`y`, and the factor is constant since the isometries act transitively on `S`.

## Main definitions

* `sphereMap T`: the action of a linear isometry `T` of `E` on the unit sphere;
  `sphereHomeomorph T` is the corresponding homeomorphism of `S`.
* `IsInvariant 𝕜 ν`: every linear isometry of `E` preserves the measure `ν` on `S`.
* `vecIntegral ν φ y`: the vector `∫ φ(⟪y, u⟫) u dν(u) ∈ E`.

## Main statements

* `exists_isometry_apply_eq`: the linear isometries act transitively on the unit sphere.
* `vecIntegral_eq_smul`: the symmetry lemma
  `∫ φ(⟪y, u⟫) u dν(u) = (∫ φ(⟪e, u⟫) ⟪e, u⟫ dν(u)) • y` for unit vectors `y` and `e`.
* `integral_norm_inner_eq`: `∫ |⟪u, v⟫| dν(u)` does not depend on the unit vector `v`.

## Tags

unit sphere, invariant measure, linear isometry
-/

open MeasureTheory Metric
open scoped InnerProductSpace

namespace ProjectionConstants.Euclidean

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Isometries acting on the unit sphere -/

/-- A linear isometry of `E`, restricted to the unit sphere. -/
def sphereMap (T : E ≃ₗᵢ[𝕜] E) (u : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨T u, by simp⟩

@[simp] lemma coe_sphereMap (T : E ≃ₗᵢ[𝕜] E) (u : sphere (0 : E) 1) :
    (sphereMap T u : E) = T u := rfl

/-- `sphereMap T` is continuous. -/
lemma continuous_sphereMap (T : E ≃ₗᵢ[𝕜] E) : Continuous (sphereMap T) :=
  (T.continuous.comp continuous_subtype_val).subtype_mk _

/-- `sphereMap T` as a homeomorphism of the unit sphere. -/
def sphereHomeomorph (T : E ≃ₗᵢ[𝕜] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 where
  toFun := sphereMap T
  invFun := sphereMap T.symm
  left_inv u := by ext; simp
  right_inv u := by ext; simp
  continuous_toFun := continuous_sphereMap T
  continuous_invFun := continuous_sphereMap T.symm

@[simp] lemma coe_sphereHomeomorph (T : E ≃ₗᵢ[𝕜] E) : ⇑(sphereHomeomorph T) = sphereMap T := rfl

/-- A unit vector is an orthonormal family on a singleton. -/
lemma orthonormal_singleton {ι : Type*} (i₀ : ι) {z : E} (hz : ‖z‖ = 1) :
    Orthonormal 𝕜 (({i₀} : Set ι).domRestrict fun _ ↦ z) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.mem_singleton_iff] at hi hj
  subst hi hj
  have h : ⟪z, z⟫_𝕜 = 1 := by rw [inner_self_eq_norm_sq_to_K, hz]; simp
  simpa [Set.domRestrict] using h

variable [FiniteDimensional 𝕜 E]

/-- **Transitivity.** The linear isometries act transitively on the unit sphere. -/
theorem exists_isometry_apply_eq {y y' : E} (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1) :
    ∃ T : E ≃ₗᵢ[𝕜] E, T y = y' := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd : 0 < Module.finrank 𝕜 E := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨y, hy0⟩
  set i₀ : Fin (Module.finrank 𝕜 E) := ⟨0, hd⟩
  have key : ∀ z : E, ‖z‖ = 1 →
      ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E, b i₀ = z := by
    intro z hz
    obtain ⟨b, hb⟩ := (orthonormal_singleton (𝕜 := 𝕜) i₀ hz)
      |>.exists_orthonormalBasis_extension_of_card_eq (𝕜 := 𝕜) (by simp)
    exact ⟨b, hb i₀ rfl⟩
  obtain ⟨b, hb⟩ := key y hy
  obtain ⟨b', hb'⟩ := key y' hy'
  refine ⟨b.repr.trans b'.repr.symm, ?_⟩
  rw [← hb, ← hb', LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
    OrthonormalBasis.repr_symm_single]

/-! ### Invariant measures -/

variable [ProperSpace E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (𝕜) in
/-- A measure on the unit sphere is **invariant** if every linear isometry preserves it. -/
def IsInvariant (ν : Measure (sphere (0 : E) 1)) : Prop :=
  ∀ T : E ≃ₗᵢ[𝕜] E, MeasurePreserving (sphereMap T) ν ν

variable {ν : Measure (sphere (0 : E) 1)}

omit [FiniteDimensional 𝕜 E] [ProperSpace E] [NormedSpace ℝ E] in
/-- Integrals against an invariant measure are invariant under the linear isometries:
`∫ F(T u) dν(u) = ∫ F(u) dν(u)`. -/
lemma IsInvariant.integral_comp (hν : IsInvariant 𝕜 ν) (T : E ≃ₗᵢ[𝕜] E) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : sphere (0 : E) 1 → G) :
    ∫ u, F (sphereMap T u) ∂ν = ∫ u, F u ∂ν :=
  (hν T).integral_comp (sphereHomeomorph T).measurableEmbedding F

omit [FiniteDimensional 𝕜 E] [NormedSpace ℝ E] in
/-- Continuous functions on the unit sphere are integrable for a finite measure. -/
lemma integrable_of_continuous [IsFiniteMeasure ν] {G : Type*} [NormedAddCommGroup G]
    {f : sphere (0 : E) 1 → G} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun u ↦ hC _ ⟨u, rfl⟩)

/-! ### The symmetry lemma -/

variable [IsFiniteMeasure ν]

variable (ν) in
/-- The vector `W(y) = ∫ φ(⟪y, u⟫) u dν(u)` in `E`. -/
noncomputable def vecIntegral (φ : 𝕜 → 𝕜) (y : E) : E :=
  ∫ u, φ ⟪y, (u : E)⟫_𝕜 • (u : E) ∂ν

omit [FiniteDimensional 𝕜 E] [NormedSpace ℝ E] in
/-- The integrand `u ↦ φ(⟪y, u⟫) u` of `vecIntegral` is integrable. -/
lemma integrable_vecIntegral {φ : 𝕜 → 𝕜} (hφ : Continuous φ) (y : E) :
    Integrable (fun u : sphere (0 : E) 1 ↦ φ ⟪y, (u : E)⟫_𝕜 • (u : E)) ν :=
  integrable_of_continuous (by fun_prop)

omit [IsFiniteMeasure ν] [FiniteDimensional 𝕜 E] in
/-- `W(Ty) = T W(y)` for a linear isometry `T`. -/
lemma vecIntegral_map (hν : IsInvariant 𝕜 ν) (φ : 𝕜 → 𝕜) (T : E ≃ₗᵢ[𝕜] E) (y : E) :
    vecIntegral ν φ (T y) = T (vecIntegral ν φ y) := by
  unfold vecIntegral
  rw [← hν.integral_comp T]
  simp only [coe_sphereMap, LinearIsometryEquiv.inner_map_map, ← T.map_smul]
  exact T.toLinearIsometry.integral_comp_comm _

omit [FiniteDimensional 𝕜 E] [IsFiniteMeasure ν] in
/-- `W(y)` is a multiple of `y`: it is fixed by every reflection that fixes `y`. -/
lemma vecIntegral_eq_inner_smul (hν : IsInvariant 𝕜 ν) (φ : 𝕜 → 𝕜) {y : E} (hy : ‖y‖ = 1) :
    vecIntegral ν φ y = ⟪y, vecIntegral ν φ y⟫_𝕜 • y := by
  set v := vecIntegral ν φ y
  set v' := v - ⟪y, v⟫_𝕜 • y with hv'
  have hyv' : ⟪v', y⟫_𝕜 = 0 := by
    rw [hv', inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hy, ← inner_conj_symm]
    simp
  set T := (𝕜 ∙ v')ᗮ.reflection
  have hTy : T y = y := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hyv')
  have hTv' : T v' = -v' := Submodule.reflection_orthogonalComplement_singleton_eq_neg v'
  have hTv : T v = v := by
    have := vecIntegral_map hν φ T y
    rw [hTy] at this
    exact this.symm
  have hdecomp : v = ⟪y, v⟫_𝕜 • y + v' := by rw [hv']; abel
  have h2 : v' = -v' := by
    have := hTv
    rw [hdecomp, map_add, map_smul, hTy, hTv'] at this
    -- `⟪y, v⟫ • y + -v' = ⟪y, v⟫ • y + v'`
    exact (add_left_cancel this).symm
  have h0 : v' = 0 := by
    have h2' : (2 : 𝕜) • v' = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel v'
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  rw [hv', sub_eq_zero] at h0
  exact h0

omit [IsFiniteMeasure ν] in
/-- The factor `⟪y, W(y)⟫` does not depend on the unit vector `y`. -/
lemma inner_vecIntegral_eq (hν : IsInvariant 𝕜 ν) (φ : 𝕜 → 𝕜) {y y' : E} (hy : ‖y‖ = 1)
    (hy' : ‖y'‖ = 1) : ⟪y, vecIntegral ν φ y⟫_𝕜 = ⟪y', vecIntegral ν φ y'⟫_𝕜 := by
  obtain ⟨T, rfl⟩ := exists_isometry_apply_eq (𝕜 := 𝕜) hy hy'
  rw [vecIntegral_map hν, LinearIsometryEquiv.inner_map_map]

omit [FiniteDimensional 𝕜 E] in
/-- `⟪y, W(y)⟫ = ∫ φ(⟪y, u⟫) ⟪y, u⟫ dν(u)`. -/
lemma inner_vecIntegral {φ : 𝕜 → 𝕜} (hφ : Continuous φ) (y : E) :
    ⟪y, vecIntegral ν φ y⟫_𝕜 = ∫ u, φ ⟪y, (u : E)⟫_𝕜 * ⟪y, (u : E)⟫_𝕜 ∂ν := by
  rw [vecIntegral, ← integral_inner (integrable_vecIntegral hφ y)]
  simp [inner_smul_right]

/-- **The symmetry lemma.** For `φ` continuous and unit vectors `y, e`,
`∫ φ(⟪y, u⟫) u dν(u) = (∫ φ(⟪e, u⟫) ⟪e, u⟫ dν(u)) • y`. -/
theorem vecIntegral_eq_smul (hν : IsInvariant 𝕜 ν) {φ : 𝕜 → 𝕜} (hφ : Continuous φ) {y e : E}
    (hy : ‖y‖ = 1) (he : ‖e‖ = 1) :
    vecIntegral ν φ y = (∫ u, φ ⟪e, (u : E)⟫_𝕜 * ⟪e, (u : E)⟫_𝕜 ∂ν) • y := by
  rw [← inner_vecIntegral hφ, inner_vecIntegral_eq hν φ he hy]
  exact vecIntegral_eq_inner_smul hν φ hy

omit [ProperSpace E] [NormedSpace ℝ E] [IsFiniteMeasure ν] in
/-- `∫ |⟪u, v⟫| dν(u)` is the same for all unit vectors `v`. -/
theorem integral_norm_inner_eq (hν : IsInvariant 𝕜 ν) {v v' : E} (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1) : ∫ u, ‖⟪(u : E), v⟫_𝕜‖ ∂ν = ∫ u, ‖⟪(u : E), v'⟫_𝕜‖ ∂ν := by
  obtain ⟨T, rfl⟩ := exists_isometry_apply_eq (𝕜 := 𝕜) hv hv'
  rw [← hν.integral_comp T (fun u ↦ ‖⟪(u : E), T v⟫_𝕜‖)]
  simp only [coe_sphereMap, LinearIsometryEquiv.inner_map_map]

end ProjectionConstants.Euclidean
