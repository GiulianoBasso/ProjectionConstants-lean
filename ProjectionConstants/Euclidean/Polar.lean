/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Euclidean.Sphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Polar coordinates and the surface measure of the sphere

Let `E` be a finite-dimensional real normed space of dimension `d` with an additive Haar
measure `μ`, and let `σ = μ.toSphere` be the corresponding surface measure on the unit sphere `S`.
We prove the integration formula in polar coordinates, show that `σ` is invariant under the
linear isometries of `E` when `E` is an inner product space, and express the mean of `|⟪u, e⟫|`
over `S` by Gaussian integrals. This is used in `ProjectionConstants.Euclidean.Values` to
evaluate the spherical-mean formula of `ProjectionConstants.Euclidean.Formula`.

## Main statements

* `integral_polar`: **polar coordinates.** If `F (r u) = G(u) h(r)` for `u ∈ S` and `r > 0`,
  then `∫ F dμ = (∫ G dσ) (∫₀^∞ r^{d-1} h(r) dr)`.
* `integral_pow_mul_exp_neg_sq`: `∫₀^∞ rᵏ e^{-r²} dr = Γ((k+1)/2) / 2`.
* `measure_preimage_isometry`: the linear isometries of `E` preserve `μ`, since `|det| = 1`.
* `isInvariant_toSphere`: if `E` is an inner product space over `𝕜`, then `σ` is invariant
  under all linear isometries of `E`.
* `mean_eq_gaussian`: for every `e ∈ E`, the mean of `|⟪u, e⟫|` over `S` is
  `(∫ |⟪x, e⟫| e^{-‖x‖²} dμ / ∫ e^{-‖x‖²} dμ) Γ(d/2) / Γ((d+1)/2)`.

## Tags

polar coordinates, surface measure, Gaussian integral
-/

open MeasureTheory Metric Set Real
open scoped InnerProductSpace Pointwise

namespace ProjectionConstants.Euclidean

/-! ### Polar coordinates -/

section Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Polar coordinates.** If `F (r • u) = G u * h r` for all unit vectors `u` and `r > 0`, then
`∫ F dμ = (∫ G dσ) (∫₀^∞ r^{d-1} h(r) dr)`, where `σ = μ.toSphere` and `d = dim E`. -/
theorem integral_polar (F : E → ℝ) (G : sphere (0 : E) 1 → ℝ) (h : ℝ → ℝ)
    (hF : ∀ (u : sphere (0 : E) 1) (r : ℝ), 0 < r → F (r • (u : E)) = G u * h r) :
    ∫ x, F x ∂μ = (∫ u, G u ∂μ.toSphere) *
      ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) * h r := by
  calc ∫ x, F x ∂μ = ∫ x : ({(0 : E)}ᶜ : Set E), F x ∂(μ.comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl F, restrict_compl_singleton]
    _ = ∫ p, F ((homeomorphUnitSphereProd E).symm p)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)]
        simp
    _ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), G p.1 * h p.2
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        congr 1
        ext ⟨u, r⟩
        rw [homeomorphUnitSphereProd_symm_apply_coe]
        exact hF u r r.2
    _ = (∫ u, G u ∂μ.toSphere) *
          ∫ r : Ioi (0 : ℝ), h r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) :=
        integral_prod_mul (fun u ↦ G u) (fun r : Ioi (0 : ℝ) ↦ h r)
    _ = _ := by
        congr 1
        simp only [Measure.volumeIoiPow, ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul, integral_subtype_comap measurableSet_Ioi
          (fun a ↦ Real.toNNReal (a ^ (Module.finrank ℝ E - 1)) • h a),
          setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
        · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _), smul_eq_mul]
        · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end Polar

/-- `∫₀^∞ rᵏ e^{-r²} dr = Γ((k+1)/2) / 2`. -/
lemma integral_pow_mul_exp_neg_sq (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ k * exp (-r ^ 2) = Gamma ((k + 1) / 2) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := k) two_pos
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  rw [show Gamma ((k + 1) / 2) / 2 = 1 / 2 * Gamma ((k + 1) / 2) by ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
  rw [Real.rpow_natCast, Real.rpow_two]

/-! ### Invariance of the surface measure -/

section Invariance

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cone `(0, 1) · A` over a set `A` of the sphere is compatible with linear isometries. -/
lemma cone_preimage (T : E ≃ₗᵢ[𝕜] E) (A : Set (sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap T ⁻¹' A) : Set E) =
      T ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' A)) := by
  ext x
  simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨sphereMap T u, hu, rfl⟩, ?_⟩
    rw [coe_sphereMap, map_real_smul T T.continuous]
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    have hv' : sphereMap T (sphereMap T.symm v) = v := Subtype.ext (by simp [coe_sphereMap])
    refine ⟨r, hr, _, ⟨sphereMap T.symm v, by rw [hv']; exact hv, rfl⟩, ?_⟩
    rw [coe_sphereMap, ← map_real_smul T.symm T.symm.continuous, hx,
      LinearIsometryEquiv.symm_apply_apply]

/-- A linear isometry preserves every additive Haar measure: its determinant has absolute
value `1`, since it maps the unit ball onto itself. -/
lemma measure_preimage_isometry (T : E ≃ₗᵢ[𝕜] E) (s : Set E) : μ (T ⁻¹' s) = μ s := by
  let L : E ≃L[ℝ] E := T.toContinuousLinearEquiv.restrictScalars ℝ
  have hL : ∀ t, μ (L ⁻¹' t) = ENNReal.ofReal |LinearMap.det (L.symm : E →ₗ[ℝ] E)| * μ t :=
    Measure.addHaar_preimage_continuousLinearEquiv μ L
  have hball : L ⁻¹' ball 0 1 = ball 0 1 := by
    ext x
    simp [L]
  have hc : ENNReal.ofReal |LinearMap.det (L.symm : E →ₗ[ℝ] E)| = 1 := by
    have h := hL (ball 0 1)
    rw [hball] at h
    have hb0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
    have hbt : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
    exact (ENNReal.mul_eq_right hb0 hbt).mp h.symm
  change μ (L ⁻¹' s) = μ s
  rw [hL, hc, one_mul]

/-- **The surface measure is invariant** under all linear isometries. -/
theorem isInvariant_toSphere : IsInvariant 𝕜 μ.toSphere := by
  intro T
  refine ⟨(continuous_sphereMap T).measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply (continuous_sphereMap T).measurable hA,
    μ.toSphere_apply' ((continuous_sphereMap T).measurable hA), μ.toSphere_apply' hA,
    cone_preimage, measure_preimage_isometry]

end Invariance

/-! ### The mean of `|⟪u, e⟫|` via Gaussian integrals -/

section Mean

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The mean of `|⟪u, e⟫|` over the sphere**, via Gaussian integrals: with `d = dim_ℝ E`,
`∫ |⟪u, e⟫| dσ / σ(S) = (∫ |⟪x, e⟫| e^{-‖x‖²} dμ / ∫ e^{-‖x‖²} dμ) Γ(d/2) / Γ((d+1)/2)`. -/
theorem mean_eq_gaussian {e : E} :
    (∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂μ.toSphere) / μ.toSphere.real univ =
      (∫ x, ‖⟪x, e⟫_𝕜‖ * exp (-‖x‖ ^ 2) ∂μ) / (∫ x, exp (-‖x‖ ^ 2) ∂μ) *
        (Gamma ((Module.finrank ℝ E : ℝ) / 2) / Gamma (((Module.finrank ℝ E : ℝ) + 1) / 2)) := by
  have hd0 : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hdc : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 = Module.finrank ℝ E := by
    rw [Nat.cast_sub hd0, Nat.cast_one, sub_add_cancel]
  have h0 := integral_polar μ (fun x ↦ exp (-‖x‖ ^ 2)) (fun _ ↦ 1) (fun r ↦ exp (-r ^ 2))
    (by intro u r hr; simp [norm_smul, abs_of_pos hr])
  have h1 := integral_polar μ (fun x ↦ ‖⟪x, e⟫_𝕜‖ * exp (-‖x‖ ^ 2))
    (fun u ↦ ‖⟪(u : E), e⟫_𝕜‖) (fun r ↦ r * exp (-r ^ 2)) (by
      intro u r hr
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left, norm_mul, RCLike.conj_ofReal,
        RCLike.norm_ofReal, abs_of_pos hr, norm_smul, RCLike.norm_ofReal, abs_of_pos hr,
        norm_eq_of_mem_sphere u, mul_one]
      ring)
  have hpow : ∀ r : ℝ, r ^ (Module.finrank ℝ E - 1) * (r * exp (-r ^ 2)) =
      r ^ Module.finrank ℝ E * exp (-r ^ 2) := by
    intro r
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hd0]
  simp only [hpow, integral_pow_mul_exp_neg_sq, integral_const, smul_eq_mul, mul_one] at h0 h1
  rw [hdc] at h0
  rw [h0, h1]
  have hg0 : 0 < Gamma ((Module.finrank ℝ E : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hg1 : 0 < Gamma (((Module.finrank ℝ E : ℝ) + 1) / 2) := Gamma_pos_of_pos (by positivity)
  have hV : 0 < μ.toSphere.real univ := by
    rw [Measure.toSphere_real_apply_univ, measureReal_def]
    exact mul_pos (by exact_mod_cast hd0)
      (ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne)
  field_simp

end Mean

end ProjectionConstants.Euclidean
