/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Euclidean.Sphere
import ProjectionConstants.ChalmersLewicki.Absolute

/-!
# The lower bound for the projection constant of Euclidean space

Let `S` be the unit sphere of an `n`-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`,
and let `ν` be an invariant finite measure on `S`. The map `x ↦ ⟪·, x⟫` embeds `E` isometrically
into `C(S, 𝕜)`. We show that every projection `P` of `C(S, 𝕜)` onto the image satisfies
`n ∫ |⟪u, e⟫| dν(u) ≤ ‖P‖ ν(S)` for a unit vector `e`. Hence `n ∫ |⟪u, e⟫| dν / ν(S) ≤ λ(E)`;
the matching upper bound is proved in `ProjectionConstants.Euclidean.UpperBound`. The test
functions are built from `clampSign` (`ProjectionConstants.ChalmersLewicki.LowerBound`).

## Main definitions

* `innerFn x`: the function `u ↦ ⟪u, x⟫` on the unit sphere.
* `sphereEmbedding`: the isometric embedding `x ↦ ⟪·, x⟫` of `E` into `C(S, 𝕜)`.
* `testFn ψ`: the test functions `u ↦ ψ(⟪·, u⟫)`, as a continuous map `S → C(S, 𝕜)`.
* `retraction hP`: for a projection `P` onto the image of `sphereEmbedding`, the map `R` with
  `sphereEmbedding ∘ R = P`.
* `sphereSuperspace 𝕜 E`: `C(S, 𝕜)` as a superspace of `E`.

## Main statements

* `le_norm_of_isProjectionOnto`: `n ∫ |⟪u, e⟫| dν(u) ≤ ‖P‖ ν(S)` for every projection `P` of
  `C(S, 𝕜)` onto the image of `sphereEmbedding`.
* `le_absProjConst`: `n ∫ |⟪u, e⟫| dν(u) / ν(S) ≤ λ(E)` for `ν ≠ 0`.

## Proof sketch

Write `P f = sphereEmbedding (R f)`. For `δ > 0` let `ψ(t) = t / max(|t|, δ)` and
`f_u = ψ(⟪·, u⟫) ∈ C(S, 𝕜)`, so that `‖f_u‖ ≤ 1` and `Re ⟪u, R f_u⟫ ≤ ‖P‖`. Averaging over `u`
and expanding in an orthonormal basis `(bᵢ)`,
`∫ ⟪u, R f_u⟫ dν(u) = ∑ᵢ ⟪bᵢ, R hᵢ⟫` with the Bochner integrals
`hᵢ = ∫ ⟪u, bᵢ⟫ f_u dν(u) ∈ C(S, 𝕜)`. By the symmetry lemma (`vecIntegral_eq_smul`),
`hᵢ = A · sphereEmbedding bᵢ` with `A = ∫ |⟪e, u⟫|² / max(|⟪e, u⟫|, δ) dν(u)`. So the average
is `n A`, and `A ≥ ∫ |⟪e, u⟫| dν - δ ν(S)`. Letting `δ → 0` gives the bound.

## Tags

projection constant, Euclidean space, averaging, Bochner integral
-/

open MeasureTheory Metric
open scoped InnerProductSpace ComplexConjugate

namespace ProjectionConstants.Euclidean

section Generic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [ProperSpace E]

/-! ### The embedding into `C(S, 𝕜)` -/

/-- The function `u ↦ ⟪u, x⟫` on the unit sphere. -/
def innerFn (x : E) : C(sphere (0 : E) 1, 𝕜) := ⟨fun u ↦ ⟪(u : E), x⟫_𝕜, by fun_prop⟩

omit [ProperSpace E] in
@[simp] lemma innerFn_apply (x : E) (u : sphere (0 : E) 1) :
    innerFn (𝕜 := 𝕜) x u = ⟪(u : E), x⟫_𝕜 :=
  rfl

/-- The isometric embedding `x ↦ ⟪·, x⟫` of `E` into `C(S, 𝕜)`. -/
noncomputable def sphereEmbedding : E →ₗᵢ[𝕜] C(sphere (0 : E) 1, 𝕜) where
  toFun := innerFn
  map_add' x y := by ext u; simp [inner_add_right]
  map_smul' c x := by ext u; simp [inner_smul_right]
  norm_map' x := by
    apply le_antisymm
    · refine (ContinuousMap.norm_le _ (norm_nonneg x)).2 fun u ↦ ?_
      calc ‖⟪(u : E), x⟫_𝕜‖ ≤ ‖(u : E)‖ * ‖x‖ := norm_inner_le_norm _ _
        _ = ‖x‖ := by rw [norm_eq_of_mem_sphere u, one_mul]
    · rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let u : sphere (0 : E) 1 := ⟨(‖x‖⁻¹ : 𝕜) • x, by simp [norm_smul, hnx.ne']⟩
        have h := ContinuousMap.norm_coe_le_norm (innerFn (𝕜 := 𝕜) x) u
        have hu : ⟪(u : E), x⟫_𝕜 = (‖x‖ : 𝕜) := by
          simp only [u, inner_smul_left, map_inv₀, RCLike.conj_ofReal,
            inner_self_eq_norm_sq_to_K]
          field_simp
        rwa [innerFn_apply, hu, RCLike.norm_ofReal, abs_of_pos hnx] at h

@[simp] lemma sphereEmbedding_apply (x : E) (u : sphere (0 : E) 1) :
    sphereEmbedding (𝕜 := 𝕜) x u = ⟪(u : E), x⟫_𝕜 := rfl

/-- The test functions `u ↦ (y ↦ ψ(⟪y, u⟫))`, as a continuous map `S → C(S, 𝕜)`. -/
noncomputable def testFn (ψ : C(𝕜, 𝕜)) : C(sphere (0 : E) 1, C(sphere (0 : E) 1, 𝕜)) :=
  ContinuousMap.curry
    ⟨fun p : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ ψ ⟪(p.2 : E), (p.1 : E)⟫_𝕜, by fun_prop⟩

omit [ProperSpace E] in
@[simp] lemma testFn_apply (ψ : C(𝕜, 𝕜)) (u y : sphere (0 : E) 1) :
    testFn ψ u y = ψ ⟪(y : E), (u : E)⟫_𝕜 := rfl

/-! ### Projections onto the image of `sphereEmbedding` -/

variable {P : C(sphere (0 : E) 1, 𝕜) →L[𝕜] C(sphere (0 : E) 1, 𝕜)}

/-- For a projection `P` onto the image of `sphereEmbedding`, the map `R` with
`sphereEmbedding ∘ R = P`. -/
noncomputable def retraction
    (hP : IsProjectionOnto (LinearMap.range (sphereEmbedding (𝕜 := 𝕜) (E := E)).toLinearMap) P) :
    C(sphere (0 : E) 1, 𝕜) →L[𝕜] E :=
  ((sphereEmbedding (𝕜 := 𝕜) (E := E)).equivRange.symm.toContinuousLinearEquiv :
      LinearMap.range (sphereEmbedding (𝕜 := 𝕜) (E := E)).toLinearMap →L[𝕜] E).comp
    (P.codRestrict _ hP.mem)

variable (hP : IsProjectionOnto (LinearMap.range (sphereEmbedding (𝕜 := 𝕜) (E := E)).toLinearMap) P)
include hP

/-- `sphereEmbedding (R f) = P f`. -/
lemma sphereEmbedding_retraction (f : C(sphere (0 : E) 1, 𝕜)) :
    sphereEmbedding (retraction hP f) = P f := by
  have h := (sphereEmbedding (𝕜 := 𝕜) (E := E)).equivRange.apply_symm_apply ⟨P f, hP.mem f⟩
  exact congrArg Subtype.val h

/-- `R` is a left inverse of `sphereEmbedding`. -/
lemma retraction_sphereEmbedding (x : E) : retraction hP (sphereEmbedding x) = x := by
  apply (sphereEmbedding (𝕜 := 𝕜) (E := E)).injective
  rw [sphereEmbedding_retraction hP]
  exact hP.map_id (sphereEmbedding x) ⟨x, rfl⟩

/-- `‖R f‖ ≤ ‖P‖ ‖f‖`. -/
lemma norm_retraction_le (f : C(sphere (0 : E) 1, 𝕜)) : ‖retraction hP f‖ ≤ ‖P‖ * ‖f‖ := by
  rw [← (sphereEmbedding (𝕜 := 𝕜) (E := E)).norm_map, sphereEmbedding_retraction hP]
  exact P.le_opNorm f

omit hP

/-! ### The averaging argument -/

variable [FiniteDimensional 𝕜 E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure (sphere (0 : E) 1)} [IsFiniteMeasure ν]

include hP in
/-- The averaging argument for a fixed `δ > 0`. -/
private lemma le_norm_aux (hν : IsInvariant 𝕜 ν) {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    (Module.finrank 𝕜 E : ℝ) * (∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν - δ * ν.real Set.univ) ≤
      ‖P‖ * ν.real Set.univ := by
  set ψ : C(𝕜, 𝕜) := ⟨clampSign δ, continuous_clampSign hδ⟩
  set F := testFn (E := E) ψ
  set R := retraction hP
  have hR : ∀ x, R (sphereEmbedding x) = x := fun x ↦ retraction_sphereEmbedding hP x
  set b := stdOrthonormalBasis 𝕜 E
  -- the pointwise bound
  have hF : ∀ u, ‖F u‖ ≤ 1 := fun u ↦
    (ContinuousMap.norm_le _ zero_le_one).2 fun y ↦ norm_clampSign_le hδ _
  have hpt : ∀ u : sphere (0 : E) 1, RCLike.re ⟪(u : E), R (F u)⟫_𝕜 ≤ ‖P‖ := by
    intro u
    calc RCLike.re ⟪(u : E), R (F u)⟫_𝕜 ≤ ‖⟪(u : E), R (F u)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖(u : E)‖ * ‖R (F u)‖ := norm_inner_le_norm _ _
      _ = ‖R (F u)‖ := by rw [norm_eq_of_mem_sphere u, one_mul]
      _ ≤ ‖P‖ * ‖F u‖ := norm_retraction_le hP _
      _ ≤ ‖P‖ * 1 := by gcongr; exact hF u
      _ = ‖P‖ := mul_one _
  -- integrability
  have hcont : Continuous fun u : sphere (0 : E) 1 ↦ ⟪(u : E), R (F u)⟫_𝕜 := by
    have : Continuous fun u : sphere (0 : E) 1 ↦ R (F u) := R.continuous.comp F.continuous
    fun_prop
  have hint := integrable_of_continuous (ν := ν) hcont
  -- the Bochner integrals `hᵢ`
  set G : Fin (Module.finrank 𝕜 E) → sphere (0 : E) 1 → C(sphere (0 : E) 1, 𝕜) :=
    fun i u ↦ ⟪(u : E), b i⟫_𝕜 • F u
  have hGc : ∀ i, Continuous (G i) := fun i ↦ by
    have : Continuous fun u : sphere (0 : E) 1 ↦ ⟪(u : E), b i⟫_𝕜 := by fun_prop
    exact this.smul F.continuous
  have hGi : ∀ i, Integrable (G i) ν := fun i ↦ integrable_of_continuous (hGc i)
  -- the constant `A`
  set A : ℝ := ∫ u, ‖⟪e, (u : E)⟫_𝕜‖ ^ 2 / max ‖⟪e, (u : E)⟫_𝕜‖ δ ∂ν
  have hφ : Continuous fun t : 𝕜 ↦ conj (clampSign δ t) :=
    (RCLike.continuous_conj).comp (continuous_clampSign hδ)
  have hW : ∀ y : sphere (0 : E) 1,
      vecIntegral ν (fun t : 𝕜 ↦ conj (clampSign δ t)) (y : E) = (A : 𝕜) • (y : E) := by
    intro y
    rw [vecIntegral_eq_smul hν hφ (norm_eq_of_mem_sphere y) he]
    congr 1
    simp_rw [conj_clampSign_mul]
    exact integral_ofReal
  have hG : ∀ i, ∫ u, G i u ∂ν = (A : 𝕜) • sphereEmbedding (b i) := by
    intro i
    ext y
    rw [← ContinuousMap.evalCLM_apply 𝕜 y, ← ContinuousLinearMap.integral_comp_comm _ (hGi i)]
    simp only [ContinuousMap.evalCLM_apply, G, ContinuousMap.smul_apply, smul_eq_mul,
      sphereEmbedding_apply]
    have h1 := congrArg (fun v ↦ conj ⟪b i, v⟫_𝕜) (hW y)
    simp only [vecIntegral] at h1
    rw [← integral_inner (integrable_vecIntegral hφ _), ← integral_conj] at h1
    simp only [inner_smul_right, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      inner_conj_symm, RCLike.conj_ofReal] at h1
    rw [← h1]
    congr 1
    ext x
    rw [mul_comm]
    rfl
  -- the average of `⟪u, R f_u⟫`
  have havg : ∫ u, ⟪(u : E), R (F u)⟫_𝕜 ∂ν = ((Module.finrank 𝕜 E * A : ℝ) : 𝕜) := by
    have e1 : ∀ u : sphere (0 : E) 1,
        ⟪(u : E), R (F u)⟫_𝕜 = ∑ i, ((innerSL 𝕜 (b i)).comp R) (G i u) := by
      intro u
      rw [← b.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [G]
    simp_rw [e1]
    rw [integral_finsetSum _ fun i _ ↦ ((innerSL 𝕜 (b i)).comp R).integrable_comp (hGi i)]
    simp_rw [ContinuousLinearMap.integral_comp_comm _ (hGi _), hG]
    simp only [ContinuousLinearMap.comp_apply, map_smul, hR, innerSL_apply_apply,
      b.inner_eq_ite, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- the bound
  have hre : ∫ u, RCLike.re ⟪(u : E), R (F u)⟫_𝕜 ∂ν = Module.finrank 𝕜 E * A := by
    rw [integral_re hint, havg, RCLike.ofReal_re]
  have hle : ∫ u, RCLike.re ⟪(u : E), R (F u)⟫_𝕜 ∂ν ≤ ‖P‖ * ν.real Set.univ := by
    calc ∫ u, RCLike.re ⟪(u : E), R (F u)⟫_𝕜 ∂ν ≤ ∫ _u, ‖P‖ ∂ν :=
          integral_mono hint.re (integrable_const _) hpt
      _ = ‖P‖ * ν.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hA : ∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν - δ * ν.real Set.univ ≤ A := by
    have h1 : Integrable (fun u : sphere (0 : E) 1 ↦ ‖⟪(u : E), e⟫_𝕜‖) ν :=
      integrable_of_continuous (by fun_prop)
    have h2 : Integrable (fun u : sphere (0 : E) 1 ↦
        ‖⟪e, (u : E)⟫_𝕜‖ ^ 2 / max ‖⟪e, (u : E)⟫_𝕜‖ δ) ν := by
      refine integrable_of_continuous (Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_)
      exact (lt_of_lt_of_le hδ (le_max_right _ _)).ne'
    calc ∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν - δ * ν.real Set.univ
        = ∫ u, (‖⟪(u : E), e⟫_𝕜‖ - δ) ∂ν := by
          rw [integral_sub h1 (integrable_const δ), integral_const, smul_eq_mul, mul_comm]
      _ ≤ A := by
          refine integral_mono (h1.sub (integrable_const δ)) h2 fun u ↦ ?_
          simp only
          rw [norm_inner_symm]
          exact sub_le_sq_div_max hδ (norm_nonneg _)
  have hn : (0 : ℝ) ≤ Module.finrank 𝕜 E := Nat.cast_nonneg _
  calc (Module.finrank 𝕜 E : ℝ) * (∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν - δ * ν.real Set.univ)
      ≤ Module.finrank 𝕜 E * A := mul_le_mul_of_nonneg_left hA hn
    _ ≤ ‖P‖ * ν.real Set.univ := hre ▸ hle

include hP in
/-- **The lower bound.** Every projection `P` of `C(S, 𝕜)` onto the image of `E` satisfies
`n ∫ |⟪u, e⟫| dν(u) ≤ ‖P‖ ν(S)`. -/
theorem le_norm_of_isProjectionOnto (hν : IsInvariant 𝕜 ν) {e : E} (he : ‖e‖ = 1) :
    (Module.finrank 𝕜 E : ℝ) * ∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν ≤ ‖P‖ * ν.real Set.univ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set n : ℝ := (Module.finrank 𝕜 E : ℝ)
  set V := ν.real Set.univ
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hV : 0 ≤ V := measureReal_nonneg
  set δ := ε / (n * V + 1) with hδ_def
  have hδ : 0 < δ := div_pos hε (by positivity)
  have h := le_norm_aux hP hν he hδ
  have hδV : n * (δ * V) ≤ ε := by
    have h1 : n * (δ * V) = ε * (n * V / (n * V + 1)) := by
      rw [hδ_def]
      field_simp
    have h2 : n * V / (n * V + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h1]
    nlinarith
  nlinarith

end Generic

section Absolute

variable {𝕜 : Type} [RCLike 𝕜] {E : Type} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [ProperSpace E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure (sphere (0 : E) 1)} [IsFiniteMeasure ν]

variable (𝕜 E) in
/-- `C(S, 𝕜)`, a superspace of `E` via `sphereEmbedding`. -/
noncomputable def sphereSuperspace : Superspace 𝕜 E := ⟨C(sphere (0 : E) 1, 𝕜), sphereEmbedding⟩

/-- **Lower bound for `λ(E)`.** For an invariant finite measure `ν ≠ 0` on the unit sphere and a
unit vector `e`, `n ∫ |⟪u, e⟫| dν(u) / ν(S) ≤ λ(E)`. -/
theorem le_absProjConst (hν : IsInvariant 𝕜 ν) (hν0 : ν ≠ 0) {e : E} (he : ‖e‖ = 1) :
    (Module.finrank 𝕜 E : ℝ) * (∫ u, ‖⟪(u : E), e⟫_𝕜‖ ∂ν) / ν.real Set.univ ≤
      absProjConst 𝕜 E := by
  have hV : 0 < ν.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν0) (measure_ne_top _ _)
  refine le_trans ?_ (sphereSuperspace 𝕜 E).relProjConst_le_absProjConst
  refine le_relProjConst _ fun P hP ↦ ?_
  rw [div_le_iff₀ hV]
  exact le_norm_of_isProjectionOnto hP hν he

end Absolute

end ProjectionConstants.Euclidean
