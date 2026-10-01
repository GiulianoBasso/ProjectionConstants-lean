/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Euclidean.Sphere
import ProjectionConstants.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The upper bound for the projection constant of Euclidean space

Let `E = 𝕜ⁿ` with the Euclidean norm, let `ν` be an invariant finite measure on its unit sphere
`S` and `c = ∫ |⟪u, e⟫| dν(u) / ν(S)` for a unit vector `e`. We show `λ(E) ≤ n c`; the matching
lower bound is proved in `ProjectionConstants.Euclidean.LowerBound`. The idea is to replace `ν`
by a finitely supported measure, to symmetrize it over the signed cyclic shifts of `𝕜ⁿ` so that
its support becomes a weighted tight frame, and to build a projection onto `E` from this frame.

## Main definitions

* `boolSign b`: the sign `±1` encoded by a boolean `b`.
* `signShift s ε`: the signed cyclic shift `(g x)ᵢ = εᵢ x_{i+s}` of `𝕜ⁿ`, a linear isometry.

## Main statements

* `exists_discrete`: `ν / ν(S)` is approximated, uniformly on `1`-Lipschitz functions vanishing
  at `0`, by a probability measure with finite support in `S` (via simple functions).
* `sum_signShift`: the `n 2ⁿ` signed cyclic shifts `g` satisfy `∑_g ⟪g z, x⟫ g z = 2ⁿ ‖z‖² x`.
* `relProjConst_le_of_frame`: a bound for the relative projection constant from a weighted
  tight frame, via Hahn–Banach.
* `relProjConst_le_mean`: `λ(E, X) ≤ n c` for every normed space `X ⊇ E`.
* `absProjConst_le`: `λ(E) ≤ n c`.

## Proof sketch

Discretize `ν` (`exists_discrete`) and symmetrize the discrete measure over the signed cyclic
shifts (`sum_signShift`). This gives points `yₖ ∈ S` and weights `wₖ ≥ 0` with
`∑ₖ wₖ ⟪yₖ, x⟫ yₖ = x / n` exactly, and `∑ₖ wₖ |⟪yₖ, v⟫| ≤ c + δ` for every unit vector `v`.
For any superspace `X`, extend the functionals `⟪yₖ, ·⟫` to functionals `gₖ` on `X` with norm
one (Hahn–Banach) and put `P x = n ∑ₖ wₖ gₖ(x) yₖ`. This is a projection onto `E` with
`‖P‖ ≤ n (c + δ)` (`relProjConst_le_of_frame`).

## Tags

projection constant, Euclidean space, tight frame, Hahn–Banach theorem
-/

open MeasureTheory Metric
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ProjectionConstants.Euclidean

/-! ### Discretization -/

section Discrete

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- **Discretization.** A nonzero finite measure `ν` on the unit sphere is approximated by a
finitely supported probability measure on the sphere: for every `δ > 0` there are finitely many
unit vectors `z` with weights `w z ≥ 0`, `∑ w z = 1`, such that
`∑ w z g(z) ≤ ∫ g dν / ν(S) + δ` for all `1`-Lipschitz `g` with `g 0 = 0`. -/
theorem exists_discrete (ν : Measure (sphere (0 : E) 1)) [IsFiniteMeasure ν] (hν0 : ν ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset E) (w : E → ℝ), (∀ z ∈ s, ‖z‖ = 1) ∧ (∀ z ∈ s, 0 ≤ w z) ∧
      ∑ z ∈ s, w z = 1 ∧ ∀ g : E → ℝ, LipschitzWith 1 g → g 0 = 0 →
        ∑ z ∈ s, w z * g z ≤ (∫ u, g u ∂ν) / ν.real Set.univ + δ := by
  classical
  set V := ν.real Set.univ with hV_def
  have hV : 0 < V := by
    rw [hV_def, measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν0) (measure_ne_top _ _)
  -- a point of the sphere
  obtain ⟨y₀⟩ : Nonempty (sphere (0 : E) 1) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hν0 (Measure.eq_zero_of_isEmpty ν)
  set f : sphere (0 : E) 1 → E := Subtype.val with hf_def
  have hf : Measurable f := measurable_subtype_coe
  have h₀ : (y₀ : E) ∈ sphere (0 : E) 1 := y₀.2
  -- approximation by simple functions with values in the sphere
  have hi : HasFiniteIntegral (fun x ↦ f x - y₀) ν := by
    refine HasFiniteIntegral.of_bounded (C := 2) (Filter.Eventually.of_forall fun x ↦ ?_)
    calc ‖f x - (y₀ : E)‖ ≤ ‖f x‖ + ‖(y₀ : E)‖ := norm_sub_le _ _
      _ = 2 := by rw [hf_def, norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere y₀]; norm_num
  have hT := SimpleFunc.tendsto_approxOn_L1_enorm hf h₀ (μ := ν)
    (Filter.Eventually.of_forall fun x ↦ subset_closure x.2) hi
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ * V) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hpos)).exists
  set φ := SimpleFunc.approxOn f hf (sphere (0 : E) 1) y₀ h₀ m with hφ_def
  have hφS : ∀ x, φ x ∈ sphere (0 : E) 1 := fun x ↦ SimpleFunc.approxOn_mem hf h₀ m x
  have hφi : Integrable φ ν := SimpleFunc.integrable_of_isFiniteMeasure φ
  refine ⟨φ.range, fun z ↦ ν.real (φ ⁻¹' {z}) / V, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := φ.mem_range.mp hz
    exact mem_sphere_zero_iff_norm.mp (hφS x)
  · intro z _
    exact div_nonneg measureReal_nonneg hV.le
  · rw [← Finset.sum_div, div_eq_one_iff_eq hV.ne']
    have h := φ.sum_range_measure_preimage_singleton ν
    rw [hV_def, measureReal_def, ← h, ENNReal.toReal_sum fun z _ ↦ measure_ne_top _ _]
    rfl
  · intro g hg hg0
    -- the discrete sum is the integral of `g ∘ φ`
    have h1 : ∑ z ∈ φ.range, ν.real (φ ⁻¹' {z}) / V * g z = (∫ x, g (φ x) ∂ν) / V := by
      have e : (∫ x, g (φ x) ∂ν) = (φ.map g).integral ν := by
        exact ((φ.map g).integral_eq_integral ((φ.map g).integrable_of_isFiniteMeasure)).symm
      rw [e, SimpleFunc.map_integral φ g hφi hg0, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [smul_eq_mul]
      ring
    rw [h1]
    -- `|∫ g ∘ φ - ∫ g| ≤ ∫ ‖φ - id‖ < δ V`
    have hgc : Continuous g := hg.continuous
    have hint1 : Integrable (fun x ↦ g (φ x)) ν :=
      (φ.map g).integrable_of_isFiniteMeasure
    have hint2 : Integrable (fun x ↦ g (f x)) ν :=
      integrable_of_continuous (hgc.comp continuous_subtype_val)
    have hint3 : Integrable (fun x ↦ ‖φ x - f x‖) ν :=
      (hφi.sub (integrable_of_continuous continuous_subtype_val)).norm
    have hdiff : ∫ x, g (φ x) ∂ν ≤ ∫ u, g u ∂ν + ∫ x, ‖φ x - f x‖ ∂ν := by
      rw [← integral_add hint2 hint3]
      refine integral_mono hint1 (hint2.add hint3) fun x ↦ ?_
      have := hg.dist_le_mul (φ x) (f x)
      simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] at this
      simp only
      linarith [le_abs_self (g (φ x) - g (f x))]
    have hsmall : ∫ x, ‖φ x - f x‖ ∂ν < δ * V := by
      rw [integral_norm_eq_lintegral_enorm (f := fun x ↦ φ x - f x)
        (hφi.sub (integrable_of_continuous continuous_subtype_val)).aestronglyMeasurable]
      rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (ne_top_of_lt hm)]
      exact hm
    rw [div_le_iff₀ hV, add_mul, div_mul_cancel₀ _ hV.ne']
    linarith

end Discrete

/-! ### Signed cyclic shifts -/

section Shift

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The sign `±1` encoded by a boolean. -/
def boolSign (b : Bool) : 𝕜 := if b then -1 else 1

/-- `(±1)² = 1`. -/
lemma boolSign_mul_self (b : Bool) : (boolSign b : 𝕜) * boolSign b = 1 := by
  cases b <;> simp [boolSign]

/-- The signs `±1` are real. -/
lemma conj_boolSign (b : Bool) : conj (boolSign b : 𝕜) = boolSign b := by
  cases b <;> simp [boolSign]

/-- Negating the boolean negates the sign. -/
lemma boolSign_not (b : Bool) : (boolSign (!b) : 𝕜) = -boolSign b := by
  cases b <;> simp [boolSign]

/-- `∑_ε εᵢ εⱼ = 2ⁿ δᵢⱼ`, the sum over all sign vectors `ε ∈ {±1}ⁿ`. -/
lemma sum_boolSign_mul_boolSign (i j : Fin n) :
    ∑ ε : Fin n → Bool, (boolSign (ε i) : 𝕜) * boolSign (ε j) = if i = j then 2 ^ n else 0 := by
  split_ifs with h
  · subst h
    simp [boolSign_mul_self]
  · -- flipping the sign at `j` changes the sign of every term
    set τ : (Fin n → Bool) → (Fin n → Bool) := fun ε ↦ Function.update ε j (!ε j)
    have hτ : Function.Involutive τ := fun ε ↦ by
      ext k
      by_cases hk : k = j
      · subst hk
        simp [τ]
      · simp [τ, Function.update_of_ne hk]
    have h1 := Equiv.sum_comp (hτ.toPerm τ) (fun ε ↦ (boolSign (ε i) : 𝕜) * boolSign (ε j))
    have h2 : ∀ ε, (boolSign (τ ε i) : 𝕜) * boolSign (τ ε j) =
        -((boolSign (ε i) : 𝕜) * boolSign (ε j)) := by
      intro ε
      simp [τ, Function.update_of_ne h, boolSign_not]
    simp only [Function.Involutive.coe_toPerm, h2, Finset.sum_neg_distrib] at h1
    linear_combination (-1 / 2 : 𝕜) * h1

/-- `‖x‖² = ∑ᵢ |xᵢ|²` in `𝕜ⁿ`. -/
lemma norm_sq_eq_sum (x : EuclideanSpace 𝕜 (Fin n)) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]

variable [NeZero n]

/-- The **signed cyclic shift** `(g x)ᵢ = εᵢ x_{i+s}` of `𝕜ⁿ`, a linear isometry. -/
noncomputable def signShift (s : Fin n) (ε : Fin n → Bool) :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.addRight s).symm).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun i ↦
      if ε i then LinearIsometryEquiv.neg 𝕜 else LinearIsometryEquiv.refl 𝕜 𝕜)

/-- `(signShift s ε x)ᵢ = εᵢ x_{i+s}`. -/
lemma signShift_apply (s : Fin n) (ε : Fin n → Bool) (x : EuclideanSpace 𝕜 (Fin n))
    (i : Fin n) : signShift s ε x i = boolSign (ε i) * x (i + s) := by
  simp only [signShift, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply, LinearIsometryEquiv.piLpCongrLeft_apply]
  cases ε i <;> simp [boolSign, Equiv.piCongrLeft']

/-- **The signed cyclic shifts form a tight frame**:
`∑_{s, ε} ⟪g z, x⟫ g z = 2ⁿ ‖z‖² x` for `g = signShift s ε`. -/
theorem sum_signShift (z x : EuclideanSpace 𝕜 (Fin n)) :
    ∑ s : Fin n, ∑ ε : Fin n → Bool, ⟪signShift s ε z, x⟫_𝕜 • signShift s ε z =
      ((2 ^ n * ‖z‖ ^ 2 : ℝ) : 𝕜) • x := by
  ext i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply', signShift_apply, map_mul, conj_boolSign]
  have key : ∀ s : Fin n, ∑ ε : Fin n → Bool,
      (∑ j, boolSign (ε j) * conj (z (j + s)) * x j) * (boolSign (ε i) * z (i + s)) =
        2 ^ n * (conj (z (i + s)) * z (i + s)) * x i := by
    intro s
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ j, ∑ ε : Fin n → Bool,
        boolSign (ε j) * conj (z (j + s)) * x j * (boolSign (ε i) * z (i + s)) =
          (conj (z (j + s)) * x j * z (i + s)) *
            ∑ ε : Fin n → Bool, (boolSign (ε i) : 𝕜) * boolSign (ε j) := by
      intro j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ε _ ↦ by ring
    simp_rw [h, sum_boolSign_mul_boolSign]
    simp
    ring
  rw [Finset.sum_congr rfl fun s _ ↦ key s, ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [RCLike.conj_mul]
  have h2 : ∑ s, ‖z (i + s)‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_sum z]
    exact Equiv.sum_comp (Equiv.addLeft i) (fun j ↦ ‖z j‖ ^ 2)
  rw [← h2]
  push_cast
  ring

end Shift

/-! ### Projections from frames -/

section Frame

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Hahn–Banach** through an isometric embedding `E → X`: the functional `⟪y, ·⟫` extends to `X`
with norm at most `‖y‖`. -/
lemma exists_extension_inner (emb : E →ₗᵢ[𝕜] X) (y : E) :
    ∃ G : X →L[𝕜] 𝕜, (∀ x, G (emb x) = ⟪y, x⟫_𝕜) ∧ ‖G‖ ≤ ‖y‖ := by
  let f : LinearMap.range emb.toLinearMap →L[𝕜] 𝕜 :=
    (innerSL 𝕜 y).comp (emb.equivRange.symm.toContinuousLinearEquiv :
      LinearMap.range emb.toLinearMap →L[𝕜] E)
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq _ f
  refine ⟨G, fun x ↦ ?_, ?_⟩
  · have h := hG ⟨emb x, x, rfl⟩
    rw [h]
    have h' : emb.equivRange.symm ⟨emb x, x, rfl⟩ = x := by
      rw [LinearIsometryEquiv.symm_apply_eq]
      rfl
    simp [f, h']
  · rw [hGn]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p ↦ ?_
    calc ‖f p‖ = ‖⟪y, emb.equivRange.symm p⟫_𝕜‖ := rfl
      _ ≤ ‖y‖ * ‖emb.equivRange.symm p‖ := norm_inner_le_norm _ _
      _ = ‖y‖ * ‖p‖ := by rw [LinearIsometryEquiv.norm_map]

/-- **Projections from frames.** Let `E ⊆ X` isometrically. Suppose that the vectors `yₖ ∈ E`,
`‖yₖ‖ ≤ 1`, and the weights `wₖ ≥ 0` satisfy `N ∑ₖ wₖ ⟪yₖ, x⟫ yₖ = x` for all `x ∈ E` and
`∑ₖ wₖ |⟪yₖ, v⟫| ≤ C ‖v‖` for all `v ∈ E`. Then `λ(E, X) ≤ N C`: extend the functionals
`⟪yₖ, ·⟫` to `gₖ` on `X` (Hahn–Banach) and put `P ξ = N ∑ₖ wₖ gₖ(ξ) yₖ`. -/
theorem relProjConst_le_of_frame (emb : E →ₗᵢ[𝕜] X) {ι : Type*} (t : Finset ι) (y : ι → E)
    (w : ι → ℝ) (hw : ∀ k ∈ t, 0 ≤ w k) (hy : ∀ k ∈ t, ‖y k‖ ≤ 1) {N C : ℝ} (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hframe : ∀ x, ∑ k ∈ t, ((N * w k : ℝ) : 𝕜) • ⟪y k, x⟫_𝕜 • y k = x)
    (hbound : ∀ v, ∑ k ∈ t, w k * ‖⟪y k, v⟫_𝕜‖ ≤ C * ‖v‖) :
    relProjConst (LinearMap.range emb.toLinearMap) ≤ N * C := by
  choose G hG hGn using fun k ↦ exists_extension_inner emb (y k)
  let P : X →L[𝕜] X := ∑ k ∈ t, ((N * w k : ℝ) : 𝕜) • (G k).smulRight (emb (y k))
  have hP : ∀ ξ, P ξ = emb (∑ k ∈ t, ((N * w k : ℝ) : 𝕜) • G k ξ • y k) := by
    intro ξ
    simp [P, map_sum, map_smul]
  refine (relProjConst_le _ (P := P) ⟨fun ξ ↦ ?_, fun ξ hξ ↦ ?_⟩).trans ?_
  · rw [hP]
    exact ⟨_, rfl⟩
  · obtain ⟨x, rfl⟩ := hξ
    change P (emb x) = emb x
    rw [hP]
    simp_rw [hG]
    rw [hframe]
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hN hC) fun ξ ↦ ?_
    rw [hP, emb.norm_map]
    set a := ∑ k ∈ t, ((w k : 𝕜) * G k ξ) • y k with ha
    have hsum : ∑ k ∈ t, ((N * w k : ℝ) : 𝕜) • G k ξ • y k = (N : 𝕜) • a := by
      rw [ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [smul_smul, smul_smul]
      push_cast
      ring_nf
    -- `‖a‖² = re ⟪a, a⟫ ≤ ∑ₖ wₖ |gₖ(ξ)| |⟪yₖ, a⟫| ≤ ‖ξ‖ C ‖a‖`
    have h1 : ‖a‖ ^ 2 ≤ ‖ξ‖ * (C * ‖a‖) := by
      calc ‖a‖ ^ 2 = RCLike.re ⟪a, a⟫_𝕜 := (inner_self_eq_norm_sq a).symm
        _ ≤ ‖⟪a, a⟫_𝕜‖ := RCLike.re_le_norm _
        _ = ‖∑ k ∈ t, ((w k : 𝕜) * G k ξ) * ⟪a, y k⟫_𝕜‖ := by
          congr 1
          calc ⟪a, a⟫_𝕜 = ⟪a, ∑ k ∈ t, ((w k : 𝕜) * G k ξ) • y k⟫_𝕜 := by rw [← ha]
            _ = _ := by rw [inner_sum]; simp_rw [inner_smul_right]
        _ ≤ ∑ k ∈ t, ‖((w k : 𝕜) * G k ξ) * ⟪a, y k⟫_𝕜‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ t, ‖ξ‖ * (w k * ‖⟪y k, a⟫_𝕜‖) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [norm_mul, norm_mul, norm_inner_symm, RCLike.norm_ofReal, abs_of_nonneg (hw k hk)]
          have hGk : ‖G k ξ‖ ≤ ‖ξ‖ :=
            ((G k).le_opNorm ξ).trans (by
              calc ‖G k‖ * ‖ξ‖ ≤ ‖y k‖ * ‖ξ‖ :=
                    mul_le_mul_of_nonneg_right (hGn k) (norm_nonneg _)
                _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right (hy k hk) (norm_nonneg _)
                _ = ‖ξ‖ := one_mul _)
          have := mul_le_mul_of_nonneg_left hGk (hw k hk)
          nlinarith [norm_nonneg ⟪y k, a⟫_𝕜, norm_nonneg (G k ξ)]
        _ = ‖ξ‖ * ∑ k ∈ t, w k * ‖⟪y k, a⟫_𝕜‖ := by rw [Finset.mul_sum]
        _ ≤ ‖ξ‖ * (C * ‖a‖) := mul_le_mul_of_nonneg_left (hbound a) (norm_nonneg _)
    have h2 : ‖a‖ ≤ C * ‖ξ‖ := by
      nlinarith [mul_nonneg hC (norm_nonneg ξ), norm_nonneg a]
    rw [hsum, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hN, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hN

end Frame

/-! ### The upper bound -/

section Upper

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `u ↦ |⟪u, v⟫|` is `1`-Lipschitz for `‖v‖ ≤ 1`. -/
lemma lipschitzWith_norm_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {v : E}
    (hv : ‖v‖ ≤ 1) : LipschitzWith 1 fun u : E ↦ ‖⟪u, v⟫_𝕜‖ := by
  refine LipschitzWith.of_dist_le_mul fun u u' ↦ ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  calc |‖⟪u, v⟫_𝕜‖ - ‖⟪u', v⟫_𝕜‖| ≤ ‖⟪u, v⟫_𝕜 - ⟪u', v⟫_𝕜‖ := abs_norm_sub_norm_le _ _
    _ = ‖⟪u - u', v⟫_𝕜‖ := by rw [inner_sub_left]
    _ ≤ ‖u - u'‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ ‖u - u'‖ := mul_le_of_le_one_right (norm_nonneg _) hv

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ} [NeZero n]
  {ν : Measure (sphere (0 : EuclideanSpace 𝕜 (Fin n)) 1)} [IsFiniteMeasure ν]

/-- **The upper bound, for one superspace.** Let `ν` be an invariant finite measure on the unit
sphere of `E = 𝕜ⁿ` and `e ∈ E` a unit vector. For every normed space `X ⊇ E`,
`λ(E, X) ≤ n ∫ |⟪u, e⟫| dν(u) / ν(S)`. -/
theorem relProjConst_le_mean (hν : IsInvariant 𝕜 ν) (hν0 : ν ≠ 0)
    {e : EuclideanSpace 𝕜 (Fin n)} (he : ‖e‖ = 1) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (emb : EuclideanSpace 𝕜 (Fin n) →ₗᵢ[𝕜] X) :
    relProjConst (LinearMap.range emb.toLinearMap) ≤
      n * (∫ u, ‖⟪(u : EuclideanSpace 𝕜 (Fin n)), e⟫_𝕜‖ ∂ν) / ν.real Set.univ := by
  classical
  set c := (∫ u, ‖⟪(u : EuclideanSpace 𝕜 (Fin n)), e⟫_𝕜‖ ∂ν) / ν.real Set.univ with hc
  have hV : 0 < ν.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν0) (measure_ne_top _ _)
  have hc0 : 0 ≤ c := div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) hV.le
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [mul_div_assoc, ← hc]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hδ : 0 < ε / n := div_pos hε hn
  obtain ⟨s, w, hs, hw, hw1, hg⟩ := exists_discrete ν hν0 hδ
  -- the discrete bound, for every vector `v`
  have hbd : ∀ v : EuclideanSpace 𝕜 (Fin n),
      ∑ z ∈ s, w z * ‖⟪z, v⟫_𝕜‖ ≤ (c + ε / n) * ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hv' : ‖(‖v‖⁻¹ : 𝕜) • v‖ = 1 := by
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hvpos.ne']
    have h := hg (fun u ↦ ‖⟪u, (‖v‖⁻¹ : 𝕜) • v⟫_𝕜‖) (lipschitzWith_norm_inner hv'.le)
      (by simp)
    rw [integral_norm_inner_eq hν hv' he, ← hc] at h
    have hscale : ∀ z : EuclideanSpace 𝕜 (Fin n),
        ‖⟪z, (‖v‖⁻¹ : 𝕜) • v⟫_𝕜‖ = ‖v‖⁻¹ * ‖⟪z, v⟫_𝕜‖ := by
      intro z
      rw [inner_smul_right, norm_mul, norm_inv, RCLike.norm_ofReal, abs_norm]
    simp_rw [hscale] at h
    calc ∑ z ∈ s, w z * ‖⟪z, v⟫_𝕜‖ = ‖v‖ * ∑ z ∈ s, w z * (‖v‖⁻¹ * ‖⟪z, v⟫_𝕜‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          field_simp
      _ ≤ ‖v‖ * (c + ε / n) := mul_le_mul_of_nonneg_left h hvpos.le
      _ = (c + ε / n) * ‖v‖ := mul_comm _ _
  -- the symmetrized frame: the points `g z` for `z ∈ s` and all signed cyclic shifts `g`
  let t : Finset (EuclideanSpace 𝕜 (Fin n) × (Fin n × (Fin n → Bool))) := s ×ˢ Finset.univ
  let y : EuclideanSpace 𝕜 (Fin n) × (Fin n × (Fin n → Bool)) → EuclideanSpace 𝕜 (Fin n) :=
    fun p ↦ signShift p.2.1 p.2.2 p.1
  let W : EuclideanSpace 𝕜 (Fin n) × (Fin n × (Fin n → Bool)) → ℝ :=
    fun p ↦ w p.1 / (n * 2 ^ n)
  have hcard : (Fintype.card (Fin n × (Fin n → Bool)) : ℝ) = n * 2 ^ n := by
    simp [Fintype.card_prod]
  have key := relProjConst_le_of_frame emb t y W (N := n) (C := c + ε / n) ?_ ?_ hn.le
    (add_nonneg hc0 hδ.le) ?_ ?_
  · calc _ ≤ n * (c + ε / n) := key
      _ = n * c + ε := by field_simp
  · rintro ⟨z, g⟩ hk
    exact div_nonneg (hw z (Finset.mem_product.mp hk).1) (by positivity)
  · rintro ⟨z, g⟩ hk
    simp [y, hs z (Finset.mem_product.mp hk).1]
  · intro x
    rw [Finset.sum_product]
    calc ∑ z ∈ s, ∑ g ∈ Finset.univ, (((n : ℝ) * W (z, g) : ℝ) : 𝕜) • ⟪y (z, g), x⟫_𝕜 • y (z, g)
        = ∑ z ∈ s, (w z : 𝕜) • x := by
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          have h := sum_signShift (𝕜 := 𝕜) z x
          rw [hs z hz] at h
          simp only [W, y]
          rw [← Finset.smul_sum, Fintype.sum_prod_type, h, smul_smul]
          congr 1
          have hn' : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
          push_cast
          field_simp
      _ = x := by
          have h1 : ∑ z ∈ s, (w z : 𝕜) = 1 := by exact_mod_cast hw1
          rw [← Finset.sum_smul, h1, one_smul]
  · intro v
    rw [Finset.sum_product, Finset.sum_comm]
    have hg' : ∀ g : Fin n × (Fin n → Bool),
        ∑ z ∈ s, W (z, g) * ‖⟪y (z, g), v⟫_𝕜‖ ≤ (c + ε / n) * ‖v‖ / (n * 2 ^ n) := by
      intro g
      have h := hbd ((signShift g.1 g.2).symm v)
      rw [LinearIsometryEquiv.norm_map] at h
      calc ∑ z ∈ s, W (z, g) * ‖⟪y (z, g), v⟫_𝕜‖
          = (∑ z ∈ s, w z * ‖⟪z, (signShift g.1 g.2).symm v⟫_𝕜‖) / (n * 2 ^ n) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            simp only [W, y]
            rw [← LinearIsometryEquiv.inner_map_map (signShift g.1 g.2) z,
              LinearIsometryEquiv.apply_symm_apply]
            ring
        _ ≤ (c + ε / n) * ‖v‖ / (n * 2 ^ n) :=
            div_le_div_of_nonneg_right h (by positivity)
    calc ∑ g, ∑ z ∈ s, W (z, g) * ‖⟪y (z, g), v⟫_𝕜‖
        ≤ ∑ g : Fin n × (Fin n → Bool), (c + ε / n) * ‖v‖ / (n * 2 ^ n) :=
          Finset.sum_le_sum fun g _ ↦ hg' g
      _ = (c + ε / n) * ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          field_simp

/-- **The upper bound for `λ(𝕜ⁿ)`.** For an invariant finite measure `ν ≠ 0` on the unit sphere
of `E = 𝕜ⁿ` and a unit vector `e`, `λ(E) ≤ n ∫ |⟪u, e⟫| dν(u) / ν(S)`. -/
theorem absProjConst_le (hν : IsInvariant 𝕜 ν) (hν0 : ν ≠ 0) {e : EuclideanSpace 𝕜 (Fin n)}
    (he : ‖e‖ = 1) :
    absProjConst 𝕜 (EuclideanSpace 𝕜 (Fin n)) ≤
      n * (∫ u, ‖⟪(u : EuclideanSpace 𝕜 (Fin n)), e⟫_𝕜‖ ∂ν) / ν.real Set.univ :=
  Real.iSup_le (fun X ↦ relProjConst_le_mean hν hν0 he X.emb)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _))
      measureReal_nonneg)

end Upper

end ProjectionConstants.Euclidean
