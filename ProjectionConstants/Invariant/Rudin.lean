/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Rudin's averaging theorem

Let a compact group `G` act continuously by bounded operators on a normed space `X`, and let
`Y ⊆ X` be a complete subspace that is invariant under `G`. Rudin [Ru, Theorem 1] observed that
if there is a bounded projection `P` of `X` onto `Y`, then its average

  `Q x = ∫_G g (P (g⁻¹ x)) dg`

over the normalized Haar measure is a bounded projection of `X` onto `Y` that commutes with the
action of `G`, with `‖Q‖ ≤ M² ‖P‖` where `M = sup_g ‖g‖`; this supremum is finite by the Baire
category theorem [Ru, (4)]. If `G` acts by isometries, then `‖Q‖ ≤ ‖P‖`. Consequently, minimal
projections onto invariant subspaces can be found among the equivariant ones, and if `P₀` is the
only equivariant projection onto `Y`, then `λ(Y, X) = ‖P₀‖` (**Rudin's principle**,
`IsRepresentation.relProjConst_eq_norm`). This principle is behind the computation of the
projection constants of the spaces of trigonometric polynomials
(`ProjectionConstants.Fourier.Trigonometric`) and, in its finite form, of Grünbaum's computations
(`ProjectionConstants.Invariant.Circulant`).

Every statement comes in a version for multiplicative groups and one for additive groups (such as
the circle `AddCircle T` acting on `C(AddCircle T, ℂ)` by translations). The elementary lemmas are
translated by `to_additive`; the averaging arguments are proved once, for an abstract averaging
scheme without group structure, and then specialized to both cases.

## Main definitions

* `IsRepresentation ρ`: `ρ : G → X →L[𝕜] X` satisfies `ρ 1 = id` and `ρ (g * h) = ρ g ∘ ρ h`;
  `IsAddRepresentation ρ` is the additive version.
* `IsEquivariant ρ Q`: the operator `Q` commutes with every `ρ g`.

## Main statements

* `IsRepresentation.exists_forall_norm_le`: a strongly continuous representation of a compact
  group is uniformly bounded [Ru, (4)].
* `IsRepresentation.exists_isProjectionOnto_isEquivariant`: **Rudin's averaging theorem**
  [Ru, Theorem 1], for any left-invariant probability measure, with the estimate
  `‖Q‖ ≤ M² ‖P‖`.
* `IsRepresentation.exists_isProjectionOnto_isEquivariant_of_compact`: Rudin's Theorem 1 as stated
  in [Ru], with the normalized Haar measure.
* `IsRepresentation.exists_isProjectionOnto_isEquivariant_of_fintype`: the version for finite
  groups, `Q = |G|⁻¹ ∑_g ρ g ∘ P ∘ ρ g⁻¹`, without topology.
* `IsRepresentation.relProjConst_eq_norm`, `IsRepresentation.relProjConst_eq_norm_of_fintype`:
  **Rudin's principle**: if `G` acts by isometries and `P₀` is the only equivariant projection onto
  a finite-dimensional invariant subspace `Y`, then `λ(Y, X) = ‖P₀‖`.

Each of these statements has an `IsAddRepresentation` counterpart for additive groups.

## Implementation notes

The average is integrated in `Y`, which is complete, so `X` itself need not be complete (in [Ru],
`X` is a Banach space and `Y` is closed). The Bochner integral needs the real structure of `Y`,
whence the assumptions `[NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]`, which hold for `𝕜 = ℝ, ℂ`.

## References

* [Ru] W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962), 429–432.

## Tags

projection constant, minimal projection, invariant subspace, Haar measure, averaging
-/

open MeasureTheory Measure Set

namespace ProjectionConstants

/-- `ρ : G → X →L[𝕜] X` is a **representation** of the additive group `G` by bounded operators
on `X`: `ρ 0 = id` and `ρ (g + h) = ρ g ∘ ρ h`. -/
structure IsAddRepresentation {G : Type*} [AddGroup G] {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (ρ : G → X →L[𝕜] X) : Prop where
  /-- `ρ 0` is the identity. -/
  map_zero : ρ 0 = ContinuousLinearMap.id 𝕜 X
  /-- `ρ` is additive. -/
  map_add : ∀ g h, ρ (g + h) = (ρ g).comp (ρ h)

/-- `ρ : G → X →L[𝕜] X` is a **representation** of `G` by bounded operators on `X`:
`ρ 1 = id` and `ρ (g * h) = ρ g ∘ ρ h`. -/
structure IsRepresentation {G : Type*} [Group G] {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (ρ : G → X →L[𝕜] X) : Prop where
  /-- `ρ 1` is the identity. -/
  map_one : ρ 1 = ContinuousLinearMap.id 𝕜 X
  /-- `ρ` is multiplicative. -/
  map_mul : ∀ g h, ρ (g * h) = (ρ g).comp (ρ h)

attribute [to_additive IsAddRepresentation] IsRepresentation

variable {G : Type*} [Group G] {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- The operator `Q` is **equivariant** for `ρ`: it commutes with every `ρ g`. -/
def IsEquivariant {ι : Type*} (ρ : ι → X →L[𝕜] X) (Q : X →L[𝕜] X) : Prop :=
  ∀ g, (ρ g).comp Q = Q.comp (ρ g)

namespace IsRepresentation

variable {ρ : G → X →L[𝕜] X}

@[to_additive]
lemma apply_apply (hρ : IsRepresentation ρ) (g h : G) (x : X) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [hρ.map_mul]
  rfl

@[to_additive]
lemma apply_inv_apply (hρ : IsRepresentation ρ) (g : G) (x : X) : ρ g (ρ g⁻¹ x) = x := by
  rw [hρ.apply_apply, mul_inv_cancel, hρ.map_one]
  rfl

@[to_additive]
lemma inv_apply_apply (hρ : IsRepresentation ρ) (g : G) (x : X) : ρ g⁻¹ (ρ g x) = x := by
  rw [hρ.apply_apply, inv_mul_cancel, hρ.map_one]
  rfl

/-! ### Uniform boundedness -/

variable [TopologicalSpace G]

/-- **Uniform boundedness** [Ru, (4)]: if `G` is a compact topological group and every orbit map
`g ↦ ρ g x` is continuous, then `sup_g ‖ρ g‖ < ∞`. The sets `{g | ‖ρ g‖ ≤ k}` are closed and cover
`G`, so one of them has interior (Baire), and finitely many translates of the interior cover `G`. -/
@[to_additive]
theorem exists_forall_norm_le [IsTopologicalGroup G] [CompactSpace G] (hρ : IsRepresentation ρ)
    (hc : ∀ x, Continuous fun g ↦ ρ g x) : ∃ M, ∀ g, ‖ρ g‖ ≤ M := by
  set E : ℕ → Set G := fun k ↦ {g | ‖ρ g‖ ≤ k}
  have hE : ∀ k, IsClosed (E k) := fun k ↦ by
    have h : E k = ⋂ x : X, {g | ‖ρ g x‖ ≤ k * ‖x‖} := by
      ext g
      simp only [E, mem_ofPred_eq, mem_iInter]
      exact ⟨fun h x ↦ (ρ g).le_of_opNorm_le h x,
        fun h ↦ ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg k) h⟩
    rw [h]
    exact isClosed_iInter fun x ↦ isClosed_le (hc x).norm continuous_const
  have hU : ⋃ k, E k = univ :=
    eq_univ_of_forall fun g ↦ mem_iUnion.2 ⟨⌈‖ρ g‖⌉₊, Nat.le_ceil ‖ρ g‖⟩
  obtain ⟨k, g₀, hg₀⟩ := nonempty_interior_of_iUnion_of_closed hE hU
  -- finitely many translates of the interior cover `G`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun h : G ↦ (h * ·) '' interior (E k))
    (fun h ↦ (Homeomorph.mulLeft h).isOpenMap _ isOpen_interior)
    (fun g _ ↦ mem_iUnion.2 ⟨g * g₀⁻¹, g₀, hg₀, by simp⟩)
  refine ⟨k * ∑ h ∈ t, ‖ρ h‖, fun g ↦ ?_⟩
  obtain ⟨h, hh, hv⟩ : ∃ h ∈ t, h⁻¹ * g ∈ interior (E k) := by simpa using ht (mem_univ g)
  have hv' : h⁻¹ * g ∈ E k := interior_subset hv
  have hk : ‖ρ (h⁻¹ * g)‖ ≤ k := hv'
  have hsum : ‖ρ h‖ ≤ ∑ h ∈ t, ‖ρ h‖ :=
    Finset.single_le_sum (f := fun h ↦ ‖ρ h‖) (fun _ _ ↦ norm_nonneg _) hh
  calc ‖ρ g‖ = ‖(ρ h).comp (ρ (h⁻¹ * g))‖ := by rw [← hρ.map_mul, mul_inv_cancel_left]
    _ ≤ ‖ρ h‖ * ‖ρ (h⁻¹ * g)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (∑ h ∈ t, ‖ρ h‖) * k := mul_le_mul hsum hk (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    _ = k * ∑ h ∈ t, ‖ρ h‖ := mul_comm _ _

end IsRepresentation

/-! ### Rudin's averaging theorem -/

/-- The Haar measure of a compact group, normalized on the whole group, is a probability
measure. -/
@[to_additive
  /-- The additive Haar measure of a compact group, normalized on the whole group, is a
  probability measure. -/]
theorem isProbabilityMeasure_haarMeasure_top [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) := by
  have h := haarMeasure_self (G := G) (K₀ := ⊤)
  rw [TopologicalSpace.PositiveCompacts.coe_top] at h
  exact ⟨h⟩

section Average

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {Y : Submodule 𝕜 X} [CompleteSpace Y]
  {P : X →L[𝕜] X}

/-- The averaging argument of [Ru, Theorem 1], without group structure: `σ g` and `τ g` play the
roles of `ρ g` and `ρ g⁻¹`, and the shifts `φ i` of the probability space `(K, μ)` realize the
invariance of the Haar measure. The average `Q x = ∫ σ g (P (τ g x)) dμ(g)` is a projection onto
`Y` of norm at most `M² ‖P‖` that commutes with the operators `R i`. -/
private theorem exists_isProjectionOnto_of_average {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K] (μ : Measure K)
    [IsProbabilityMeasure μ] {σ τ : K → X →L[𝕜] X} (hσ : Continuous fun p : K × X ↦ σ p.1 p.2)
    (hτ : ∀ x, Continuous fun g ↦ τ g x) {M : ℝ} (hσM : ∀ g, ‖σ g‖ ≤ M) (hτM : ∀ g, ‖τ g‖ ≤ M)
    (hστ : ∀ g x, σ g (τ g x) = x) (hσY : ∀ g, ∀ y ∈ Y, σ g y ∈ Y)
    (hτY : ∀ g, ∀ y ∈ Y, τ g y ∈ Y) (hP : IsProjectionOnto Y P) {ι : Type*}
    (R : ι → X →L[𝕜] X) (hRY : ∀ i, ∀ y ∈ Y, R i y ∈ Y)
    (hR : ∀ i, ∃ φ : K → K, (∀ f : K → Y, ∫ g, f (φ g) ∂μ = ∫ g, f g ∂μ) ∧
      ∀ g x, σ (φ g) (P (τ (φ g) (R i x))) = R i (σ g (P (τ g x)))) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant R Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  have : Nonempty K := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hσM (Classical.arbitrary K))
  -- the integrand, with values in `Y`
  let F : X → K → Y := fun x g ↦ ⟨σ g (P (τ g x)), hσY g _ (hP.mem _)⟩
  have hFc : ∀ x, Continuous (F x) := fun x ↦
    (hσ.comp (continuous_id.prodMk (P.continuous.comp (hτ x)))).subtype_mk _
  have hFi : ∀ x, Integrable (F x) μ := fun x ↦
    integrableOn_univ.1 ((hFc x).continuousOn.integrableOn_compact' isCompact_univ
      MeasurableSet.univ)
  have hFn : ∀ x g, ‖F x g‖ ≤ M ^ 2 * ‖P‖ * ‖x‖ := fun x g ↦ by
    have h₁ : ‖τ g x‖ ≤ M * ‖x‖ := (τ g).le_of_opNorm_le (hτM g) x
    have h₂ : ‖P (τ g x)‖ ≤ ‖P‖ * (M * ‖x‖) := (P.le_opNorm _).trans (by gcongr)
    calc ‖F x g‖ = ‖σ g (P (τ g x))‖ := rfl
      _ ≤ M * (‖P‖ * (M * ‖x‖)) := (σ g).le_of_opNorm_le (hσM g) _ |>.trans (by gcongr)
      _ = M ^ 2 * ‖P‖ * ‖x‖ := by ring
  -- the averaged operator `X → Y`
  let Q₀ : X →ₗ[𝕜] Y :=
    { toFun := fun x ↦ ∫ g, F x g ∂μ
      map_add' := fun x x' ↦ by
        rw [← integral_add (hFi x) (hFi x')]
        congr 1
        ext g
        simp [F]
      map_smul' := fun c x ↦ by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1
        ext g
        simp [F] }
  have hQ₀ : ∀ x, ‖Q₀ x‖ ≤ M ^ 2 * ‖P‖ * ‖x‖ := fun x ↦ by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (hFn x))
    rwa [probReal_univ, mul_one] at h
  let Q : X →L[𝕜] X := Y.subtypeL.comp (Q₀.mkContinuous _ hQ₀)
  have hQ : ∀ x, Q x = ((∫ g, F x g ∂μ : Y) : X) := fun _ ↦ rfl
  refine ⟨Q, ⟨fun x ↦ (Q₀ x).2, fun y hy ↦ ?_⟩, fun i ↦ ?_,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hQ₀⟩
  · -- on `Y` the integrand is constant
    have hF : ∀ g, F y g = ⟨y, hy⟩ := fun g ↦ Subtype.ext <| by
      simp only [F]
      rw [hP.map_id _ (hτY _ _ hy), hστ]
    rw [hQ, integral_eq_const (Filter.Eventually.of_forall hF)]
  · -- equivariance: substitute `g ↦ φ g`
    obtain ⟨φ, hφ, hφR⟩ := hR i
    let RY : Y →L[𝕜] Y := ((R i).comp Y.subtypeL).codRestrict Y fun y ↦ hRY i _ y.2
    ext x
    have h₁ : ∫ g, F (R i x) g ∂μ = ∫ g, RY (F x g) ∂μ := by
      rw [← hφ (F (R i x))]
      congr 1
      ext g
      exact hφR g x
    have h₂ : ∫ g, RY (F x g) ∂μ = RY (∫ g, F x g ∂μ) := RY.integral_comp_comm (hFi x)
    simp only [ContinuousLinearMap.comp_apply, hQ, h₁, h₂]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] {ρ : G → X →L[𝕜] X}

/-- **Rudin's averaging theorem** [Ru, Theorem 1]. Let `G` be a compact group with a left-invariant
probability measure `μ`, acting continuously on `X` by operators of norm at most `M`, and let
`Y ⊆ X` be a complete invariant subspace. If `P` is a projection of `X` onto `Y`, then
`Q x = ∫ ρ g (P (ρ g⁻¹ x)) dμ(g)` is an equivariant projection onto `Y` with `‖Q‖ ≤ M² ‖P‖`. -/
theorem IsRepresentation.exists_isProjectionOnto_isEquivariant (μ : Measure G)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (hρ : IsRepresentation ρ)
    (hc : Continuous fun p : G × X ↦ ρ p.1 p.2) {M : ℝ} (hM : ∀ g, ‖ρ g‖ ≤ M)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  refine exists_isProjectionOnto_of_average μ hc
    (fun x ↦ (hc.comp (continuous_id.prodMk continuous_const)).comp continuous_inv) hM
    (fun g ↦ hM g⁻¹) (hρ.apply_inv_apply) hY (fun g ↦ hY g⁻¹) hP ρ hY fun h ↦
    ⟨(h * ·), fun f ↦ integral_mul_left_eq_self f h, fun g x ↦ ?_⟩
  simp only
  rw [hρ.apply_apply (h * g)⁻¹ h x, show (h * g)⁻¹ * h = g⁻¹ by group, ← hρ.apply_apply h g]

/-- **Rudin's averaging theorem** [Ru, Theorem 1] for an additive compact group `G` with a
left-invariant probability measure `μ`: `Q x = ∫ ρ g (P (ρ (-g) x)) dμ(g)` is an equivariant
projection onto `Y` with `‖Q‖ ≤ M² ‖P‖`. -/
theorem IsAddRepresentation.exists_isProjectionOnto_isEquivariant {G : Type*} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {ρ : G → X →L[𝕜] X} (hρ : IsAddRepresentation ρ) (hc : Continuous fun p : G × X ↦ ρ p.1 p.2)
    {M : ℝ} (hM : ∀ g, ‖ρ g‖ ≤ M) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  refine exists_isProjectionOnto_of_average μ hc
    (fun x ↦ (hc.comp (continuous_id.prodMk continuous_const)).comp continuous_neg) hM
    (fun g ↦ hM (-g)) (hρ.apply_neg_apply) hY (fun g ↦ hY (-g)) hP ρ hY fun h ↦
    ⟨(h + ·), fun f ↦ integral_add_left_eq_self f h, fun g x ↦ ?_⟩
  simp only
  rw [hρ.apply_apply (-(h + g)) h x,
    show -(h + g) + h = -g by rw [neg_add_rev, neg_add_cancel_right], ← hρ.apply_apply h g]

/-- **Rudin's averaging theorem** [Ru, Theorem 1]: if a compact group acts continuously by bounded
operators on `X`, and `Y ⊆ X` is a complete invariant subspace onto which there is a projection,
then there is also a projection onto `Y` that commutes with the action. -/
theorem IsRepresentation.exists_isProjectionOnto_isEquivariant_of_compact
    (hρ : IsRepresentation ρ) (hc : Continuous fun p : G × X ↦ ρ p.1 p.2)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q := by
  obtain ⟨M, hM⟩ :=
    hρ.exists_forall_norm_le fun x ↦ hc.comp (continuous_id.prodMk continuous_const)
  have := isProbabilityMeasure_haarMeasure_top (G := G)
  let μ := haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  obtain ⟨Q, hQ, hQe, -⟩ := hρ.exists_isProjectionOnto_isEquivariant μ hc hM hY hP
  exact ⟨Q, hQ, hQe⟩

/-- **Rudin's averaging theorem** [Ru, Theorem 1] for additive compact groups: if `G` acts
continuously by bounded operators on `X`, and `Y ⊆ X` is a complete invariant subspace onto which
there is a projection, then there is also a projection onto `Y` that commutes with the action. -/
theorem IsAddRepresentation.exists_isProjectionOnto_isEquivariant_of_compact {G : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {ρ : G → X →L[𝕜] X} (hρ : IsAddRepresentation ρ)
    (hc : Continuous fun p : G × X ↦ ρ p.1 p.2) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q := by
  obtain ⟨M, hM⟩ :=
    hρ.exists_forall_norm_le fun x ↦ hc.comp (continuous_id.prodMk continuous_const)
  have := isProbabilityMeasure_addHaarMeasure_top (G := G)
  let μ := addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  obtain ⟨Q, hQ, hQe, -⟩ := hρ.exists_isProjectionOnto_isEquivariant μ hc hM hY hP
  exact ⟨Q, hQ, hQe⟩

end Average

/-! ### Finite groups -/

section Finite

variable {Y : Submodule 𝕜 X} {P : X →L[𝕜] X}

/-- The averaging argument for a finite index set: `Q = |K|⁻¹ ∑_g σ g ∘ P ∘ τ g`. -/
private theorem exists_isProjectionOnto_of_sum {K : Type*} [Finite K] [Nonempty K]
    {σ τ : K → X →L[𝕜] X} {M : ℝ} (hσM : ∀ g, ‖σ g‖ ≤ M) (hτM : ∀ g, ‖τ g‖ ≤ M)
    (hστ : ∀ g x, σ g (τ g x) = x) (hσY : ∀ g, ∀ y ∈ Y, σ g y ∈ Y)
    (hτY : ∀ g, ∀ y ∈ Y, τ g y ∈ Y) (hP : IsProjectionOnto Y P) {ι : Type*}
    (R : ι → X →L[𝕜] X)
    (hR : ∀ i, ∃ φ : K ≃ K, ∀ g, (σ (φ g)).comp (P.comp ((τ (φ g)).comp (R i))) =
      (R i).comp ((σ g).comp (P.comp (τ g)))) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant R Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  have := Fintype.ofFinite K
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hσM (Classical.arbitrary K))
  have hK : (Fintype.card K : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let Q : X →L[𝕜] X := (Fintype.card K : 𝕜)⁻¹ • ∑ g, (σ g).comp (P.comp (τ g))
  have hQ : ∀ x, Q x = (Fintype.card K : 𝕜)⁻¹ • ∑ g, σ g (P (τ g x)) := fun x ↦ by
    simp [Q]
  refine ⟨Q, ⟨fun x ↦ ?_, fun y hy ↦ ?_⟩, fun i ↦ ?_, ?_⟩
  · rw [hQ]
    exact Y.smul_mem _ (Y.sum_mem fun g _ ↦ hσY g _ (hP.mem _))
  · have h : ∀ g, σ g (P (τ g y)) = y := fun g ↦ by rw [hP.map_id _ (hτY g _ hy), hστ]
    simp only [hQ, h, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      inv_mul_cancel₀ hK, one_smul]
  · obtain ⟨φ, hφ⟩ := hR i
    simp only [Q, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]
    congr 1
    symm
    rw [← Equiv.sum_comp φ]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simpa only [ContinuousLinearMap.comp_assoc] using hφ g
  · have hK' : (0 : ℝ) < Fintype.card K := Nat.cast_pos.2 Fintype.card_pos
    have hterm : ∀ g, ‖(σ g).comp (P.comp (τ g))‖ ≤ M * (‖P‖ * M) := fun g ↦ by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hσM g) ?_
        (norm_nonneg _) hM0)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (hτM g) (norm_nonneg _))
    calc ‖Q‖ = ‖(Fintype.card K : 𝕜)⁻¹ • ∑ g, (σ g).comp (P.comp (τ g))‖ := rfl
      _ ≤ ‖((Fintype.card K : 𝕜)⁻¹)‖ * ‖∑ g, (σ g).comp (P.comp (τ g))‖ :=
          norm_smul_le ((Fintype.card K : 𝕜)⁻¹) (∑ g, (σ g).comp (P.comp (τ g)))
      _ ≤ ‖((Fintype.card K : 𝕜)⁻¹)‖ * ∑ g, ‖(σ g).comp (P.comp (τ g))‖ := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ (Fintype.card K : ℝ)⁻¹ * ∑ _g : K, M * (‖P‖ * M) := by
          rw [norm_inv, RCLike.norm_natCast]
          gcongr with g
          exact hterm g
      _ = M ^ 2 * ‖P‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- **Rudin's averaging theorem for finite groups**: if `P` is a projection onto a `G`-invariant
subspace `Y` and `‖ρ g‖ ≤ M`, then `Q = |G|⁻¹ ∑_g ρ g ∘ P ∘ ρ g⁻¹` is an equivariant projection onto
`Y` with `‖Q‖ ≤ M² ‖P‖`. -/
theorem IsRepresentation.exists_isProjectionOnto_isEquivariant_of_fintype [Finite G]
    {ρ : G → X →L[𝕜] X} (hρ : IsRepresentation ρ) {M : ℝ} (hM : ∀ g, ‖ρ g‖ ≤ M)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  refine exists_isProjectionOnto_of_sum (τ := fun g ↦ ρ g⁻¹) hM (fun g ↦ hM g⁻¹)
    hρ.apply_inv_apply hY (fun g ↦ hY g⁻¹) hP ρ fun h ↦ ⟨Equiv.mulLeft h, fun g ↦ ?_⟩
  ext x
  simp only [Equiv.coe_mulLeft, ContinuousLinearMap.comp_apply]
  rw [hρ.apply_apply (h * g)⁻¹ h x, show (h * g)⁻¹ * h = g⁻¹ by group, ← hρ.apply_apply h g]

/-- **Rudin's averaging theorem for finite additive groups**: `Q = |G|⁻¹ ∑_g ρ g ∘ P ∘ ρ (-g)` is
an equivariant projection onto `Y` with `‖Q‖ ≤ M² ‖P‖`. -/
theorem IsAddRepresentation.exists_isProjectionOnto_isEquivariant_of_fintype {G : Type*}
    [AddGroup G] [Finite G] {ρ : G → X →L[𝕜] X} (hρ : IsAddRepresentation ρ) {M : ℝ}
    (hM : ∀ g, ‖ρ g‖ ≤ M) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP : IsProjectionOnto Y P) :
    ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  refine exists_isProjectionOnto_of_sum (τ := fun g ↦ ρ (-g)) hM (fun g ↦ hM (-g))
    hρ.apply_neg_apply hY (fun g ↦ hY (-g)) hP ρ fun h ↦ ⟨Equiv.addLeft h, fun g ↦ ?_⟩
  ext x
  simp only [Equiv.coe_addLeft, ContinuousLinearMap.comp_apply]
  rw [hρ.apply_apply (-(h + g)) h x,
    show -(h + g) + h = -g by rw [neg_add_rev, neg_add_cancel_right], ← hρ.apply_apply h g]

end Finite

/-! ### Rudin's principle -/

section Principle

variable {Y : Submodule 𝕜 X} [FiniteDimensional 𝕜 Y] {P₀ : X →L[𝕜] X}

/-- If every projection onto `Y` can be averaged to an equivariant projection of no larger norm,
and `P₀` is the only equivariant projection onto `Y`, then `λ(Y, X) = ‖P₀‖`. -/
private lemma relProjConst_eq_norm_of_average {ι : Type*} {ρ : ι → X →L[𝕜] X}
    (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀)
    (havg : ∀ P, IsProjectionOnto Y P →
      ∃ Q : X →L[𝕜] X, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ 1 ^ 2 * ‖P‖) :
    relProjConst Y = ‖P₀‖ := by
  refine le_antisymm (relProjConst_le Y hP₀) (le_relProjConst Y fun P hP ↦ ?_)
  obtain ⟨Q, hQ, hQe, hQn⟩ := havg P hP
  rw [← huniq Q hQ hQe]
  simpa using hQn

private lemma norm_le_one_of_forall {ι : Type*} {ρ : ι → X →L[𝕜] X}
    (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (g : ι) : ‖ρ g‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simpa using hiso g x

/-- **Rudin's principle** [Ru]: let a compact group `G` act continuously on `X` by contractions
(hence isometries), let `Y ⊆ X` be a finite-dimensional invariant subspace, and suppose that `P₀`
is the only equivariant projection onto `Y`. Then `P₀` is a minimal projection:
`λ(Y, X) = ‖P₀‖`. -/
theorem IsRepresentation.relProjConst_eq_norm [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] {ρ : G → X →L[𝕜] X} (hρ : IsRepresentation ρ)
    (hc : Continuous fun p : G × X ↦ ρ p.1 p.2) (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀) :
    relProjConst Y = ‖P₀‖ := by
  have := isProbabilityMeasure_haarMeasure_top (G := G)
  have : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y
  exact relProjConst_eq_norm_of_average hP₀ huniq fun P hP ↦
    hρ.exists_isProjectionOnto_isEquivariant (haarMeasure ⊤) hc (norm_le_one_of_forall hiso) hY hP

/-- **Rudin's principle** [Ru] for additive compact groups: if `P₀` is the only equivariant
projection onto the finite-dimensional invariant subspace `Y`, then `λ(Y, X) = ‖P₀‖`. -/
theorem IsAddRepresentation.relProjConst_eq_norm [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {ρ : G → X →L[𝕜] X} (hρ : IsAddRepresentation ρ)
    (hc : Continuous fun p : G × X ↦ ρ p.1 p.2) (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀) :
    relProjConst Y = ‖P₀‖ := by
  have := isProbabilityMeasure_addHaarMeasure_top (G := G)
  have : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y
  exact relProjConst_eq_norm_of_average hP₀ huniq fun P hP ↦
    hρ.exists_isProjectionOnto_isEquivariant (addHaarMeasure ⊤) hc (norm_le_one_of_forall hiso)
      hY hP

/-- **Rudin's principle for finite groups**: if a finite group acts on `X` by contractions and
`P₀` is the only equivariant projection onto the finite-dimensional invariant subspace `Y`, then
`λ(Y, X) = ‖P₀‖`. -/
theorem IsRepresentation.relProjConst_eq_norm_of_fintype [Finite G] {ρ : G → X →L[𝕜] X}
    (hρ : IsRepresentation ρ) (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀) :
    relProjConst Y = ‖P₀‖ :=
  relProjConst_eq_norm_of_average hP₀ huniq fun _ hP ↦
    hρ.exists_isProjectionOnto_isEquivariant_of_fintype (norm_le_one_of_forall hiso) hY hP

/-- **Rudin's principle for finite additive groups**: if `P₀` is the only equivariant projection
onto the finite-dimensional invariant subspace `Y`, then `λ(Y, X) = ‖P₀‖`. -/
theorem IsAddRepresentation.relProjConst_eq_norm_of_fintype {G : Type*} [AddGroup G] [Finite G]
    {ρ : G → X →L[𝕜] X} (hρ : IsAddRepresentation ρ) (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖)
    (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀) :
    relProjConst Y = ‖P₀‖ :=
  relProjConst_eq_norm_of_average hP₀ huniq fun _ hP ↦
    hρ.exists_isProjectionOnto_isEquivariant_of_fintype (norm_le_one_of_forall hiso) hY hP

end Principle

end ProjectionConstants
