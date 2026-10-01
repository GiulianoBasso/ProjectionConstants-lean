/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Fourier.Lebesgue
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Complemented translation-invariant subspaces of `C(𝕋)`

For `N ⊆ ℤ` let `C_N(𝕋) = {f ∈ C(𝕋) : f̂(k) = 0 for k ∉ N}` be the space of continuous functions
on the circle `𝕋 = AddCircle T` with Fourier spectrum in `N`; by [Ru, §3 and §4], these are all the
closed translation-invariant subspaces of `C(𝕋)`. Rudin [Ru, Theorem 2 and §4] proved that
`C_N(𝕋)` is complemented in `C(𝕋)` if and only if `N` differs from a periodic set in at most
finitely many places.

The proof combines Rudin's averaging theorem with Helson's theorem on idempotent measures. If
`C_N(𝕋)` is complemented, then averaging over the translations gives a projection onto `C_N(𝕋)`
that commutes with the translations, and such a projection maps `eₖ` to `eₖ` for `k ∈ N` and to
`0` for `k ∉ N`: the indicator function `1_N` is a bounded Fourier multiplier on `C(𝕋)`.
Conversely, the multiplier operator with symbol `1_N` is a projection onto `C_N(𝕋)`. This
reduction is `exists_isProjectionOnto_spectralSubspace_iff`. If `N` is periodic, then `1_N` is a
finite linear combination of characters of a finite cyclic group, and its multiplier operator is a
linear combination of finitely many translations; finite modifications of `N` change it by an
operator of finite rank. This proves the "if" part of Rudin's theorem
(`exists_isProjectionOnto_spectralSubspace_of_periodic`). The "only if" part rests on Helson's
theorem [He] that `1_N` is the Fourier–Stieltjes transform of a measure only if `N` is periodic up
to finitely many places, which is not formalized here.

The most prominent case is `N = ℕ`: the **disc algebra** `A(𝕋) = C_ℕ(𝕋)` (classically identified
with the algebra of holomorphic functions on the open unit disc that extend continuously to its
closure) is not complemented in `C(𝕋)`; the analogous statement for `H¹ ⊆ L¹` is a theorem of
Newman [Ne]. Here no idempotent measures are needed: if `Q` were a bounded multiplier with symbol
`1_ℕ`, then the Fourier partial sum operator `Sₙ = e₋ₙ Q eₙ - eₙ₊₁ Q e₋₍ₙ₊₁₎` would have norm at
most `2 ‖Q‖`, contradicting `‖Sₙ‖ = Lₙ → ∞` (`ProjectionConstants.Fourier.Lebesgue`).

## Main definitions

* `spectralSubspace T N`: the space `C_N(𝕋)` of continuous functions with spectrum in `N`.
* `discAlgebra T`: the disc algebra `A(𝕋) = C_ℕ(𝕋)`.

## Main statements

* `fourierCoeff_injective`: a continuous function on the circle is determined by its Fourier
  coefficients.
* `exists_isProjectionOnto_spectralSubspace_iff`: **Rudin's reduction** [Ru, Theorem 2]: `C_N(𝕋)`
  is complemented in `C(𝕋)` if and only if there is a bounded operator `Q` on `C(𝕋)` with
  `Q eₖ = 1_N(k) eₖ` for all `k`.
* `exists_isProjectionOnto_spectralSubspace_of_periodic`: [Ru, Theorem 2], "if" part: if `N`
  differs from a periodic set in finitely many places, then `C_N(𝕋)` is complemented.
* `not_exists_isProjectionOnto_discAlgebra`: **the disc algebra is not complemented in `C(𝕋)`**
  [Ru, §4].

## References

* [Ru] W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962), 429–432.
* [He] H. Helson, *Note on harmonic functions*, Proc. Amer. Math. Soc. 4 (1953), 686–691.
* [Ne] D. J. Newman, *The nonexistence of projections from `L¹` to `H¹`*, Proc. Amer. Math. Soc.
  12 (1961), 98–99.

## Tags

disc algebra, complemented subspace, invariant subspace, Fourier multiplier, Riesz projection,
projection constant
-/

open MeasureTheory AddCircle Finset Filter

noncomputable section

namespace ProjectionConstants

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ### Fourier uniqueness -/

/-- A continuous function on the circle is determined by its Fourier coefficients. -/
theorem fourierCoeff_injective :
    Function.Injective fun f : C(AddCircle T, ℂ) ↦ fourierCoeff f := by
  intro f g h
  refine ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle ?_
  refine fourierBasis.repr.injective (lp.ext <| funext fun k ↦ ?_)
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
  exact congrFun h k

/-! ### Spectral subspaces -/

variable (T) in
/-- The space `C_N(𝕋)` of continuous functions on the circle whose Fourier coefficients vanish
outside `N`. -/
def spectralSubspace (N : Set ℤ) : Submodule ℂ C(AddCircle T, ℂ) where
  carrier := {f | ∀ k ∉ N, fourierCoeff f k = 0}
  add_mem' {f g} hf hg k hk := by
    rw [← fourierCoeffCLM_apply, map_add, fourierCoeffCLM_apply, fourierCoeffCLM_apply, hf k hk,
      hg k hk, add_zero]
  zero_mem' k _ := by
    rw [← fourierCoeffCLM_apply, map_zero]
  smul_mem' c f hf k hk := by
    rw [← fourierCoeffCLM_apply, map_smul, fourierCoeffCLM_apply, hf k hk, smul_zero]

lemma mem_spectralSubspace {N : Set ℤ} {f : C(AddCircle T, ℂ)} :
    f ∈ spectralSubspace T N ↔ ∀ k ∉ N, fourierCoeff f k = 0 :=
  Iff.rfl

lemma isClosed_spectralSubspace (N : Set ℤ) :
    IsClosed (spectralSubspace T N : Set C(AddCircle T, ℂ)) := by
  have h : (spectralSubspace T N : Set C(AddCircle T, ℂ)) =
      ⋂ k ∈ Nᶜ, fourierCoeffCLM k ⁻¹' {0} := by
    ext f
    simp [mem_spectralSubspace]
  rw [h]
  exact isClosed_biInter fun k _ ↦ isClosed_singleton.preimage (fourierCoeffCLM k).continuous

instance (N : Set ℤ) : CompleteSpace (spectralSubspace T N) :=
  (isClosed_spectralSubspace N).completeSpace_coe

lemma fourier_mem_spectralSubspace_iff {N : Set ℤ} {k : ℤ} :
    fourier k ∈ spectralSubspace T N ↔ k ∈ N := by
  simp only [mem_spectralSubspace, fourierCoeff_fourier, Pi.single_apply]
  refine ⟨fun h ↦ by_contra fun hk ↦ by simpa using h k hk, fun hk j hj ↦ ?_⟩
  rw [ite_eq_right fun h : j = k ↦ hj (h ▸ hk)]

/-- The spaces `C_N(𝕋)` are invariant under translations. -/
lemma circleTranslate_mem_spectralSubspace {N : Set ℤ} (y : AddCircle T)
    {f : C(AddCircle T, ℂ)} (hf : f ∈ spectralSubspace T N) :
    circleTranslate y f ∈ spectralSubspace T N := fun k hk ↦ by
  rw [fourierCoeff_circleTranslate, hf k hk, mul_zero]

/-- A projection onto `C_N(𝕋)` that commutes with the translations acts on the characters as the
indicator function of `N`. -/
lemma IsProjectionOnto.apply_fourier_eq_indicator {N : Set ℤ}
    {Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)} (hQ : IsProjectionOnto (spectralSubspace T N) Q)
    (hQe : IsEquivariant circleTranslate Q) (k : ℤ) : Q (fourier k) = N.indicator fourier k := by
  by_cases hk : k ∈ N
  · rw [Set.indicator_of_mem hk, hQ.map_id _ (fourier_mem_spectralSubspace_iff.2 hk)]
  -- `Q eₖ = c eₖ` lies in `C_N(𝕋)`, so its `k`-th Fourier coefficient `c` vanishes
  have h := hQ.mem (fourier k) k hk
  rw [hQe.apply_fourier_eq_smul k] at h ⊢
  rw [← fourierCoeffCLM_apply, map_smul, fourierCoeffCLM_apply, fourierCoeff_fourier,
    Pi.single_eq_same, smul_eq_mul, mul_one] at h
  rw [h, zero_smul, Set.indicator_of_notMem hk]

/-- If `Q eⱼ = 1_N(j) eⱼ` for all `j`, then `(Q f)^(k) = 1_N(k) f̂(k)` for all `f`. -/
lemma fourierCoeff_apply_of_forall_apply_fourier {N : Set ℤ}
    {Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hQ : ∀ j, Q (fourier j) = N.indicator fourier j) (f : C(AddCircle T, ℂ)) (k : ℤ) :
    fourierCoeff (Q f) k = N.indicator (fourierCoeff f) k := by
  by_cases hk : k ∈ N
  · rw [Set.indicator_of_mem hk]
    have h : (fourierCoeffCLM k).comp Q = fourierCoeffCLM (T := T) k := by
      refine ContinuousLinearMap.ext_fourier fun j ↦ ?_
      rw [ContinuousLinearMap.comp_apply, hQ]
      by_cases hj : j ∈ N
      · rw [Set.indicator_of_mem hj]
      · rw [Set.indicator_of_notMem hj, map_zero, fourierCoeffCLM_apply, fourierCoeff_fourier,
          Pi.single_apply, ite_eq_right fun h : k = j ↦ hj (h ▸ hk)]
    exact congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] ℂ ↦ L f) h
  · rw [Set.indicator_of_notMem hk]
    have h : (fourierCoeffCLM k).comp Q = 0 := by
      refine ContinuousLinearMap.ext_fourier fun j ↦ ?_
      rw [ContinuousLinearMap.comp_apply, hQ, zero_apply]
      by_cases hj : j ∈ N
      · rw [Set.indicator_of_mem hj, fourierCoeffCLM_apply, fourierCoeff_fourier,
          Pi.single_apply, ite_eq_right fun h : k = j ↦ hk (h ▸ hj)]
      · rw [Set.indicator_of_notMem hj, map_zero]
    exact congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] ℂ ↦ L f) h

/-- **Rudin's reduction** [Ru, Theorem 2 and §4]: the space `C_N(𝕋)` is complemented in `C(𝕋)` if
and only if the indicator function of `N` is a bounded Fourier multiplier on `C(𝕋)`, i.e. there is
a bounded operator `Q` on `C(𝕋)` with `Q eₖ = eₖ` for `k ∈ N` and `Q eₖ = 0` for `k ∉ N`. The
"only if" direction is Rudin's averaging theorem
(`IsAddRepresentation.exists_isProjectionOnto_isEquivariant_of_compact`). -/
theorem exists_isProjectionOnto_spectralSubspace_iff (N : Set ℤ) :
    (∃ P, IsProjectionOnto (spectralSubspace T N) P) ↔
      ∃ Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ),
        ∀ k, Q (fourier k) = N.indicator fourier k := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ, hQe⟩ :=
      isAddRepresentation_circleTranslate.exists_isProjectionOnto_isEquivariant_of_compact
        continuous_circleTranslate (fun y _ hf ↦ circleTranslate_mem_spectralSubspace y hf) hP
    exact ⟨Q, hQ.apply_fourier_eq_indicator hQe⟩
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun f k hk ↦ ?_, fun f hf ↦ fourierCoeff_injective (funext fun k ↦
      show fourierCoeff (Q f) k = fourierCoeff f k from ?_)⟩
    · rw [fourierCoeff_apply_of_forall_apply_fourier hQ, Set.indicator_of_notMem hk]
    · rw [fourierCoeff_apply_of_forall_apply_fourier hQ]
      by_cases hk : k ∈ N
      · rw [Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem hk, hf k hk]

/-! ### Periodic sets -/

/-- Orthogonality of the characters of the cyclic group of order `p`:
`∑_{m < p} eⱼ(mT/p) = p` if `p ∣ j`, and `0` otherwise. -/
lemma sum_fourier_apply_nsmul {p : ℕ} (hp : 0 < p) (j : ℤ) :
    ∑ m ∈ range p, fourier j (m • ((T / p : ℝ) : AddCircle T)) =
      if (p : ℤ) ∣ j then (p : ℂ) else 0 := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.out.ne'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set z := fourier j ((T / p : ℝ) : AddCircle T)
  have hz (m : ℕ) : fourier j (m • ((T / p : ℝ) : AddCircle T)) = z ^ m := by
    simp only [z, fourier_apply, smul_comm j m, toCircle_nsmul, Circle.coe_pow]
  simp only [hz]
  have hzp : z ^ p = 1 := by
    rw [← hz, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by positivity),
      AddCircle.coe_period, fourier_eval_zero]
  have hz' : z = Complex.exp (j / p * (2 * Real.pi * Complex.I)) := by
    simp only [z, fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  split_ifs with hdvd
  · obtain ⟨q, rfl⟩ := hdvd
    have hz1 : z = 1 := by
      rw [hz', show ((p * q : ℤ) : ℂ) / p = q by push_cast; field_simp,
        Complex.exp_int_mul_two_pi_mul_I]
    simp [hz1]
  · have hz1 : z ≠ 1 := by
      rw [hz', Ne, Complex.exp_eq_one_iff]
      rintro ⟨q, hq⟩
      refine hdvd ⟨q, ?_⟩
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have h3 : (j : ℂ) = p * q := by
        have := mul_right_cancel₀ h2 hq
        field_simp at this
        linear_combination this
      exact_mod_cast h3
    have h := geom_sum_mul z p
    rw [hzp, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hz1)

variable (T) in
/-- The multiplier operator of the residue class `r + pℤ`:
`p⁻¹ ∑_{m < p} eᵣ(mT/p) τ_{mT/p}`. -/
def residueMultiplier (p : ℕ) (r : ℤ) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  (p : ℂ)⁻¹ • ∑ m ∈ range p,
    fourier r (m • ((T / p : ℝ) : AddCircle T)) • circleTranslate (m • ((T / p : ℝ) : AddCircle T))

lemma residueMultiplier_fourier {p : ℕ} (hp : 0 < p) (r k : ℤ) :
    residueMultiplier T p r (fourier k) = if (p : ℤ) ∣ r - k then fourier k else 0 := by
  have h : ∀ m : ℕ, fourier r (m • ((T / p : ℝ) : AddCircle T)) •
      circleTranslate (m • ((T / p : ℝ) : AddCircle T)) (fourier k) =
        fourier (r - k) (m • ((T / p : ℝ) : AddCircle T)) • fourier k := fun m ↦ by
    rw [circleTranslate_fourier, smul_smul, sub_eq_add_neg, fourier_add]
  simp only [residueMultiplier, smul_apply, _root_.sum_apply, h, ← Finset.sum_smul,
    sum_fourier_apply_nsmul hp, smul_smul]
  split_ifs
  · rw [inv_mul_cancel₀ (by exact_mod_cast hp.ne'), one_smul]
  · rw [mul_zero, zero_smul]

omit hT in
/-- A set of period `p` is invariant under all shifts by multiples of `p`. -/
lemma add_mul_mem_iff {N : Set ℤ} {p : ℤ} (hN : ∀ k, k + p ∈ N ↔ k ∈ N) (k q : ℤ) :
    k + p * q ∈ N ↔ k ∈ N := by
  induction q using Int.induction_on with
  | zero => simp
  | succ i ih => rw [show k + p * (i + 1) = k + p * i + p by ring, hN, ih]
  | pred i ih => rw [← hN, show k + p * (-i - 1) + p = k + p * -i by ring, ih]

/-- If `N` has period `p`, then `1_N` is a bounded Fourier multiplier on `C(𝕋)`. -/
lemma exists_apply_fourier_eq_indicator_of_periodic {N : Set ℤ} {p : ℕ} (hp : 0 < p)
    (hN : ∀ k : ℤ, k + p ∈ N ↔ k ∈ N) :
    ∃ Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ),
      ∀ k, Q (fourier k) = N.indicator fourier k := by
  classical
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  refine ⟨∑ r ∈ (Ico (0 : ℤ) p).filter (· ∈ N), residueMultiplier T p r, fun k ↦ ?_⟩
  -- the residue `r ∈ [0, p)` with `p ∣ r - k` is `k % p`
  have hres : ∀ r ∈ (Ico (0 : ℤ) p).filter (· ∈ N), ((p : ℤ) ∣ r - k ↔ r = k % p) := by
    intro r hr
    obtain ⟨hr0, hrp⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hr).1
    refine ⟨fun h ↦ ?_, ?_⟩
    · have h1 : k % p = r % p := Int.modEq_iff_dvd.2 h
      rw [h1, Int.emod_eq_of_lt hr0 hrp]
    · rintro rfl
      exact ⟨-(k / p), by rw [Int.emod_def]; ring⟩
  rw [_root_.sum_apply, Finset.sum_congr rfl fun r hr ↦ by
    rw [residueMultiplier_fourier hp, if_congr (hres r hr) rfl rfl], Finset.sum_ite_eq']
  have hmem : k % p ∈ (Ico (0 : ℤ) p).filter (· ∈ N) ↔ k ∈ N := by
    rw [Finset.mem_filter, Finset.mem_Ico,
      and_iff_right ⟨Int.emod_nonneg _ hp'.ne', Int.emod_lt_of_pos _ hp'⟩, Int.emod_def,
      sub_eq_add_neg, ← mul_neg, add_mul_mem_iff hN]
  by_cases hk : k ∈ N
  · rw [ite_eq_left (hmem.2 hk), Set.indicator_of_mem hk]
  · rw [ite_eq_right (mt hmem.1 hk), Set.indicator_of_notMem hk]

/-- Finite modifications of `N` preserve the existence of a bounded multiplier with symbol `1_N`. -/
lemma exists_apply_fourier_eq_indicator_of_finite {N N' : Set ℤ} (hfin : (symmDiff N N').Finite)
    {Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hQ : ∀ k, Q (fourier k) = N.indicator fourier k) :
    ∃ Q' : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ),
      ∀ k, Q' (fourier k) = N'.indicator fourier k := by
  classical
  let c : ℤ → ℂ := fun k ↦ N'.indicator 1 k - N.indicator 1 k
  -- the rank-one projections `f ↦ f̂(k) eₖ`
  let R : ℤ → C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
    fun k ↦ (fourierCoeffCLM k).smulRight (fourier k)
  refine ⟨Q + ∑ k ∈ hfin.toFinset, c k • R k, fun j ↦ ?_⟩
  have hsum : (∑ k ∈ hfin.toFinset, c k • R k) (fourier j) =
      if j ∈ hfin.toFinset then c j • fourier j else 0 := by
    simp only [_root_.sum_apply, smul_apply, R, ContinuousLinearMap.smulRight_apply,
      fourierCoeffCLM_apply, fourierCoeff_fourier, Pi.single_apply, ite_smul, one_smul, zero_smul,
      smul_ite, smul_zero]
    exact Finset.sum_ite_eq' _ _ _
  simp only [add_apply, hQ, hsum, Set.Finite.mem_toFinset]
  by_cases hj : j ∈ N <;> by_cases hj' : j ∈ N' <;>
    simp [c, hj, hj', Set.mem_symmDiff, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- **Rudin's theorem, "if" part** [Ru, Theorem 2 and §4]: if `N` differs from a periodic set in
finitely many places, then `C_N(𝕋)` is complemented in `C(𝕋)`. -/
theorem exists_isProjectionOnto_spectralSubspace_of_periodic {N N' : Set ℤ} {p : ℕ} (hp : 0 < p)
    (hN : ∀ k : ℤ, k + p ∈ N ↔ k ∈ N) (hfin : (symmDiff N N').Finite) :
    ∃ P, IsProjectionOnto (spectralSubspace T N') P := by
  obtain ⟨Q, hQ⟩ := exists_apply_fourier_eq_indicator_of_periodic (T := T) hp hN
  exact (exists_isProjectionOnto_spectralSubspace_iff N').2
    (exists_apply_fourier_eq_indicator_of_finite hfin hQ)

/-! ### The disc algebra -/

variable (T) in
/-- The disc algebra `A(𝕋) = C_ℕ(𝕋)` of continuous functions on the circle whose negative Fourier
coefficients vanish. -/
def discAlgebra : Submodule ℂ C(AddCircle T, ℂ) :=
  spectralSubspace T (Set.Ici 0)

/-- **The disc algebra is not complemented in `C(𝕋)`** [Ru, §4]: there is no bounded projection of
`C(𝕋)` onto `A(𝕋)`. If there were one, there would be a bounded multiplier `Q` with symbol `1_ℕ`
(`exists_isProjectionOnto_spectralSubspace_iff`), and then `Sₙ = e₋ₙ Q eₙ - eₙ₊₁ Q e₋₍ₙ₊₁₎`, so that
`Lₙ = ‖Sₙ‖ ≤ 2 ‖Q‖` for all `n`, which contradicts `Lₙ → ∞`. -/
theorem not_exists_isProjectionOnto_discAlgebra :
    ¬∃ P : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ), IsProjectionOnto (discAlgebra T) P := by
  rw [discAlgebra, exists_isProjectionOnto_spectralSubspace_iff]
  rintro ⟨Q, hQ⟩
  -- multiplication by the characters
  let M (k : ℤ) := ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ) (fourier k)
  have hM (k : ℤ) : ‖M k‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans (fourier_norm k).le
  have hMf (k j : ℤ) : M k (fourier j) = fourier (k + j) := by
    ext x
    rw [ContinuousLinearMap.mul_apply', ContinuousMap.mul_apply, fourier_add]
  have hQf (j : ℤ) : Q (fourier j) = if 0 ≤ j then fourier j else 0 := by
    rw [hQ]
    split_ifs with hj
    · exact Set.indicator_of_mem (Set.mem_Ici.2 hj) _
    · exact Set.indicator_of_notMem (fun h ↦ hj (Set.mem_Ici.1 h)) _
  -- `e₋ₙ Q eₙ` and `eₙ₊₁ Q e₋₍ₙ₊₁₎` are the multipliers with symbols `1_{[-n, ∞)}`, `1_{[n+1, ∞)}`
  have hA (n : ℕ) (j : ℤ) :
      (M (-n)).comp (Q.comp (M n)) (fourier j) = if -(n : ℤ) ≤ j then fourier j else 0 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hMf, hQf]
    by_cases h : -(n : ℤ) ≤ j
    · rw [ite_eq_left (show (0 : ℤ) ≤ n + j by omega), hMf, ite_eq_left h, neg_add_cancel_left]
    · rw [ite_eq_right (show ¬(0 : ℤ) ≤ n + j by omega), map_zero, ite_eq_right h]
  have hB (n : ℕ) (j : ℤ) : (M (n + 1)).comp (Q.comp (M (-(n + 1)))) (fourier j) =
      if (n : ℤ) + 1 ≤ j then fourier j else 0 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hMf, hQf]
    by_cases h : (n : ℤ) + 1 ≤ j
    · rw [ite_eq_left (show (0 : ℤ) ≤ -(n + 1) + j by omega), hMf, ite_eq_left h,
        add_neg_cancel_left]
    · rw [ite_eq_right (show ¬(0 : ℤ) ≤ -(n + 1) + j by omega), map_zero, ite_eq_right h]
  -- hence `Sₙ = e₋ₙ Q eₙ - eₙ₊₁ Q e₋₍ₙ₊₁₎`
  have hS (n : ℕ) : fourierPartialSum T n =
      (M (-n)).comp (Q.comp (M n)) - (M (n + 1)).comp (Q.comp (M (-(n + 1)))) := by
    refine ContinuousLinearMap.ext_fourier fun j ↦ ?_
    rw [fourierPartialSum_fourier, sub_apply, hA, hB]
    by_cases h₁ : -(n : ℤ) ≤ j <;> by_cases h₂ : (n : ℤ) + 1 ≤ j
    · rw [ite_eq_right (show j ∉ Icc (-(n : ℤ)) n by rw [Finset.mem_Icc]; omega),
        ite_eq_left h₁, ite_eq_left h₂, sub_self]
    · rw [ite_eq_left (show j ∈ Icc (-(n : ℤ)) n from Finset.mem_Icc.2 ⟨h₁, by omega⟩),
        ite_eq_left h₁, ite_eq_right h₂, sub_zero]
    · omega
    · rw [ite_eq_right (show j ∉ Icc (-(n : ℤ)) n by rw [Finset.mem_Icc]; omega),
        ite_eq_right h₁, ite_eq_right h₂, sub_zero]
  have hbound (n : ℕ) : lebesgueConst T n ≤ 2 * ‖Q‖ := by
    have hcomp (a b : ℤ) : ‖(M a).comp (Q.comp (M b))‖ ≤ ‖Q‖ :=
      calc ‖(M a).comp (Q.comp (M b))‖ ≤ ‖M a‖ * (‖Q‖ * ‖M b‖) :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ 1 * (‖Q‖ * 1) := by gcongr <;> exact hM _
        _ = ‖Q‖ := by ring
    rw [← norm_fourierPartialSum, hS]
    calc _ ≤ ‖(M (-n)).comp (Q.comp (M n))‖ + ‖(M (n + 1)).comp (Q.comp (M (-(n + 1))))‖ :=
          norm_sub_le _ _
      _ ≤ ‖Q‖ + ‖Q‖ := add_le_add (hcomp _ _) (hcomp _ _)
      _ = 2 * ‖Q‖ := by ring
  obtain ⟨n, hn⟩ := (tendsto_lebesgueConst_atTop (T := T)).eventually_gt_atTop (2 * ‖Q‖) |>.exists
  exact (hbound n).not_gt hn

end ProjectionConstants
