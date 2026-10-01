/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Euclidean.Formula
import ProjectionConstants.Euclidean.Polar
import ProjectionConstants.Invariant.L1
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The projection constants of `ℓ₂ⁿ(ℝ)` and `ℓ₂ⁿ(ℂ)`

We compute the absolute projection constant of `𝕜ⁿ` with the Euclidean norm, for `𝕜 = ℝ` or
`ℂ`, from the spherical-mean formula `absProjConst_euclideanSpace_eq`
(`ProjectionConstants.Euclidean.Formula`). This gives the formulas of Grünbaum [G] and
Rutovitz [R].

## Main definitions

* `Euclidean.lebesgue 𝕜 n`: the Lebesgue measure on `𝕜ⁿ`, transported from `Fin n → 𝕜`.

## Main statements

* `absProjConst_euclideanSpace`: with `d = dim_ℝ 𝕜`,
  `λ(𝕜ⁿ) = n Γ((d+1)/2) Γ(dn/2) / (Γ(d/2) Γ((dn+1)/2))`.
* `absProjConst_euclideanSpace_real`: `λ(ℓ₂ⁿ(ℝ)) = 2 Γ(n/2 + 1) / (√π Γ((n+1)/2))` ([G], [R]);
  `absProjConst_euclideanSpace_real_eq_grunbaum` is the same formula in the form
  `n Γ(n/2) / (√π Γ((n+1)/2))` of [G, Theorem 4].
* `absProjConst_euclideanSpace_complex`: `λ(ℓ₂ⁿ(ℂ)) = (√π / 2) n! / Γ(n + 1/2)` [R].
* `absProjConst_euclideanSpace_real_one`, `absProjConst_euclideanSpace_real_two`,
  `absProjConst_euclideanSpace_real_three`, `absProjConst_euclideanSpace_complex_one`,
  `absProjConst_euclideanSpace_complex_two`: the values `λ(ℓ₂¹) = 1`, `λ(ℓ₂²(ℝ)) = 4/π`,
  `λ(ℓ₂³(ℝ)) = 3/2` and `λ(ℓ₂²(ℂ)) = 4/3`.
* `absProjConst_euclideanSpace_real_odd`: `λ(ℓ₂²ᵐ⁺¹(ℝ)) = (2m + 1) C(2m, m) / 4ᵐ`.
* `absProjConst_euclideanSpace_real_odd_eq_l1`: `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹)`, the remark in
  [G, §5] (Grünbaum proved `λ(ℓ₂ⁿ(ℝ)) ≤ rₙ` and observed `r₂ₘ₋₁ = λ(ℓ₁²ᵐ⁻¹)`).

## Proof sketch

By `absProjConst_euclideanSpace_eq`, `λ(𝕜ⁿ) = n ∫ |⟪u, e⟫| dσ / σ(S)` for the surface measure
`σ = μ.toSphere` of the Lebesgue measure `μ` of `𝕜ⁿ` (invariant by
`Euclidean.isInvariant_toSphere`) and `e = (1, 0, …, 0)`. By `Euclidean.mean_eq_gaussian` the
mean is `(∫ |x₁| e^{-‖x‖²} dμ / ∫ e^{-‖x‖²} dμ) Γ(dn/2) / Γ((dn+1)/2)`, and by Fubini the ratio
of the Gaussian integrals is `∫_𝕜 |t| e^{-|t|²} dt / ∫_𝕜 e^{-|t|²} dt = Γ((d+1)/2) / Γ(d/2)`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960).
* [R] D. Rutovitz, *Some parameters associated with finite-dimensional Banach spaces*,
  J. London Math. Soc. 40 (1965).

## Tags

projection constant, Euclidean space, Gamma function
-/

open MeasureTheory Metric Set Real
open scoped InnerProductSpace Nat

namespace ProjectionConstants.Euclidean

section Generic

variable {𝕜 : Type} [RCLike 𝕜] [MeasureSpace 𝕜] [BorelSpace 𝕜]
  [(volume : Measure 𝕜).IsAddHaarMeasure]

/-- `∫_𝕜 |t|ᵏ e^{-|t|²} dt = d ω Γ((d + k)/2) / 2`, where `d = dim_ℝ 𝕜` and `ω` is the volume of
the unit ball of `𝕜`. -/
lemma integral_norm_pow_mul_exp (k : ℕ) :
    ∫ t : 𝕜, ‖t‖ ^ k * exp (-‖t‖ ^ 2) =
      Module.finrank ℝ 𝕜 * (volume : Measure 𝕜).real (ball 0 1) *
        (Gamma (((Module.finrank ℝ 𝕜 : ℝ) + k) / 2) / 2) := by
  rw [integral_fun_norm_addHaar (volume : Measure 𝕜) (fun r ↦ r ^ k * exp (-r ^ 2))]
  have hd : 0 < Module.finrank ℝ 𝕜 := Module.finrank_pos
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ 𝕜 - 1) • (y ^ k * exp (-y ^ 2)) =
      ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ 𝕜 - 1 + k) * exp (-y ^ 2) := by
    congr 1
    ext y
    rw [smul_eq_mul, pow_add]
    ring
  have h2 : ((Module.finrank ℝ 𝕜 - 1 + k : ℕ) : ℝ) + 1 = Module.finrank ℝ 𝕜 + k := by
    rw [Nat.cast_add, Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [h1, integral_pow_mul_exp_neg_sq, h2, nsmul_eq_mul, smul_eq_mul]
  ring

variable (𝕜) in
/-- The Lebesgue measure on `𝕜ⁿ`, transported from `Fin n → 𝕜`. -/
noncomputable def lebesgue (n : ℕ) : Measure (EuclideanSpace 𝕜 (Fin n)) :=
  Measure.map (MeasurableEquiv.toLp 2 (Fin n → 𝕜)) volume

/-- `lebesgue 𝕜 n` is an additive Haar measure. -/
instance (n : ℕ) : (lebesgue 𝕜 n).IsAddHaarMeasure :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ 𝕜)).symm.isAddHaarMeasure_map volume

omit [RCLike 𝕜] [BorelSpace 𝕜] [(volume : Measure 𝕜).IsAddHaarMeasure] in
/-- Integrals against `lebesgue 𝕜 n` are integrals over `Fin n → 𝕜`. -/
lemma integral_lebesgue {n : ℕ} (f : EuclideanSpace 𝕜 (Fin n) → ℝ) :
    ∫ x, f x ∂lebesgue 𝕜 n = ∫ y : Fin n → 𝕜, f (WithLp.toLp 2 y) :=
  integral_map_equiv _ f

omit [MeasureSpace 𝕜] [BorelSpace 𝕜] [(volume : Measure 𝕜).IsAddHaarMeasure] in
/-- `e^{-‖x‖²} = ∏ᵢ e^{-|xᵢ|²}` in `𝕜ⁿ`. -/
lemma exp_neg_norm_sq_toLp {n : ℕ} (y : Fin n → 𝕜) :
    exp (-‖WithLp.toLp 2 y‖ ^ 2) = ∏ i, exp (-‖y i‖ ^ 2) := by
  rw [norm_sq_eq_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

omit [BorelSpace 𝕜] in
/-- `∫_{𝕜ⁿ} e^{-‖x‖²} dx = (∫_𝕜 e^{-|t|²} dt)ⁿ`. -/
lemma integral_exp_neg_norm_sq (n : ℕ) :
    ∫ x, exp (-‖x‖ ^ 2) ∂lebesgue 𝕜 n = (∫ t : 𝕜, exp (-‖t‖ ^ 2)) ^ n := by
  rw [integral_lebesgue]
  simp_rw [exp_neg_norm_sq_toLp]
  rw [integral_fintype_prod_volume_eq_pow (fun t : 𝕜 ↦ exp (-‖t‖ ^ 2)), Fintype.card_fin]

omit [BorelSpace 𝕜] in
/-- `∫_{𝕜ⁿ} |x₁| e^{-‖x‖²} dx = (∫_𝕜 |t| e^{-|t|²} dt) (∫_𝕜 e^{-|t|²} dt)ⁿ⁻¹`. -/
lemma integral_norm_inner_single_mul_exp (m : ℕ) :
    ∫ x, ‖⟪x, EuclideanSpace.single 0 (1 : 𝕜)⟫_𝕜‖ * exp (-‖x‖ ^ 2) ∂lebesgue 𝕜 (m + 1) =
      (∫ t : 𝕜, ‖t‖ * exp (-‖t‖ ^ 2)) * (∫ t : 𝕜, exp (-‖t‖ ^ 2)) ^ m := by
  rw [integral_lebesgue]
  let g : Fin (m + 1) → 𝕜 → ℝ := fun i t ↦ (if i = 0 then ‖t‖ else 1) * exp (-‖t‖ ^ 2)
  have h : ∀ y : Fin (m + 1) → 𝕜,
      ‖⟪WithLp.toLp 2 y, EuclideanSpace.single 0 (1 : 𝕜)⟫_𝕜‖ * exp (-‖WithLp.toLp 2 y‖ ^ 2) =
        ∏ i, g i (y i) := by
    intro y
    rw [EuclideanSpace.inner_single_right, one_mul, RCLike.norm_conj, exp_neg_norm_sq_toLp,
      Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ 0 (fun i ↦ ‖y i‖)]
    simp
  simp_rw [h]
  rw [integral_fintype_prod_volume_eq_prod, Fin.prod_univ_succ]
  simp [g, Fin.succ_ne_zero]

end Generic

end ProjectionConstants.Euclidean

namespace ProjectionConstants

open Euclidean

section Generic

variable {𝕜 : Type} [RCLike 𝕜] [MeasureSpace 𝕜] [BorelSpace 𝕜]
  [(volume : Measure 𝕜).IsAddHaarMeasure]

/-- **The projection constant of `𝕜ⁿ`.** With `d = dim_ℝ 𝕜`,
`λ(𝕜ⁿ) = n Γ((d+1)/2) Γ(dn/2) / (Γ(d/2) Γ((dn+1)/2))`. -/
theorem absProjConst_euclideanSpace (n : ℕ) [NeZero n] :
    absProjConst 𝕜 (EuclideanSpace 𝕜 (Fin n)) =
      n * (Gamma (((Module.finrank ℝ 𝕜 : ℝ) + 1) / 2) / Gamma ((Module.finrank ℝ 𝕜 : ℝ) / 2)) *
        (Gamma ((Module.finrank ℝ 𝕜 : ℝ) * n / 2) /
          Gamma (((Module.finrank ℝ 𝕜 : ℝ) * n + 1) / 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have he : ‖EuclideanSpace.single (0 : Fin (m + 1)) (1 : 𝕜)‖ = 1 := by simp
  rw [absProjConst_euclideanSpace_eq (isInvariant_toSphere (lebesgue 𝕜 (m + 1)))
    (Measure.toSphere_ne_zero _) he, mul_div_assoc, mean_eq_gaussian,
    integral_norm_inner_single_mul_exp, integral_exp_neg_norm_sq,
    ← Module.finrank_mul_finrank ℝ 𝕜 (EuclideanSpace 𝕜 (Fin (m + 1))),
    finrank_euclideanSpace_fin]
  have hA₀ := integral_norm_pow_mul_exp (𝕜 := 𝕜) 0
  have hA₁ := integral_norm_pow_mul_exp (𝕜 := 𝕜) 1
  simp only [pow_zero, one_mul, pow_one, Nat.cast_zero, add_zero, Nat.cast_one] at hA₀ hA₁
  rw [hA₀, hA₁]
  have hd : (0 : ℝ) < Module.finrank ℝ 𝕜 := by exact_mod_cast Module.finrank_pos
  have hω : 0 < (volume : Measure 𝕜).real (ball 0 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' measure_ball_lt_top.ne
  have hg : 0 < Gamma ((Module.finrank ℝ 𝕜 : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hg' : 0 < Gamma (((Module.finrank ℝ 𝕜 : ℝ) * (m + 1 : ℕ) + 1) / 2) :=
    Gamma_pos_of_pos (by positivity)
  push_cast
  field_simp
  ring

end Generic

/-! ### The real and complex cases -/

/-- **Grünbaum's formula** ([G]; see also [R]): `λ(ℓ₂ⁿ(ℝ)) = 2 Γ(n/2 + 1) / (√π Γ((n+1)/2))`. -/
theorem absProjConst_euclideanSpace_real (n : ℕ) [NeZero n] :
    absProjConst ℝ (EuclideanSpace ℝ (Fin n)) =
      2 * Gamma (n / 2 + 1) / (√π * Gamma ((n + 1) / 2)) := by
  rw [absProjConst_euclideanSpace, Module.finrank_self]
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [Gamma_add_one (by positivity : (n : ℝ) / 2 ≠ 0)]
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  have hg : 0 < Gamma (((n : ℝ) + 1) / 2) := Gamma_pos_of_pos (by positivity)
  norm_num [Gamma_one_half_eq]
  field_simp

/-- **Rutovitz's formula** [R]: `λ(ℓ₂ⁿ(ℂ)) = (√π / 2) n! / Γ(n + 1/2)`. -/
theorem absProjConst_euclideanSpace_complex (n : ℕ) [NeZero n] :
    absProjConst ℂ (EuclideanSpace ℂ (Fin n)) = √π / 2 * n ! / Gamma (n + 1 / 2) := by
  rw [absProjConst_euclideanSpace, Complex.finrank_real_complex]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h1 : (((2 : ℕ) : ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
  have h2 : ((2 : ℕ) : ℝ) / 2 = 1 := by norm_num
  have h3 : ((2 : ℕ) : ℝ) * n / 2 = n := by push_cast; ring
  have h4 : (((2 : ℕ) : ℝ) * n + 1) / 2 = n + 1 / 2 := by push_cast; ring
  have hfact : (n : ℝ) * Gamma n = n ! := by
    rw [← Gamma_add_one hn, Gamma_nat_eq_factorial]
  have hg : 0 < Gamma ((n : ℝ) + 1 / 2) := Gamma_pos_of_pos (by positivity)
  rw [h1, h2, h3, h4, Gamma_add_one (by norm_num), Gamma_one_half_eq, Gamma_one, ← hfact]
  field_simp

/-! ### Special values -/

private lemma Gamma_three_halves : Gamma (3 / 2) = √π / 2 := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq]
  ring

private lemma Gamma_five_halves : Gamma (5 / 2) = 3 * √π / 4 := by
  rw [show (5 : ℝ) / 2 = 3 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_three_halves]
  ring

/-- `λ(ℓ₂¹(ℝ)) = 1`. -/
theorem absProjConst_euclideanSpace_real_one : absProjConst ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by
  rw [absProjConst_euclideanSpace_real]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  norm_num [Gamma_three_halves]
  field_simp

/-- `λ(ℓ₂²(ℝ)) = 4/π`. -/
theorem absProjConst_euclideanSpace_real_two :
    absProjConst ℝ (EuclideanSpace ℝ (Fin 2)) = 4 / π := by
  rw [absProjConst_euclideanSpace_real]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  norm_num [Gamma_three_halves]
  field_simp
  rw [sq_sqrt pi_pos.le]
  ring

/-- `λ(ℓ₂³(ℝ)) = 3/2`. -/
theorem absProjConst_euclideanSpace_real_three :
    absProjConst ℝ (EuclideanSpace ℝ (Fin 3)) = 3 / 2 := by
  rw [absProjConst_euclideanSpace_real]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  norm_num [Gamma_five_halves]
  field_simp
  ring

/-- `λ(ℓ₂¹(ℂ)) = 1`. -/
theorem absProjConst_euclideanSpace_complex_one :
    absProjConst ℂ (EuclideanSpace ℂ (Fin 1)) = 1 := by
  rw [absProjConst_euclideanSpace_complex]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  norm_num [Gamma_three_halves]
  exact hs.ne'

/-- `λ(ℓ₂²(ℂ)) = 4/3`. -/
theorem absProjConst_euclideanSpace_complex_two :
    absProjConst ℂ (EuclideanSpace ℂ (Fin 2)) = 4 / 3 := by
  rw [absProjConst_euclideanSpace_complex]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  norm_num [Gamma_five_halves]
  field_simp

/-! ### Grünbaum's form of the formula and odd dimensions -/

/-- **Grünbaum's form** of the formula for `λ(ℓ₂ⁿ(ℝ))` [G, Theorem 4]:
`λ(ℓ₂ⁿ(ℝ)) = n Γ(n/2) / (√π Γ((n+1)/2))`. Grünbaum proved the upper bound and conjectured
equality; equality is due to Rutovitz [R]. -/
theorem absProjConst_euclideanSpace_real_eq_grunbaum (n : ℕ) [NeZero n] :
    absProjConst ℝ (EuclideanSpace ℝ (Fin n)) =
      n * Gamma (n / 2) / (√π * Gamma ((n + 1) / 2)) := by
  have hn : (n : ℝ) / 2 ≠ 0 := div_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne n)) two_ne_zero
  rw [absProjConst_euclideanSpace_real, Gamma_add_one hn]
  ring

/-- `Γ(m + 1/2) = (2m)! √π / (4ᵐ m!)`. -/
lemma Gamma_nat_add_half (m : ℕ) : Gamma (m + 1 / 2) = (2 * m)! * √π / (4 ^ m * m !) := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_add, Gamma_one_half_eq]; simp
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) + 1 / 2 = (m + 1 / 2) + 1 by push_cast; ring,
      Gamma_add_one (by positivity), ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `λ(ℓ₂²ᵐ⁺¹(ℝ)) = (2m + 1) C(2m, m) / 4ᵐ`. -/
theorem absProjConst_euclideanSpace_real_odd (m : ℕ) :
    absProjConst ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) =
      (2 * m + 1) * (2 * m).choose m / 4 ^ m := by
  rw [absProjConst_euclideanSpace_real]
  have h₁ : ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = ((m + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
  have h₂ : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [h₁, h₂, Gamma_nat_add_half, Gamma_nat_eq_factorial]
  have hc := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
  rw [show 2 * m - m = m by omega] at hc
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, ← hc]
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  push_cast
  field_simp
  ring

/-- `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹)`: the remark in [G, §5], combined with Rutovitz's theorem [R]. -/
theorem absProjConst_euclideanSpace_real_odd_eq_l1 (m : ℕ) :
    absProjConst ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) =
      absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 1) ↦ ℝ) := by
  rw [absProjConst_euclideanSpace_real_odd, absProjConst_l1, show 2 * m + 1 - 1 = 2 * m by omega,
    show 2 * m / 2 = m by omega, pow_mul]
  norm_num

end ProjectionConstants
