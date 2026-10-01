/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Fourier.Trigonometric
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Growth of the Lebesgue constants

The Lebesgue constants `Lₙ = ∫_𝕋 |Dₙ(t)| dt`, which are the projection constants
`λ(𝒯ₙ, C(𝕋))` of the trigonometric polynomials of degree at most `n`
(`ProjectionConstants.Fourier.Trigonometric`), grow logarithmically:

  `(4 / π²) log (n + 1) ≤ Lₙ ≤ 1 + log (2n + 1)`.

Both bounds come from the closed form `|sin(πx/T)| |Dₙ(x)| = |sin((2n + 1)πx/T)|` of the Dirichlet
kernel. For the lower bound, `sin t ≤ t` gives `|Dₙ(x)| ≥ (2n + 1) |sin((2n + 1)πx/T)| / (jπ)` on
the interval `[(j - 1)T/(2n + 1), jT/(2n + 1)]`, whose contribution to the integral is therefore at
least `2T/(jπ²)`; summing over `j ≤ n` gives the harmonic number `Hₙ ≥ log (n + 1)`. For the upper
bound, `|Dₙ| ≤ 2n + 1` near `0`, and `|Dₙ(x)| ≤ T/(2x)` on `(0, T/2]` by Jordan's inequality.
The first Lebesgue constant is computed from `D₁(x) = 1 + 2 cos(2πx/T)`.

Since `λ(𝒯ₙ, C(𝕋)) = Lₙ → ∞`, the uniform boundedness principle shows that no sequence of
projections `Pₙ` of `C(𝕋)` onto `𝒯ₙ` converges strongly to the identity (the theorem of
Kharshiladze and Lozinskiĭ, see [DGMMM, §1]); for the Fourier partial sums `Sₙ`, already the
functionals `f ↦ Sₙ f(0)` are unbounded, so some continuous function has a Fourier series that
diverges at `0` (du Bois-Reymond).

## Main statements

* `abs_sin_mul_norm_dirichletKernel`: `|sin(πx/T)| |Dₙ(x)| = |sin((2n + 1)πx/T)|`.
* `lebesgueConst_eq_intervalIntegral`: `Lₙ = T⁻¹ ∫_a^{a+T} |Dₙ(x)| dx`.
* `lebesgueConst_zero`, `lebesgueConst_one`: `L₀ = 1` and `L₁ = 1/3 + 2√3/π`, so that
  `λ(𝒯₁, C(𝕋)) = 1/3 + 2√3/π ≈ 1.436` (`relProjConst_trigPoly_one`).
* `four_div_pi_sq_mul_harmonic_le_lebesgueConst`, `four_div_pi_sq_mul_log_le_lebesgueConst`:
  `(4/π²) Hₙ ≤ Lₙ` and `(4/π²) log (n + 1) ≤ Lₙ`.
* `lebesgueConst_le_one_add_log`: `Lₙ ≤ 1 + log (2n + 1)`.
* `tendsto_lebesgueConst_atTop`, `tendsto_relProjConst_trigPoly_atTop`: `λ(𝒯ₙ, C(𝕋)) = Lₙ → ∞`.
* `exists_not_bddAbove_of_isProjectionOnto`, `exists_not_tendsto_of_isProjectionOnto`:
  **Kharshiladze–Lozinskiĭ**: for every sequence of projections `Pₙ` of `C(𝕋)` onto `𝒯ₙ` there is
  a continuous function `f` such that `‖Pₙ f‖` is unbounded; in particular `Pₙ f ↛ f`.
* `exists_not_bddAbove_fourierPartialSum_apply_zero`: **du Bois-Reymond**: there is a continuous
  function on the circle whose Fourier partial sums at `0` are unbounded.

## References

* [DGMMM] A. Defant, D. Galicer, M. Mansilla, M. Mastyło, S. Muro, *Projection constants for
  spaces of multivariate polynomials*, arXiv:2208.06467.
* [Zy] A. Zygmund, *Trigonometric series*, Vol. I, 2nd ed., Cambridge University Press, 1959.

## Tags

Lebesgue constant, Dirichlet kernel, trigonometric polynomials, projection constant, uniform
boundedness, divergent Fourier series
-/

open MeasureTheory AddCircle Finset Filter Real
open scoped Topology

noncomputable section

namespace ProjectionConstants

variable {T : ℝ}

/-! ### The closed form of the Dirichlet kernel -/

/-- `eₖ(x) = e₁(x)ᵏ`. -/
lemma fourier_apply_eq_zpow (k : ℤ) (x : AddCircle T) : fourier k x = fourier 1 x ^ k := by
  rw [fourier_apply, toCircle_zsmul, Circle.coe_zpow, fourier_one]

lemma fourier_one_apply_ne_zero (x : AddCircle T) : fourier 1 x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_fourier_apply]
  exact one_ne_zero

/-- `Dₙ(x) = e₁(x)⁻ⁿ ∑_{j < 2n+1} e₁(x)ʲ`. -/
lemma dirichletKernel_apply_eq_mul_sum (n : ℕ) (x : AddCircle T) :
    dirichletKernel T n x =
      fourier 1 x ^ (-(n : ℤ)) * ∑ j ∈ range (2 * n + 1), fourier 1 x ^ j := by
  rw [dirichletKernel_apply, Int.Icc_eq_finset_map, Finset.sum_map, Finset.mul_sum,
    show ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 by omega]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [fourier_apply_eq_zpow, zpow_add₀ (fourier_one_apply_ne_zero x), zpow_natCast]

/-- `|Dₙ(x)| ≤ 2n + 1`. -/
lemma norm_dirichletKernel_apply_le (n : ℕ) (x : AddCircle T) :
    ‖dirichletKernel T n x‖ ≤ 2 * n + 1 := by
  rw [dirichletKernel_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_fourier_apply, Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
  rw [show ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 by omega]
  push_cast
  rfl

/-- The closed form of the Dirichlet kernel: `|sin(πx/T)| |Dₙ(x)| = |sin((2n + 1)πx/T)|`. -/
lemma abs_sin_mul_norm_dirichletKernel (n : ℕ) (x : ℝ) :
    |sin (π * x / T)| * ‖dirichletKernel T n x‖ = |sin ((2 * n + 1) * (π * x / T))| := by
  set w : ℂ := fourier 1 (x : AddCircle T)
  have hw : w = Complex.exp (Complex.I * ((2 * π * x / T : ℝ) : ℂ)) := by
    simp only [w, fourier_coe_apply]
    push_cast
    congr 1
    ring
  -- `|w ^ m - 1| = 2 |sin(mπx/T)|`
  have key (m : ℕ) : ‖w ^ m - 1‖ = 2 * |sin (m * (π * x / T))| := by
    rw [hw, ← Complex.exp_nat_mul, show (m : ℂ) * (Complex.I * ((2 * π * x / T : ℝ) : ℂ)) =
      Complex.I * ((m * (2 * π * x / T) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    congr 3
    ring
  have hD : ‖dirichletKernel T n x‖ = ‖∑ j ∈ range (2 * n + 1), w ^ j‖ := by
    rw [dirichletKernel_apply_eq_mul_sum, norm_mul, norm_zpow, norm_fourier_apply, one_zpow,
      one_mul]
  have h := congrArg norm (geom_sum_mul w (2 * n + 1))
  rw [norm_mul, ← hD, key (2 * n + 1), ← pow_one w, key 1] at h
  push_cast at h
  rw [one_mul] at h
  linear_combination h / 2

/-! ### The Lebesgue constants as integrals over intervals -/

variable [hT : Fact (0 < T)]

/-- `Lₙ = T⁻¹ ∫_a^{a+T} |Dₙ(x)| dx`. -/
lemma lebesgueConst_eq_intervalIntegral (n : ℕ) (a : ℝ) :
    lebesgueConst T n = T⁻¹ * ∫ x in a..a + T, ‖dirichletKernel T n x‖ := by
  rw [lebesgueConst, integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T a,
    smul_eq_mul]

omit hT in
lemma continuous_norm_dirichletKernel_coe (n : ℕ) :
    Continuous fun x : ℝ ↦ ‖dirichletKernel T n x‖ :=
  ((dirichletKernel T n).continuous.comp (AddCircle.continuous_mk' T)).norm

/-- Since the Dirichlet kernel is even, `Lₙ = (2/T) ∫_0^{T/2} |Dₙ(x)| dx`. -/
lemma lebesgueConst_eq_two_div_mul_integral (n : ℕ) :
    lebesgueConst T n = 2 / T * ∫ x in (0 : ℝ)..T / 2, ‖dirichletKernel T n x‖ := by
  have hc (a b : ℝ) : IntervalIntegrable (fun x : ℝ ↦ ‖dirichletKernel T n x‖) volume a b :=
    (continuous_norm_dirichletKernel_coe n).intervalIntegrable a b
  have hsymm : ∫ x in -(T / 2)..0, ‖dirichletKernel T n x‖ =
      ∫ x in (0 : ℝ)..T / 2, ‖dirichletKernel T n x‖ := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := T / 2)
      (fun x : ℝ ↦ ‖dirichletKernel T n x‖)
    rw [neg_zero] at h
    rw [← h]
    congr 1
    ext x
    rw [AddCircle.coe_neg, dirichletKernel_neg]
  rw [lebesgueConst_eq_intervalIntegral n (-(T / 2)), show -(T / 2) + T = T / 2 by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (hc _ 0) (hc 0 _), hsymm]
  ring

omit hT in
@[simp] lemma dirichletKernel_zero : dirichletKernel T 0 = 1 := by
  ext x
  simp [dirichletKernel]

/-- `L₀ = 1`. -/
@[simp] lemma lebesgueConst_zero : lebesgueConst T 0 = 1 := by
  simp [lebesgueConst]

/-- `λ(𝒯₀, C(𝕋)) = 1`: the constants are `1`-complemented. -/
lemma relProjConst_trigPoly_zero : relProjConst (trigPoly T 0) = 1 := by
  rw [relProjConst_trigPoly, lebesgueConst_zero]

/-! ### The lower bound -/

omit hT in
/-- `∫_{jπ/c}^{(j+1)π/c} |sin(cx)| dx = 2/c`. -/
lemma integral_abs_sin_mul {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∫ x in j * π / c..(j + 1) * π / c, |sin (c * x)| = 2 / c := by
  have hper : Function.Periodic (fun x ↦ |sin x|) π := fun x ↦ by
    simp only [sin_add_pi, abs_neg]
  rw [intervalIntegral.integral_comp_mul_left (fun x ↦ |sin x|) hc.ne',
    show c * (j * π / c) = j * π by field_simp,
    show c * ((j + 1) * π / c) = j * π + π by field_simp,
    hper.intervalIntegral_add_eq (j * π) 0, zero_add,
    intervalIntegral.integral_congr (g := sin) fun x hx ↦ abs_of_nonneg <|
      sin_nonneg_of_nonneg_of_le_pi (by simpa [pi_pos.le] using hx.1)
        (by simpa [pi_pos.le] using hx.2),
    integral_sin, cos_zero, cos_pi, smul_eq_mul]
  field_simp
  ring

/-- The lower bound `(4/π²) Hₙ ≤ Lₙ`, where `Hₙ = ∑_{j=1}^n 1/j` is the `n`-th harmonic number. -/
theorem four_div_pi_sq_mul_harmonic_le_lebesgueConst (n : ℕ) :
    4 / π ^ 2 * harmonic n ≤ lebesgueConst T n := by
  have hT' := hT.out
  set D : ℝ → ℝ := fun x ↦ ‖dirichletKernel T n x‖
  have hDc : Continuous D := continuous_norm_dirichletKernel_coe n
  set c : ℝ := (2 * n + 1) * (π / T)
  have hc : 0 < c := by positivity
  set a : ℕ → ℝ := fun j ↦ j * π / c
  have ha (j : ℕ) : a j = j * T / (2 * n + 1) := by
    simp only [a, c]
    field_simp
  -- pointwise bound on the `(j + 1)`-th interval
  have hpt (j : ℕ) (hj : j < n) (x : ℝ) (hx : x ∈ Set.Icc (a j) (a (j + 1))) :
      (2 * n + 1) / ((j + 1) * π) * |sin (c * x)| ≤ D x := by
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have hx0 : 0 ≤ x := le_trans (by rw [ha]; positivity) hx.1
    have hx1 : x ≤ (j + 1) * T / (2 * n + 1) := by simpa [ha] using hx.2
    have hθ : π * x / T ≤ (j + 1) * π / (2 * n + 1) := by
      rw [div_le_div_iff₀ hT' (by positivity)]
      have := mul_le_mul_of_nonneg_left hx1 pi_pos.le
      rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
      nlinarith
    have hθπ : π * x / T ≤ π := hθ.trans <| by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
    have hs0 : 0 ≤ sin (π * x / T) := sin_nonneg_of_nonneg_of_le_pi (by positivity) hθπ
    have key := abs_sin_mul_norm_dirichletKernel (T := T) n x
    rw [abs_of_nonneg hs0] at key
    have hcx : c * x = (2 * n + 1) * (π * x / T) := by
      simp only [c]
      ring
    have hle : (2 * n + 1) / ((j + 1) * π) * sin (π * x / T) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      calc (2 * n + 1) * sin (π * x / T) ≤ (2 * n + 1) * ((j + 1) * π / (2 * n + 1)) := by
            gcongr
            exact (sin_le (by positivity)).trans hθ
        _ = (j + 1) * π := by field_simp
    rw [hcx, ← key]
    calc (2 * n + 1) / ((j + 1) * π) * (sin (π * x / T) * D x)
        = (2 * n + 1) / ((j + 1) * π) * sin (π * x / T) * D x := by ring
      _ ≤ 1 * D x := by gcongr
      _ = D x := one_mul _
  -- the integral over the `(j + 1)`-th interval
  have hint (j : ℕ) (hj : j < n) : 2 * T / ((j + 1) * π ^ 2) ≤ ∫ x in a j..a (j + 1), D x := by
    have hab : a j ≤ a (j + 1) := by
      simp only [a]
      gcongr
      linarith
    calc 2 * T / ((j + 1) * π ^ 2) = (2 * n + 1) / ((j + 1) * π) * (2 / c) := by
          simp only [c]
          field_simp
      _ = ∫ x in a j..a (j + 1), (2 * n + 1) / ((j + 1) * π) * |sin (c * x)| := by
          rw [intervalIntegral.integral_const_mul, ← integral_abs_sin_mul hc j]
          push_cast [a]
          rfl
      _ ≤ ∫ x in a j..a (j + 1), D x :=
          intervalIntegral.integral_mono_on hab
            (Continuous.intervalIntegrable (by fun_prop) _ _) (hDc.intervalIntegrable _ _)
            (hpt j hj)
  -- sum over the intervals
  have hsum : ∑ j ∈ range n, ∫ x in a j..a (j + 1), D x = ∫ x in a 0..a n, D x :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ hDc.intervalIntegrable _ _
  have hmono : ∫ x in a 0..a n, D x ≤ ∫ x in (0 : ℝ)..T / 2, D x := by
    refine intervalIntegral.integral_mono_interval (by simp [a]) (by rw [ha, ha]; gcongr; simp)
      ?_ (ae_of_all _ fun x ↦ norm_nonneg _) (hDc.intervalIntegrable _ _)
    rw [ha, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hH : (harmonic n : ℝ) = ∑ j ∈ range n, 1 / ((j : ℝ) + 1) := by
    simp [harmonic]
  rw [lebesgueConst_eq_two_div_mul_integral]
  calc 4 / π ^ 2 * harmonic n = 2 / T * ∑ j ∈ range n, 2 * T / ((j + 1) * π ^ 2) := by
        rw [hH, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        field_simp
        ring
    _ ≤ 2 / T * ∑ j ∈ range n, ∫ x in a j..a (j + 1), D x := by
        gcongr with j hj
        exact hint j (Finset.mem_range.1 hj)
    _ = 2 / T * ∫ x in a 0..a n, D x := by rw [hsum]
    _ ≤ 2 / T * ∫ x in (0 : ℝ)..T / 2, D x := by gcongr

/-- The classical lower bound `(4/π²) log (n + 1) ≤ Lₙ`. -/
theorem four_div_pi_sq_mul_log_le_lebesgueConst (n : ℕ) :
    4 / π ^ 2 * log (n + 1) ≤ lebesgueConst T n := by
  refine le_trans ?_ (four_div_pi_sq_mul_harmonic_le_lebesgueConst n)
  gcongr
  exact_mod_cast log_add_one_le_harmonic n

/-! ### The upper bound -/

/-- The upper bound `Lₙ ≤ 1 + log (2n + 1)`. -/
theorem lebesgueConst_le_one_add_log (n : ℕ) :
    lebesgueConst T n ≤ 1 + log (2 * n + 1) := by
  have hT' := hT.out
  set D : ℝ → ℝ := fun x ↦ ‖dirichletKernel T n x‖
  have hDc : Continuous D := continuous_norm_dirichletKernel_coe n
  set x₀ : ℝ := T / (2 * (2 * n + 1))
  have hx₀ : 0 < x₀ := by positivity
  have hx₀T : x₀ ≤ T / 2 := by
    simp only [x₀]
    rw [div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  -- near `0`, `|Dₙ| ≤ 2n + 1`
  have h₁ : ∫ x in (0 : ℝ)..x₀, D x ≤ (2 * n + 1) * x₀ := by
    calc ∫ x in (0 : ℝ)..x₀, D x ≤ ∫ x in (0 : ℝ)..x₀, (2 * n + 1 : ℝ) :=
          intervalIntegral.integral_mono_on hx₀.le (hDc.intervalIntegrable _ _)
            intervalIntegrable_const fun x _ ↦ norm_dirichletKernel_apply_le n x
      _ = (2 * n + 1) * x₀ := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  -- away from `0`, `|Dₙ(x)| ≤ T/(2x)` by Jordan's inequality
  have h₂ : ∫ x in x₀..T / 2, D x ≤ T / 2 * log (2 * n + 1) := by
    have hinv : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume x₀ (T / 2) :=
      intervalIntegral.intervalIntegrable_inv (fun x hx ↦ by
        rw [Set.uIcc_of_le hx₀T] at hx
        exact (hx₀.trans_le hx.1).ne') continuousOn_id
    calc ∫ x in x₀..T / 2, D x ≤ ∫ x in x₀..T / 2, T / 2 * x⁻¹ := by
          refine intervalIntegral.integral_mono_on hx₀T (hDc.intervalIntegrable _ _)
            (hinv.const_mul _) fun x hx ↦ ?_
          have hx0 : 0 < x := hx₀.trans_le hx.1
          have hθ : π * x / T ≤ π / 2 := by
            rw [div_le_div_iff₀ hT' two_pos]
            nlinarith [hx.2, pi_pos]
          have hjordan : 2 / π * (π * x / T) ≤ sin (π * x / T) :=
            mul_le_sin (by positivity) hθ
          have hs : 0 < sin (π * x / T) :=
            lt_of_lt_of_le (by positivity) hjordan
          have key := abs_sin_mul_norm_dirichletKernel (T := T) n x
          rw [abs_of_pos hs] at key
          have hDx : sin (π * x / T) * D x ≤ 1 := key ▸ abs_sin_le_one _
          have h2x : 2 * x / T ≤ sin (π * x / T) := by
            convert hjordan using 1
            field_simp
          calc D x ≤ 1 / sin (π * x / T) := by
                rw [le_div_iff₀ hs, mul_comm]
                exact hDx
            _ ≤ 1 / (2 * x / T) := by gcongr
            _ = T / 2 * x⁻¹ := by field_simp
      _ = T / 2 * log (2 * n + 1) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx₀ (by positivity)]
          congr 2
          simp only [x₀]
          field_simp
  rw [lebesgueConst_eq_two_div_mul_integral, ← intervalIntegral.integral_add_adjacent_intervals
    (hDc.intervalIntegrable 0 x₀) (hDc.intervalIntegrable x₀ (T / 2))]
  calc 2 / T * ((∫ x in (0 : ℝ)..x₀, D x) + ∫ x in x₀..T / 2, D x)
      ≤ 2 / T * ((2 * n + 1) * x₀ + T / 2 * log (2 * n + 1)) := by gcongr
    _ = 1 + log (2 * n + 1) := by
        simp only [x₀]
        field_simp

/-! ### The first Lebesgue constant -/

omit hT in
/-- `D₁(x) = 1 + 2 cos(2πx/T)`. -/
lemma dirichletKernel_one_apply_coe (x : ℝ) :
    dirichletKernel T 1 x = ((1 + 2 * cos (2 * π * x / T) : ℝ) : ℂ) := by
  have hI : Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ) = {-1, 0, 1} := by decide
  have h2 := Complex.two_cos ((2 * π * x / T : ℝ) : ℂ)
  rw [dirichletKernel_apply, hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, fourier_coe_apply, fourier_coe_apply, fourier_coe_apply]
  push_cast at h2 ⊢
  rw [show 2 * π * Complex.I * -1 * x / T = -(2 * π * x / T) * Complex.I by ring,
    show 2 * π * Complex.I * 0 * x / T = 0 by ring,
    show 2 * π * Complex.I * 1 * x / T = 2 * π * x / T * Complex.I by ring, Complex.exp_zero]
  linear_combination -h2

/-- The first Lebesgue constant: `L₁ = 1/3 + 2√3/π`. -/
theorem lebesgueConst_one : lebesgueConst T 1 = 1 / 3 + 2 * √3 / π := by
  have hT' := hT.out
  set f : ℝ → ℝ := fun u ↦ |1 + 2 * cos u|
  have hf : Continuous f := by fun_prop
  -- substitute `u = 2πx/T`
  have hsub : ∫ x in (0 : ℝ)..T / 2, ‖dirichletKernel T 1 x‖ =
      T / (2 * π) * ∫ u in (0 : ℝ)..π, f u := by
    have h := intervalIntegral.integral_comp_mul_left f (a := 0) (b := T / 2)
      (div_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hT'.ne')
    rw [mul_zero, show 2 * π / T * (T / 2) = π by field_simp, smul_eq_mul, inv_div] at h
    rw [← h]
    congr 1
    ext x
    rw [dirichletKernel_one_apply_coe, Complex.norm_real, Real.norm_eq_abs,
      show 2 * π / T * x = 2 * π * x / T by ring]
  -- the sign of `1 + 2 cos u` changes at `2π/3`
  have hcos : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have hsin : sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
  have h₁ : ∫ u in (0 : ℝ)..2 * π / 3, f u = 2 * π / 3 + √3 := by
    rw [intervalIntegral.integral_congr (g := fun u ↦ 1 + 2 * cos u) fun u hu ↦ ?_]
    · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_cos.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        integral_cos, hsin, sin_zero, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [Set.uIcc_of_le (by positivity)] at hu
    refine abs_of_nonneg ?_
    have := cos_le_cos_of_nonneg_of_le_pi hu.1 (by linarith [pi_pos]) hu.2
    linarith
  have h₂ : ∫ u in 2 * π / 3..π, f u = √3 - π / 3 := by
    rw [intervalIntegral.integral_congr (g := fun u ↦ -(1 + 2 * cos u)) fun u hu ↦ ?_]
    · rw [intervalIntegral.integral_neg, intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_cos.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        integral_cos, hsin, sin_pi, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hu
    refine abs_of_nonpos ?_
    have := cos_le_cos_of_nonneg_of_le_pi (by positivity) hu.2 hu.1
    linarith
  rw [lebesgueConst_eq_two_div_mul_integral, hsub,
    ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 (2 * π / 3))
      (hf.intervalIntegrable _ π), h₁, h₂]
  field_simp
  ring

/-- `λ(𝒯₁, C(𝕋)) = 1/3 + 2√3/π ≈ 1.436`. -/
theorem relProjConst_trigPoly_one : relProjConst (trigPoly T 1) = 1 / 3 + 2 * √3 / π := by
  rw [relProjConst_trigPoly, lebesgueConst_one]

/-! ### Unboundedness and its consequences -/

/-- The Lebesgue constants tend to infinity. -/
theorem tendsto_lebesgueConst_atTop : Tendsto (lebesgueConst T) atTop atTop := by
  refine tendsto_atTop_mono four_div_pi_sq_mul_log_le_lebesgueConst ?_
  refine Tendsto.const_mul_atTop (by positivity) (tendsto_log_atTop.comp ?_)
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- The projection constants `λ(𝒯ₙ, C(𝕋))` of the trigonometric polynomials tend to infinity. -/
theorem tendsto_relProjConst_trigPoly_atTop :
    Tendsto (fun n ↦ relProjConst (trigPoly T n)) atTop atTop := by
  simpa only [relProjConst_trigPoly] using tendsto_lebesgueConst_atTop

/-- **Kharshiladze–Lozinskiĭ**: for every sequence of projections `Pₙ` of `C(𝕋)` onto the
trigonometric polynomials `𝒯ₙ` of degree at most `n`, there is a continuous function `f` such that
`‖Pₙ f‖` is unbounded. Indeed `‖Pₙ‖ ≥ λ(𝒯ₙ, C(𝕋)) = Lₙ → ∞`, so this follows from the uniform
boundedness principle. -/
theorem exists_not_bddAbove_of_isProjectionOnto
    {P : ℕ → C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hP : ∀ n, IsProjectionOnto (trigPoly T n) (P n)) :
    ∃ f : C(AddCircle T, ℂ), ¬BddAbove (Set.range fun n ↦ ‖P n f‖) := by
  by_contra! h
  obtain ⟨C, hC⟩ := banach_steinhaus fun f ↦
    (h f).imp fun C hC n ↦ hC ⟨n, rfl⟩
  obtain ⟨n, hn⟩ := (tendsto_lebesgueConst_atTop (T := T)).eventually_gt_atTop C |>.exists
  have := (relProjConst_le _ (hP n)).trans (hC n)
  rw [relProjConst_trigPoly] at this
  linarith

/-- **Kharshiladze–Lozinskiĭ**: no sequence of projections `Pₙ` of `C(𝕋)` onto `𝒯ₙ` converges
strongly to the identity. -/
theorem exists_not_tendsto_of_isProjectionOnto
    {P : ℕ → C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hP : ∀ n, IsProjectionOnto (trigPoly T n) (P n)) :
    ∃ f : C(AddCircle T, ℂ), ¬Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by
  obtain ⟨f, hf⟩ := exists_not_bddAbove_of_isProjectionOnto hP
  exact ⟨f, fun h ↦ hf h.norm.bddAbove_range⟩

/-- **du Bois-Reymond**: there is a continuous function on the circle whose Fourier partial sums
at `0` are unbounded, because the functionals `f ↦ Sₙ f(0)` have norms `Lₙ → ∞`. -/
theorem exists_not_bddAbove_fourierPartialSum_apply_zero :
    ∃ f : C(AddCircle T, ℂ), ¬BddAbove (Set.range fun n ↦ ‖fourierPartialSum T n f 0‖) := by
  by_contra! h
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n ↦ (ContinuousMap.evalCLM ℂ (0 : AddCircle T)).comp (fourierPartialSum T n))
    fun f ↦ (h f).imp fun C hC n ↦ hC ⟨n, rfl⟩
  obtain ⟨n, hn⟩ := (tendsto_lebesgueConst_atTop (T := T)).eventually_gt_atTop C |>.exists
  have := hC n
  rw [norm_evalCLM_comp_fourierPartialSum] at this
  linarith

/-- **du Bois-Reymond**: there is a continuous function on the circle whose Fourier series
diverges at `0`. -/
theorem exists_not_tendsto_fourierPartialSum_apply_zero :
    ∃ f : C(AddCircle T, ℂ), ∀ z : ℂ, ¬Tendsto (fun n ↦ fourierPartialSum T n f 0) atTop (𝓝 z) := by
  obtain ⟨f, hf⟩ := exists_not_bddAbove_fourierPartialSum_apply_zero (T := T)
  exact ⟨f, fun z h ↦ hf h.norm.bddAbove_range⟩

end ProjectionConstants
