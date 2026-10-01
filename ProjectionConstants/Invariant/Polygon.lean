/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Invariant.Circulant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The projection constants of the regular polygons

Let `N ≥ 2`. The vectors `c = (cos(kπ/N))_k` and `s = (sin(kπ/N))_k`, `k ∈ ℤ/2N`, span a plane
`regularPolygon N` in `ℓ∞(ℤ/2N)`. The norm of `x₀ c + x₁ s` is
`max_k |x₀ cos(kπ/N) + x₁ sin(kπ/N)|`, so the unit ball of this plane is a regular `2N`-gon (its
sides lie on the lines `x₀ cos(kπ/N) + x₁ sin(kπ/N) = ±1`). Grünbaum [G, Theorem 1] computed its
projection constant for `N = 2ⁿ⁻¹`, and remarked that the hexagon (`N = 3`) has projection constant
`4/3` [G, §3]. We prove, for every `N ≥ 2`,

  `λ(regularPolygon N) = (2/N) ∑_{k<N} |cos(kπ/N)|`,

which equals `(2/N) cot(π/2N)` for even `N` and `2 / (N sin(π/2N))` for odd `N`.

The vectors `c` and `s` are orthogonal with `‖c‖₂² = ‖s‖₂² = N`, and the orthogonal projection onto
their span is the circulant matrix `P_{jk} = cos((j - k)π/N) / N`. By
`absProjConst_range_eq_sum_norm` it is a minimal projection, and
`λ = (1/N) ∑_{k ∈ ℤ/2N} |cos(kπ/N)|`.
The closed forms follow from the telescoping identity
`2 sin(α/2) ∑_{j<M} cos(jα + β) = sin((M - 1/2)α + β) + sin(α/2 - β)`.

## Main definitions

* `polygonMatrix N`: the `2N × 2` matrix with rows `(cos(kπ/N), sin(kπ/N))`, `k ∈ ℤ/2N`.
* `regularPolygon N`: the plane spanned by its columns, whose unit ball is a regular `2N`-gon.
* `polygonKernel N`: the function `k ↦ cos(kπ/N) / N` on `ℤ/2N`.

## Main statements

* `absProjConst_regularPolygon`: `λ(regularPolygon N) = (2/N) ∑_{k<N} |cos(kπ/N)|` for `N ≥ 2`.
* `absProjConst_regularPolygon_of_even`, `absProjConst_regularPolygon_of_odd`: the closed forms.
* `absProjConst_regularPolygon_two_pow`: **Grünbaum's theorem** [G, Theorem 1]: the plane whose
  unit ball is a regular `2ⁿ`-gon has projection constant `2²⁻ⁿ cot(2⁻ⁿπ)`.
* `absProjConst_regularPolygon_two`, `absProjConst_regularPolygon_three`,
  `absProjConst_regularPolygon_four`: the square, the hexagon and the octagon have projection
  constants `1`, `4/3` and `(1 + √2)/2`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.

## Tags

projection constant, regular polygon, Minkowski plane, circulant matrix
-/

open Real Finset Matrix

namespace ProjectionConstants

/-! ### Trigonometric sums -/

section Trigonometric

/-- **A telescoping sum of cosines**:
`2 sin(α/2) ∑_{j<M} cos(jα + β) = sin((M - 1/2)α + β) + sin(α/2 - β)`. -/
theorem two_mul_sin_mul_sum_range_cos (α β : ℝ) (M : ℕ) :
    2 * sin (α / 2) * ∑ j ∈ range M, cos (j * α + β) =
      sin ((M - 1 / 2) * α + β) + sin (α / 2 - β) := by
  induction M with
  | zero =>
    have h : ((0 : ℕ) - 1 / 2 : ℝ) * α + β = -(α / 2 - β) := by push_cast; ring
    rw [Finset.sum_range_zero, mul_zero, h, sin_neg, neg_add_cancel]
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := sin_sub_sin ((((M + 1 : ℕ) : ℝ) - 1 / 2) * α + β) (((M : ℝ) - 1 / 2) * α + β)
    have e₁ : ((((M + 1 : ℕ) : ℝ) - 1 / 2) * α + β - (((M : ℝ) - 1 / 2) * α + β)) / 2 = α / 2 := by
      push_cast; ring
    have e₂ : ((((M + 1 : ℕ) : ℝ) - 1 / 2) * α + β + (((M : ℝ) - 1 / 2) * α + β)) / 2 =
        M * α + β := by
      push_cast; ring
    rw [e₁, e₂] at h
    linarith

/-- `∑_{j<2N} cos(2πj/N + β) = 0` for `N ≥ 2`: the `N`-th roots of unity sum to zero. -/
theorem sum_range_cos_mul_two_pi_div_add {N : ℕ} (hN : 2 ≤ N) (β : ℝ) :
    ∑ j ∈ range (2 * N), cos (j * (2 * π / N) + β) = 0 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : sin (2 * π / N / 2) ≠ 0 := by
    rw [show 2 * π / N / 2 = π / N by ring]
    refine (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]
  have h := two_mul_sin_mul_sum_range_cos (2 * π / N) β (2 * N)
  have e : (((2 * N : ℕ) : ℝ) - 1 / 2) * (2 * π / N) + β =
      -(2 * π / N / 2 - β) + (2 : ℤ) * (2 * π) := by
    push_cast
    field_simp
    ring
  rw [e, sin_add_int_mul_two_pi, sin_neg, neg_add_cancel] at h
  exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero two_ne_zero hs)

/-- `∑_{k<N} |cos(kπ/N)| = sin((2⌊N/2⌋ + 1)π/2N) / sin(π/2N)` for `N ≥ 1`. -/
theorem sum_range_abs_cos {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range N, |cos (k * π / N)| =
      sin ((2 * (N / 2 : ℕ) + 1) * π / (2 * N)) / sin (π / (2 * N)) := by
  set M := N / 2 with hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2M : (2 * M : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * M ≤ N)
  have h2M' : (N : ℝ) ≤ 2 * M + 1 := by exact_mod_cast (by omega : N ≤ 2 * M + 1)
  -- rotate the angles into `[-π/2, π/2]`: `∑_{k<N} |cos(kπ/N)| = ∑_{j<N} cos((j - M)π/N)`
  have hrot : ∑ k ∈ range N, |cos (k * π / N)| =
      ∑ j ∈ range N, cos (j * (π / N) + -(M * (π / N))) := by
    have hsplit₁ := Finset.sum_range_add (fun k : ℕ ↦ |cos (k * π / N)|) (N - M) M
    rw [Nat.sub_add_cancel (by omega : M ≤ N)] at hsplit₁
    have hsplit₂ := Finset.sum_range_add (fun j : ℕ ↦ cos (j * (π / N) + -(M * (π / N)))) M (N - M)
    rw [Nat.add_sub_cancel' (by omega : M ≤ N)] at hsplit₂
    rw [hsplit₁, hsplit₂, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : (i : ℝ) + 1 ≤ M := by exact_mod_cast (mem_range.1 hi)
      have harg : ((N - M + i : ℕ) : ℝ) * π / N = (i * (π / N) + -(M * (π / N))) + π := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]
        field_simp
        ring
      rw [harg, cos_add_pi, abs_neg, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)]
      · have : (M : ℝ) * (π / N) ≤ π / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ hNr two_pos]
          nlinarith [pi_pos]
        have : 0 ≤ (i : ℝ) * (π / N) := by positivity
        linarith
      · have : (i : ℝ) * (π / N) ≤ M * (π / N) := by gcongr; exact (mem_range.1 hi).le
        linarith [pi_pos]
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : (2 * k : ℝ) + 1 ≤ N := by
        have := mem_range.1 hk
        exact_mod_cast (by omega : 2 * k + 1 ≤ N)
      have harg : ((M + k : ℕ) : ℝ) * (π / N) + -(M * (π / N)) = k * π / N := by
        push_cast
        ring
      rw [harg, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)]
      · have : 0 ≤ (k : ℝ) * π / N := by positivity
        linarith [pi_pos]
      · rw [div_le_div_iff₀ hNr two_pos]
        nlinarith [pi_pos]
  -- the telescoping sum
  have hs : 0 < sin (π / (2 * N)) := by
    refine sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [pi_pos]
  have h := two_mul_sin_mul_sum_range_cos (π / N) (-(M * (π / N))) N
  have e₁ : π / N / 2 = π / (2 * N) := by ring
  have e₂ : ((N : ℝ) - 1 / 2) * (π / N) + -(M * (π / N)) =
      π - (2 * M + 1) * π / (2 * N) := by
    field_simp
    ring
  have e₃ : π / (2 * N) - -(M * (π / N)) = (2 * M + 1) * π / (2 * N) := by
    field_simp
    ring
  rw [e₁, e₂, e₃, sin_pi_sub] at h
  rw [hrot, eq_div_iff hs.ne']
  linarith

end Trigonometric

/-! ### The regular polygon planes -/

/-- Sums over `ℤ/n` of functions of the representatives `0, …, n - 1`. -/
theorem sum_zmod_val {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k : ZMod n, f k.val = ∑ j ∈ range n, f j :=
  Finset.sum_nbij (·.val) (fun k _ ↦ mem_range.2 (ZMod.val_lt k))
    (fun _ _ _ _ h ↦ ZMod.val_injective n h)
    (fun j hj ↦ ⟨(j : ZMod n), mem_univ _, ZMod.val_natCast_of_lt (mem_range.1 hj)⟩)
    fun _ _ ↦ rfl

variable (N : ℕ)

/-- The `2N × 2` matrix with rows `(cos(kπ/N), sin(kπ/N))`, `k ∈ ℤ/2N`: the outer normals of the
sides of a regular `2N`-gon. -/
noncomputable def polygonMatrix : Matrix (ZMod (2 * N)) (Fin 2) ℝ :=
  Matrix.of fun k ↦ ![cos (k.val * π / N), sin (k.val * π / N)]

/-- The **regular `2N`-gon plane**: the span of `(cos(kπ/N))_k` and `(sin(kπ/N))_k` in
`ℓ∞(ℤ/2N)`. For `N ≥ 2` it is two-dimensional (`finrank_regularPolygon`), and the norm of
`polygonMatrix N *ᵥ x` is `max_k |x₀ cos(kπ/N) + x₁ sin(kπ/N)|` (`polygonMatrix_mulVec`), so its
unit ball is a regular `2N`-gon. -/
noncomputable def regularPolygon : Submodule ℝ (ZMod (2 * N) → ℝ) :=
  LinearMap.range (polygonMatrix N).toLin'

/-- The function `k ↦ cos(kπ/N) / N` on `ℤ/2N`: the orthogonal projection onto `regularPolygon N`
is `circulant (polygonKernel N)`. -/
noncomputable def polygonKernel (k : ZMod (2 * N)) : ℝ := cos (k.val * π / N) / N

/-- The coordinates of the vector `x₀ c + x₁ s ∈ regularPolygon N`. -/
@[simp] theorem polygonMatrix_mulVec (x : Fin 2 → ℝ) (k : ZMod (2 * N)) :
    (polygonMatrix N *ᵥ x) k = x 0 * cos (k.val * π / N) + x 1 * sin (k.val * π / N) := by
  simp [polygonMatrix, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

variable [NeZero N]

/-- `cos((a - b)π/N) = cos(aπ/N - bπ/N)` in `ℤ/2N`: the cosine has period `2π`. -/
theorem cos_val_sub_mul_pi_div (a b : ZMod (2 * N)) :
    cos ((a - b).val * π / N) = cos (a.val * π / N - b.val * π / N) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h : (((a - b).val : ℤ) : ZMod (2 * N)) = ((a.val - b.val : ℤ) : ZMod (2 * N)) := by
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
  have ht' : ((a.val : ℤ) - b.val - (a - b).val : ℝ) = 2 * N * t := by exact_mod_cast ht
  have e : (a - b).val * π / N = (a.val * π / N - b.val * π / N) + (-t : ℤ) * (2 * π) := by
    have h₁ : ((a - b).val : ℝ) = a.val - b.val - 2 * N * t := by push_cast at ht'; linarith
    rw [h₁]
    push_cast
    field_simp
    ring
  rw [e, cos_add_int_mul_two_pi]

/-- The orthogonal projection onto `regularPolygon N` is circulant:
`circulant (polygonKernel N) = N⁻¹ • M Mᵀ` for `M = polygonMatrix N`. -/
theorem circulant_polygonKernel :
    circulant (polygonKernel N) = (N : ℝ)⁻¹ • (polygonMatrix N * (polygonMatrix N)ᵀ) := by
  ext a b
  simp only [circulant_apply, polygonKernel, cos_val_sub_mul_pi_div, cos_sub, Matrix.smul_apply,
    mul_apply, transpose_apply, polygonMatrix, of_apply, Fin.sum_univ_two, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The columns of `polygonMatrix N` are orthogonal of squared length `N`, for `N ≥ 2`. -/
theorem polygonMatrix_transpose_mul_self (hN : 2 ≤ N) :
    (polygonMatrix N)ᵀ * polygonMatrix N = (N : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hc := sum_range_cos_mul_two_pi_div_add hN 0
  have hs := sum_range_cos_mul_two_pi_div_add hN (-(π / 2))
  simp only [add_zero] at hc
  -- the three sums `∑ cos², ∑ cos sin, ∑ sin²` over `k < 2N`
  have e₁ : ∀ j : ℕ, cos (j * π / N) * cos (j * π / N) = 1 / 2 + cos (j * (2 * π / N)) / 2 :=
    fun j ↦ by rw [← sq, cos_sq, show 2 * (j * π / N) = j * (2 * π / N) by ring]
  have e₂ : ∀ j : ℕ, sin (j * π / N) * sin (j * π / N) = 1 / 2 - cos (j * (2 * π / N)) / 2 :=
    fun j ↦ by rw [← sq, sin_sq, cos_sq, show 2 * (j * π / N) = j * (2 * π / N) by ring]; ring
  have e₃ : ∀ j : ℕ, cos (j * π / N) * sin (j * π / N) =
      cos (j * (2 * π / N) + -(π / 2)) / 2 := fun j ↦ by
    rw [← sub_eq_add_neg, cos_sub_pi_div_two,
      show j * (2 * π / N) = 2 * (j * π / N) by ring, sin_two_mul]
    ring
  ext i j
  simp only [mul_apply, transpose_apply, polygonMatrix, of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [sum_zmod_val (fun k ↦ ![cos (k * π / N), sin (k * π / N)] i *
    ![cos (k * π / N), sin (k * π / N)] j)]
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      cons_val_zero, cons_val_one, cons_val_fin_one, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, one_apply_eq, one_apply_ne, mul_one, mul_zero]
  · simp only [e₁, Finset.sum_add_distrib, ← Finset.sum_div, hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · simp only [e₃, ← Finset.sum_div, hs, zero_div]
  · simp only [mul_comm (sin _), e₃, ← Finset.sum_div, hs, zero_div]
  · simp only [e₂, Finset.sum_sub_distrib, ← Finset.sum_div, hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

/-- `regularPolygon N` is a plane for `N ≥ 2`. -/
theorem finrank_regularPolygon (hN : 2 ≤ N) : Module.finrank ℝ (regularPolygon N) = 2 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hinj := injective_toLin'_of_conjTranspose_mul_self (c := (N : ℝ)) hN0
    (by rw [conjTranspose_eq_transpose_of_trivial, polygonMatrix_transpose_mul_self N hN])
  rw [regularPolygon, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- **The projection constant of the regular `2N`-gon plane**:
`λ(regularPolygon N) = (2/N) ∑_{k<N} |cos(kπ/N)|` for `N ≥ 2`. -/
theorem absProjConst_regularPolygon (hN : 2 ≤ N) :
    absProjConst ℝ (regularPolygon N) = 2 / N * ∑ k ∈ range N, |cos (k * π / N)| := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [regularPolygon, absProjConst_range_eq_sum_norm (c := (N : ℝ)) hN0
    (by rw [conjTranspose_eq_transpose_of_trivial, polygonMatrix_transpose_mul_self N hN])
    (by rw [conjTranspose_eq_transpose_of_trivial, circulant_polygonKernel])]
  simp only [polygonKernel, Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rw [sum_zmod_val (fun k ↦ |cos (k * π / N)| / N), ← Finset.sum_div, two_mul,
    Finset.sum_range_add]
  -- `|cos((N + k)π/N)| = |cos(kπ/N)|`
  have h : ∀ k : ℕ, |cos (((N + k : ℕ) : ℝ) * π / N)| = |cos (k * π / N)| := fun k ↦ by
    rw [show ((N + k : ℕ) : ℝ) * π / N = k * π / N + π by push_cast; field_simp; ring,
      cos_add_pi, abs_neg]
  simp only [h]
  ring

/-- For even `N ≥ 2`: `λ(regularPolygon N) = (2/N) cot(π/2N)`. -/
theorem absProjConst_regularPolygon_of_even (hN : 2 ≤ N) (he : Even N) :
    absProjConst ℝ (regularPolygon N) = 2 / N * cot (π / (2 * N)) := by
  obtain ⟨t, rfl⟩ := he
  rw [absProjConst_regularPolygon _ hN, sum_range_abs_cos (by omega), cot_eq_cos_div_sin,
    show (t + t) / 2 = t by omega]
  congr 2
  rw [show (2 * (t : ℕ) + 1 : ℝ) * π / (2 * ((t + t : ℕ) : ℝ)) = π / (2 * ((t + t : ℕ) : ℝ)) + π / 2
    by have : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
       push_cast; field_simp; ring,
    sin_add_pi_div_two]

/-- For odd `N ≥ 3`: `λ(regularPolygon N) = 2 / (N sin(π/2N))`. -/
theorem absProjConst_regularPolygon_of_odd (hN : 2 ≤ N) (ho : Odd N) :
    absProjConst ℝ (regularPolygon N) = 2 / (N * sin (π / (2 * N))) := by
  obtain ⟨t, rfl⟩ := ho
  rw [absProjConst_regularPolygon _ hN, sum_range_abs_cos (by omega),
    show (2 * t + 1) / 2 = t by omega]
  rw [show (2 * (t : ℕ) + 1 : ℝ) * π / (2 * ((2 * t + 1 : ℕ) : ℝ)) = π / 2 by
    push_cast; field_simp, sin_pi_div_two]
  field_simp

/-- **Grünbaum's theorem** [G, Theorem 1]: for `n ≥ 2`, the plane whose unit ball is a regular
`2ⁿ`-gon has projection constant `2²⁻ⁿ cot(2⁻ⁿπ)`. -/
theorem absProjConst_regularPolygon_two_pow (n : ℕ) (hn : 2 ≤ n) :
    absProjConst ℝ (regularPolygon (2 ^ (n - 1))) = 4 / 2 ^ n * cot (π / 2 ^ n) := by
  have hN : 2 ≤ 2 ^ (n - 1) := Nat.le_self_pow (by omega) 2
  have he : Even (2 ^ (n - 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have h₂ : (2 : ℝ) * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  rw [absProjConst_regularPolygon_of_even _ hN he]
  push_cast
  rw [h₂, ← h₂]
  field_simp
  ring

/-- The square: `λ(regularPolygon 2) = λ(ℓ∞²) = 1`. -/
theorem absProjConst_regularPolygon_two : absProjConst ℝ (regularPolygon 2) = 1 := by
  rw [absProjConst_regularPolygon 2 le_rfl]
  simp [Finset.sum_range_succ, cos_pi_div_two]

/-- **The regular hexagon** [G, §3, Remark (ii)]: `λ(regularPolygon 3) = 4/3`. -/
theorem absProjConst_regularPolygon_three : absProjConst ℝ (regularPolygon 3) = 4 / 3 := by
  rw [absProjConst_regularPolygon_of_odd 3 (by norm_num) (by decide)]
  rw [show π / (2 * ((3 : ℕ) : ℝ)) = π / 6 by push_cast; ring, sin_pi_div_six]
  norm_num

/-- The regular octagon (Grünbaum's theorem for `n = 3`): `λ(regularPolygon 4) = (1 + √2)/2`. -/
theorem absProjConst_regularPolygon_four :
    absProjConst ℝ (regularPolygon 4) = (1 + √2) / 2 := by
  rw [absProjConst_regularPolygon 4 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, zero_mul,
    zero_div, cos_zero, abs_one]
  have h1 : cos ((1 : ℕ) * π / (4 : ℕ)) = √2 / 2 := by
    rw [show ((1 : ℕ) : ℝ) * π / (4 : ℕ) = π / 4 by push_cast; ring, cos_pi_div_four]
  have h2 : cos ((2 : ℕ) * π / (4 : ℕ)) = 0 := by
    rw [show ((2 : ℕ) : ℝ) * π / (4 : ℕ) = π / 2 by push_cast; ring, cos_pi_div_two]
  have h3 : cos ((3 : ℕ) * π / (4 : ℕ)) = -(√2 / 2) := by
    rw [show ((3 : ℕ) : ℝ) * π / (4 : ℕ) = π / 4 + π / 2 by push_cast; ring, cos_add_pi_div_two,
      sin_pi_div_four]
  have hs : (0 : ℝ) ≤ √2 / 2 := by positivity
  rw [h1, h2, h3, abs_neg, abs_zero, abs_of_nonneg hs]
  push_cast
  ring

end ProjectionConstants
