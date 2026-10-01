/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.SignMatrix
import ProjectionConstants.ForMathlib.Real

/-!
# Stationarity of maximizing orthonormal pairs

If an orthonormal pair `u, v` maximizes `xᵀAx + yᵀAy` among all orthonormal pairs, then the
plane spanned by `u, v` is invariant under the symmetric matrix `A`. This is the part of the
equality case of Fan's maximum principle that we need (cf. [AMOP, Lemma 3.1]).

To see this, let `z` be orthogonal to `u` and `v`, and replace `u` by the unit vector
`x = (u + t z) / √(1 + t² ‖z‖²)`. The pair `x, v` is again orthonormal, and comparing its value
with the value at `u, v` gives `2t zᵀAu + t² c ≤ 0` for all `t` and a constant `c`, hence
`zᵀAu = 0`.

## Main statements

* `dotProduct_mulVec_eq_zero_of_fanValue_le`: stationarity, `zᵀAu = 0` whenever `z ⊥ u, v`.
* `mulVec_apply_eq_of_fanValue_le`, `mulVec_apply_eq_of_fanValue_le'`: invariance,
  `Au = (uᵀAu) u + (vᵀAu) v` and `Av = (uᵀAv) u + (vᵀAv) v`.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants

variable {ι : Type*} [Fintype ι]

/-- **Stationarity.** If `u, v` maximizes `xᵀAx + yᵀAy` and `z ⊥ u, v`, then `z ⊥ Au`. -/
theorem dotProduct_mulVec_eq_zero_of_fanValue_le {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {u v : ι → ℝ} (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) {z : ι → ℝ}
    (hzu : z ⬝ᵥ u = 0) (hzv : z ⬝ᵥ v = 0) : z ⬝ᵥ A *ᵥ u = 0 := by
  set n := z ⬝ᵥ z with hn_def
  have hn0 : 0 ≤ n := dotProduct_self_nonneg z
  refine eq_zero_of_forall_quadratic_nonpos (c := z ⬝ᵥ A *ᵥ z - (u ⬝ᵥ A *ᵥ u) * n) fun t ↦ ?_
  -- the unit vector `x = (u + t z) / √(1 + t² n)`
  have hpos : 0 < 1 + t ^ 2 * n := by positivity
  set s := 1 / Real.sqrt (1 + t ^ 2 * n) with hs_def
  have hs2 : s ^ 2 = 1 / (1 + t ^ 2 * n) := by
    rw [hs_def, div_pow, Real.sq_sqrt hpos.le, one_pow]
  set x : ι → ℝ := fun i ↦ s * u i + (s * t) * z i with hx_def
  have hux : u ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact hzu
  have hvz : v ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact hzv
  have hxx : x ⬝ᵥ x = 1 := by
    rw [hx_def, linearComb_dotProduct, dotProduct_linearComb, dotProduct_linearComb, h.left_self,
      hux, hzu, ← hn_def]
    have : s ^ 2 * (1 + t ^ 2 * n) = 1 := by rw [hs2]; field_simp
    linear_combination this
  have hxv : x ⬝ᵥ v = 0 := by
    rw [hx_def, linearComb_dotProduct, h.left_right, hzv]
    ring
  have hle := hmax x v ⟨hxx, h.right_self, hxv⟩
  simp only [fanValue] at hle
  have hq : x ⬝ᵥ A *ᵥ x =
      s ^ 2 * (u ⬝ᵥ A *ᵥ u + 2 * t * (z ⬝ᵥ A *ᵥ u) + t ^ 2 * (z ⬝ᵥ A *ᵥ z)) := by
    rw [hx_def, linearComb_dotProduct_mulVec_linearComb hA]
    ring
  rw [hq, hs2] at hle
  have hle' : u ⬝ᵥ A *ᵥ u + 2 * t * (z ⬝ᵥ A *ᵥ u) + t ^ 2 * (z ⬝ᵥ A *ᵥ z) ≤
      (u ⬝ᵥ A *ᵥ u) * (1 + t ^ 2 * n) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 / (1 + t ^ 2 * n) *
      (u ⬝ᵥ A *ᵥ u + 2 * t * (z ⬝ᵥ A *ᵥ u) + t ^ 2 * (z ⬝ᵥ A *ᵥ z)) ≤ u ⬝ᵥ A *ᵥ u) hpos.le
    rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
    linarith
  nlinarith [hle']

/-- **Invariance.** A maximizing orthonormal pair spans an `A`-invariant plane:
`Au = (uᵀAu) u + (vᵀAu) v`. -/
theorem mulVec_apply_eq_of_fanValue_le {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {u v : ι → ℝ} (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) :
    ∀ i, (A *ᵥ u) i = (u ⬝ᵥ A *ᵥ u) * u i + (v ⬝ᵥ A *ᵥ u) * v i := by
  set r : ι → ℝ := fun i ↦ (A *ᵥ u) i - (u ⬝ᵥ A *ᵥ u) * u i - (v ⬝ᵥ A *ᵥ u) * v i with hr_def
  have hlin : ∀ y : ι → ℝ, r ⬝ᵥ y = (A *ᵥ u) ⬝ᵥ y - (u ⬝ᵥ A *ᵥ u) * (u ⬝ᵥ y) -
      (v ⬝ᵥ A *ᵥ u) * (v ⬝ᵥ y) := by
    intro y
    simp only [hr_def, dotProduct, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  have hru : r ⬝ᵥ u = 0 := by
    rw [hlin, h.left_self, dotProduct_comm v u, h.left_right, dotProduct_comm (A *ᵥ u) u]; ring
  have hrv : r ⬝ᵥ v = 0 := by
    rw [hlin, h.right_self, h.left_right, dotProduct_comm (A *ᵥ u) v]; ring
  have hst := dotProduct_mulVec_eq_zero_of_fanValue_le hA h hmax hru hrv
  have hrr : r ⬝ᵥ r = 0 := by
    have e : r ⬝ᵥ r = r ⬝ᵥ A *ᵥ u - (u ⬝ᵥ A *ᵥ u) * (r ⬝ᵥ u) - (v ⬝ᵥ A *ᵥ u) * (r ⬝ᵥ v) := by
      rw [dotProduct_comm r (A *ᵥ u), dotProduct_comm r u, dotProduct_comm r v]
      exact hlin r
    rw [e, hst, hru, hrv]; ring
  intro i
  have := eq_zero_of_dotProduct_self_eq_zero hrr i
  simp only [hr_def] at this
  linarith

/-- **Invariance**, the same for `v`: `Av = (uᵀAv) u + (vᵀAv) v`. -/
theorem mulVec_apply_eq_of_fanValue_le' {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {u v : ι → ℝ} (h : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A u v) :
    ∀ i, (A *ᵥ v) i = (u ⬝ᵥ A *ᵥ v) * u i + (v ⬝ᵥ A *ᵥ v) * v i := by
  have hmax' : ∀ x y, IsOrthonormalPair x y → fanValue A x y ≤ fanValue A v u := fun x y hxy ↦
    (fanValue_comm A v u) ▸ hmax x y hxy
  intro i
  have := mulVec_apply_eq_of_fanValue_le hA h.symm hmax' i
  linarith

end ProjectionConstants
