/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.KyFan.Stationary
import Mathlib.Algebra.BigOperators.Field

/-!
# Optimal projections commute with `A`

Let `A` be a real symmetric matrix, and let `P` maximize `Tr(AP) = frobeniusInner A P` over the
orthogonal projections of rank at most `n` (the set `orthProjsLe ι n`). Then `AP = PA`
(cf. [AMOP, Lemma 3.1]). To see this, we rotate a unit vector `u` of the range of `P` towards a
vector `x` of its kernel. This changes `Tr(AP)` by `2t xᵀAu + O(t²)`, so `xᵀAu = 0`. Hence the
range of `P` is `A`-invariant.

The rotation is a composition of two rank-one updates: the direction `u` is removed from the range
of `P` and the direction `u + t x` is added.

## Main statements

* `isStarProjection_sub_rankOne`: if `Pu = u` and `u ≠ 0`, then `P - uuᵀ/|u|²` is an orthogonal
  projection.
* `isStarProjection_add_rankOne`: if `Qv = 0` and `v ≠ 0`, then `Q + vvᵀ/|v|²` is an orthogonal
  projection.
* `dotProduct_mulVec_eq_zero_of_isMaxOn`: stationarity, `xᵀAu = 0` whenever `Pu = u` and `Px = 0`.
* `sum_mul_eq_sum_mul_of_isMaxOn`: `AP = PA`.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

variable {ι : Type*} [Fintype ι]

/-! ### Rank-one updates of projections -/

/-- If `Pu = u` and `u ≠ 0`, then `P - uuᵀ/|u|²` is an orthogonal projection. -/
lemma isStarProjection_sub_rankOne {P : Matrix ι ι ℝ} (hP : IsStarProjection P) {u : ι → ℝ}
    (hu : ∀ i, ∑ k, P i k * u k = u i) (ha : u ⬝ᵥ u ≠ 0) :
    IsStarProjection (Matrix.of fun i j ↦ P i j - u i * u j / (u ⬝ᵥ u)) := by
  set a := u ⬝ᵥ u with ha_def
  have hu' : ∀ j, ∑ k, u k * P k j = u j := fun j ↦ by
    rw [← hu j]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hP.apply_comm k j]
    ring
  refine IsStarProjection.of_apply (fun i j ↦ ?_) (fun i j ↦ ?_)
  · simp only [Matrix.of_apply]
    rw [hP.apply_comm i j]
    ring
  · simp only [Matrix.of_apply]
    have e : ∀ k, (P i k - u i * u k / a) * (P k j - u k * u j / a) =
        P i k * P k j - u j / a * (P i k * u k) - u i / a * (u k * P k j) +
          u i * u j / a ^ 2 * (u k * u k) := fun k ↦ by ring
    rw [sum_congr rfl fun k _ ↦ e k]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [hP.sum_mul_apply i j, hu i, hu' j]
    have hsum : ∑ k, u k * u k = a := rfl
    rw [hsum]
    field_simp
    ring

/-- If `Qv = 0` and `v ≠ 0`, then `Q + vvᵀ/|v|²` is an orthogonal projection. -/
lemma isStarProjection_add_rankOne {Q : Matrix ι ι ℝ} (hQ : IsStarProjection Q) {v : ι → ℝ}
    (hv : ∀ i, ∑ k, Q i k * v k = 0) (hb : v ⬝ᵥ v ≠ 0) :
    IsStarProjection (Matrix.of fun i j ↦ Q i j + v i * v j / (v ⬝ᵥ v)) := by
  set b := v ⬝ᵥ v with hb_def
  have hv' : ∀ j, ∑ k, v k * Q k j = 0 := fun j ↦ by
    rw [← hv j]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hQ.apply_comm k j]
    ring
  refine IsStarProjection.of_apply (fun i j ↦ ?_) (fun i j ↦ ?_)
  · simp only [Matrix.of_apply]
    rw [hQ.apply_comm i j]
    ring
  · simp only [Matrix.of_apply]
    have e : ∀ k, (Q i k + v i * v k / b) * (Q k j + v k * v j / b) =
        Q i k * Q k j + v j / b * (Q i k * v k) + v i / b * (v k * Q k j) +
          v i * v j / b ^ 2 * (v k * v k) := fun k ↦ by ring
    rw [sum_congr rfl fun k _ ↦ e k]
    simp only [sum_add_distrib, ← mul_sum]
    rw [hQ.sum_mul_apply i j, hv i, hv' j]
    have hsum : ∑ k, v k * v k = b := rfl
    rw [hsum]
    field_simp
    ring

/-- `Tr(A (P - uuᵀ/a + vvᵀ/b)) = Tr(AP) - uᵀAu/a + vᵀAv/b`. -/
lemma frobeniusInner_sub_add_rankOne (A P : Matrix ι ι ℝ) (u v : ι → ℝ) (a b : ℝ) :
    frobeniusInner A (Matrix.of fun i j ↦ (P i j - u i * u j / a) + v i * v j / b) =
      frobeniusInner A P - (u ⬝ᵥ A *ᵥ u) / a + (v ⬝ᵥ A *ᵥ v) / b := by
  simp only [frobeniusInner, dotProduct_mulVec_self_eq_sum, Matrix.of_apply, sum_div,
    ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  ring

/-- `Pu = u` and `Px = 0` imply `u ⊥ x`. -/
lemma dotProduct_eq_zero_of_mulVec {P : Matrix ι ι ℝ} (hP : IsStarProjection P) {u x : ι → ℝ}
    (hu : ∀ i, ∑ k, P i k * u k = u i) (hx : ∀ i, ∑ k, P i k * x k = 0) : u ⬝ᵥ x = 0 := by
  calc u ⬝ᵥ x = ∑ i, (∑ k, P i k * u k) * x i := by simp only [dotProduct, hu]
    _ = ∑ k, u k * ∑ i, P k i * x i := by
        simp only [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun i _ ↦ ?_
        rw [hP.apply_comm k i]
        ring
    _ = 0 := by simp [hx]

/-! ### Stationarity -/

/-- **Stationarity.** Let `A` be symmetric. If `P` maximizes `Tr(AP)` over `orthProjsLe ι n`,
`Pu = u` and `Px = 0`, then `xᵀAu = 0`. -/
theorem dotProduct_mulVec_eq_zero_of_isMaxOn {n : ℕ} {A P : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hP : P ∈ orthProjsLe ι n)
    (hmax : ∀ P', P' ∈ orthProjsLe ι n → frobeniusInner A P' ≤ frobeniusInner A P) {u x : ι → ℝ}
    (hu : ∀ i, ∑ k, P i k * u k = u i) (hx : ∀ i, ∑ k, P i k * x k = 0) :
    x ⬝ᵥ A *ᵥ u = 0 := by
  by_cases ha : u ⬝ᵥ u = 0
  · have hu0 := eq_zero_of_dotProduct_self_eq_zero ha
    simp [dotProduct, mulVec_apply_eq_sum, hu0]
  set a := u ⬝ᵥ u with ha_def
  have hapos : 0 < a := lt_of_le_of_ne (dotProduct_self_nonneg u) (Ne.symm ha)
  have hux : u ⬝ᵥ x = 0 := dotProduct_eq_zero_of_mulVec hP.1 hu hx
  set c := x ⬝ᵥ x with hc_def
  have hc0 : 0 ≤ c := dotProduct_self_nonneg x
  refine (mul_eq_zero.mp ?_).resolve_left ha
  refine eq_zero_of_forall_quadratic_nonpos (c := a * (x ⬝ᵥ A *ᵥ x) - c * (u ⬝ᵥ A *ᵥ u)) fun t ↦ ?_
  set v : ι → ℝ := fun i ↦ 1 * u i + t * x i with hv_def
  have hvv : v ⬝ᵥ v = a + t ^ 2 * c := by
    rw [hv_def, linearComb_dotProduct, dotProduct_linearComb, dotProduct_linearComb,
      dotProduct_comm x u, hux]
    ring
  have hb : 0 < v ⬝ᵥ v := by rw [hvv]; positivity
  have hQ := isStarProjection_sub_rankOne hP.1 hu ha
  have hQv : ∀ i, ∑ k, (Matrix.of fun i j ↦ P i j - u i * u j / a) i k * v k = 0 := by
    intro i
    simp only [Matrix.of_apply, hv_def]
    have e : ∀ k, (P i k - u i * u k / a) * (1 * u k + t * x k) =
        P i k * u k + t * (P i k * x k) - u i / a * (u k * u k) - u i * t / a * (u k * x k) :=
      fun k ↦ by ring
    rw [sum_congr rfl fun k _ ↦ e k]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [hu i, hx i]
    have h1 : ∑ k, u k * u k = a := rfl
    have h2 : ∑ k, u k * x k = 0 := hux
    rw [h1, h2]
    field_simp
    ring
  have hPt := isStarProjection_add_rankOne hQ hQv hb.ne'
  have htr : (Matrix.of fun i j ↦ (Matrix.of fun i j ↦ P i j - u i * u j / a) i j +
      v i * v j / (v ⬝ᵥ v)).trace = P.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, sum_add_distrib, sum_sub_distrib,
      ← sum_div]
    have h1 : ∑ i, u i * u i = a := rfl
    have h2 : ∑ i, v i * v i = v ⬝ᵥ v := rfl
    rw [h1, h2, div_self ha, div_self hb.ne']
    ring
  have hle := hmax _ ⟨hPt, by rw [htr]; exact hP.2⟩
  have htv : frobeniusInner A (Matrix.of fun i j ↦
      (Matrix.of fun i j ↦ P i j - u i * u j / a) i j + v i * v j / (v ⬝ᵥ v)) =
      frobeniusInner A P - (u ⬝ᵥ A *ᵥ u) / a + (v ⬝ᵥ A *ᵥ v) / (v ⬝ᵥ v) := by
    simp only [Matrix.of_apply]
    exact frobeniusInner_sub_add_rankOne A P u v a (v ⬝ᵥ v)
  rw [htv] at hle
  have hqv : v ⬝ᵥ A *ᵥ v =
      1 ^ 2 * (u ⬝ᵥ A *ᵥ u) + 2 * 1 * t * (x ⬝ᵥ A *ᵥ u) + t ^ 2 * (x ⬝ᵥ A *ᵥ x) :=
    linearComb_dotProduct_mulVec_linearComb hA u x 1 t
  have h1 : (v ⬝ᵥ A *ᵥ v) / (v ⬝ᵥ v) ≤ (u ⬝ᵥ A *ᵥ u) / a := by linarith
  rw [div_le_div_iff₀ hb hapos, hqv, hvv] at h1
  nlinarith [h1]

/-- **Commutation** (cf. [AMOP, Lemma 3.1]). Let `A` be symmetric. If `P` maximizes `Tr(AP)`
over `orthProjsLe ι n`, then `AP = PA`. -/
theorem sum_mul_eq_sum_mul_of_isMaxOn {n : ℕ} {A P : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hP : P ∈ orthProjsLe ι n)
    (hmax : ∀ P', P' ∈ orthProjsLe ι n → frobeniusInner A P' ≤ frobeniusInner A P) (i j : ι) :
    ∑ k, A i k * P k j = ∑ k, P i k * A k j := by
  classical
  -- `AP = PAP`
  have key : ∀ l j, ∑ m, A l m * P m j = ∑ k, P l k * ∑ m, A k m * P m j := by
    intro l j
    have hx : ∀ i, ∑ k, P i k * ((if k = l then 1 else 0) - P k l) = 0 := by
      intro i
      simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
        ite_true]
      rw [hP.1.sum_mul_apply i l]
      ring
    have h := dotProduct_mulVec_eq_zero_of_isMaxOn hA hP hmax (u := fun k ↦ P k j)
      (fun i ↦ hP.1.sum_mul_apply i j) hx
    simp only [dotProduct, mulVec_apply_eq_sum] at h
    simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ite_true] at h
    rw [sub_eq_zero] at h
    rw [h]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hP.1.apply_comm l k]
  -- `PAP` is symmetric
  have hsym : ∀ l j, ∑ k, P l k * ∑ m, A k m * P m j = ∑ k, P j k * ∑ m, A k m * P m l := by
    intro l j
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ ↦ sum_congr rfl fun k _ ↦ ?_
    rw [hP.1.apply_comm m j, hA.apply k m, hP.1.apply_comm l k]
    ring
  have e1 : ∑ k, P i k * A k j = ∑ k, A j k * P k i := by
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hP.1.apply_comm i k, hA.apply j k]
    ring
  rw [e1, key j i, hsym j i, ← key i j]

end ProjectionConstants.AlmostMinimal
