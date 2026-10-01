/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Config
import ProjectionConstants.ForMathlib.Real

/-!
# Quadratic form estimates and rounding of weights

This file contains the estimates used in the proof of [AMOP, Theorem 1.2] in
`ProjectionConstants.AlmostMinimal.Main`. A configuration `(S, w)` is a sign matrix `S` together
with weights `w`; its value is `kyFanSumLe n (weightedSign S w)` (see
`ProjectionConstants.AlmostMinimal.Config`).

## Main statements

* `dotProduct_mulVec_hadamard_le`: let `V` bound the values of all configurations on `ι`. Then
  `xᵀ(S ∘ P)x ≤ V |x|²` for every sign matrix `S` and every `P ∈ orthProjsLe ι n`. The weights are
  `wᵢ = xᵢ²/|x|²`, and the signs of `x` are absorbed into `S` by switching.
* `abs_dotProduct_mulVec_le_of_nonneg`: for a matrix `G` with nonnegative entries, the one-sided
  bound `yᵀGy ≤ c|y|²` implies `|yᵀGy| ≤ c|y|²`.
* `mulVec_dotProduct_mulVec_le`: for symmetric `G` with `|yᵀGy| ≤ c|y|²`, `|Gx| ≤ c|x|`.
* `sub_dotProduct_mulVec_le`: near a maximizer `v` of the quadratic form of `B` on the sphere,
  the loss is quadratic in `|x - v|`.
* `sum_sq_sqrt_div_sub_sqrt_le`: rounding the weights. If `N wᵢ ≤ pᵢ < N wᵢ + 1`, `d = ∑ pᵢ` and
  `qᵢ = pᵢ/d`, then `∑ (√qᵢ - √wᵢ)² = O(1/d²)`.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

variable {ι : Type*} [Fintype ι]

/-! ### Quadratic forms -/

/-- The Hadamard product `S ∘ P` of a sign matrix and an orthogonal projection is symmetric. -/
lemma hadamard_apply_comm {S P : Matrix ι ι ℝ} (hS : IsSignMatrix S) (hP : IsStarProjection P)
    (i j : ι) : (S ⊙ P) j i = (S ⊙ P) i j := by
  simp only [hadamard_apply, hS.symm, hP.apply_comm]

/-- **Switching.** If `V` bounds `kyFanSumLe n (weightedSign S' w')` for all sign matrices `S'` and
weights `w'`, then `xᵀ(S ∘ P)x ≤ V |x|²` for every sign matrix `S` and every
`P ∈ orthProjsLe ι n`. -/
theorem dotProduct_mulVec_hadamard_le {n : ℕ} {S P : Matrix ι ι ℝ} (hS : IsSignMatrix S)
    (hP : P ∈ orthProjsLe _ n) {V : ℝ}
    (hV : ∀ (S' : Matrix ι ι ℝ) (w' : ι → ℝ), IsSignMatrix S' → IsWeight w' →
      kyFanSumLe n (weightedSign S' w') ≤ V)
    (x : ι → ℝ) : x ⬝ᵥ S ⊙ P *ᵥ x ≤ V * (x ⬝ᵥ x) := by
  by_cases hx : x ⬝ᵥ x = 0
  · have h0 := eq_zero_of_dotProduct_self_eq_zero hx
    simp [dotProduct_mulVec_self_eq_sum, h0, hx]
  set a := x ⬝ᵥ x with ha_def
  have ha : 0 < a := lt_of_le_of_ne (dotProduct_self_nonneg x) (Ne.symm hx)
  set σ : ι → ℝ := fun i ↦ if 0 ≤ x i then 1 else -1 with hσ
  have hσ2 : ∀ i, σ i * σ i = 1 := fun i ↦ by
    simp only [hσ]
    split_ifs <;> norm_num
  have hσx : ∀ i, σ i * |x i| = x i := fun i ↦ by
    simp only [hσ]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  set S' : Matrix ι ι ℝ := Matrix.of fun i j ↦ σ i * S i j * σ j with hS'_def
  have hS' : IsSignMatrix S' := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i ↦ ?_⟩
    · simp only [hS'_def, Matrix.of_apply, hS.symm]
      ring
    · simp only [hS'_def, Matrix.of_apply]
      rcases hS.pm i j with h | h <;> simp only [hσ] <;> split_ifs <;> simp [h]
    · simp only [hS'_def, Matrix.of_apply, hS.diag, mul_one]
      exact hσ2 i
  set ω : ι → ℝ := fun i ↦ x i ^ 2 / a with hω_def
  have hω : IsWeight ω := by
    refine ⟨fun i ↦ by positivity, ?_⟩
    simp only [hω_def, ← sum_div]
    rw [div_eq_one_iff_eq ha.ne']
    simp only [ha_def, dotProduct, sq]
  have hsq : ∀ i, √(ω i) = |x i| / √a := fun i ↦ by
    simp only [hω_def]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hsa : √a * √a = a := Real.mul_self_sqrt ha.le
  have hsa0 : √a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hwm : ∀ i j, weightedSign S' ω i j = x i * S i j * x j / a := by
    intro i j
    simp only [weightedSign, hS'_def, Matrix.of_apply, hsq]
    have e : |x i| / √a * (σ i * S i j * σ j) * (|x j| / √a) =
        (σ i * |x i|) * S i j * (σ j * |x j|) / (√a * √a) := by
      field_simp
    rw [e, hσx i, hσx j, hsa]
  have htv : frobeniusInner (weightedSign S' ω) P = (x ⬝ᵥ S ⊙ P *ᵥ x) / a := by
    simp only [frobeniusInner, hwm, dotProduct_mulVec_self_eq_sum, hadamard_apply, sum_div]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    ring
  have h1 := (frobeniusInner_le_kyFanSumLe _ hP).trans (hV S' ω hS' hω)
  rw [htv, div_le_iff₀ ha] at h1
  linarith

/-- For a matrix `G` with nonnegative entries, the one-sided bound `yᵀGy ≤ c|y|²` for all `y`
implies `|yᵀGy| ≤ c|y|²`. -/
theorem abs_dotProduct_mulVec_le_of_nonneg {G : Matrix ι ι ℝ} (hG0 : ∀ i j, 0 ≤ G i j) {c : ℝ}
    (h : ∀ y, y ⬝ᵥ G *ᵥ y ≤ c * (y ⬝ᵥ y)) (y : ι → ℝ) : |y ⬝ᵥ G *ᵥ y| ≤ c * (y ⬝ᵥ y) := by
  refine abs_le.mpr ⟨?_, h y⟩
  have h1 : -(y ⬝ᵥ G *ᵥ y) ≤ (fun i ↦ |y i|) ⬝ᵥ G *ᵥ (fun i ↦ |y i|) := by
    simp only [dotProduct_mulVec_self_eq_sum, ← sum_neg_distrib]
    refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
    have := hG0 i j
    have h2 : -(y i * y j) ≤ |y i| * |y j| := by
      rw [← abs_mul]
      exact neg_le_abs _
    nlinarith
  have h2 := h (fun i ↦ |y i|)
  have h3 : (fun i ↦ |y i|) ⬝ᵥ (fun i ↦ |y i|) = y ⬝ᵥ y := by
    simp only [dotProduct, abs_mul_abs_self]
  rw [h3] at h2
  linarith

/-- **Polarization.** For symmetric `G` with `|yᵀGy| ≤ c|y|²` for all `y`, we have
`|Gx|² ≤ c²|x|²`. -/
theorem mulVec_dotProduct_mulVec_le {G : Matrix ι ι ℝ} (hG : G.IsSymm) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, |y ⬝ᵥ G *ᵥ y| ≤ c * (y ⬝ᵥ y)) (x : ι → ℝ) :
    (G *ᵥ x) ⬝ᵥ G *ᵥ x ≤ c ^ 2 * (x ⬝ᵥ x) := by
  set z := G *ᵥ x with hz
  set s := z ⬝ᵥ z with hs
  set a := x ⬝ᵥ x with ha
  have hs0 : 0 ≤ s := dotProduct_self_nonneg z
  have ha0 : 0 ≤ a := dotProduct_self_nonneg x
  have hzx : z ⬝ᵥ G *ᵥ x = s := rfl
  have key : ∀ t : ℝ, 2 * t * s ≤ c * (a + t ^ 2 * s) := by
    intro t
    have hp := linearComb_dotProduct_mulVec_linearComb hG x z 1 t
    have hm := linearComb_dotProduct_mulVec_linearComb hG x z 1 (-t)
    have hdp : (fun i ↦ 1 * x i + t * z i) ⬝ᵥ (fun i ↦ 1 * x i + t * z i) =
        a + 2 * t * (x ⬝ᵥ z) + t ^ 2 * s := by
      rw [linearComb_dotProduct, dotProduct_linearComb, dotProduct_linearComb, dotProduct_comm z x]
      ring
    have hdm : (fun i ↦ 1 * x i + -t * z i) ⬝ᵥ (fun i ↦ 1 * x i + -t * z i) =
        a - 2 * t * (x ⬝ᵥ z) + t ^ 2 * s := by
      rw [linearComb_dotProduct, dotProduct_linearComb, dotProduct_linearComb, dotProduct_comm z x]
      ring
    have h1 := (abs_le.mp (h (fun i ↦ 1 * x i + t * z i))).2
    have h2 := (abs_le.mp (h (fun i ↦ 1 * x i + -t * z i))).1
    rw [hp, hdp, hzx] at h1
    rw [hm, hdm, hzx] at h2
    nlinarith
  rcases hc.lt_or_eq with hcpos | hc0
  · have h1 := key (1 / c)
    have e1 : 2 * (1 / c) * s = 2 * s / c := by ring
    have e2 : c * (a + (1 / c) ^ 2 * s) = c * a + s / c := by field_simp
    rw [e1, e2] at h1
    have e3 : 2 * s / c = s / c + s / c := by ring
    have h2 : s / c ≤ c * a := by linarith
    have h3 := (div_le_iff₀ hcpos).mp h2
    nlinarith
  · have h1 := key 1
    rw [← hc0] at h1
    rw [← hc0]
    nlinarith

/-- **The quadratic bound.** Let `v` maximize the quadratic form of `B` on the sphere,
`xᵀBx ≤ V|x|²` with equality at `v`. Then `V|x|² - xᵀBx ≤ (V + K)|x - v|²`, where `K` bounds
`-yᵀBy/|y|²`. -/
theorem sub_dotProduct_mulVec_le {B : Matrix ι ι ℝ} (hB : B.IsSymm) {V K : ℝ} {v : ι → ℝ}
    (hle : ∀ x, x ⬝ᵥ B *ᵥ x ≤ V * (x ⬝ᵥ x)) (hlow : ∀ y, -(y ⬝ᵥ B *ᵥ y) ≤ K * (y ⬝ᵥ y))
    (hv : v ⬝ᵥ B *ᵥ v = V * (v ⬝ᵥ v)) (x : ι → ℝ) :
    V * (x ⬝ᵥ x) - x ⬝ᵥ B *ᵥ x ≤ (V + K) * ((fun i ↦ x i - v i) ⬝ᵥ (fun i ↦ x i - v i)) := by
  -- the bilinear form `V⟨v, y⟩ - yᵀBv` vanishes
  have hβ : ∀ y, V * (v ⬝ᵥ y) - y ⬝ᵥ B *ᵥ v = 0 := by
    intro y
    have h := eq_zero_of_forall_quadratic_nonpos (β := -(V * (v ⬝ᵥ y) - y ⬝ᵥ B *ᵥ v))
      (c := -(V * (y ⬝ᵥ y) - y ⬝ᵥ B *ᵥ y)) fun t ↦ by
        have h1 := hle (fun i ↦ 1 * v i + t * y i)
        rw [linearComb_dotProduct_mulVec_linearComb hB v y 1 t, linearComb_dotProduct,
          dotProduct_linearComb, dotProduct_linearComb, dotProduct_comm y v] at h1
        nlinarith [hv]
    linarith
  set r : ι → ℝ := fun i ↦ x i - v i with hr
  have hx : x = fun i ↦ 1 * v i + 1 * r i := by
    funext i
    simp only [hr]
    ring
  have hc : V * (x ⬝ᵥ x) - x ⬝ᵥ B *ᵥ x = V * (r ⬝ᵥ r) - r ⬝ᵥ B *ᵥ r := by
    rw [hx, linearComb_dotProduct_mulVec_linearComb hB v r 1 1, linearComb_dotProduct,
      dotProduct_linearComb, dotProduct_linearComb, dotProduct_comm r v, hv]
    have := hβ r
    linarith
  rw [hc]
  linarith [hlow r]

/-! ### Rounding the weights -/

/-- **Rounding.** Let `w` be a weight on `Fin m` with `wᵢ ≥ ε₀ > 0`, let `N ≥ 1`, and let
`N wᵢ ≤ pᵢ < N wᵢ + 1`. Then `d = ∑ pᵢ` satisfies `N ≤ d` and
`∑ (√(pᵢ/d) - √wᵢ)² ≤ m (m + 1)² / (ε₀ d²)`. -/
theorem sum_sq_sqrt_div_sub_sqrt_le {m : ℕ} {w : Fin m → ℝ} (hw : IsWeight w) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hmin : ∀ i, ε₀ ≤ w i) {N : ℝ} (hN : 1 ≤ N) (p : Fin m → ℝ)
    (hp1 : ∀ i, N * w i ≤ p i) (hp2 : ∀ i, p i < N * w i + 1) :
    N ≤ ∑ i, p i ∧
      ∑ i, (√(p i / ∑ k, p k) - √(w i)) ^ 2 ≤ m * (m + 1) ^ 2 / (ε₀ * (∑ k, p k) ^ 2) := by
  set d := ∑ k, p k with hd
  have hdN : N ≤ d := by
    calc N = ∑ i, N * w i := by rw [← mul_sum, hw.sum_eq, mul_one]
      _ ≤ d := sum_le_sum fun i _ ↦ hp1 i
  have hdm : d ≤ N + m := by
    calc d ≤ ∑ i : Fin m, (N * w i + 1) := sum_le_sum fun i _ ↦ (hp2 i).le
      _ = N + m := by rw [sum_add_distrib, ← mul_sum, hw.sum_eq, mul_one]; simp
  have hdpos : 0 < d := by linarith
  refine ⟨hdN, ?_⟩
  have hw1 : ∀ i, w i ≤ 1 := fun i ↦ by
    rw [← hw.sum_eq]
    exact single_le_sum (f := w) (fun j _ ↦ hw.nonneg j) (mem_univ i)
  have hterm : ∀ i, (√(p i / d) - √(w i)) ^ 2 ≤ (m + 1) ^ 2 / (ε₀ * d ^ 2) := by
    intro i
    have hwi : 0 < w i := lt_of_lt_of_le hε₀ (hmin i)
    have hpi : 0 ≤ p i := le_trans (by nlinarith [hw.nonneg i]) (hp1 i)
    have h1 := Real.sq_sqrt_sub_sqrt_le (div_nonneg hpi hdpos.le) hwi
    have h2 : |p i - d * w i| ≤ m + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [hp1 i, hp2 i, hw1 i, hw.nonneg i]
    have h3 : (p i / d - w i) ^ 2 ≤ ((m + 1) / d) ^ 2 := by
      have e : p i / d - w i = (p i - d * w i) / d := by field_simp
      rw [e, div_pow, div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := sq_abs (p i - d * w i)
      nlinarith [abs_nonneg (p i - d * w i)]
    calc (√(p i / d) - √(w i)) ^ 2 ≤ (p i / d - w i) ^ 2 / w i := h1
      _ ≤ ((m + 1) / d) ^ 2 / ε₀ := by
          apply div_le_div₀ (by positivity) h3 hε₀ (hmin i)
      _ = (m + 1) ^ 2 / (ε₀ * d ^ 2) := by field_simp
  calc ∑ i, (√(p i / d) - √(w i)) ^ 2 ≤ ∑ _i : Fin m, (m + 1) ^ 2 / (ε₀ * d ^ 2) :=
        sum_le_sum fun i _ ↦ hterm i
    _ = m * (m + 1) ^ 2 / (ε₀ * d ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ProjectionConstants.AlmostMinimal
