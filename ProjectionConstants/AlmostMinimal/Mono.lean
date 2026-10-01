/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Main
import ProjectionConstants.GrunbaumConjecture.Main

/-!
# Strict monotonicity of the maximal projection constants

The maximal projection constants `λ_ℝ(k) = maxProjConst ℝ k` (written `Π_k` in [JFA] and
[AMOP]) are strictly increasing in `k`; this is a folklore result. Here it is proved with an
explicit gap: `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)` for `k ≥ 2`, and `λ_ℝ(1) < λ_ℝ(2)`.

A configuration is a pair `(w, P)` of weights `w` (`IsWeight w`) and an orthogonal projection `P`
of rank `k` (`P ∈ orthProjs ℝ ι k`). Its value with the best sign matrix, the sign pattern of `P`,
is `F(w, P) = ∑ᵢⱼ √(wᵢ wⱼ) |pᵢⱼ|` (`configValue`). By the formula of Chalmers and Lewicki
(`ProjectionConstants.ChalmersLewicki.Absolute`), `λ_ℝ(k) = sup F(w, P)`
(`configValue_le_maxProjConst`, `exists_lt_configValue`). In the language of measures, `(w, P)` is
the isotropic measure `∑ wᵢ δ_{rᵢ/√wᵢ}` on `ℝᵏ`, where `P = VVᵀ` and `rᵢ` are the rows of `V`, and
`F` is `∫∫ |⟨x, y⟩|`.

1. **Splitting** (`configValue_splitProj`). For a set `G` of indices with weight `g > 0`, each
   `i ∈ G` is replaced by two copies with half the weight, and a new direction is added in which
   the copies have opposite signs. This gives a configuration of rank `k + 1` with value
   `F(w, P) + ∑_{i, j ∈ G} (wᵢwⱼ/g - √(wᵢwⱼ)|pᵢⱼ|)₊`. In particular, `λ_ℝ(k) ≤ λ_ℝ(k + 1)`.
2. **A heavy index** (`configValue_le_of_diag_pos`). For every index `i` with `pᵢᵢ > 0`,
   `F(w, P) ≤ wᵢ + (1 - wᵢ) λ_ℝ(k - 1) + 2 √(1 - pᵢᵢ)`.
3. **A uniform gain** (`exists_le_splitGain`). If `F(w, P) ≥ λ_ℝ(k) - θ/12` with `θ = 1/(8k)`,
   then some `G` gives a gain of at least `θ³/100`.

## Main definitions

* `configValue w P`: the value `F(w, P) = ∑ᵢⱼ √(wᵢ wⱼ) |pᵢⱼ|` of a configuration.
* `splitWeight G w`, `splitProj G w g P`: the configuration on `ι ⊕ ι` obtained by splitting the
  indices in `G`.
* `splitGain G w g P`: the gain `∑_{a, b ∈ G} (wₐ w_b / g - √(wₐ w_b) |p_ab|)₊` of the splitting.

## Main statements

* `configValue_splitProj`: the value after splitting is `F(w, P) + splitGain G w g P`.
* `configValue_add_splitGain_le`, `maxProjConst_real_le_succ`: `F(w, P) + gain(G) ≤ λ_ℝ(k + 1)`,
  hence `λ_ℝ(k) ≤ λ_ℝ(k + 1)`.
* `configValue_le_of_diag_pos`: the bound for a heavy index.
* `exists_le_splitGain`: the uniform gain.
* `ProjectionConstants.maxProjConst_real_add_le_succ`: `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)` for
  `k ≥ 2`.
* `ProjectionConstants.maxProjConst_real_lt_succ`: `λ_ℝ(k) < λ_ℝ(k + 1)` for `k ≥ 1`.
* `ProjectionConstants.strictMono_maxProjConst_real`: `n ↦ λ_ℝ(n + 1)` is strictly increasing.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

section Basic

variable {ι : Type*} [Fintype ι]

/-- The value `F(w, P) = ∑ᵢⱼ √(wᵢ wⱼ) |pᵢⱼ|` of a configuration `(w, P)`. It is the value
`Tr(√D S √D P)`, `D = diag(w)`, for the sign pattern `S` of `P`. -/
noncomputable def configValue (w : ι → ℝ) (P : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, √(w i) * √(w j) * |P i j|

/-- `F(w, P) = ∑ᵢⱼ tᵢ tⱼ |pᵢⱼ|` with `tᵢ = √wᵢ`. -/
lemma configValue_eq_weightedAbsSum (w : ι → ℝ) (P : Matrix ι ι ℝ) :
    configValue w P = weightedAbsSum (fun i ↦ √(w i)) P := by
  simp only [configValue, weightedAbsSum, Real.norm_eq_abs]

/-- **The value of a configuration is at most `λ_ℝ(k)`**, by the formula of Chalmers and Lewicki
(`weightedAbsSum_le_maxProjConst`). -/
theorem configValue_le_maxProjConst {k : ℕ} {w : ι → ℝ} {P : Matrix ι ι ℝ} (hw : IsWeight w)
    (hP : P ∈ orthProjs ℝ ι k) : configValue w P ≤ maxProjConst ℝ k := by
  rw [configValue_eq_weightedAbsSum]
  exact weightedAbsSum_le_maxProjConst hw.isUnitWeight_sqrt hP

end Basic

/-- **Near-optimal configurations.** For `k ≥ 1` and `δ > 0` some configuration `(w, P)` of rank
`k` has value `F(w, P) > λ_ℝ(k) - δ`, by the formula of Chalmers and Lewicki
(`exists_lt_weightedAbsSum`). -/
theorem exists_lt_configValue {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d : ℕ) (w : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ), IsWeight w ∧
      P ∈ orthProjs ℝ (Fin d) k ∧ maxProjConst ℝ k - δ < configValue w P := by
  obtain ⟨d, t, P, ht, hP, hlt⟩ := exists_lt_weightedAbsSum (𝕜 := ℝ) hk hδ
  refine ⟨d, fun i ↦ t i ^ 2, P, ht.isWeight_sq, hP, hlt.trans_le (le_of_eq ?_)⟩
  simp only [configValue_eq_weightedAbsSum, Real.sqrt_sq (ht.nonneg _)]

/-! ### Splitting -/

private lemma abs_add_abs_sub {t s : ℝ} (hs : 0 ≤ s) : |t + s| + |t - s| = 2 * max |t| s := by
  rcases le_total 0 t with ht | ht
  · rcases le_total s t with hst | hst
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg ht,
        max_eq_left hst]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg ht,
        max_eq_right hst]
      ring
  · rcases le_total s (-t) with hst | hst
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos ht,
        max_eq_left hst]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos ht,
        max_eq_right hst]
      ring

private lemma key_pair {t q g : ℝ} (hq : 0 ≤ q) (hg : 0 < g) :
    q * (|t / 2 + q / (2 * g)| + |t / 2 - q / (2 * g)|) =
      q * |t| + max (q ^ 2 / g - q * |t|) 0 := by
  have h1 : |t / 2 + q / (2 * g)| + |t / 2 - q / (2 * g)| = (|t + q / g| + |t - q / g|) / 2 := by
    rw [show t / 2 + q / (2 * g) = (t + q / g) / 2 by field_simp,
      show t / 2 - q / (2 * g) = (t - q / g) / 2 by field_simp, abs_div, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [h1, abs_add_abs_sub (div_nonneg hq hg.le)]
  have h2 : q * (2 * max |t| (q / g) / 2) = max (q * |t|) (q * (q / g)) := by
    rw [show 2 * max |t| (q / g) / 2 = max |t| (q / g) by ring, mul_max_of_nonneg _ _ hq]
  rw [h2]
  rcases le_total (q * |t|) (q * (q / g)) with h | h
  · rw [max_eq_right h, max_eq_left (by rw [sq]; linarith [show q * (q / g) = q * q / g by ring])]
    rw [sq]
    ring
  · rw [max_eq_left h, max_eq_right (by rw [sq]; linarith [show q * (q / g) = q * q / g by ring])]
    ring

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset ι)

/-- The index of which `x ∈ ι ⊕ ι` is a copy: `Sum.inl a` and `Sum.inr a` are the two copies of
`a`. When the indices in `G` are split, the second copy of `a` has weight zero unless `a ∈ G`. -/
def splitBase : ι ⊕ ι → ι
  | Sum.inl a => a
  | Sum.inr a => a

/-- The coefficient of the old coordinates: `1/√2` on the two copies of `a ∈ G`, `1` on the first
copy of `a ∉ G`, and `0` on the unused second copy of `a ∉ G`. -/
noncomputable def splitCoeff : ι ⊕ ι → ℝ
  | Sum.inl a => if a ∈ G then 1 / √2 else 1
  | Sum.inr a => if a ∈ G then 1 / √2 else 0

/-- The new coordinate: `±√(wₐ/(2g))` on the two copies of `a ∈ G`, and `0` otherwise. -/
noncomputable def splitDir (w : ι → ℝ) (g : ℝ) : ι ⊕ ι → ℝ
  | Sum.inl a => if a ∈ G then √(w a / (2 * g)) else 0
  | Sum.inr a => if a ∈ G then -√(w a / (2 * g)) else 0

/-- The weights after splitting `G`: `wₐ/2` on both copies of `a ∈ G`, `wₐ` on the first copy of
`a ∉ G`, and `0` on the second copy of `a ∉ G`. -/
noncomputable def splitWeight (w : ι → ℝ) (x : ι ⊕ ι) : ℝ := splitCoeff G x ^ 2 * w (splitBase x)

/-- The projection after splitting `G`: the old projection on the copies plus the new direction,
`cₓ c_y P_{base x, base y} + uₓ u_y` with `c = splitCoeff G` and `u = splitDir G w g`. -/
noncomputable def splitProj (w : ι → ℝ) (g : ℝ) (P : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.of fun x y ↦ splitCoeff G x * splitCoeff G y * P (splitBase x) (splitBase y) +
    splitDir G w g x * splitDir G w g y

private lemma inv_sqrt2_sq : (1 / √2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

private lemma inv_sqrt2_mul : (1 / √2 : ℝ) * (1 / √2) = 1 / 2 := by
  rw [← sq, inv_sqrt2_sq]

private lemma inv_sqrt2_nonneg : (0 : ℝ) ≤ 1 / √2 := by positivity

omit [Fintype ι] in
/-- The coefficients `splitCoeff G x` are nonnegative. -/
lemma splitCoeff_nonneg (x : ι ⊕ ι) : 0 ≤ splitCoeff G x := by
  rcases x with a | a <;> simp only [splitCoeff] <;> split_ifs <;>
    first | exact inv_sqrt2_nonneg | norm_num

/-- The squared coefficients of the two copies of `a` add up to one:
`∑ₓ splitCoeff G x ^ 2 * f (splitBase x) = ∑ₐ f a`. -/
lemma sum_splitCoeff_sq (f : ι → ℝ) : ∑ x, splitCoeff G x ^ 2 * f (splitBase x) = ∑ a, f a := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  simp only [splitCoeff, splitBase]
  split_ifs
  · rw [inv_sqrt2_sq]
    ring
  · ring

/-- The new direction is orthogonal to the old coordinates:
`∑ₓ splitCoeff G x * splitDir G w g x * f (splitBase x) = 0`. -/
lemma sum_splitCoeff_mul_splitDir (w : ι → ℝ) (g : ℝ) (f : ι → ℝ) :
    ∑ x, splitCoeff G x * splitDir G w g x * f (splitBase x) = 0 := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_eq_zero fun a _ ↦ ?_
  simp only [splitCoeff, splitDir, splitBase]
  split_ifs <;> ring

/-- The new direction is a unit vector if `g` is the weight of `G`. -/
lemma sum_splitDir_sq {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) {g : ℝ} (hg : 0 < g)
    (hgG : ∑ a ∈ G, w a = g) : ∑ x, splitDir G w g x ^ 2 = 1 := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib]
  have e : ∀ a, (splitDir G w g (Sum.inl a)) ^ 2 + (splitDir G w g (Sum.inr a)) ^ 2 =
      if a ∈ G then w a / g else 0 := fun a ↦ by
    simp only [splitDir]
    split_ifs
    · rw [neg_sq, Real.sq_sqrt (div_nonneg (hw a) (by linarith))]
      field_simp
      ring
    · ring
  simp only [e]
  rw [← sum_filter]
  have hf : univ.filter (fun a ↦ a ∈ G) = G := by ext a; simp
  rw [hf, ← sum_div, hgG, div_self hg.ne']

variable {G}

/-- Splitting turns an orthogonal projection into an orthogonal projection. -/
lemma isStarProjection_splitProj {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) {g : ℝ} (hg : 0 < g)
    (hgG : ∑ a ∈ G, w a = g) {P : Matrix ι ι ℝ} (hP : IsStarProjection P) :
    IsStarProjection (splitProj G w g P) := by
  refine IsStarProjection.of_apply (fun x y ↦ ?_) (fun x y ↦ ?_)
  · simp only [splitProj, Matrix.of_apply, hP.apply_comm]
    ring
  · simp only [splitProj, Matrix.of_apply]
    have e : ∀ z, (splitCoeff G x * splitCoeff G z * P (splitBase x) (splitBase z) +
          splitDir G w g x * splitDir G w g z) *
        (splitCoeff G z * splitCoeff G y * P (splitBase z) (splitBase y) +
          splitDir G w g z * splitDir G w g y) =
        splitCoeff G x * splitCoeff G y *
          (splitCoeff G z ^ 2 * (P (splitBase x) (splitBase z) * P (splitBase z) (splitBase y))) +
        splitCoeff G x * splitDir G w g y *
          (splitCoeff G z * splitDir G w g z * P (splitBase x) (splitBase z)) +
        splitDir G w g x * splitCoeff G y *
          (splitCoeff G z * splitDir G w g z * P (splitBase z) (splitBase y)) +
        splitDir G w g x * splitDir G w g y * splitDir G w g z ^ 2 := fun z ↦ by ring
    simp only [e, sum_add_distrib, ← mul_sum]
    rw [sum_splitCoeff_sq G (fun c ↦ P (splitBase x) c * P c (splitBase y)),
      sum_splitCoeff_mul_splitDir G w g (fun c ↦ P (splitBase x) c),
      sum_splitCoeff_mul_splitDir G w g (fun c ↦ P c (splitBase y)),
      sum_splitDir_sq G hw hg hgG, hP.sum_mul_apply]
    ring

/-- Splitting increases the trace by one. -/
lemma trace_splitProj {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) {g : ℝ} (hg : 0 < g) (hgG : ∑ a ∈ G, w a = g)
    (P : Matrix ι ι ℝ) : ∑ x, splitProj G w g P x x = ∑ a, P a a + 1 := by
  simp only [splitProj, Matrix.of_apply, sum_add_distrib]
  have hu : ∑ x, splitDir G w g x * splitDir G w g x = 1 := by
    simpa [sq] using sum_splitDir_sq G hw hg hgG
  rw [hu, ← sum_splitCoeff_sq G (fun a ↦ P a a)]
  congr 1
  refine sum_congr rfl fun x _ ↦ ?_
  ring

/-- The weights after splitting are weights. -/
lemma isWeight_splitWeight {w : ι → ℝ} (hw : IsWeight w) : IsWeight (splitWeight G w) := by
  refine ⟨fun x ↦ mul_nonneg (sq_nonneg _) (hw.nonneg _), ?_⟩
  simp only [splitWeight]
  rw [sum_splitCoeff_sq G w, hw.sum_eq]

omit [Fintype ι] in
/-- `√(splitWeight G w x) = splitCoeff G x * √(w (splitBase x))`. -/
lemma sqrt_splitWeight (w : ι → ℝ) (x : ι ⊕ ι) :
    √(splitWeight G w x) = splitCoeff G x * √(w (splitBase x)) := by
  rw [splitWeight, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (splitCoeff_nonneg G x)]

end Split

section SplitValue

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The gain of splitting `G`: `∑_{a, b ∈ G} (wₐ w_b / g - √(wₐ w_b) |p_ab|)₊`. -/
noncomputable def splitGain (G : Finset ι) (w : ι → ℝ) (g : ℝ) (P : Matrix ι ι ℝ) : ℝ :=
  ∑ a ∈ G, ∑ b ∈ G, max (w a * w b / g - √(w a) * √(w b) * |P a b|) 0

private lemma sum_mem_eq (G : Finset ι) (f : ι → ℝ) :
    ∑ a ∈ G, f a = ∑ a, if a ∈ G then f a else 0 := by
  rw [← sum_filter]
  congr 1
  ext a
  simp

private lemma split_both {q P α β g : ℝ} (hq : 0 ≤ q) (hg : 0 < g) (hαβ : α * β = q / (2 * g)) :
    1 / √2 * (1 / √2) * q * |1 / √2 * (1 / √2) * P + α * β| +
      1 / √2 * (1 / √2) * q * |1 / √2 * (1 / √2) * P + α * -β| +
      (1 / √2 * (1 / √2) * q * |1 / √2 * (1 / √2) * P + -α * β| +
        1 / √2 * (1 / √2) * q * |1 / √2 * (1 / √2) * P + -α * -β|) =
      q * |P| + max (q ^ 2 / g - q * |P|) 0 := by
  rw [inv_sqrt2_mul, show α * -β = -(α * β) by ring, show -α * β = -(α * β) by ring,
    show -α * -β = α * β by ring, hαβ]
  have e1 : |1 / 2 * P + q / (2 * g)| = |P / 2 + q / (2 * g)| := by ring_nf
  have e2 : |1 / 2 * P + -(q / (2 * g))| = |P / 2 - q / (2 * g)| := by ring_nf
  rw [e1, e2, ← key_pair hq hg]
  ring

private lemma split_one {q P α : ℝ} :
    1 / √2 * 1 * q * |1 / √2 * 1 * P + α * 0| +
      1 / √2 * 0 * q * |1 / √2 * 0 * P + α * 0| +
      (1 / √2 * 1 * q * |1 / √2 * 1 * P + -α * 0| +
        1 / √2 * 0 * q * |1 / √2 * 0 * P + -α * 0|) =
      q * |P| := by
  simp only [mul_zero, zero_mul, add_zero, mul_one, abs_mul, abs_of_nonneg inv_sqrt2_nonneg]
  linear_combination (2 * q * |P|) * inv_sqrt2_mul

private lemma split_one' {q P α : ℝ} :
    1 * (1 / √2) * q * |1 * (1 / √2) * P + 0 * α| +
      1 * (1 / √2) * q * |1 * (1 / √2) * P + 0 * -α| +
      (0 * (1 / √2) * q * |0 * (1 / √2) * P + 0 * α| +
        0 * (1 / √2) * q * |0 * (1 / √2) * P + 0 * -α|) =
      q * |P| := by
  simp only [zero_mul, add_zero, one_mul, abs_mul, abs_of_nonneg inv_sqrt2_nonneg]
  linear_combination (2 * q * |P|) * inv_sqrt2_mul

private lemma split_none {q P : ℝ} :
    1 * 1 * q * |1 * 1 * P + 0 * 0| + 1 * 0 * q * |1 * 0 * P + 0 * 0| +
      (0 * 1 * q * |0 * 1 * P + 0 * 0| + 0 * 0 * q * |0 * 0 * P + 0 * 0|) = q * |P| := by
  simp

/-- **The splitting identity.** `F(w', P') = F(w, P) + gain(G)` for the weights
`w' = splitWeight G w` and the projection `P' = splitProj G w g P`. -/
theorem configValue_splitProj (G : Finset ι) {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) {g : ℝ} (hg : 0 < g)
    (P : Matrix ι ι ℝ) :
    configValue (splitWeight G w) (splitProj G w g P) = configValue w P + splitGain G w g P := by
  have hT : configValue (splitWeight G w) (splitProj G w g P) =
      ∑ x, ∑ y, (splitCoeff G x * splitCoeff G y * (√(w (splitBase x)) * √(w (splitBase y))) *
        |splitCoeff G x * splitCoeff G y * P (splitBase x) (splitBase y) +
          splitDir G w g x * splitDir G w g y|) := by
    simp only [configValue, sqrt_splitWeight, splitProj, Matrix.of_apply]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by ring
  have hgain : splitGain G w g P = ∑ a, ∑ b, if a ∈ G ∧ b ∈ G then
      max (w a * w b / g - √(w a) * √(w b) * |P a b|) 0 else 0 := by
    unfold splitGain
    rw [sum_mem_eq G]
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases ha : a ∈ G
    · simp only [ha, ite_true, true_and]
      rw [sum_mem_eq G]
    · simp [ha]
  rw [hT, hgain, configValue, ← sum_add_distrib]
  simp only [Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
  have hsq : ∀ c, √(w c / (2 * g)) = √(w c) / √(2 * g) := fun c ↦
    Real.sqrt_div (hw c) _
  have h2g : √(2 * g) * √(2 * g) = 2 * g := Real.mul_self_sqrt (by linarith)
  have h2g0 : √(2 * g) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  by_cases ha : a ∈ G <;> by_cases hb : b ∈ G
  · simp only [splitCoeff, splitDir, splitBase, ha, hb, ite_true, and_self]
    rw [split_both (by positivity) hg]
    · rw [mul_pow, Real.sq_sqrt (hw a), Real.sq_sqrt (hw b)]
    · rw [hsq, hsq, div_mul_div_comm, h2g]
  · simp only [splitCoeff, splitDir, splitBase, ha, hb, ite_true, ite_false, and_false, add_zero]
    exact split_one
  · simp only [splitCoeff, splitDir, splitBase, ha, hb, ite_true, ite_false, false_and, add_zero]
    exact split_one'
  · simp only [splitCoeff, splitDir, splitBase, ha, hb, ite_false, and_false, add_zero]
    exact split_none

end SplitValue

section Consequences

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
/-- The gain of a splitting is nonnegative. -/
lemma splitGain_nonneg (G : Finset ι) (w : ι → ℝ) (g : ℝ) (P : Matrix ι ι ℝ) :
    0 ≤ splitGain G w g P :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ le_max_right _ _

omit [DecidableEq ι] in
/-- **Splitting gives a configuration of rank `k + 1`**: `F(w, P) + gain(G) ≤ λ_ℝ(k + 1)`. -/
theorem configValue_add_splitGain_le {k : ℕ} {w : ι → ℝ} (hw : IsWeight w) {P : Matrix ι ι ℝ}
    (hP : P ∈ orthProjs ℝ ι k) (G : Finset ι) (hg : 0 < ∑ a ∈ G, w a) :
    configValue w P + splitGain G w (∑ a ∈ G, w a) P ≤ maxProjConst ℝ (k + 1) := by
  classical
  have hP' : (splitProj G w (∑ a ∈ G, w a) P) ∈ orthProjs ℝ (ι ⊕ ι) (k + 1) := by
    refine ⟨isStarProjection_splitProj hw.nonneg hg rfl hP.1, ?_⟩
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [trace_splitProj hw.nonneg hg rfl, show ∑ i, P i i = k from hP.2]
    push_cast
    ring
  rw [← configValue_splitProj G hw.nonneg hg P]
  exact configValue_le_maxProjConst (isWeight_splitWeight hw) hP'

end Consequences

/-- `λ_ℝ(k) ≤ λ_ℝ(k + 1)` for `k ≥ 1`: split all indices. -/
theorem maxProjConst_real_le_succ {k : ℕ} (hk : 1 ≤ k) :
    maxProjConst ℝ k ≤ maxProjConst ℝ (k + 1) := by
  refine le_of_forall_pos_lt_add fun δ hδ ↦ ?_
  obtain ⟨d, w, P, hw, hP, hlt⟩ := exists_lt_configValue hk hδ
  have hg : 0 < ∑ a ∈ (univ : Finset (Fin d)), w a := by rw [hw.sum_eq]; exact one_pos
  have h1 := configValue_add_splitGain_le hw hP univ hg
  have h2 := splitGain_nonneg (univ : Finset (Fin d)) w (∑ a ∈ univ, w a) P
  linarith

/-- `4/3 ≤ λ_ℝ(k)` for `k ≥ 2`, since `λ_ℝ(2) = 4/3`
(`GrunbaumConjecture.maxProjConst_real_two`). -/
theorem four_thirds_le_maxProjConst_real {k : ℕ} (hk : 2 ≤ k) : 4 / 3 ≤ maxProjConst ℝ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [GrunbaumConjecture.maxProjConst_real_two]
  | succ k hk ih => exact ih.trans (maxProjConst_real_le_succ (by omega))

section Heavy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A heavy index.** For every index `i` with `pᵢᵢ > 0`,
`F(w, P) ≤ wᵢ + (1 - wᵢ) λ_ℝ(k - 1) + 2 √(1 - pᵢᵢ)`. -/
theorem configValue_le_of_diag_pos {k : ℕ} (hk : 2 ≤ k) {w : ι → ℝ} (hw : IsWeight w)
    {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι k) (i : ι) (hpi : 0 < P i i) :
    configValue w P ≤ w i + (1 - w i) * maxProjConst ℝ (k - 1) + 2 * √(1 - P i i) := by
  classical
  set m := w i with hm
  set a := P i i with ha
  have ha1 : a ≤ 1 := hP.1.diag_le_one i
  have hm0 : 0 ≤ m := hw.nonneg i
  have hwrest : ∑ l : {l // l ≠ i}, w l = 1 - m := by
    rw [Fintype.sum_subtype_ne_eq_sub i w, hw.sum_eq]
  have hm1 : m ≤ 1 := by
    have : 0 ≤ ∑ l : {l // l ≠ i}, w l := sum_nonneg fun l _ ↦ hw.nonneg l
    linarith
  have hrow : ∑ l, P i l ^ 2 = a := (hP.1.diag_eq_sum_sq i).symm
  have hprest : ∑ l : {l // l ≠ i}, P i l ^ 2 = a - a ^ 2 := by
    rw [Fintype.sum_subtype_ne_eq_sub i (fun l ↦ P i l ^ 2), hrow]
  -- the mixed terms
  set X := ∑ l : {l // l ≠ i}, √(w l) * |P i l| with hX
  have hX0 : 0 ≤ X := sum_nonneg fun l _ ↦ by positivity
  have hXsq : X ^ 2 ≤ (1 - m) * (a - a ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun l : {l // l ≠ i} ↦ √(w l))
      (fun l ↦ |P i l|)
    simp only [Real.sq_sqrt (hw.nonneg _), sq_abs] at h
    rwa [hwrest, hprest] at h
  -- the rest
  set s := ∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |P j l| with hs
  have hdecomp : configValue w P = m * a + 2 * √m * X + s := by
    have h1 : ∀ j, ∑ l, √(w j) * √(w l) * |P j l| =
        √(w j) * √m * |P j i| + ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |P j l| := fun j ↦ by
      rw [Fintype.sum_subtype_ne_eq_sub i (fun l ↦ √(w j) * √(w l) * |P j l|)]
      ring
    have e1 : configValue w P = ∑ j, √(w j) * √m * |P j i| +
        ∑ j, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |P j l| := by
      simp only [configValue, h1, sum_add_distrib]
    have e2 := Fintype.sum_subtype_ne_eq_sub i (fun j ↦ √(w j) * √m * |P j i|)
    have e3 :=
      Fintype.sum_subtype_ne_eq_sub i (fun j ↦ ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |P j l|)
    have e4 : ∑ j : {j // j ≠ i}, √(w j) * √m * |P j i| = √m * X := by
      rw [hX, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [hP.1.apply_comm j i]
      ring
    have e5 : ∑ l : {l // l ≠ i}, √m * √(w l) * |P i l| = √m * X := by
      rw [hX, mul_sum]
      refine sum_congr rfl fun l _ ↦ by ring
    have e6 : √m * √m * |P i i| = m * a := by
      rw [Real.mul_self_sqrt hm0, abs_of_pos hpi]
    simp only at e2 e3
    rw [e4, e6] at e2
    rw [e5] at e3
    rw [e1, hs]
    linarith
  -- the projection `Q = P - (P eᵢ)(P eᵢ)ᵀ / pᵢᵢ` of rank `k - 1`
  have hdot : (fun l ↦ P l i) ⬝ᵥ (fun l ↦ P l i) = a := by
    simp only [dotProduct]
    rw [← hrow]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [hP.1.apply_comm l i, sq]
  have hQop := isStarProjection_sub_rankOne (u := fun l ↦ P l i) hP.1
    (fun j ↦ hP.1.sum_mul_apply j i) (by rw [hdot]; exact hpi.ne')
  simp only [hdot] at hQop
  set Q : Matrix ι ι ℝ := Matrix.of fun j l ↦ P j l - P j i * P l i / a with hQ
  have hQi : ∀ l, Q i l = 0 := fun l ↦ by
    simp only [hQ, Matrix.of_apply]
    rw [← ha, mul_comm, mul_div_assoc, div_self hpi.ne', mul_one, hP.1.apply_comm l i, sub_self]
  have hQi' : ∀ j, Q j i = 0 := fun j ↦ by rw [hQop.apply_comm i j]; exact hQi j
  have hQtr : ∑ j, Q j j = (k : ℝ) - 1 := by
    simp only [hQ, Matrix.of_apply, sum_sub_distrib, ← sum_div]
    rw [show ∑ j, P j j = k from hP.2]
    have : ∑ j, P j i * P j i = a := by
      rw [← hrow]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [hP.1.apply_comm j i, sq]
    rw [this, div_self hpi.ne']
  set Q' : Matrix {j // j ≠ i} {j // j ≠ i} ℝ := Matrix.of fun j l ↦ Q j l with hQ'
  have hQ'proj : Q' ∈ orthProjs ℝ _ (k - 1) := by
    refine ⟨IsStarProjection.of_apply (fun j l ↦ hQop.apply_comm j l) (fun j l ↦ ?_), ?_⟩
    · simp only [hQ', Matrix.of_apply]
      rw [Fintype.sum_subtype_ne_eq_sub i (fun c ↦ Q j c * Q c l), hQi', zero_mul, sub_zero,
        hQop.sum_mul_apply]
    · simp only [Matrix.trace, Matrix.diag_apply, hQ', Matrix.of_apply]
      rw [Fintype.sum_subtype_ne_eq_sub i (fun j ↦ Q j j), hQi, sub_zero, hQtr,
        Nat.cast_sub (by omega)]
      simp
  -- the rest is bounded by `(1 - m) λ_ℝ(k - 1)` plus a small term
  have hsQ : ∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |Q j l| ≤
      (1 - m) * maxProjConst ℝ (k - 1) := by
    rcases hm1.lt_or_eq with hm1' | hm1'
    · set w' : {j // j ≠ i} → ℝ := fun j ↦ w j / (1 - m) with hw'
      have hpos : 0 < 1 - m := by linarith
      have hw'w : IsWeight w' := by
        refine ⟨fun j ↦ div_nonneg (hw.nonneg _) hpos.le, ?_⟩
        simp only [hw', ← sum_div, hwrest]
        exact div_self hpos.ne'
      have h := configValue_le_maxProjConst hw'w hQ'proj
      have e : configValue w' Q' =
          (∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |Q j l|) / (1 - m) := by
        simp only [configValue, hw', hQ', Matrix.of_apply, sum_div]
        refine sum_congr rfl fun j _ ↦ sum_congr rfl fun l _ ↦ ?_
        rw [Real.sqrt_div (hw.nonneg _), Real.sqrt_div (hw.nonneg _)]
        have hs1 : √(1 - m) * √(1 - m) = 1 - m := Real.mul_self_sqrt hpos.le
        have hs2 : √(1 - m) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
        field_simp
        rw [sq, hs1]
      rw [e, div_le_iff₀ hpos] at h
      linarith
    · have hz : ∀ j : {j // j ≠ i}, w j = 0 := by
        have h0 : ∑ l : {l // l ≠ i}, w l = 0 := by rw [hwrest, hm1', sub_self]
        intro j
        exact (sum_eq_zero_iff_of_nonneg (fun (l : {l // l ≠ i}) _ ↦ hw.nonneg l)).mp h0 j
          (mem_univ j)
      simp [hz, hm1']
  have hsbound : s ≤ ∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |Q j l| +
      X ^ 2 / a := by
    have hterm : ∀ j l : ι, |P j l| ≤ |Q j l| + |P j i| * |P l i| / a := fun j l ↦ by
      have e : P j l = Q j l + P j i * P l i / a := by simp only [hQ, Matrix.of_apply]; ring
      rw [e]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_div, abs_mul, abs_of_pos hpi]
    have hXX : (∑ j : {j // j ≠ i}, √(w j) * |P j i|) = X := by
      rw [hX]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [hP.1.apply_comm j i]
    calc s ≤ ∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i},
            √(w j) * √(w l) * (|Q j l| + |P j i| * |P l i| / a) := by
          refine sum_le_sum fun j _ ↦ sum_le_sum fun l _ ↦ ?_
          exact mul_le_mul_of_nonneg_left (hterm j l) (by positivity)
      _ = ∑ j : {j // j ≠ i}, ∑ l : {l // l ≠ i}, √(w j) * √(w l) * |Q j l| +
            (∑ j : {j // j ≠ i}, √(w j) * |P j i|) *
              (∑ l : {l // l ≠ i}, √(w l) * |P l i|) / a := by
          rw [sum_mul_sum, sum_div, ← sum_add_distrib]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [sum_div, ← sum_add_distrib]
          refine sum_congr rfl fun l _ ↦ ?_
          ring
      _ = _ := by rw [hXX, sq]
  -- the estimates
  have h1 : m * a ≤ m := by nlinarith
  have h2 : X ^ 2 / a ≤ 1 - a := by
    rw [div_le_iff₀ hpi]
    nlinarith
  have h1a : 0 ≤ 1 - a := by linarith
  have h3 : 1 - a ≤ √(1 - a) := by
    rw [Real.le_sqrt h1a h1a]
    nlinarith
  have h4 : 2 * √m * X ≤ √(1 - a) := by
    rw [Real.le_sqrt (by positivity) h1a]
    have hsm : √m ^ 2 = m := Real.sq_sqrt hm0
    have h5 : (2 * √m * X) ^ 2 = 4 * m * X ^ 2 := by rw [mul_pow, mul_pow, hsm]; ring
    rw [h5]
    have h6 : 4 * m * X ^ 2 ≤ 4 * m * ((1 - m) * (a - a ^ 2)) :=
      mul_le_mul_of_nonneg_left hXsq (by positivity)
    have h7 : 4 * m * ((1 - m) * (a - a ^ 2)) ≤ 1 - a := by
      have h8 : 4 * m * (1 - m) ≤ 1 := by nlinarith [sq_nonneg (2 * m - 1)]
      have h9 : 0 ≤ a * (1 - a) := mul_nonneg hpi.le h1a
      have h10 : a * (1 - a) ≤ 1 - a := by nlinarith
      calc 4 * m * ((1 - m) * (a - a ^ 2)) = (4 * m * (1 - m)) * (a * (1 - a)) := by ring
        _ ≤ 1 * (a * (1 - a)) := mul_le_mul_of_nonneg_right h8 h9
        _ ≤ 1 - a := by linarith
    linarith
  rw [hdecomp]
  linarith

end Heavy

section Gain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
/-- Collect indices until the weight first reaches `θ`. -/
private lemma exists_subset_sum_between {w : ι → ℝ} {θ : ℝ} (hθ : 0 < θ) (hsmall : ∀ i, w i < θ)
    (s : Finset ι) (hs : θ ≤ ∑ i ∈ s, w i) :
    ∃ G ⊆ s, θ ≤ ∑ i ∈ G, w i ∧ ∑ i ∈ G, w i < 2 * θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs; linarith
  | insert a t hat ih =>
    by_cases ht : θ ≤ ∑ i ∈ t, w i
    · obtain ⟨G, hG, h1, h2⟩ := ih ht
      exact ⟨G, hG.trans (subset_insert a t), h1, h2⟩
    · refine ⟨insert a t, subset_refl _, hs, ?_⟩
      rw [sum_insert hat]
      push Not at ht
      linarith [hsmall a]

omit [DecidableEq ι] in
/-- **Light indices.** Let `G` be a set of indices of weight `g > 0` with `2k g ≤ 1/2`, and let
`pₐₐ ≤ 2k wₐ` for all `a ∈ G`. Then the gain of splitting `G` is at least `g/2`. -/
lemma le_splitGain_of_light {k : ℕ} {w : ι → ℝ} (hw : IsWeight w) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) (G : Finset ι) (hG : ∀ a ∈ G, P a a ≤ 2 * k * w a)
    (hg : 0 < ∑ a ∈ G, w a) (hg2 : 2 * k * ∑ a ∈ G, w a ≤ 1 / 2) :
    (∑ a ∈ G, w a) / 2 ≤ splitGain G w (∑ a ∈ G, w a) P := by
  set g := ∑ a ∈ G, w a with hg_def
  have hT : ∑ a ∈ G, ∑ b ∈ G, √(w a) * √(w b) * |P a b| ≤ g / 2 := by
    have habs : ∀ a b, |P a b| ≤ √(P a a) * √(P b b) := fun a b ↦ by
      rw [← Real.sqrt_mul (hP.diag_nonneg a), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hP.sq_apply_le_mul a b)
    calc ∑ a ∈ G, ∑ b ∈ G, √(w a) * √(w b) * |P a b|
        ≤ ∑ a ∈ G, ∑ b ∈ G, (√(w a) * √(P a a)) * (√(w b) * √(P b b)) := by
          refine sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ ?_
          calc √(w a) * √(w b) * |P a b| ≤ √(w a) * √(w b) * (√(P a a) * √(P b b)) :=
                mul_le_mul_of_nonneg_left (habs a b) (by positivity)
            _ = (√(w a) * √(P a a)) * (√(w b) * √(P b b)) := by ring
      _ = (∑ a ∈ G, √(w a) * √(P a a)) ^ 2 := by rw [sq, sum_mul_sum]
      _ ≤ (∑ a ∈ G, √(w a) ^ 2) * (∑ a ∈ G, √(P a a) ^ 2) := sum_mul_sq_le_sq_mul_sq _ _ _
      _ = g * ∑ a ∈ G, P a a := by
          simp only [Real.sq_sqrt (hw.nonneg _), Real.sq_sqrt (hP.diag_nonneg _), hg_def]
      _ ≤ g * (2 * k * g) := by
          apply mul_le_mul_of_nonneg_left _ hg.le
          rw [hg_def, mul_sum]
          exact sum_le_sum fun a ha ↦ hG a ha
      _ ≤ g / 2 := by nlinarith
  have hlin : g - ∑ a ∈ G, ∑ b ∈ G, √(w a) * √(w b) * |P a b| ≤ splitGain G w g P := by
    have e : g = ∑ a ∈ G, ∑ b ∈ G, w a * w b / g := by
      simp only [← sum_div, ← mul_sum, ← sum_mul, ← hg_def]
      field_simp
    rw [splitGain]
    conv_lhs => rw [e]
    rw [← sum_sub_distrib]
    refine sum_le_sum fun a _ ↦ ?_
    rw [← sum_sub_distrib]
    exact sum_le_sum fun b _ ↦ le_max_left _ _
  linarith

omit [DecidableEq ι] in
/-- **A uniform gain.** Let `k ≥ 2` and `θ = 1/(8k)`. If `F(w, P) ≥ λ_ℝ(k) - θ/12`, then some
`G` gives a gain of at least `θ³/100`. -/
theorem exists_le_splitGain {k : ℕ} (hk : 2 ≤ k) {w : ι → ℝ} (hw : IsWeight w) {P : Matrix ι ι ℝ}
    (hP : P ∈ orthProjs ℝ ι k) (hF : maxProjConst ℝ k - 1 / (8 * (k : ℝ)) / 12 ≤ configValue w P) :
    ∃ G : Finset ι, 0 < ∑ a ∈ G, w a ∧
      (1 / (8 * (k : ℝ))) ^ 3 / 100 ≤ splitGain G w (∑ a ∈ G, w a) P := by
  classical
  set θ : ℝ := 1 / (8 * (k : ℝ)) with hθ
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 16 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h43 := four_thirds_le_maxProjConst_real hk
  by_cases hA : ∃ i, θ ≤ w i
  · obtain ⟨i, hi⟩ := hA
    by_cases hA1 : P i i ≤ 1 - θ ^ 2 / 100
    · -- split the single index `i`
      refine ⟨{i}, by rw [sum_singleton]; linarith, ?_⟩
      rw [splitGain, sum_singleton, sum_singleton, sum_singleton]
      have hwi : 0 < w i := by linarith
      have e : w i * w i / w i - √(w i) * √(w i) * |P i i| = w i * (1 - P i i) := by
        rw [Real.mul_self_sqrt hwi.le, abs_of_nonneg (hP.1.diag_nonneg i)]
        field_simp
      rw [e]
      refine le_trans ?_ (le_max_left _ _)
      have h1 : θ * (θ ^ 2 / 100) ≤ w i * (θ ^ 2 / 100) :=
        mul_le_mul_of_nonneg_right hi (by positivity)
      have h2 : w i * (θ ^ 2 / 100) ≤ w i * (1 - P i i) :=
        mul_le_mul_of_nonneg_left (by linarith) hwi.le
      nlinarith
    · -- a heavy index with `pᵢᵢ` close to `1` contradicts near-optimality
      push Not at hA1
      exfalso
      have hpi : 0 < P i i := by nlinarith
      have hheavy := configValue_le_of_diag_pos hk hw hP i hpi
      have hmono : maxProjConst ℝ (k - 1) ≤ maxProjConst ℝ k := by
        have := maxProjConst_real_le_succ (k := k - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      have hw1 : w i ≤ 1 := by
        rw [← hw.sum_eq]
        exact single_le_sum (f := w) (fun j _ ↦ hw.nonneg j) (mem_univ i)
      have hsqrt : √(1 - P i i) < θ / 10 := by
        rw [show θ / 10 = √((θ / 10) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_lt_sqrt (by linarith [hP.1.diag_le_one i]) (by nlinarith)
      have h1 : (1 - w i) * maxProjConst ℝ (k - 1) ≤ (1 - w i) * maxProjConst ℝ k :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
      have h2 : w i * (maxProjConst ℝ k - 1) ≥ θ * (1 / 3) := by nlinarith
      nlinarith
  · -- all indices are light: collect indices with `pₐₐ ≤ 2k wₐ`
    push Not at hA
    set H := univ.filter fun a ↦ P a a ≤ 2 * k * w a with hH
    have hHc : ∑ a ∈ Hᶜ, w a ≤ 1 / 2 := by
      have h1 : ∀ a ∈ Hᶜ, 2 * k * w a ≤ P a a := fun a ha ↦ by
        simp only [hH, mem_compl, mem_filter, mem_univ, true_and, not_le] at ha
        exact ha.le
      have h2 : 2 * k * ∑ a ∈ Hᶜ, w a ≤ ∑ a ∈ Hᶜ, P a a := by
        rw [mul_sum]
        exact sum_le_sum h1
      have h3 : ∑ a ∈ Hᶜ, P a a ≤ ∑ a, P a a :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ ↦ hP.1.diag_nonneg a
      rw [show ∑ a, P a a = k from hP.2] at h3
      have hk' : (0 : ℝ) < k := by linarith
      nlinarith
    have hHsum : θ ≤ ∑ a ∈ H, w a := by
      have := sum_add_sum_compl H w
      rw [hw.sum_eq] at this
      linarith
    obtain ⟨G, hGH, hG1, hG2⟩ := exists_subset_sum_between hθ0 hA H hHsum
    have hGmem : ∀ a ∈ G, P a a ≤ 2 * k * w a := fun a ha ↦ by
      have := hGH ha
      simp only [hH, mem_filter, mem_univ, true_and] at this
      exact this
    have hg2 : 2 * k * ∑ a ∈ G, w a ≤ 1 / 2 := by
      have : 2 * (k : ℝ) * (2 * θ) = 1 / 2 := by rw [hθ]; field_simp; ring
      nlinarith
    refine ⟨G, by linarith, ?_⟩
    have h := le_splitGain_of_light hw hP.1 G hGmem (by linarith) hg2
    have hθsq : θ ^ 2 ≤ 1 := by nlinarith
    have hθcube : θ ^ 3 ≤ θ := by
      have : θ ^ 3 = θ * θ ^ 2 := by ring
      rw [this]
      nlinarith
    have h1 : θ ^ 3 / 100 ≤ θ / 2 := by linarith
    linarith

end Gain

/-- `λ_ℝ(k) + (1/(8k))³/100 ≤ λ_ℝ(k + 1)` for `k ≥ 2`. -/
private theorem maxProjConst_real_add_cube_le_succ {k : ℕ} (hk : 2 ≤ k) :
    maxProjConst ℝ k + (1 / (8 * (k : ℝ))) ^ 3 / 100 ≤ maxProjConst ℝ (k + 1) := by
  set θ : ℝ := 1 / (8 * (k : ℝ)) with hθ
  have hθ0 : 0 < θ := by positivity
  refine le_of_forall_pos_lt_add fun δ hδ ↦ ?_
  obtain ⟨d, w, P, hw, hP, hlt⟩ :=
    exists_lt_configValue (k := k) (by omega) (δ := min δ (θ / 12)) (lt_min hδ (by positivity))
  have hm1 := min_le_left δ (θ / 12)
  have hm2 := min_le_right δ (θ / 12)
  obtain ⟨G, hg, hgain⟩ := exists_le_splitGain hk hw hP (by linarith)
  have h1 := configValue_add_splitGain_le hw hP G hg
  linarith

end ProjectionConstants.AlmostMinimal

namespace ProjectionConstants

open AlmostMinimal

/-- **Quantitative strict monotonicity.** `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)` for
`k ≥ 2`, an explicit form of the folklore strict monotonicity of `λ_ℝ`. -/
theorem maxProjConst_real_add_le_succ {k : ℕ} (hk : 2 ≤ k) :
    maxProjConst ℝ k + 1 / (51200 * (k : ℝ) ^ 3) ≤ maxProjConst ℝ (k + 1) := by
  have h : (1 / (8 * (k : ℝ))) ^ 3 / 100 = 1 / (51200 * (k : ℝ) ^ 3) := by
    rw [div_pow, mul_pow]
    ring
  rw [← h]
  exact maxProjConst_real_add_cube_le_succ hk

/-- **Strict monotonicity** (folklore). `λ_ℝ(k) < λ_ℝ(k + 1)` for all `k ≥ 1`. -/
theorem maxProjConst_real_lt_succ {k : ℕ} (hk : 1 ≤ k) :
    maxProjConst ℝ k < maxProjConst ℝ (k + 1) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    have h1 : maxProjConst ℝ 1 ≤ 1 := by simpa using maxProjConst_le_sqrt (𝕜 := ℝ) 1
    rw [GrunbaumConjecture.maxProjConst_real_two]
    linarith
  · have h1 := maxProjConst_real_add_le_succ h
    have h2 : 0 < 1 / (51200 * (k : ℝ) ^ 3) := by positivity
    linarith

/-- **Strict monotonicity** (folklore). `n ↦ λ_ℝ(n + 1)` is strictly increasing, that is, the
maximal projection constants `λ_ℝ(n)`, `n ≥ 1`, are strictly increasing. -/
theorem strictMono_maxProjConst_real : StrictMono fun n : ℕ ↦ maxProjConst ℝ (n + 1) :=
  strictMono_nat_of_lt_succ fun n ↦ maxProjConst_real_lt_succ (by omega)

end ProjectionConstants
