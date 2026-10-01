/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Formula
import ProjectionConstants.Matrix.Commute
import ProjectionConstants.ForMathlib.Real

/-!
# First-order conditions for maximizers of the Chalmers–Lewicki quantity

Let `(t, P)` maximize `weightedAbsSum t P = ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` over the unit weights `t`
(`IsUnitWeight t`: `t ≥ 0` and `∑ᵢ tᵢ² = 1`) and the orthogonal projections `P` of rank `r`, and
let `λ` be the maximum, the Chalmers–Lewicki quantity `clConst ℝ ι r`. This file proves the
first-order conditions of [KMMP, Claims 2.1–2.3], which are used for the reweighting in
`ProjectionConstants.Stabilization.Reweight`.

* `mul_sum_eq_of_max`: `tᵢ ∑ⱼ tⱼ |Pᵢⱼ| = λ tᵢ²` for every `i`, i.e. `t` is an eigenvector of
  `(|Pᵢⱼ|)` on its support (perturb `tᵢ`).
* `IsMaximizer.exists_quadratic` (real case, Parseval form `P = Uᵀ U` with columns `uᵢ`): there is
  a matrix `H` with `⟨uᵢ, H uᵢ⟩ = λ tᵢ²` for all `i`. Indeed `P` maximizes `Q ↦ Tr(M Q)` for
  `M = (tᵢ tⱼ sgn Pᵢⱼ)`, so `M P = P M` (`commute_of_isMaxOn`), and `H = U M Uᵀ` works.

## Main definitions

* `IsMaximizer r t U`: `(t, U)` is a maximizer of the Chalmers–Lewicki quantity in Parseval
  form, that is, `t` is a unit weight, `U Uᵀ = I_r`, and `∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| = λ`.

## Main statements

* `mul_sum_eq_of_max`: the condition on the weights, for matrices over `𝕜 = ℝ` or `ℂ`
  (`RCLike 𝕜`).
* `IsMaximizer.weight_eq`: the condition on the weights in Parseval form,
  `tᵢ ∑ⱼ tⱼ |⟨uᵢ, uⱼ⟩| = λ tᵢ²`.
* `IsMaximizer.exists_quadratic`: the quadratic form `H` with `⟨uᵢ, H uᵢ⟩ = λ tᵢ²`.

## References

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.
-/

open Matrix Finset

namespace ProjectionConstants.Stabilization

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` is homogeneous of degree two in `t`. -/
lemma weightedAbsSum_smul (c : ℝ) (t : ι → ℝ) (P : Matrix ι ι 𝕜) :
    weightedAbsSum (c • t) P = c ^ 2 * weightedAbsSum t P := by
  simp only [weightedAbsSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- **Maximality, homogeneous form**: `∑ᵢⱼ vᵢ vⱼ |Pᵢⱼ| ≤ L ‖v‖²` for all `v ≥ 0`. -/
lemma weightedAbsSum_le_mul_of_max {P : Matrix ι ι 𝕜} {L : ℝ}
    (hmax : ∀ t, IsUnitWeight t → weightedAbsSum t P ≤ L) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    weightedAbsSum v P ≤ L * ∑ i, v i ^ 2 := by
  set q := ∑ i, v i ^ 2 with hq
  rcases (sum_nonneg fun i _ ↦ sq_nonneg (v i) : 0 ≤ q).eq_or_lt with hq0 | hq0
  · -- `v = 0`
    have hv0 : ∀ i, v i = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (v j)).mp hq0.symm i (mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : weightedAbsSum v P = 0 := by simp [weightedAbsSum, hv0]
    rw [this, hq, ← hq0, mul_zero]
  · have hw : IsUnitWeight ((1 / √q) • v) := by
      refine ⟨fun i ↦ mul_nonneg (by positivity) (hv i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← hq]
      rw [div_pow, one_pow, Real.sq_sqrt hq0.le, one_div_mul_cancel hq0.ne']
    have h := hmax _ hw
    rw [weightedAbsSum_smul, div_pow, one_pow, Real.sq_sqrt hq0.le, one_div_mul_eq_div,
      div_le_iff₀ hq0] at h
    exact h

/-- Expanding `∑ᵢⱼ vᵢ vⱼ |Pᵢⱼ|` at `v = t + s eᵢ`. -/
lemma weightedAbsSum_add_single {P : Matrix ι ι 𝕜} (hP : ∀ k l, ‖P l k‖ = ‖P k l‖) (t : ι → ℝ)
    (i : ι) (s : ℝ) [DecidableEq ι] :
    weightedAbsSum (t + (Pi.single i s : ι → ℝ)) P =
      weightedAbsSum t P + 2 * s * ∑ j, t j * ‖P i j‖ + s ^ 2 * ‖P i i‖ := by
  set e : ι → ℝ := Pi.single i s with he
  have hsingle : ∀ f : ι → ℝ, ∑ k, e k * f k = s * f i := fun f ↦ by
    rw [sum_eq_single i (fun k _ hk ↦ by simp [he, hk]) (by simp)]
    simp [he]
  have e' : ∀ k l, (t + e) k * (t + e) l * ‖P k l‖ =
      t k * t l * ‖P k l‖ + e k * (t l * ‖P k l‖) +
        e l * (t k * ‖P l k‖) + e k * (e l * ‖P k l‖) := by
    intro k l
    rw [hP l k]
    simp only [Pi.add_apply]
    ring
  unfold weightedAbsSum
  simp_rw [e', sum_add_distrib]
  rw [sum_comm (f := fun k l ↦ e l * (t k * ‖P l k‖))]
  simp_rw [← Finset.mul_sum, hsingle]
  ring

/-- **The weights of a maximizer** ([KMMP, Claims 2.1 and 2.3]): if `t` maximizes
`∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` among unit weights, then `tᵢ ∑ⱼ tⱼ |Pᵢⱼ| = λ tᵢ²` with `λ` the maximum. -/
theorem mul_sum_eq_of_max {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : IsStarProjection P)
    (hmax : ∀ t', IsUnitWeight t' → weightedAbsSum t' P ≤ weightedAbsSum t P) (i : ι) :
    t i * ∑ j, t j * ‖P i j‖ = weightedAbsSum t P * t i ^ 2 := by
  classical
  set L := weightedAbsSum t P
  set b := ∑ j, t j * ‖P i j‖
  rcases (ht.nonneg i).eq_or_lt with h0 | hpos
  · rw [← h0]
    ring
  -- perturb `tᵢ`
  have key : ∀ s, |s| ≤ t i → 0 ≤ 2 * s * (L * t i - b) + s ^ 2 * (L - ‖P i i‖) := by
    intro s hs
    have hv : ∀ j, 0 ≤ (t + (Pi.single i s : ι → ℝ)) j := by
      intro j
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs with hj
      · subst hj
        linarith [neg_abs_le s]
      · simpa using ht.nonneg j
    have h1 := weightedAbsSum_le_mul_of_max hmax hv
    rw [weightedAbsSum_add_single hP.norm_apply_symm] at h1
    have h3 : ∑ j, (t + (Pi.single i s : ι → ℝ)) j ^ 2 = 1 + 2 * s * t i + s ^ 2 := by
      have e : ∀ j, (t + (Pi.single i s : ι → ℝ)) j ^ 2 =
          t j ^ 2 + (Pi.single i s : ι → ℝ) j * (2 * t j) +
            (Pi.single i s : ι → ℝ) j * (Pi.single i s : ι → ℝ) j := by
        intro j
        simp only [Pi.add_apply]
        ring
      simp_rw [e, sum_add_distrib]
      rw [ht.sum_sq, sum_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp),
        sum_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp)]
      simp only [Pi.single_eq_same]
      ring
    rw [h3] at h1
    nlinarith
  have := eq_zero_of_forall_quadratic_nonneg hpos key
  have hb : b = L * t i := by linarith
  rw [hb]
  ring

end Weights

/-! ### Maximizers in Parseval form (real case) -/

section Real

variable {ι : Type*} [Fintype ι] {r : ℕ}

variable (r) in
/-- `(t, U)` is a **maximizer** of the Chalmers–Lewicki quantity in Parseval form: `t` is a unit
weight, `U Uᵀ = I_r`, and `∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩|` is maximal. -/
structure IsMaximizer (t : ι → ℝ) (U : Matrix (Fin r) ι ℝ) : Prop where
  /-- `t` is a unit weight. -/
  unit : IsUnitWeight t
  /-- `U Uᵀ = I_r`: the columns `uᵢ` of `U` form a Parseval frame of `ℝ^r`. -/
  parseval : U * Uᴴ = 1
  /-- The value `∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩|` is the maximum `clConst ℝ ι r`. -/
  eq : weightedAbsSum t (Uᴴ * U) = clConst ℝ ι r

namespace IsMaximizer

variable {t : ι → ℝ} {U : Matrix (Fin r) ι ℝ}

omit [Fintype ι] in
/-- The entries of the Gram matrix `Uᵀ U` are the inner products `⟨uᵢ, uⱼ⟩` of the columns. -/
lemma gram_apply (U : Matrix (Fin r) ι ℝ) (i j : ι) :
    (Uᴴ * U) i j = ∑ k, U k i * U k j := by
  simp [Matrix.mul_apply]

omit [Fintype ι] in
/-- The Gram matrix `Uᵀ U` is symmetric. -/
lemma gram_symm (U : Matrix (Fin r) ι ℝ) (i j : ι) : (Uᴴ * U) j i = (Uᴴ * U) i j := by
  rw [gram_apply, gram_apply]
  exact sum_congr rfl fun k _ ↦ mul_comm _ _

variable (h : IsMaximizer r t U)
include h

/-- `P = Uᵀ U` is an orthogonal projection of rank `r`. -/
lemma mem_orthProjs : Uᴴ * U ∈ orthProjs ℝ ι r :=
  conjTranspose_mul_self_mem_orthProjs h.parseval

/-- **The weights** ([KMMP, Claims 2.1 and 2.3]): `tᵢ ∑ⱼ tⱼ |⟨uᵢ, uⱼ⟩| = λ tᵢ²`. -/
lemma weight_eq (i : ι) :
    t i * ∑ j, t j * |(Uᴴ * U) i j| = clConst ℝ ι r * t i ^ 2 := by
  have := mul_sum_eq_of_max h.unit h.mem_orthProjs.1
    (fun t' ht' ↦ h.eq ▸ le_clConst ht' h.mem_orthProjs) i
  simpa only [Real.norm_eq_abs, h.eq] using this

/-- **The quadratic form** ([KMMP, Claims 2.2 and 2.3]): there is a matrix `H` with
`⟨uᵢ, H uᵢ⟩ = λ tᵢ²` for every column `uᵢ` of `U`. -/
lemma exists_quadratic :
    ∃ H : Matrix (Fin r) (Fin r) ℝ, ∀ i, (Uᴴ * H * U) i i = clConst ℝ ι r * t i ^ 2 := by
  classical
  set P := Uᴴ * U with hPdef
  have hP := h.mem_orthProjs
  set ε : ι → ι → ℝ := fun i j ↦ if 0 ≤ P i j then 1 else -1 with hεdef
  have hε : ∀ i j, ε i j * P i j = |P i j| := by
    intro i j
    simp only [hεdef]
    split_ifs with hij
    · rw [one_mul, abs_of_nonneg hij]
    · rw [abs_of_neg (not_le.mp hij)]
      ring
  have hεle : ∀ i j (x : ℝ), ε i j * x ≤ |x| := by
    intro i j x
    simp only [hεdef]
    split_ifs
    · rw [one_mul]
      exact le_abs_self x
    · rw [neg_one_mul]
      exact neg_le_abs x
  have hεs : ∀ i j, ε j i = ε i j := by
    intro i j
    simp only [hεdef, hPdef, gram_symm]
  set M : Matrix ι ι ℝ := Matrix.of fun i j ↦ t i * t j * ε i j with hMdef
  have hMh : Mᴴ = M := by
    ext i j
    simp only [hMdef, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, hεs]
    ring
  have htrace : ∀ Q : Matrix ι ι ℝ, (M * Q).trace = ∑ i, ∑ j, t i * t j * (ε i j * Q j i) := by
    intro Q
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hMdef, Matrix.of_apply]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have htP : (M * P).trace = clConst ℝ ι r := by
    rw [htrace, ← h.eq]
    unfold weightedAbsSum
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [hPdef, gram_symm, ← hPdef, hε, Real.norm_eq_abs]
  have hmaxQ : ∀ Q ∈ orthProjs ℝ ι r, RCLike.re (M * Q).trace ≤ RCLike.re (M * P).trace := by
    intro Q hQ
    simp only [RCLike.re_to_real]
    rw [htP, htrace]
    refine le_trans ?_ (le_clConst h.unit hQ)
    unfold weightedAbsSum
    refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs, ← hQ.1.norm_apply_symm i j, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hεle i j _)
      (mul_nonneg (h.unit.nonneg i) (h.unit.nonneg j))
  have hcomm := commute_of_isMaxOn hMh hP hmaxQ
  refine ⟨U * M * Uᴴ, fun i ↦ ?_⟩
  have e1 : Uᴴ * (U * M * Uᴴ) * U = M * P := by
    calc Uᴴ * (U * M * Uᴴ) * U = P * M * P := by simp only [hPdef, Matrix.mul_assoc]
      _ = M * P * P := by rw [← hcomm]
      _ = M * P := by rw [Matrix.mul_assoc, hP.1.mul_self]
  rw [e1, Matrix.mul_apply, ← h.weight_eq i, Finset.mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  simp only [hMdef, Matrix.of_apply]
  rw [hPdef, gram_symm, ← hPdef, ← hε]
  ring

end IsMaximizer

end Real

end ProjectionConstants.Stabilization
