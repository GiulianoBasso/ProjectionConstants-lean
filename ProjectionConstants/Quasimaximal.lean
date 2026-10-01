/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Absolute
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quasimaximal and maximal projection constants agree

We prove [DL, Theorem 2.2]: the maximal absolute projection constant equals the quasimaximal
absolute projection constant, `λ_𝕜(m) = μ_𝕜(m)` (`maxProjConst_eq_quasiMaxConst`). The real case
is contained in the proof of [JFA, Theorem 1.2].

By the formula of Chalmers and Lewicki [DL, Theorem 1.1], in the form
`maxProjConst_eq_iSup_clConst`, it suffices to show `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ μ_𝕜(m)` for all unit
weights `t` and all `P ∈ orthProjs 𝕜 ι m`. Write `P = Uᴴ U` with `U Uᴴ = I_m` and let `uᵢ` be the
columns of `U`.

* For positive integers `nᵢ`, split the `i`-th coordinate into `nᵢ²` copies, each carrying
  `uᵢ / nᵢ` (`splitMatrix`). This gives an orthogonal projection `P'` of rank `m` on
  `N' = ∑ᵢ nᵢ²` coordinates with `(1/N') ∑ |P'ₖₗ| = ∑ᵢⱼ nᵢ nⱼ |Pᵢⱼ| / ∑ᵢ nᵢ²`, hence
  `∑ᵢⱼ nᵢ nⱼ |Pᵢⱼ| / ∑ᵢ nᵢ² ≤ μ_𝕜(m, N') ≤ μ_𝕜(m)`.
* The quotient `g(v) = ∑ᵢⱼ vᵢ vⱼ |Pᵢⱼ| / ∑ᵢ vᵢ²` is homogeneous and continuous at `t`, and
  `(⌊k tᵢ⌋ + 1)/k → tᵢ` as `k → ∞`, so `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = g(t) ≤ μ_𝕜(m)`.

## Main definitions

* `SplitIndex n`: the index set in which the coordinate `i` is replaced by `nᵢ²` copies.
* `splitMatrix n P`: the split matrix `P'_{(i,a),(j,b)} = Pᵢⱼ / (nᵢ nⱼ)`.
* `splitQuotient P v`: the homogeneous quotient `∑ᵢⱼ vᵢ vⱼ |Pᵢⱼ| / ∑ᵢ vᵢ²`.

## Main statements

* `splitMatrix_mem_orthProjs`: splitting preserves the orthogonal projections of rank `m`.
* `nat_weighted_le_quasiMaxConst`: `∑ᵢⱼ nᵢ nⱼ |Pᵢⱼ| / ∑ᵢ nᵢ² ≤ μ_𝕜(m)` for positive integers `nᵢ`.
* `weightedAbsSum_le_quasiMaxConst`: `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ μ_𝕜(m)` for unit weights `t`.
* `clConst_le_quasiMaxConst`: `clConst 𝕜 ι m ≤ μ_𝕜(m)`.
* `maxProjConst_eq_quasiMaxConst`: `λ_𝕜(m) = μ_𝕜(m)`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
-/

open Matrix Finset Filter Topology

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-! ### Splitting coordinates -/

section Split

variable (n : ι → ℕ)

/-- The blown-up index set: the coordinate `i` is replaced by `nᵢ²` copies. -/
abbrev SplitIndex := Σ i : ι, Fin (n i ^ 2)

/-- The split matrix `P'_{(i,a),(j,b)} = Pᵢⱼ / (nᵢ nⱼ)`; if `P = Uᴴ U`, it is the Gram matrix of
the vectors `uᵢ / nᵢ`, each repeated `nᵢ²` times. -/
noncomputable def splitMatrix (P : Matrix ι ι 𝕜) : Matrix (SplitIndex n) (SplitIndex n) 𝕜 :=
  Matrix.of fun x y ↦ P x.1 y.1 / ((n x.1 : 𝕜) * (n y.1 : 𝕜))

variable {n}

lemma card_splitIndex : Fintype.card (SplitIndex n) = ∑ i, n i ^ 2 := by
  simp [Fintype.card_sigma]

lemma splitMatrix_mem_orthProjs {m : ℕ} (hn : ∀ i, n i ≠ 0) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : splitMatrix n P ∈ orthProjs 𝕜 (SplitIndex n) m := by
  have hn' : ∀ i, (n i : 𝕜) ≠ 0 := fun i ↦ by exact_mod_cast hn i
  have hidem : ∀ i j, ∑ k, P i k * P k j = P i j := fun i j ↦ by
    have := congrFun (congrFun hP.1.mul_self i) j
    simpa [mul_apply] using this
  refine ⟨.of_conjTranspose_eq ?_ ?_, ?_⟩
  · ext x y
    simp only [splitMatrix, conjTranspose_apply, of_apply, star_div₀, star_mul', star_natCast,
      hP.1.apply_symm x.1 y.1, star_star]
    ring
  · ext x y
    simp only [splitMatrix, mul_apply, of_apply, Fintype.sum_sigma, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hidem x.1 y.1, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    field_simp [hn' k, hn' x.1, hn' y.1]
  · rw [← hP.2]
    simp only [Matrix.trace, diag_apply, splitMatrix, of_apply, Fintype.sum_sigma, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    field_simp [hn' i]

lemma absSum_splitMatrix (hn : ∀ i, n i ≠ 0) (P : Matrix ι ι 𝕜) :
    absSum (splitMatrix n P) = ∑ i, ∑ j, (n i : ℝ) * n j * ‖P i j‖ := by
  have hn' : ∀ i, (0 : ℝ) < n i := fun i ↦ by exact_mod_cast Nat.pos_of_ne_zero (hn i)
  simp only [absSum, splitMatrix, of_apply, norm_div, norm_mul, RCLike.norm_natCast,
    Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  field_simp [(hn' i).ne', (hn' j).ne']

/-- For positive integers `nᵢ`: `∑ᵢⱼ nᵢ nⱼ |Pᵢⱼ| / ∑ᵢ nᵢ² ≤ μ_𝕜(m)`. -/
theorem nat_weighted_le_quasiMaxConst {m : ℕ} (hn : ∀ i, n i ≠ 0) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) :
    (∑ i, ∑ j, (n i : ℝ) * n j * ‖P i j‖) / (∑ i, (n i : ℝ) ^ 2) ≤ quasiMaxConst 𝕜 m := by
  have h := le_quasiRelConst (splitMatrix_mem_orthProjs hn hP)
  rw [absSum_splitMatrix hn, card_splitIndex] at h
  push_cast at h
  exact h.trans quasiRelConst_le_quasiMaxConst'

end Split

/-! ### Density -/

/-- The homogeneous quotient `g(v) = ∑ᵢⱼ vᵢ vⱼ |Pᵢⱼ| / ∑ᵢ vᵢ²`. -/
noncomputable def splitQuotient (P : Matrix ι ι 𝕜) (v : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, v i * v j * ‖P i j‖) / ∑ i, v i ^ 2

lemma splitQuotient_smul (P : Matrix ι ι 𝕜) (v : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    splitQuotient P (c • v) = splitQuotient P v := by
  simp only [splitQuotient, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i, ∑ j, c * v i * (c * v j) * ‖P i j‖ = c ^ 2 * ∑ i, ∑ j, v i * v j * ‖P i j‖ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have e2 : ∑ i, (c * v i) ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **The main step of [DL, Theorem 2.2].** `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ μ_𝕜(m)` for every unit weight `t`
and every `P ∈ orthProjs 𝕜 ι m`. -/
theorem weightedAbsSum_le_quasiMaxConst {m : ℕ} {t : ι → ℝ} (ht : IsUnitWeight t)
    {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    weightedAbsSum t P ≤ quasiMaxConst 𝕜 m := by
  -- approximating vectors `v k = (⌊k t⌋ + 1)/k`
  let n : ℕ → ι → ℕ := fun k i ↦ ⌊t i * k⌋₊ + 1
  let v : ℕ → ι → ℝ := fun k i ↦ (n k i : ℝ) / k
  have hv : Tendsto v atTop (𝓝 t) := by
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    have h1 : Tendsto (fun k : ℕ ↦ (⌊t i * k⌋₊ : ℝ) / k) atTop (𝓝 (t i)) :=
      (tendsto_nat_floor_mul_div_atTop (ht.nonneg i)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ ↦ (1 : ℝ) / k) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k ↦ ?_
    simp only [v, n]
    push_cast
    ring
  -- continuity of the quotient at `t`
  have hcont : ContinuousAt (splitQuotient P) t := by
    have hnum : Continuous fun w : ι → ℝ ↦ ∑ i, ∑ j, w i * w j * ‖P i j‖ :=
      continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
        ((continuous_apply i).mul (continuous_apply j)).mul continuous_const
    have hden : Continuous fun w : ι → ℝ ↦ ∑ i, w i ^ 2 :=
      continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2
    exact hnum.continuousAt.div hden.continuousAt (by rw [ht.sum_sq]; exact one_ne_zero)
  have hlim := hcont.tendsto.comp hv
  have hval : splitQuotient P t = weightedAbsSum t P := by
    rw [splitQuotient, ht.sum_sq, div_one]; rfl
  rw [← hval]
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun k hk ↦ ?_⟩)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
  have hvk : v k = ((k : ℝ)⁻¹) • fun i ↦ (n k i : ℝ) := by
    ext i; simp [v, div_eq_inv_mul]
  simp only [Function.comp_apply]
  rw [hvk, splitQuotient_smul _ _ (inv_ne_zero hk0)]
  exact nat_weighted_le_quasiMaxConst (fun i ↦ Nat.succ_ne_zero _) hP

/-- `clConst 𝕜 ι m ≤ μ_𝕜(m)`. -/
theorem clConst_le_quasiMaxConst (m : ℕ) : clConst 𝕜 ι m ≤ quasiMaxConst 𝕜 m :=
  clConst_le quasiMaxConst_nonneg fun _ _ ht hP ↦ weightedAbsSum_le_quasiMaxConst ht hP

/-- **Quasimaximal and maximal projection constants agree** ([DL, Theorem 2.2]).
`λ_𝕜(m) = μ_𝕜(m)`: the maximal absolute projection constant equals the quasimaximal absolute
projection constant. -/
theorem maxProjConst_eq_quasiMaxConst {𝕜 : Type} [RCLike 𝕜] (m : ℕ) :
    maxProjConst 𝕜 m = quasiMaxConst 𝕜 m := by
  refine le_antisymm ?_ (quasiMaxConst_le_maxProjConst m)
  rw [maxProjConst_eq_iSup_clConst]
  exact Real.iSup_le (fun N ↦ clConst_le_quasiMaxConst m) quasiMaxConst_nonneg

end ProjectionConstants
