/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.UpperBound
import ProjectionConstants.Matrix.Commute

/-!
# The formula of Chalmers and Lewicki: the lower bound

We prove the lower bound in the formula of Chalmers and Lewicki [DL, Theorem 1.1]:
`clConst 𝕜 (Fin N) m ≤ λ_𝕜(m, N)` (`clConst_le_maxRelProjConst`).

The main tool is **trace duality in `ℓ∞`** (`re_trace_le_relProjConst`): if `P₀² = P₀`,
`A P₀ = P₀ A` and the columns of `A` satisfy `|Aⱼᵢ| ≤ αᵢ` with `∑ᵢ αᵢ ≤ 1`, then
`Re tr(A P₀) ≤ λ(range P₀, ℓ∞^ι)`.

Let `t > 0` be weights with `∑ᵢ tᵢ² = 1` and let `P ∈ orthProjs 𝕜 ι m`. Let `Q` maximize
`∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` over `orthProjs 𝕜 ι m` (by compactness) and let `S = sgn(Q)` be its sign
pattern (`phaseMatrix Q`). Then `Q` also maximizes `Re tr(B ·)` for `B = D S D`, `D = diag(t)`,
hence `B Q = Q B` (`commute_of_isMaxOn`). The subspace `Y = D⁻¹ range(Q)` and the matrix
`A = S D²` satisfy the hypotheses of trace duality, which gives `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ(Y, ℓ∞^ι)`
(`exists_le_relProjConst`). Weights with vanishing entries are handled by perturbing `t` to
`t + ε` and normalizing.

## Main definitions

* `phase z`: the phase `z / |z|` of a scalar `z` (and `0` for `z = 0`).
* `phaseMatrix P`: the sign pattern `sgn(P) = (Pᵢⱼ / |Pᵢⱼ|)ᵢⱼ` of a matrix `P`.
* `clampSign δ`: the continuous approximation `t ↦ t / max(|t|, δ)` of the phase.

## Main statements

* `re_trace_le_relProjConst`: trace duality in `ℓ∞`.
* `exists_le_relProjConst`: for weights `t > 0` with `∑ᵢ tᵢ² = 1` and `P ∈ orthProjs 𝕜 ι m`
  there is an `m`-dimensional subspace `Y ⊆ ℓ∞^ι` with `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ(Y, ℓ∞^ι)`.
* `clConst_le_maxRelProjConst`: `clConst 𝕜 (Fin N) m ≤ λ_𝕜(m, N)`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

open Matrix Finset
open scoped ComplexConjugate

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Sign patterns -/

/-- The phase (or sign) `z / |z|` of a scalar `z`, and `0` for `z = 0`. -/
noncomputable def phase (z : 𝕜) : 𝕜 := ((‖z‖⁻¹ : ℝ) : 𝕜) * z

lemma norm_phase_le (z : 𝕜) : ‖phase z‖ ≤ 1 := by
  rw [phase, norm_mul, RCLike.norm_ofReal, abs_inv, abs_norm]
  by_cases hz : z = 0
  · simp [hz]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

lemma phase_mul_star (z : 𝕜) : phase z * star z = (‖z‖ : 𝕜) := by
  rw [phase, mul_assoc, RCLike.star_def, RCLike.mul_conj]
  by_cases hz : z = 0
  · simp [hz]
  · have : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    push_cast
    field_simp

lemma star_phase (z : 𝕜) : star (phase z) = phase (star z) := by
  simp [phase, RCLike.star_def]

/-- The sign pattern `sgn(P) = (Pᵢⱼ / |Pᵢⱼ|)ᵢⱼ` of a matrix. -/
noncomputable def phaseMatrix (P : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 := Matrix.of fun i j ↦ phase (P i j)

omit [Fintype ι] [DecidableEq ι] in
/-- For a Hermitian matrix, `Pⱼᵢ = conj Pᵢⱼ`. -/
private lemma apply_eq_star_of_herm {P : Matrix ι ι 𝕜} (hP : Pᴴ = P) (i j : ι) :
    P j i = star (P i j) := by
  conv_lhs => rw [← hP]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma phaseMatrix_conjTranspose {P : Matrix ι ι 𝕜} (hP : Pᴴ = P) :
    (phaseMatrix P)ᴴ = phaseMatrix P := by
  ext i j
  simp only [phaseMatrix, conjTranspose_apply, of_apply, star_phase]
  rw [← apply_eq_star_of_herm hP]

omit [Fintype ι] [DecidableEq ι] in
lemma norm_phaseMatrix_apply_le (P : Matrix ι ι 𝕜) (i j : ι) : ‖phaseMatrix P i j‖ ≤ 1 :=
  norm_phase_le _

/-! ### A continuous approximation of the sign -/

/-- `t ↦ t / max(|t|, δ)`, a continuous approximation of the sign function. -/
noncomputable def clampSign (δ : ℝ) (t : 𝕜) : 𝕜 := ((max ‖t‖ δ)⁻¹ : ℝ) • t

/-- `clampSign δ` is continuous for `δ > 0`. -/
lemma continuous_clampSign {δ : ℝ} (hδ : 0 < δ) : Continuous (clampSign (𝕜 := 𝕜) δ) := by
  unfold clampSign
  refine Continuous.smul ?_ continuous_id
  exact (continuous_norm.max continuous_const).inv₀ fun t ↦
    (lt_of_lt_of_le hδ (le_max_right _ _)).ne'

/-- `|t / max(|t|, δ)| ≤ 1`. -/
lemma norm_clampSign_le {δ : ℝ} (hδ : 0 < δ) (t : 𝕜) : ‖clampSign δ t‖ ≤ 1 := by
  have hpos : 0 < max ‖t‖ δ := lt_of_lt_of_le hδ (le_max_right _ _)
  rw [clampSign, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos,
    mul_one]
  exact le_max_left _ _

/-- `conj (t / max(|t|, δ)) · t = |t|² / max(|t|, δ)`. -/
lemma conj_clampSign_mul (δ : ℝ) (t : 𝕜) :
    conj (clampSign δ t) * t = ((‖t‖ ^ 2 / max ‖t‖ δ : ℝ) : 𝕜) := by
  simp only [clampSign, RCLike.real_smul_eq_coe_mul, map_mul, RCLike.conj_ofReal]
  rw [mul_assoc, RCLike.conj_mul]
  push_cast
  ring

/-- `s - δ ≤ s² / max(s, δ)` for `s ≥ 0` and `δ > 0`. -/
lemma sub_le_sq_div_max {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) :
    s - δ ≤ s ^ 2 / max s δ := by
  rcases le_total s δ with h | h
  · rw [max_eq_right h]
    have : 0 ≤ s ^ 2 / δ := by positivity
    linarith
  · rw [max_eq_left h]
    rcases eq_or_lt_of_le hs with rfl | hs'
    · simp; linarith
    · rw [pow_two, mul_div_assoc, div_self hs'.ne', mul_one]; linarith

/-! ### Trace duality -/

/-- **Trace duality in `ℓ∞`.** If `P₀` is idempotent, `A` commutes with `P₀`, and the entries
of the `i`-th column of `A` are bounded by `αᵢ` with `∑ᵢ αᵢ ≤ 1`, then
`Re tr(A P₀) ≤ λ(range P₀, ℓ∞^ι)`. -/
theorem re_trace_le_relProjConst {P₀ A : Matrix ι ι 𝕜} (hP₀ : P₀ * P₀ = P₀)
    (hAP : A * P₀ = P₀ * A) {α : ι → ℝ} (hα : ∀ i j, ‖A j i‖ ≤ α i) (hsum : ∑ i, α i ≤ 1) :
    RCLike.re (A * P₀).trace ≤ relProjConst (LinearMap.range (Matrix.toLin' P₀)) := by
  refine le_relProjConst_of_rowSumNorm _ fun R hR ↦ ?_
  have hRP : R * P₀ = P₀ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v ↦ ?_)
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    exact hR.map_id _ ⟨v, rfl⟩
  have hPR : P₀ * R = R := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v ↦ ?_)
    simp only [Matrix.toLin'_apply]
    obtain ⟨w, hw⟩ := hR.mem v
    rw [Matrix.toLin'_apply] at hw
    rw [← mulVec_mulVec, ← hw, mulVec_mulVec, hP₀]
  have htr : (A * P₀).trace = (A * R).trace := by
    calc (A * P₀).trace = (A * R * P₀).trace := by rw [Matrix.mul_assoc, hRP]
      _ = (P₀ * (A * R)).trace := by rw [Matrix.trace_mul_comm]
      _ = (A * P₀ * R).trace := by rw [← Matrix.mul_assoc, ← hAP]
      _ = (A * R).trace := by rw [Matrix.mul_assoc, hPR]
  have hα0 : ∀ i, 0 ≤ α i := fun i ↦ (norm_nonneg _).trans (hα i i)
  rw [htr]
  calc RCLike.re (A * R).trace ≤ ‖(A * R).trace‖ := RCLike.re_le_norm _
    _ = ‖∑ j, ∑ i, A j i * R i j‖ := by simp [Matrix.trace, Matrix.mul_apply]
    _ ≤ ∑ j, ∑ i, ‖A j i‖ * ‖R i j‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ = ∑ i, ∑ j, ‖A j i‖ * ‖R i j‖ := Finset.sum_comm
    _ ≤ ∑ i, α i * ∑ j, ‖R i j‖ := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [mul_sum]
        exact sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hα i j) (norm_nonneg _)
    _ ≤ ∑ i, α i * rowSumNorm R :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (row_le_rowSumNorm R i) (hα0 i)
    _ = (∑ i, α i) * rowSumNorm R := by rw [sum_mul]
    _ ≤ 1 * rowSumNorm R := mul_le_mul_of_nonneg_right hsum (rowSumNorm_nonneg R)
    _ = rowSumNorm R := one_mul _

/-! ### The weighted lower bound -/

omit [DecidableEq ι] in
lemma continuous_weightedAbsSum (t : ι → ℝ) :
    Continuous fun P : Matrix ι ι 𝕜 ↦ weightedAbsSum t P :=
  continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    continuous_const.mul (continuous_apply_apply i j).norm

omit [DecidableEq ι] in
private lemma trace_mul_eq_sum (B Q : Matrix ι ι 𝕜) : (B * Q).trace = ∑ i, ∑ j, B i j * Q j i := by
  simp [Matrix.trace, Matrix.mul_apply]

private lemma diag_mul_mul_diag_apply (t : ι → ℝ) (S : Matrix ι ι 𝕜) (i j : ι) :
    (diagonal (fun i ↦ (t i : 𝕜)) * S * diagonal (fun i ↦ (t i : 𝕜))) i j =
      (t i : 𝕜) * S i j * (t j : 𝕜) := by
  rw [mul_diagonal, diagonal_mul]

/-- `Re tr(D S D Q) ≤ ∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` for `|Sᵢⱼ| ≤ 1`, `t ≥ 0` and Hermitian `Q`. -/
private lemma re_trace_diag_mul_le {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) {S Q : Matrix ι ι 𝕜}
    (hS : ∀ i j, ‖S i j‖ ≤ 1) (hQ : Qᴴ = Q) :
    RCLike.re (diagonal (fun i ↦ (t i : 𝕜)) * S * diagonal (fun i ↦ (t i : 𝕜)) * Q).trace ≤
      weightedAbsSum t Q := by
  rw [trace_mul_eq_sum, map_sum]
  refine sum_le_sum fun i _ ↦ ?_
  rw [map_sum]
  refine sum_le_sum fun j _ ↦ ?_
  rw [diag_mul_mul_diag_apply]
  refine (RCLike.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg (ht i),
    abs_of_nonneg (ht j), apply_eq_star_of_herm hQ, norm_star]
  have := hS i j
  have := ht i
  have := ht j
  have := norm_nonneg (Q i j)
  have : t i * ‖S i j‖ * t j * ‖Q i j‖ ≤ t i * 1 * t j * ‖Q i j‖ := by gcongr
  linarith

/-- `Re tr(D S D Q) = ∑ᵢⱼ tᵢ tⱼ |Qᵢⱼ|` for `D = diag(t)`, the sign pattern `S = sgn(Q)` and
Hermitian `Q`. -/
lemma re_trace_diag_phaseMatrix {t : ι → ℝ} {Q : Matrix ι ι 𝕜} (hQ : Qᴴ = Q) :
    RCLike.re (diagonal (fun i ↦ (t i : 𝕜)) * phaseMatrix Q * diagonal (fun i ↦ (t i : 𝕜)) *
      Q).trace = weightedAbsSum t Q := by
  rw [trace_mul_eq_sum, map_sum, weightedAbsSum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [diag_mul_mul_diag_apply, apply_eq_star_of_herm hQ]
  have h := phase_mul_star (Q i j)
  have e : (t i : 𝕜) * phaseMatrix Q i j * (t j : 𝕜) * star (Q i j) =
      ((t i * t j * ‖Q i j‖ : ℝ) : 𝕜) := by
    simp only [phaseMatrix, of_apply]
    push_cast
    calc (t i : 𝕜) * phase (Q i j) * (t j : 𝕜) * star (Q i j)
        = (t i : 𝕜) * (t j : 𝕜) * (phase (Q i j) * star (Q i j)) := by ring
      _ = _ := by rw [h]
  rw [e, RCLike.ofReal_re]

omit [DecidableEq ι] in
/-- **The formula of Chalmers and Lewicki, lower bound for positive weights.** For weights
`t > 0` with `∑ᵢ tᵢ² = 1` and `P ∈ orthProjs 𝕜 ι m` there is an `m`-dimensional subspace
`Y ⊆ ℓ∞^ι` with `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ(Y, ℓ∞^ι)`. -/
theorem exists_le_relProjConst {m : ℕ} {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (ht1 : ∑ i, t i ^ 2 = 1) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    ∃ Y : Submodule 𝕜 (ι → 𝕜), Module.finrank 𝕜 Y = m ∧ weightedAbsSum t P ≤ relProjConst Y := by
  classical
  -- a maximizer `Q` of `∑ tᵢ tⱼ |Qᵢⱼ|`
  obtain ⟨Q, hQ, hQmax⟩ := (isCompact_orthProjs (𝕜 := 𝕜) (ι := ι) m).exists_isMaxOn ⟨P, hP⟩
    (continuous_weightedAbsSum t).continuousOn
  set D : Matrix ι ι 𝕜 := diagonal fun i ↦ (t i : 𝕜) with hD
  set Dinv : Matrix ι ι 𝕜 := diagonal fun i ↦ ((t i)⁻¹ : 𝕜) with hDinv
  have htne : ∀ i, (t i : 𝕜) ≠ 0 := fun i ↦ by exact_mod_cast (ht i).ne'
  have hDD : Dinv * D = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; field_simp [htne i]
  have hDD' : D * Dinv = 1 := by
    rw [hDinv, hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; field_simp [htne i]
  set S := phaseMatrix Q with hS
  set B := D * S * D with hB
  have hDh : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hBh : Bᴴ = B := by
    rw [hB, conjTranspose_mul, conjTranspose_mul, hDh,
      phaseMatrix_conjTranspose hQ.1.conjTranspose_eq, Matrix.mul_assoc]
  -- `Q` maximizes `Re tr(B ·)`, hence commutes with `B`
  have hBQ : B * Q = Q * B := by
    refine commute_of_isMaxOn hBh hQ fun Q' hQ' ↦ ?_
    calc RCLike.re (B * Q').trace ≤ weightedAbsSum t Q' :=
          re_trace_diag_mul_le (fun i ↦ (ht i).le) (norm_phaseMatrix_apply_le Q)
            hQ'.1.conjTranspose_eq
      _ ≤ weightedAbsSum t Q := hQmax hQ'
      _ = RCLike.re (B * Q).trace := (re_trace_diag_phaseMatrix hQ.1.conjTranspose_eq).symm
  -- conjugation by `D`
  have hconj : ∀ X Y : Matrix ι ι 𝕜, Dinv * X * D * (Dinv * Y * D) = Dinv * (X * Y) * D := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D Dinv, hDD', Matrix.one_mul]
  have htrconj : ∀ X : Matrix ι ι 𝕜, (Dinv * X * D).trace = X.trace := by
    intro X
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hDD', Matrix.mul_one]
  -- the subspace `Y = D⁻¹ range(Q)` and the certificate `A = S D²`
  set P₀ := Dinv * Q * D with hP₀
  have hP₀P₀ : P₀ * P₀ = P₀ := by rw [hP₀, hconj, hQ.1.mul_self]
  have htrP₀ : P₀.trace = m := by rw [hP₀, htrconj, hQ.2]
  set A := S * D * D with hA
  have hA' : A = Dinv * B * D := by
    rw [hA, hB, ← Matrix.mul_assoc Dinv, ← Matrix.mul_assoc Dinv, hDD, Matrix.one_mul]
  have hAP : A * P₀ = P₀ * A := by
    rw [hA', hP₀, hconj, hconj, hBQ]
  have htrA : (A * P₀).trace = (B * Q).trace := by
    rw [hA', hP₀, hconj, htrconj]
  have hαA : ∀ i j, ‖A j i‖ ≤ t i ^ 2 := by
    intro i j
    rw [hA, mul_diagonal, mul_diagonal, norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_pos (ht i)]
    have h1 := norm_phaseMatrix_apply_le Q j i
    have := ht i
    nlinarith
  refine ⟨LinearMap.range (Matrix.toLin' P₀), ?_, ?_⟩
  · have h := finrank_range_eq_trace hP₀P₀
    rw [htrP₀] at h
    exact_mod_cast h
  · calc weightedAbsSum t P ≤ weightedAbsSum t Q := hQmax hP
      _ = RCLike.re (B * Q).trace := (re_trace_diag_phaseMatrix hQ.1.conjTranspose_eq).symm
      _ = RCLike.re (A * P₀).trace := by rw [htrA]
      _ ≤ _ := re_trace_le_relProjConst hP₀P₀ hAP hαA (le_of_eq ht1)

/-! ### From positive weights to all weights -/

/-- **The formula of Chalmers and Lewicki, lower bound** ([DL, Theorem 1.1]).
`clConst 𝕜 (Fin N) m ≤ λ_𝕜(m, N)`: `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ λ_𝕜(m, N)` for every unit weight `t` and
every `P ∈ orthProjs 𝕜 (Fin N) m`. -/
theorem clConst_le_maxRelProjConst (m N : ℕ) : clConst 𝕜 (Fin N) m ≤ maxRelProjConst 𝕜 m N := by
  refine clConst_le (maxRelProjConst_nonneg m N) fun t P ht hP ↦ ?_
  set L := maxRelProjConst 𝕜 m N
  have hL := maxRelProjConst_nonneg (𝕜 := 𝕜) m N
  -- positive weights
  have hpos : ∀ s : Fin N → ℝ, (∀ i, 0 < s i) → ∑ i, s i ^ 2 = 1 → weightedAbsSum s P ≤ L := by
    intro s hs hs1
    obtain ⟨Y, hY, hle⟩ := exists_le_relProjConst hs hs1 hP
    exact hle.trans (relProjConst_le_maxRelProjConst Y hY)
  -- perturb `t` to `t + ε` and normalize
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set n : ℝ := (N : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set ε : ℝ := min 1 (δ / (3 * n * L + 1)) with hε_def
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (3 * n * L + 1) ≤ δ := by
    have := min_le_right 1 (δ / (3 * n * L + 1))
    rw [← hε_def] at this
    calc ε * (3 * n * L + 1) ≤ δ / (3 * n * L + 1) * (3 * n * L + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  set u : Fin N → ℝ := fun i ↦ t i + ε
  set c : ℝ := ∑ i, u i ^ 2 with hc
  have hu : ∀ i, 0 < u i := fun i ↦ by have := ht.nonneg i; positivity
  have hti1 : ∀ i, t i ≤ 1 := fun i ↦ by
    have h := single_le_sum (f := fun i ↦ t i ^ 2) (fun j _ ↦ sq_nonneg (t j)) (mem_univ i)
    rw [ht.sum_sq] at h
    nlinarith [ht.nonneg i]
  have hc1 : 1 ≤ c := by
    rw [hc, ← ht.sum_sq]
    exact sum_le_sum fun i _ ↦ by have := ht.nonneg i; nlinarith
  have hc2 : c ≤ 1 + 3 * n * ε := by
    have h : ∀ i, u i ^ 2 ≤ t i ^ 2 + 3 * ε := fun i ↦ by
      have := ht.nonneg i; have := hti1 i; nlinarith
    calc c ≤ ∑ i, (t i ^ 2 + 3 * ε) := sum_le_sum fun i _ ↦ h i
      _ = 1 + 3 * n * ε := by
          rw [sum_add_distrib, ht.sum_sq]; simp [n]; ring
  have hc0 : 0 < c := by linarith
  -- the normalized weights `s = u / √c`
  set s : Fin N → ℝ := fun i ↦ u i / √c
  have hs : ∀ i, 0 < s i := fun i ↦ div_pos (hu i) (Real.sqrt_pos.2 hc0)
  have hs1 : ∑ i, s i ^ 2 = 1 := by
    simp only [s, div_pow, Real.sq_sqrt hc0.le, ← sum_div, ← hc, div_self hc0.ne']
  have h1 : weightedAbsSum t P ≤ c * weightedAbsSum s P := by
    have e : c * weightedAbsSum s P = weightedAbsSum u P := by
      simp only [weightedAbsSum, mul_sum, s]
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
      have hsq : √c ^ 2 = c := Real.sq_sqrt hc0.le
      have hsc : √c ≠ 0 := (Real.sqrt_pos.2 hc0).ne'
      field_simp
      rw [hsq]
      ring
    rw [e]
    refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
    have := ht.nonneg i; have := ht.nonneg j
    have : t i * t j ≤ u i * u j := by
      simp only [u]; nlinarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  calc weightedAbsSum t P ≤ c * weightedAbsSum s P := h1
    _ ≤ (1 + 3 * n * ε) * L := by
        have := hpos s hs hs1
        have := weightedAbsSum_nonneg (fun i ↦ (hs i).le) P
        nlinarith
    _ ≤ L + δ := by nlinarith

end ProjectionConstants
