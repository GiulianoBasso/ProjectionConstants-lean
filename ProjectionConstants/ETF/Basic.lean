/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ChalmersLewicki.Absolute

/-!
# Equiangular tight frames and the bound `δ_{m,N}`

An **equiangular tight frame** `ETF(m, N)` is a family of `N` unit vectors `u₁, …, u_N ∈ 𝕜^m`
that is tight (`U Uᴴ = α I_m` for the matrix `U` with columns `uᵢ` and some `α > 0`) and
equiangular (`|⟨uᵢ, uⱼ⟩|` is the same for all `i ≠ j`). The rescaled Gram matrix
`P = (m/N) Uᴴ U` of an ETF is an orthogonal projection of rank `m` with constant diagonal `m/N`
whose off-diagonal entries have modulus `(m/N) φ_{m,N}`, and `(1/N) ∑ᵢⱼ |Pᵢⱼ| = δ_{m,N}`. The
sign pattern of `P` is a polynomial in `P`, so trace duality (`re_trace_le_relProjConst`) gives
`δ_{m,N} ≤ λ(range P, ℓ∞^N)`; in particular `δ_{m,N} ≤ λ_𝕜(m, N)` if an `ETF(m, N)` exists. The
number `δ_{m,N}` is also the upper bound of König, Lewis and Lin [KLL] for `λ_𝕜(m, N)`, see
[DL, Theorem 1.2] and `ProjectionConstants.Bounds.KLL`.

## Main definitions

* `delta m N`: `δ_{m,N} = (m/N) (1 + √((N-1)(N-m)/m))`.
* `etfAngle m N`: `φ_{m,N} = √((N-m)/(m(N-1)))`.
* `IsETF U`: the columns of `U ∈ 𝕜^{m×ι}` form an equiangular tight frame.
* `ExistsETF 𝕜 m N`: there is an equiangular tight frame of `N` vectors in `𝕜^m`.
* `IsETFProj m P`: `P` is an **ETF projection**, an orthogonal projection of rank `m` with
  constant diagonal `m/N` and off-diagonal entries of constant modulus.

## Main statements

* `IsETF.isETFProj`, `IsETFProj.exists_isETF`: ETFs and ETF projections correspond to each
  other.
* `IsETFProj.norm_apply`: the off-diagonal entries of an ETF projection have modulus
  `(m/N) φ_{m,N}`, that is, `|⟨uᵢ, uⱼ⟩| = φ_{m,N}` for `i ≠ j` [DL, (4)].
* `IsETFProj.absSum_div_eq`: `(1/N) ∑ᵢⱼ |Pᵢⱼ| = δ_{m,N}` for an ETF projection `P`.
* `absSum_div_le_relProjConst`: if the sign pattern of an orthogonal projection `P` commutes
  with `P`, then `(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ λ(range P, ℓ∞^N)`.
* `IsETFProj.commute_phaseMatrix`: the sign pattern of an ETF projection commutes with it.
* `IsETFProj.delta_le_relProjConst`: `δ_{m,N} ≤ λ(range P, ℓ∞^N)` for an ETF projection `P`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [KLL] H. König, D. R. Lewis, P.-K. Lin, *Finite dimensional projection constants*,
  Studia Math. 75 (1983).
-/

open Matrix Finset

namespace ProjectionConstants

/-- `δ_{m,N} = (m/N) (1 + √((N-1)(N-m)/m))`, the bound of König, Lewis and Lin. -/
noncomputable def delta (m N : ℕ) : ℝ := m / N * (1 + √((N - 1) * (N - m) / m))

/-- The angle of an equiangular tight frame, `φ_{m,N} = √((N-m)/(m(N-1)))`. -/
noncomputable def etfAngle (m N : ℕ) : ℝ := √((N - m) / (m * (N - 1)))

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The columns `uᵢ` of `U ∈ 𝕜^{m×ι}` form an **equiangular tight frame**: they are unit
vectors, `U Uᴴ = α I_m` for some `α > 0`, and `|⟨uᵢ, uⱼ⟩|` is the same for all `i ≠ j`. -/
structure IsETF {m : ℕ} (U : Matrix (Fin m) ι 𝕜) : Prop where
  /-- The columns are unit vectors. -/
  unit : ∀ i, (Uᴴ * U) i i = 1
  /-- The frame is tight: `U Uᴴ = α I_m` for some `α > 0`. -/
  tight : ∃ α : ℝ, 0 < α ∧ U * Uᴴ = (α : 𝕜) • 1
  /-- The inner products of distinct columns have constant modulus. -/
  equiangular : ∃ c : ℝ, ∀ i j, i ≠ j → ‖(Uᴴ * U) i j‖ = c

variable (𝕜) in
/-- There is an equiangular tight frame of `N` vectors in `𝕜^m`. -/
def ExistsETF (m N : ℕ) : Prop := ∃ U : Matrix (Fin m) (Fin N) 𝕜, IsETF U

/-- An **ETF projection**, the Gram form of an equiangular tight frame: an orthogonal
projection of rank `m` with diagonal `m/N` and off-diagonal entries of constant modulus. -/
structure IsETFProj (m : ℕ) (P : Matrix ι ι 𝕜) : Prop where
  /-- `P` is an orthogonal projection of rank `m`. -/
  mem : P ∈ orthProjs 𝕜 ι m
  /-- The diagonal entries of `P` are `m/N`. -/
  diag : ∀ i, P i i = (m : 𝕜) / Fintype.card ι
  /-- The off-diagonal entries of `P` have constant modulus. -/
  equiangular : ∃ c : ℝ, ∀ i j, i ≠ j → ‖P i j‖ = c

/-! ### Frames and projections -/

section Correspondence

variable {m : ℕ}

/-- The tightness constant of an ETF is `N/m`. -/
lemma IsETF.tight_const {U : Matrix (Fin m) ι 𝕜} (hU : IsETF U) {α : ℝ}
    (hα : U * Uᴴ = (α : 𝕜) • 1) : α * m = Fintype.card ι := by
  have h1 : (U * Uᴴ).trace = (α * m : ℝ) := by
    rw [hα, trace_smul, trace_one]; simp
  have h2 : (U * Uᴴ).trace = (Fintype.card ι : 𝕜) := by
    rw [trace_mul_comm]
    simp [Matrix.trace, hU.unit]
  exact_mod_cast h1.symm.trans h2

/-- An ETF gives an ETF projection `(m/N) Uᴴ U`. -/
theorem IsETF.isETFProj {U : Matrix (Fin m) ι 𝕜} (hU : IsETF U) (hm : m ≠ 0) :
    IsETFProj m (((m : 𝕜) / Fintype.card ι) • (Uᴴ * U)) := by
  obtain ⟨α, hα0, hα⟩ := hU.tight
  have hαm := hU.tight_const hα
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    rw [← hαm]; exact mul_ne_zero hα0.ne' hm'
  have hαeq : (α : 𝕜) = Fintype.card ι / m := by
    have : α = Fintype.card ι / m := by field_simp; linarith
    rw [this]; push_cast; rfl
  refine ⟨⟨.of_conjTranspose_eq ?_ ?_, ?_⟩, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    simp
  · rw [smul_mul_smul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc U, hα, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, smul_smul, hαeq]
    congr 1
    have : (Fintype.card ι : 𝕜) ≠ 0 := by exact_mod_cast hN
    have : (m : 𝕜) ≠ 0 := by exact_mod_cast hm
    field_simp
  · rw [trace_smul, trace_mul_comm, hα, trace_smul, trace_one, hαeq]
    have : (Fintype.card ι : 𝕜) ≠ 0 := by exact_mod_cast hN
    have : (m : 𝕜) ≠ 0 := by exact_mod_cast hm
    simp only [Fintype.card_fin, smul_eq_mul]
    field_simp
  · intro i
    rw [Matrix.smul_apply, hU.unit, smul_eq_mul, mul_one]
  · obtain ⟨c, hc⟩ := hU.equiangular
    refine ⟨(m / Fintype.card ι) * c, fun i j hij ↦ ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hc i j hij, norm_div, RCLike.norm_natCast,
      RCLike.norm_natCast]

/-- An ETF projection comes from an ETF in `𝕜^m`. -/
theorem IsETFProj.exists_isETF {P : Matrix ι ι 𝕜} (hP : IsETFProj m P)
    (hm : m ≠ 0) : ∃ U : Matrix (Fin m) ι 𝕜, IsETF U := by
  obtain ⟨V, hV, hVP⟩ := exists_parseval_of_mem_orthProjs hP.mem
  have hNpos : (0 : ℝ) < Fintype.card ι := by
    have := le_card_of_mem_orthProjs hP.mem
    have : 0 < Fintype.card ι := lt_of_lt_of_le (Nat.pos_of_ne_zero hm) this
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  set s : ℝ := √(Fintype.card ι / m) with hs
  have hs2 : s ^ 2 = Fintype.card ι / m := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hN𝕜 : (Fintype.card ι : 𝕜) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hm𝕜 : (m : 𝕜) ≠ 0 := by exact_mod_cast hm
  refine ⟨(s : 𝕜) • V, ⟨fun i ↦ ?_, ⟨s ^ 2, by positivity, ?_⟩, ?_⟩⟩
  · rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVP, Matrix.smul_apply,
      hP.diag, RCLike.star_def, RCLike.conj_ofReal, smul_eq_mul, ← sq, ← RCLike.ofReal_pow, hs2]
    push_cast
    field_simp
  · rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV, RCLike.star_def,
      RCLike.conj_ofReal, ← sq]
    push_cast
    rfl
  · obtain ⟨c, hc⟩ := hP.equiangular
    refine ⟨s ^ 2 * c, fun i j hij ↦ ?_⟩
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVP, Matrix.smul_apply,
      RCLike.star_def, RCLike.conj_ofReal, smul_eq_mul, norm_mul, hc i j hij, norm_mul,
      RCLike.norm_ofReal, abs_of_pos hs0, ← sq]

end Correspondence

/-! ### The angle and the value of an ETF -/

section Angle

variable [DecidableEq ι] {m : ℕ} {P : Matrix ι ι 𝕜}

omit [DecidableEq ι] in
lemma IsETFProj.re_diag (hP : IsETFProj m P) (i : ι) :
    RCLike.re (P i i) = m / Fintype.card ι := by
  rw [hP.diag, show ((m : 𝕜) / Fintype.card ι) = ((m / Fintype.card ι : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]

omit [DecidableEq ι] in
lemma IsETFProj.norm_diag (hP : IsETFProj m P) (i : ι) : ‖P i i‖ = m / Fintype.card ι := by
  rw [hP.mem.1.norm_diag_eq, hP.re_diag]

/-- A real identity behind [DL, (4)]: if `x = x² + (N-1)c²` with `x = m/N`, then
`c = x φ_{m,N}`. -/
private lemma etf_angle_aux {m N c : ℝ} (hm : 0 < m) (hmN : m ≤ N) (hN : 2 ≤ N) (hc : 0 ≤ c)
    (h : m / N = (m / N) ^ 2 + (N - 1) * c ^ 2) :
    c = m / N * √((N - m) / (m * (N - 1))) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hcsq : c ^ 2 = (m / N) ^ 2 * ((N - m) / (m * (N - 1))) := by
    have e : (N - 1) * c ^ 2 = m / N - (m / N) ^ 2 := by linarith
    have e2 : c ^ 2 = (m / N - (m / N) ^ 2) / (N - 1) := by
      rw [← e]; field_simp
    rw [e2]
    field_simp
  have hx : 0 ≤ (N - m) / (m * (N - 1)) := by
    apply div_nonneg <;> nlinarith
  rw [← Real.sqrt_sq hc, hcsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

omit [DecidableEq ι] in
/-- The off-diagonal entries of an ETF projection have modulus `(m/N) φ_{m,N}` ([DL, (4)]). -/
theorem IsETFProj.norm_apply (hP : IsETFProj m P) (hm : m ≠ 0) {i j : ι} (hij : i ≠ j) :
    ‖P i j‖ = m / Fintype.card ι * etfAngle m (Fintype.card ι) := by
  classical
  obtain ⟨c, hc⟩ := hP.equiangular
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmN : (m : ℝ) ≤ Fintype.card ι := by exact_mod_cast le_card_of_mem_orthProjs hP.mem
  have hN2 : (2 : ℝ) ≤ Fintype.card ι := by
    have : 2 ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.one_lt_card.2 ⟨i, mem_univ _, j, mem_univ _, hij⟩
    exact_mod_cast this
  have hrow := hP.mem.1.re_diag_eq_sum_row i
  rw [hP.re_diag] at hrow
  have hsplit : ∑ k, ‖P i k‖ ^ 2 = (m / Fintype.card ι) ^ 2 + (Fintype.card ι - 1) * c ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hP.norm_diag]
    have h2 : ∑ k ∈ univ.erase i, ‖P i k‖ ^ 2 = ∑ k ∈ univ.erase i, c ^ 2 :=
      sum_congr rfl fun k hk ↦ by rw [hc i k (Ne.symm (ne_of_mem_erase hk))]
    rw [h2, sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
      Nat.cast_sub (Fintype.card_pos_iff.2 ⟨i⟩)]
    push_cast
    ring
  rw [hsplit] at hrow
  have hc0 : 0 ≤ c := by rw [← hc i j hij]; exact norm_nonneg _
  rw [hc i j hij, etfAngle]
  exact etf_angle_aux hm0 hmN hN2 hc0 hrow

omit [DecidableEq ι] in
/-- `(1/N) ∑ᵢⱼ |Pᵢⱼ| = δ_{m,N}` for an ETF projection. -/
theorem IsETFProj.absSum_div_eq (hP : IsETFProj m P) (hm : m ≠ 0) :
    absSum P / Fintype.card ι = delta m (Fintype.card ι) := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmN : (m : ℝ) ≤ Fintype.card ι := by exact_mod_cast le_card_of_mem_orthProjs hP.mem
  have hne : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · have : (Fintype.card ι : ℝ) = 0 := by simp
      linarith
    · exact h
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
  have hrow : ∀ i, ∑ j, ‖P i j‖ = m / Fintype.card ι +
      (Fintype.card ι - 1) * (m / Fintype.card ι * etfAngle m (Fintype.card ι)) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hP.norm_diag]
    have h2 : ∑ k ∈ univ.erase i, ‖P i k‖ =
        ∑ k ∈ univ.erase i, m / Fintype.card ι * etfAngle m (Fintype.card ι) :=
      sum_congr rfl fun k hk ↦ hP.norm_apply hm (Ne.symm (ne_of_mem_erase hk))
    rw [h2, sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
      Nat.cast_sub Fintype.card_pos]
    push_cast
    ring
  rw [absSum, sum_congr rfl fun i _ ↦ hrow i, sum_const, card_univ, nsmul_eq_mul, delta,
    etfAngle]
  generalize hNdef : (Fintype.card ι : ℝ) = N at *
  have hN0 : 0 < N := lt_of_lt_of_le hm0 hmN
  rcases eq_or_lt_of_le (show (1 : ℝ) ≤ N by linarith) with hN1 | hN1
  · subst hN1
    have hm1' : (m : ℝ) = 1 := le_antisymm hmN hm1
    rw [hm1']
    simp
  -- `(N - 1) φ = √((N-1)(N-m)/m)`
  have hN1' : 0 < N - 1 := by linarith
  have h : (N - 1) * √((N - m) / (m * (N - 1))) = √((N - 1) * (N - m) / m) := by
    rw [show (N - 1) * (N - m) / m = (N - 1) ^ 2 * ((N - m) / (m * (N - 1))) by
      field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN1'.le]
  rw [← h]
  field_simp

end Angle

/-! ### Lower bounds from commuting sign patterns -/

section LowerBound

variable [DecidableEq ι] {m : ℕ}

/-- The phase of a positive real number is `1`. -/
lemma phase_ofReal_of_pos {x : ℝ} (hx : 0 < x) : phase (x : 𝕜) = 1 := by
  rw [phase, RCLike.norm_ofReal, abs_of_pos hx, ← RCLike.ofReal_mul, inv_mul_cancel₀ hx.ne',
    RCLike.ofReal_one]

/-- If the sign pattern `sgn(P)` of an orthogonal projection commutes with `P`, then
`(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ λ(range P, ℓ∞^N)`. -/
theorem absSum_div_le_relProjConst {P : Matrix ι ι 𝕜} (hP : IsStarProjection P)
    (hcomm : phaseMatrix P * P = P * phaseMatrix P) :
    absSum P / Fintype.card ι ≤ relProjConst (LinearMap.range (Matrix.toLin' P)) := by
  cases isEmpty_or_nonempty ι
  · simp [absSum, relProjConst_nonneg]
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  set A : Matrix ι ι 𝕜 := ((1 / N : ℝ) : 𝕜) • phaseMatrix P
  have hAP : A * P = P * A := by
    simp only [A, Matrix.smul_mul, Matrix.mul_smul, hcomm]
  have hα : ∀ i j, ‖A j i‖ ≤ 1 / N := by
    intro i j
    simp only [A, Matrix.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal]
    rw [abs_of_pos (by positivity)]
    calc 1 / N * ‖phaseMatrix P j i‖ ≤ 1 / N * 1 :=
          mul_le_mul_of_nonneg_left (norm_phaseMatrix_apply_le P j i) (by positivity)
      _ = 1 / N := mul_one _
  have hsum : ∑ _i : ι, 1 / N ≤ 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    rw [mul_one_div, div_self hN.ne']
  have htr : RCLike.re (A * P).trace = absSum P / N := by
    have h := re_trace_diag_phaseMatrix (t := fun _ ↦ (1 : ℝ)) hP.conjTranspose_eq
    simp only [RCLike.ofReal_one, diagonal_one, Matrix.one_mul, Matrix.mul_one] at h
    simp only [A, Matrix.smul_mul, trace_smul, smul_eq_mul, RCLike.re_ofReal_mul, h,
      weightedAbsSum, one_mul, absSum]
    ring
  rw [← htr]
  exact re_trace_le_relProjConst hP.mul_self hAP hα hsum

omit [DecidableEq ι] in
/-- The sign pattern of an ETF projection is a polynomial in `P`, hence commutes with `P`. -/
theorem IsETFProj.commute_phaseMatrix {P : Matrix ι ι 𝕜} (hP : IsETFProj m P) (hm : m ≠ 0) :
    phaseMatrix P * P = P * phaseMatrix P := by
  classical
  obtain ⟨c, hc⟩ := hP.equiangular
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hN0 : (0 : ℝ) < Fintype.card ι :=
    lt_of_lt_of_le hm0 (by exact_mod_cast le_card_of_mem_orthProjs hP.mem)
  have hdiag : ∀ i, phase (P i i) = 1 := by
    intro i
    rw [hP.diag, show ((m : 𝕜) / Fintype.card ι) = ((m / Fintype.card ι : ℝ) : 𝕜) by
      push_cast; rfl, phase_ofReal_of_pos (by positivity)]
  rcases eq_or_ne c 0 with rfl | hc0
  · -- `P` is diagonal and `sgn P = 1`
    have hS : phaseMatrix P = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [show phaseMatrix P i i = phase (P i i) from rfl, hdiag]
        simp
      · have : P i j = 0 := norm_eq_zero.1 (hc i j hij)
        simp [phaseMatrix, this, phase, hij]
    rw [hS, Matrix.one_mul, Matrix.mul_one]
  · -- `sgn P = 1 + (P - (m/N) 1)/c`
    have hS : phaseMatrix P = 1 + ((1 / c : ℝ) : 𝕜) • (P - ((m : 𝕜) / Fintype.card ι) • 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [show phaseMatrix P i i = phase (P i i) from rfl, hdiag]
        simp [hP.diag]
      · simp only [phaseMatrix, of_apply, phase, Matrix.add_apply, one_apply_ne hij,
          Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_zero, sub_zero, zero_add,
          hc i j hij]
        push_cast
        ring
    rw [hS]
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, sub_mul, mul_sub]

/-- **The lower bound from ETF projections.** If `P` is an ETF projection of rank `m`, then
`δ_{m,N} ≤ λ(range P, ℓ∞^N)`. -/
theorem IsETFProj.delta_le_relProjConst {P : Matrix ι ι 𝕜} (hP : IsETFProj m P) (hm : m ≠ 0) :
    delta m (Fintype.card ι) ≤ relProjConst (LinearMap.range (Matrix.toLin' P)) := by
  rw [← hP.absSum_div_eq hm]
  exact absSum_div_le_relProjConst hP.mem.1 (hP.commute_phaseMatrix hm)

end LowerBound

end ProjectionConstants
