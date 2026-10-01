/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Bounds.KLL

/-!
# The equality case in the bound of König, Lewis and Lin

We characterize the equality case of the bound `λ_𝕜(m, N) ≤ δ_{m,N}` of König, Lewis and Lin
(`ProjectionConstants.Bounds.KLL`), following [DL, Theorem 1.2] ([KLL], [FS]). For `1 ≤ m ≤ N`
the following are equivalent:

* (i) there is an equiangular tight frame of `N` vectors in `𝕜^m`;
* (ii) `μ_𝕜(m, N) = δ_{m,N}`;
* (iii) `λ_𝕜(m, N) = δ_{m,N}`.

The implications (i) ⇒ (ii) ⇒ (iii) follow from `quasiRelConst_eq_delta_of_existsETF` and
`μ ≤ λ ≤ δ`. For (iii) ⇒ (i) we take a maximizer `(t, P)` of the Chalmers–Lewicki functional
[DL, Theorem 1.1] (`exists_clConst_eq`) and analyse the equality cases in the proof of the bound
`weightedAbsSum_le_delta`.

## Main statements

* `isETFProj_of_delta_le_weightedAbsSum`: if `2 ≤ m < N`, `t` is a unit weight, `P` is an
  orthogonal projection of rank `m` and `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≥ δ_{m,N}`, then `P` is the Gram matrix
  of an equiangular tight frame (`IsETFProj`).
* `existsETF_of_maxRelProjConst_eq_delta`: if `λ_𝕜(m, N) = δ_{m,N}`, then there is an
  `ETF(m, N)`.
* `existsETF_tfae`: the equivalence of (i), (ii) and (iii) [DL, Theorem 1.2].

## Proof sketch

With `xᵢ = tᵢ²` and `pᵢ = Pᵢᵢ`, the three Cauchy–Schwarz inequalities in the proof of
`weightedAbsSum_le_delta` become equalities. If the diagonal of `P` is constant, this forces `t`
to be uniform and `|Pᵢⱼ|` to be constant off the diagonal, so `P` is an ETF projection.
Otherwise `xᵢ - 1/N = κ (pᵢ - m/N)` and `κ |Pᵢⱼ| = tᵢ tⱼ` for some `κ > 0`, and the identity
`pᵢ = ∑ⱼ |Pᵢⱼ|²` becomes an affine equation for `pᵢ`; since the `pᵢ` are not all equal, both of
its coefficients vanish, which forces `N = m + 1` and `κ = -1`, a contradiction. The cases
`m = 1` and `m = N` are trivial (`existsETF_one_left`, `existsETF_self`).

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [KLL] H. König, D. R. Lewis, P.-K. Lin, *Finite dimensional projection constants*,
  Studia Math. 75 (1983).
* [FS] S. Foucart, L. Skrzypek, *On maximal relative projection constants* (2017).

## Tags

projection constant, equiangular tight frame
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-! ### Equality in the Cauchy–Schwarz inequality -/

/-- Equality in `√a √b + √c √d ≤ √(a + c) √(b + d)`. -/
private lemma sqrt_mul_eq_of_sqrt_mul_add_sqrt_mul_eq {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (h : √a * √b + √c * √d = √(a + c) * √(b + d)) :
    √a * √d = √c * √b := by
  have h2 := congrArg (· ^ 2) h
  simp only [mul_pow, Real.sq_sqrt (add_nonneg ha hc), Real.sq_sqrt (add_nonneg hb hd)] at h2
  have e : (√a * √b + √c * √d) ^ 2 = a * b + c * d + 2 * (√a * √b) * (√c * √d) := by
    rw [add_sq, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
      Real.sq_sqrt hd]
    ring
  rw [e] at h2
  have h3 : (√a * √d - √c * √b) ^ 2 = 0 := by
    have e2 : (√a * √d - √c * √b) ^ 2 = a * d + c * b - 2 * (√a * √b) * (√c * √d) := by
      rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
        Real.sq_sqrt hd]
      ring
    rw [e2]
    linarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
  linarith

/-! ### `δ_{m,N} > 1` -/

/-- `δ_{m,N} > 1` for `2 ≤ m < N`. -/
lemma one_lt_delta {m N : ℕ} (hm : 2 ≤ m) (hmN : m < N) : 1 < delta m N := by
  rw [delta_eq (by omega) hmN.le]
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmN' : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [← Real.sqrt_mul (by rw [sub_nonneg, div_le_one hN0]; linarith)]
  have key : (1 - (m : ℝ) / N) ^ 2 < (1 - 1 / (N : ℝ)) * ((m : ℝ) - m ^ 2 / N) := by
    rw [← sub_pos]
    have e : (1 - 1 / (N : ℝ)) * ((m : ℝ) - m ^ 2 / N) - (1 - (m : ℝ) / N) ^ 2 =
        (N - m) * N * (m - 1) / (N : ℝ) ^ 2 := by
      field_simp
      ring
    rw [e]
    apply div_pos _ (by positivity)
    apply mul_pos (mul_pos (by linarith) hN0) (by linarith)
  have hlt : 1 - m / N < √((1 - 1 / N) * (m - m ^ 2 / N)) :=
    Real.lt_sqrt_of_sq_lt key
  linarith

/-! ### The equality case -/

/-- **Equality in the bound of König, Lewis and Lin.** If `2 ≤ m < N`, `t` is a unit weight, `P`
is an orthogonal projection of rank `m` and `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≥ δ_{m,N}`, then `P` is an ETF
projection. -/
theorem isETFProj_of_delta_le_weightedAbsSum {m : ℕ} (hm : 2 ≤ m)
    (hmN : m < Fintype.card ι) {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) (hδ : delta m (Fintype.card ι) ≤ weightedAbsSum t P) :
    IsETFProj m P := by
  classical
  have hδ1 := one_lt_delta hm hmN
  rw [delta_eq (by omega) hmN.le] at hδ
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmN' : (m : ℝ) + 1 ≤ N := by rw [hN_def]; exact_mod_cast hmN
  have hN0 : 0 < N := by linarith
  -- notation
  set x : ι → ℝ := fun i ↦ t i ^ 2 with hx
  set p : ι → ℝ := fun i ↦ RCLike.re (P i i) with hp
  set g : ι → ι → ℝ := fun i j ↦ ‖P i j‖ with hg
  have hx1 : ∑ i, x i = 1 := ht.sum_sq
  have hp1 : ∑ i, p i = m := sum_re_diag hP
  have hgii : ∀ i, g i i = p i := fun i ↦ hP.1.norm_diag_eq i
  have hrow : ∀ i, ∑ j, g i j ^ 2 = p i := fun i ↦ (hP.1.re_diag_eq_sum_row i).symm
  have hp_le : ∀ i, p i ≤ 1 := fun i ↦ hP.1.re_diag_le_one i
  have hx0 : ∀ i, 0 ≤ x i := fun i ↦ sq_nonneg _
  set X := ∑ i, x i ^ 2 with hX
  set Q := ∑ i, p i ^ 2 with hQ
  set S := univ.filter (fun q : ι × ι ↦ q.1 ≠ q.2) with hS
  -- the decomposition of the proof of `weightedAbsSum_le_delta`
  have hsplit : weightedAbsSum t P = ∑ i, x i * p i +
      ∑ q ∈ S, (t q.1 * t q.2) * g q.1 q.2 := by
    have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag
      (fun q : ι × ι ↦ (t q.1 * t q.2) * g q.1 q.2)
    rw [Fintype.sum_prod_type] at h; simp only at h
    change ∑ i, ∑ j, t i * t j * g i j = _
    rw [h]
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hgii]; simp [x, sq]
  have e_tt : ∑ q ∈ S, (t q.1 * t q.2) ^ 2 = 1 - X := by
    have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag (fun q : ι × ι ↦ x q.1 * x q.2)
    rw [Fintype.sum_prod_type] at h; simp only at h; rw [← Finset.sum_mul_sum, hx1] at h
    have e : ∑ q ∈ S, (t q.1 * t q.2) ^ 2 = ∑ q ∈ S, x q.1 * x q.2 :=
      sum_congr rfl fun q _ ↦ by simp [x]; ring
    rw [e, hX]
    simp only [← sq] at h
    linarith
  have e_gg : ∑ q ∈ S, g q.1 q.2 ^ 2 = m - Q := by
    have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag (fun q : ι × ι ↦ g q.1 q.2 ^ 2)
    rw [Fintype.sum_prod_type] at h; simp only at h
    have e : ∑ i, ∑ j, g i j ^ 2 = m := by
      rw [← hp1]; exact sum_congr rfl fun i _ ↦ hrow i
    simp only [hgii] at h
    rw [hQ]
    linarith
  have e_D : ∑ i, x i * p i = m / N + ∑ i, (x i - 1 / N) * (p i - m / N) := by
    have : ∑ i, (x i - 1 / N) * (p i - m / N) =
        ∑ i, x i * p i - (m / N) * ∑ i, x i - (1 / N) * ∑ i, p i + N * (1 / N * (m / N)) := by
      simp only [sub_mul, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul]
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring
    rw [this, hx1, hp1]
    field_simp
    ring
  have e1 : ∑ i, (x i - 1 / N) ^ 2 = X - 1 / N := by
    have : ∑ i, (x i - 1 / N) ^ 2 = X - 2 / N * ∑ i, x i + N * (1 / N) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring
    rw [this, hx1]
    field_simp
    ring
  have e2 : ∑ i, (p i - m / N) ^ 2 = Q - m ^ 2 / N := by
    have : ∑ i, (p i - m / N) ^ 2 = Q - 2 * (m / N) * ∑ i, p i + N * (m / N) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring
    rw [this, hp1]
    field_simp
    ring
  have hX1 : 1 / N ≤ X := by
    linarith [e1 ▸ sum_nonneg fun i (_ : i ∈ univ) ↦ sq_nonneg (x i - 1 / N)]
  have hX2 : X ≤ 1 := by
    linarith [e_tt ▸ sum_nonneg fun q (_ : q ∈ S) ↦ sq_nonneg (t q.1 * t q.2)]
  have hQ1 : m ^ 2 / N ≤ Q := by
    linarith [e2 ▸ sum_nonneg fun i (_ : i ∈ univ) ↦ sq_nonneg (p i - m / N)]
  have hQ2 : Q ≤ m := by linarith [e_gg ▸ sum_nonneg fun q (_ : q ∈ S) ↦ sq_nonneg (g q.1 q.2)]
  -- the three inequalities
  set A := √(X - 1 / N) with hA
  set B := √(1 - X) with hB
  set C := √(Q - m ^ 2 / N) with hC
  set D := √(m - Q) with hD
  have hcs1 := Real.sum_mul_le_sqrt_mul_sqrt S (fun q ↦ t q.1 * t q.2) (fun q ↦ g q.1 q.2)
  rw [e_tt, e_gg] at hcs1
  have hcs2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun i ↦ x i - 1 / N) (fun i ↦ p i - m / N)
  rw [e1, e2] at hcs2
  have h2d := Real.sqrt_mul_add_sqrt_mul_le (sub_nonneg.2 hX1) (sub_nonneg.2 hQ1)
    (sub_nonneg.2 hX2) (sub_nonneg.2 hQ2)
  rw [show X - 1 / N + (1 - X) = 1 - 1 / N by ring,
    show Q - m ^ 2 / N + (m - Q) = m - m ^ 2 / N by ring] at h2d
  rw [hsplit, e_D] at hδ
  -- hence all three are equalities
  have eq1 : ∑ q ∈ S, (t q.1 * t q.2) * g q.1 q.2 = B * D := by linarith
  have eq2 : ∑ i, (x i - 1 / N) * (p i - m / N) = A * C := by linarith
  have eq3 : A * C + B * D = √(1 - 1 / N) * √(m - m ^ 2 / N) := by linarith
  have E1 : ∀ q ∈ S, D * (t q.1 * t q.2) = B * g q.1 q.2 := by
    have := Real.eq_of_sum_mul_eq_sqrt_mul_sqrt (s := S) (f := fun q ↦ t q.1 * t q.2)
      (g := fun q ↦ g q.1 q.2) (by rw [e_tt, e_gg]; exact eq1)
    simpa only [e_tt, e_gg] using this
  have E2 : ∀ i, C * (x i - 1 / N) = A * (p i - m / N) := by
    have := Real.eq_of_sum_mul_eq_sqrt_mul_sqrt (s := univ) (f := fun i ↦ x i - 1 / N)
      (g := fun i ↦ p i - m / N) (by rw [e1, e2]; exact eq2)
    simp only [e1, e2] at this
    exact fun i ↦ this i (mem_univ i)
  have E3 : A * D = B * C := by
    have := sqrt_mul_eq_of_sqrt_mul_add_sqrt_mul_eq (sub_nonneg.2 hX1) (sub_nonneg.2 hQ1)
      (sub_nonneg.2 hX2) (sub_nonneg.2 hQ2)
      (by rw [show X - 1 / N + (1 - X) = 1 - 1 / N by ring,
        show Q - m ^ 2 / N + (m - Q) = m - m ^ 2 / N by ring]; exact eq3)
    rw [hA, hD, hB, hC]
    linarith
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = X - 1 / N := Real.sq_sqrt (sub_nonneg.2 hX1)
  have hBsq : B ^ 2 = 1 - X := Real.sq_sqrt (sub_nonneg.2 hX2)
  have hCsq : C ^ 2 = Q - m ^ 2 / N := Real.sq_sqrt (sub_nonneg.2 hQ1)
  have hDsq : D ^ 2 = m - Q := Real.sq_sqrt (sub_nonneg.2 hQ2)
  -- `B > 0`: otherwise the off-diagonal part vanishes and the value is at most `1`
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    exfalso
    rw [← h, zero_mul] at eq1
    have hxp : ∑ i, x i * p i ≤ 1 := by
      rw [← hx1]
      exact sum_le_sum fun i _ ↦ mul_le_of_le_one_right (hx0 i) (hp_le i)
    have hδ' : delta m (Fintype.card ι) ≤ 1 := by
      rw [delta_eq (by omega) hmN.le]
      linarith
    linarith
  -- the sum of the deviations of the diagonal vanishes
  have hvsum : ∑ i, (p i - m / N) = 0 := by
    rw [sum_sub_distrib, hp1, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  by_cases hC0' : C = 0
  · -- constant diagonal: `P` is an ETF projection
    have hQ : Q = m ^ 2 / N := by
      have : Q - m ^ 2 / N = 0 := by rw [← hCsq, hC0']; ring
      linarith
    have hpi : ∀ i, p i = m / N := by
      have h0 : ∑ i, (p i - m / N) ^ 2 = 0 := by rw [e2, hQ]; ring
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (p j - m / N))).1 h0 i
        (mem_univ i)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    have hDpos : 0 < D := by
      have : 0 < D ^ 2 := by
        rw [hDsq, hQ]
        have : (m : ℝ) - m ^ 2 / N = m * (N - m) / N := by field_simp
        rw [this]
        apply div_pos (mul_pos (by linarith) (by linarith)) hN0
      refine lt_of_le_of_ne hD0 fun h ↦ ?_
      rw [← h] at this
      simp at this
    have hA0' : A = 0 := by
      have : A * D = 0 := by rw [E3, hC0', mul_zero]
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hDpos.ne'
    have hxi : ∀ i, x i = 1 / N := by
      have hX' : X = 1 / N := by
        have := hAsq
        rw [hA0'] at this
        linarith
      have h0 : ∑ i, (x i - 1 / N) ^ 2 = 0 := by rw [e1, hX']; ring
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (x j - 1 / N))).1 h0 i
        (mem_univ i)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    have htt : ∀ i j, t i * t j = 1 / N := by
      intro i j
      have hi : t i = √(1 / N) := by
        rw [← hxi i]; simp only [x]; rw [Real.sqrt_sq (ht.nonneg i)]
      have hj : t j = √(1 / N) := by
        rw [← hxi j]; simp only [x]; rw [Real.sqrt_sq (ht.nonneg j)]
      rw [hi, hj, Real.mul_self_sqrt (by positivity)]
    refine ⟨hP, fun i ↦ ?_, ⟨D / (B * N), fun i j hij ↦ ?_⟩⟩
    · rw [hP.1.diag_eq_re i]
      have := hpi i
      simp only [p] at this
      rw [this, hN_def]
      push_cast
      rfl
    · have h := E1 (i, j) (by simp [S, hij])
      simp only at h
      rw [htt i j, mul_one_div, div_eq_iff hN0.ne'] at h
      change g i j = _
      rw [eq_div_iff (mul_pos hBpos hN0).ne', h]
      ring
  · -- non-constant diagonal: a contradiction
    exfalso
    have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hC0')
    have hDpos : 0 < D := by
      rcases hD0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, mul_zero] at E3
        have := mul_pos hBpos hCpos
        linarith
    set κ := B / D with hκ
    have hκpos : 0 < κ := div_pos hBpos hDpos
    -- `xᵢ - 1/N = κ (pᵢ - m/N)`
    have hxκ : ∀ i, x i = 1 / N + κ * (p i - m / N) := by
      intro i
      have h1 : C * (D * (x i - 1 / N)) = C * (B * (p i - m / N)) := by
        linear_combination D * (E2 i) + (p i - m / N) * E3
      have h2 := mul_left_cancel₀ hCpos.ne' h1
      have h3 : x i - 1 / N = B / D * (p i - m / N) := by
        rw [div_mul_eq_mul_div, eq_div_iff hDpos.ne', mul_comm]
        exact h2
      rw [hκ]
      linarith
    -- `κ |Pᵢⱼ| = tᵢ tⱼ` off the diagonal
    have hgκ : ∀ i j, i ≠ j → κ * g i j = t i * t j := by
      intro i j hij
      have h := E1 (i, j) (by simp [S, hij])
      simp only at h
      rw [hκ]
      field_simp
      linarith
    -- the row identity
    have hrowκ : ∀ i, κ ^ 2 * (p i - p i ^ 2) = x i * (1 - x i) := by
      intro i
      have hr := hrow i
      rw [← Finset.add_sum_erase _ _ (mem_univ i), hgii] at hr
      have hoff : κ ^ 2 * ∑ j ∈ univ.erase i, g i j ^ 2 = x i * ∑ j ∈ univ.erase i, x j := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun j hj ↦ ?_
        have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        have := hgκ i j hji
        calc κ ^ 2 * g i j ^ 2 = (κ * g i j) ^ 2 := by ring
          _ = (t i * t j) ^ 2 := by rw [this]
          _ = x i * x j := by simp only [x]; ring
      have hxe : ∑ j ∈ univ.erase i, x j = 1 - x i := by
        rw [← hx1, ← Finset.add_sum_erase _ _ (mem_univ i)]; ring
      rw [hxe] at hoff
      have : p i - p i ^ 2 = ∑ j ∈ univ.erase i, g i j ^ 2 := by linarith
      rw [this, hoff]
    -- an affine equation for the diagonal entries
    set L := κ ^ 2 * (1 - 2 * m / N) - κ * (1 - 2 / N) with hL
    set R := 1 / N * (1 - 1 / N) - κ ^ 2 * (m / N) * (1 - m / N) with hR
    have hlin : ∀ i, (p i - m / N) * L = R := by
      intro i
      have h := hrowκ i
      rw [hxκ i] at h
      rw [hL, hR]
      linear_combination h
    have hR0 : R = 0 := by
      have h := Finset.sum_congr rfl fun i (_ : i ∈ univ) ↦ hlin i
      rw [← sum_mul, hvsum, zero_mul, sum_const, card_univ, nsmul_eq_mul] at h
      have : (Fintype.card ι : ℝ) ≠ 0 := hN0.ne'
      rcases mul_eq_zero.1 h.symm with h' | h'
      · exact absurd h' this
      · exact h'
    have hL0 : L = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, p i - m / N ≠ 0 := by
        by_contra! hcon
        have : ∑ i, (p i - m / N) ^ 2 = 0 := sum_eq_zero fun i _ ↦ by rw [hcon i]; ring
        rw [e2, ← hCsq] at this
        have : C = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        exact hC0' this
      have := hlin i
      rw [hR0] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hi
      · exact h
    -- the final contradiction
    have hR' : N - 1 = κ ^ 2 * m * (N - m) := by
      rw [hR] at hR0
      field_simp at hR0
      linarith
    have hL' : κ * (N - 2 * m) = N - 2 := by
      rw [hL] at hL0
      have : κ * (κ * (N - 2 * m) - (N - 2)) = 0 := by
        field_simp at hL0
        linear_combination hL0
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hκpos.ne'
      · linarith
    have hf : N ^ 2 * (m - 1) * (N - m - 1) = 0 := by
      have : (N - 1) * (N - 2 * m) ^ 2 = m * (N - m) * (N - 2) ^ 2 := by
        rw [hR', ← hL']; ring
      linear_combination -this
    have hNm : N - m - 1 = 0 := by
      rcases mul_eq_zero.1 hf with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h') hN0.ne'
        · linarith
      · exact h
    have h1 : κ * (1 - m) = m - 1 := by
      have : N = m + 1 := by linarith
      rw [this] at hL'
      linarith
    have h2 : (κ + 1) * ((m : ℝ) - 1) = 0 := by linear_combination -h1
    have h3 : 0 < (κ + 1) * ((m : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    linarith

/-! ### Trivial equiangular tight frames -/

/-- An orthonormal basis is an `ETF(N, N)`. -/
theorem existsETF_self (N : ℕ) : ExistsETF 𝕜 N N := by
  refine ⟨1, ⟨fun i ↦ by simp, ⟨1, one_pos, by simp⟩, ⟨0, fun i j hij ↦ by simp [hij]⟩⟩⟩

/-- `N ≥ 1` copies of `1 ∈ 𝕜¹` form an `ETF(1, N)`. -/
theorem existsETF_one_left {N : ℕ} (hN : 1 ≤ N) : ExistsETF 𝕜 1 N := by
  refine ⟨Matrix.of fun _ _ ↦ 1, ⟨fun i ↦ ?_, ⟨N, by exact_mod_cast hN, ?_⟩,
    ⟨1, fun i j _ ↦ ?_⟩⟩⟩
  · simp [Matrix.mul_apply]
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply]

/-! ### Equiangular tight frames and the equality case -/

/-- **The equality case** ([DL, Theorem 1.2], (iii) ⇒ (i)). If `λ_𝕜(m, N) = δ_{m,N}`, then there
is an equiangular tight frame of `N` vectors in `𝕜^m`. -/
theorem existsETF_of_maxRelProjConst_eq_delta {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (h : maxRelProjConst 𝕜 m N = delta m N) : ExistsETF 𝕜 m N := by
  rcases hm.lt_or_eq with hm2 | rfl
  swap
  · exact existsETF_one_left hmN
  rcases hmN.lt_or_eq with hmN' | rfl
  swap
  · exact existsETF_self m
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨t, P, ht, hP, hval⟩ := exists_clConst_eq (𝕜 := 𝕜) (ι := Fin N) (m := m)
    (by simpa using hmN)
  rw [← maxRelProjConst_eq_clConst, h] at hval
  have hETF := isETFProj_of_delta_le_weightedAbsSum (by omega) (by simpa using hmN') ht hP
    (by simpa using hval.ge)
  exact hETF.exists_isETF (by omega)

/-- **The equality case of the bound of König, Lewis and Lin** ([DL, Theorem 1.2], [KLL], [FS]).
For `1 ≤ m ≤ N` the following are equivalent: (i) there is an equiangular tight frame of `N`
vectors in `𝕜^m`; (ii) `μ_𝕜(m, N) = δ_{m,N}`; (iii) `λ_𝕜(m, N) = δ_{m,N}`. -/
theorem existsETF_tfae {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    List.TFAE [ExistsETF 𝕜 m N, quasiRelConst 𝕜 (Fin N) m = delta m N,
      maxRelProjConst 𝕜 m N = delta m N] := by
  tfae_have 1 → 2 := fun h ↦ (quasiRelConst_eq_delta_of_existsETF (by omega) h).1
  tfae_have 2 → 3 := fun h ↦ le_antisymm (maxRelProjConst_le_delta (by omega))
    (h ▸ quasiRelConst_le_maxRelProjConst m N)
  tfae_have 3 → 1 := existsETF_of_maxRelProjConst_eq_delta hm hmN
  tfae_finish

end ProjectionConstants
