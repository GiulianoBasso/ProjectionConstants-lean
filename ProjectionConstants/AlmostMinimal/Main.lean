/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Blowup
import ProjectionConstants.ChalmersLewicki.SignMatrix

/-!
# Almost minimal orthogonal projections

We prove the main theorem of [AMOP].

**Theorem** ([AMOP, Theorem 1.2]). Let `n ≥ 1`. For every `ε > 0` there are an integer `d` and an
`n`-dimensional subspace `E ⊆ ℓ₁^d` such that the orthogonal projection `P : ℓ₁^d → E` satisfies
`λ_ℝ(n) - ε ≤ ‖P‖ ≤ λ(E, ℓ₁^d) + ε`.

Here `λ_ℝ(n) = maxProjConst ℝ n` is the maximal projection constant, written `Π_n` in [JFA] and
[AMOP], and `λ(E, ℓ₁^d) = relProjConst (l1Sub E)` is the relative projection constant of `E` in
`ℓ₁^d`. We use the formula of Chalmers and Lewicki in the form of [AMOP, (2.1)]: `λ_ℝ(n)` is the
supremum of `kyFanSum n (√D S √D)` over all `d`, all sign matrices `S ∈ 𝒮_d` and all nonnegative
diagonal matrices `D ∈ 𝒟_d` of trace one (`maxProjConst_real_eq_sSup`,
`exists_lt_kyFanSum_weightedSign`).

## Main statements

* `exists_almost_minimal_orthProj`: [AMOP, Theorem 1.2] for matrices: `P` is a symmetric
  idempotent `d × d` matrix of rank `n`, `E` is its range, and `‖P‖ = colSumNorm P`.
* `ProjectionConstants.exists_almost_minimal_orthogonal_projection`: [AMOP, Theorem 1.2] for
  subspaces `E` of `ℓ₁^d = PiLp 1 (fun _ : Fin d ↦ ℝ)` and bounded operators `P`.

## Proof

We follow [AMOP, Section 5], in the form of the remark in [JFA-E], which does not need polyhedral
maximizers. Instead of the spectral gap [AMOP, Lemma 3.3] and the lower bound
`λ_ℝ(n) > √(2/π) √n`, we bound the variance of the column sums. A configuration `(S, w)` is a
sign matrix `S` together with weights `w`, and its value is `kyFanSumLe n (weightedSign S w)` (see
`ProjectionConstants.AlmostMinimal.Config`).

1. Take `m` minimal such that some configuration on `m` points has value `> λ_ℝ(n) - ε/4`, and a
   maximizer `(S₀, w₀)` among the configurations on `m` points (`exists_isGlobalMax`). By
   minimality, all weights are positive (`kyFanSumLe_weightedSign_le_restrict`). Let `V` be its
   value.
2. Let `P₀` be optimal and `B = S₀ ∘ P₀ = |P₀|` (`sign_mul_nonneg_of_isMax`). Then
   `xᵀBx ≤ V|x|²`, with equality at `v = √w₀`. So `V - xᵀBx ≤ 2V |x - v|²` for unit vectors `x`
   (`sub_dotProduct_mulVec_le`).
3. Round the weights: `pᵢ = ⌈N w₀ᵢ⌉`, `d = ∑ pᵢ`, `qᵢ = pᵢ/d`. Then `|√q - √w₀|² = O(1/d²)`
   (`sum_sq_sqrt_div_sub_sqrt_le`).
4. Let `S'` maximize the value of `(S, q)` over the sign matrices `S`, and let `Q` be optimal
   for `(S', q)`. With `Λ = diag(q)`, the projection `Q` commutes with `√Λ S' √Λ`
   (`sum_mul_eq_sum_mul_of_isMaxOn`), and `S' ∘ Q = |Q|`. The value `m̄` of `(S', q)` satisfies
   `V - O(1/d²) ≤ √qᵀB√q ≤ m̄ ≤ V`.
5. Blow up (`ProjectionConstants.AlmostMinimal.Blowup`): let `P = blowupProj p Q` and
   `S = blowupSign p S'`. The average column sum of `|P|` is `m̄`, and the sum of the squared
   column sums is `|G s|² ≤ V² d` with `G = |Q|` and `s = √p`. So the variance of the column sums
   is at most `d (V² - m̄²) = O(1/d)`. Hence every column sum is at most `m̄ + ε/2`.
6. Trace duality with `A = S/d` gives `λ(E, ℓ₁^d) ≥ Tr(AP) = m̄` (`trace_mul_le_relProjConst`).
   Finally, we pad to dimension `n` (`exists_orthProj_of_colSum_le`).

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

/-- For `n ≥ 1` and every weight `w`, the all-ones sign matrix `J` satisfies
`kyFanSumLe n (weightedSign J w) ≥ 1`: the projection onto `√w` has the value `1`. -/
lemma one_le_kyFanSumLe_ones {ι : Type*} [Fintype ι] {n : ℕ} (hn : 1 ≤ n) {w : ι → ℝ}
    (hw : IsWeight w) : 1 ≤ kyFanSumLe n (weightedSign (Matrix.of fun _ _ ↦ (1 : ℝ)) w) := by
  have hsq : ∀ i, √(w i) * √(w i) = w i := fun i ↦ Real.mul_self_sqrt (hw.nonneg i)
  have hP : (Matrix.of fun i j ↦ √(w i) * √(w j)) ∈ orthProjsLe ι n := by
    refine ⟨IsStarProjection.of_apply (fun i j ↦ by simp only [Matrix.of_apply]; ring)
      fun i j ↦ ?_, ?_⟩
    · simp only [Matrix.of_apply]
      have e : ∀ k, √(w i) * √(w k) * (√(w k) * √(w j)) = √(w i) * √(w j) * w k := fun k ↦ by
        rw [show √(w i) * √(w k) * (√(w k) * √(w j)) = √(w i) * √(w j) * (√(w k) * √(w k)) by
          ring, hsq k]
      simp only [e, ← mul_sum, hw.sum_eq, mul_one]
    · simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, hsq, hw.sum_eq]
      exact_mod_cast hn
  refine le_trans (le_of_eq ?_) (frobeniusInner_le_kyFanSumLe _ hP)
  simp only [frobeniusInner, weightedSign_apply, Matrix.of_apply, mul_one]
  have e : ∀ i j, √(w i) * √(w j) * (√(w i) * √(w j)) = w i * w j := fun i j ↦ by
    rw [show √(w i) * √(w j) * (√(w i) * √(w j)) = (√(w i) * √(w i)) * (√(w j) * √(w j)) by ring,
      hsq i, hsq j]
  simp only [e, ← mul_sum, ← sum_mul, hw.sum_eq, one_mul]

/-- For `n ≥ 1` and `δ > 0`, some configuration `(S, w)` has the value
`kyFanSumLe n (weightedSign S w) > λ_ℝ(n) - δ`. -/
lemma exists_lt_kyFanSumLe_weightedSign {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ), IsSignMatrix S ∧ IsWeight w ∧
      maxProjConst ℝ n - δ < kyFanSumLe n (weightedSign S w) := by
  obtain ⟨d, S, w, hS, hw, h⟩ := exists_lt_kyFanSum_weightedSign hn hδ
  exact ⟨d, S, w, hS, hw, h.trans_le (kyFanSum_le_kyFanSumLe n _)⟩

/-- **Almost minimal orthogonal projections**, matrix form ([AMOP, Theorem 1.2]). Let `n ≥ 1`
and `ε > 0`. There are `d` and an `n`-dimensional subspace `E ⊆ ℓ₁^d` such that the orthogonal
projection `P` onto `E` satisfies `λ_ℝ(n) - ε ≤ ‖P‖ ≤ λ(E, ℓ₁^d) + ε`. Here `P` is a symmetric
idempotent `d × d` matrix, `E` is its range, `‖P‖ = colSumNorm P` is the operator norm on `ℓ₁^d`,
and `λ(E, ℓ₁^d) = relProjConst (l1Sub E)`. -/
theorem exists_almost_minimal_orthProj (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (P : Matrix (Fin d) (Fin d) ℝ), P.IsSymm ∧ P * P = P ∧
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) = n ∧
      maxProjConst ℝ n - ε ≤ colSumNorm P ∧
        colSumNorm P ≤ relProjConst (l1Sub (LinearMap.range (Matrix.toLin' P))) + ε := by
  classical
  set c := maxProjConst ℝ n - ε / 4 with hc
  -- Step 1: a maximizer on a minimal number of points.
  have hex : ∃ m, ∃ (S : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ),
      IsSignMatrix S ∧ IsWeight w ∧ c < kyFanSumLe n (weightedSign S w) := by
    obtain ⟨d, S, w, hS, hw, h⟩ :=
      exists_lt_kyFanSumLe_weightedSign hn (show 0 < ε / 4 by positivity)
    exact ⟨d, S, w, hS, hw, h⟩
  set m := Nat.find hex with hm
  obtain ⟨S₁, w₁, hS₁, hw₁, hc₁⟩ := Nat.find_spec hex
  have hne : Nonempty (Fin m) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hw₁.sum_eq
    simp [Finset.univ_eq_empty] at this
  have hmpos : 0 < m := Fin.pos_iff_nonempty.mpr hne
  obtain ⟨S₀, w₀, hmax⟩ := exists_isGlobalMax (ι := Fin m) n
  set V := kyFanSumLe n (weightedSign S₀ w₀) with hV
  have hVall : ∀ (S' : Matrix (Fin m) (Fin m) ℝ) (w' : Fin m → ℝ), IsSignMatrix S' → IsWeight w' →
      kyFanSumLe n (weightedSign S' w') ≤ V := hmax.max
  have hVc : c < V := hc₁.trans_le (hVall S₁ w₁ hS₁ hw₁)
  have hw₀pos : ∀ i, 0 < w₀ i := by
    intro j
    by_contra hj
    push Not at hj
    have hj0 : w₀ j = 0 := le_antisymm hj (hmax.weight.nonneg j)
    have hr := kyFanSumLe_weightedSign_le_restrict (n := n) hmax.sign hj0
    have hcard : Fintype.card {k : Fin m // k ≠ j} = m - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    set e := (Fintype.equivFinOfCardEq hcard).symm with he
    set Sr : Matrix {k : Fin m // k ≠ j} {k : Fin m // k ≠ j} ℝ :=
      Matrix.of fun a b ↦ S₀ a b with hSr_def
    set wr : {k : Fin m // k ≠ j} → ℝ := fun a ↦ w₀ a with hwr_def
    have hSr : IsSignMatrix Sr :=
      ⟨fun a b ↦ hmax.sign.symm a b, fun a b ↦ hmax.sign.pm a b, fun a ↦ hmax.sign.diag a⟩
    have hwr : IsWeight wr := by
      refine ⟨fun a ↦ hmax.weight.nonneg a, ?_⟩
      simp only [hwr_def]
      rw [Fintype.sum_subtype_ne_eq_sub j w₀, hmax.weight.sum_eq, hj0, sub_zero]
    have h1 : c < kyFanSumLe n (weightedSign (Sr.submatrix e e) (wr ∘ e)) := by
      rw [weightedSign_submatrix, kyFanSumLe_submatrix n e]
      exact hVc.trans_le hr
    have h2 := Nat.find_min' hex ⟨Sr.submatrix e e, wr ∘ e, hSr.submatrix e,
      hwr.comp_equiv e, h1⟩
    omega
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ w₀ univ_nonempty
  set ε₀ := w₀ i₀ with hε₀_def
  have hε₀ : 0 < ε₀ := hw₀pos i₀
  have hmin : ∀ i, ε₀ ≤ w₀ i := fun i ↦ hi₀ i (mem_univ i)
  have hV1 : 1 ≤ V :=
    (one_le_kyFanSumLe_ones hn hmax.weight).trans (hVall _ _ isSignMatrix_ones hmax.weight)
  have hV0 : 0 ≤ V := by linarith
  -- Step 2: the quadratic bound at the maximizer.
  obtain ⟨P₀, hP₀, hP₀opt⟩ := exists_frobeniusInner_eq_kyFanSumLe n (weightedSign S₀ w₀)
  have hsign₀ := sign_mul_nonneg_of_isMax hmax.sign hw₀pos
    (fun S' hS' ↦ hVall S' w₀ hS' hmax.weight) hP₀ hP₀opt
  have hBsym := hadamard_apply_comm hmax.sign hP₀.1
  have hBle : ∀ x, x ⬝ᵥ S₀ ⊙ P₀ *ᵥ x ≤ V * (x ⬝ᵥ x) :=
    dotProduct_mulVec_hadamard_le hmax.sign hP₀ hVall
  have hB0 : ∀ i j, 0 ≤ (S₀ ⊙ P₀) i j := fun i j ↦ hsign₀ i j
  have hBabs := abs_dotProduct_mulVec_le_of_nonneg hB0 hBle
  set v : Fin m → ℝ := fun i ↦ √(w₀ i) with hv_def
  have hsw : ∀ i, √(w₀ i) * √(w₀ i) = w₀ i := fun i ↦ Real.mul_self_sqrt (hmax.weight.nonneg i)
  have hv : v ⬝ᵥ S₀ ⊙ P₀ *ᵥ v = V * (v ⬝ᵥ v) := by
    have e1 : v ⬝ᵥ S₀ ⊙ P₀ *ᵥ v = frobeniusInner (weightedSign S₀ w₀) P₀ := by
      simp only [dotProduct_mulVec_self_eq_sum, frobeniusInner, hadamard_apply, weightedSign,
        Matrix.of_apply, hv_def]
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
      ring
    have e2 : v ⬝ᵥ v = 1 := by
      simp only [dotProduct, hv_def, hsw, hmax.weight.sum_eq]
    rw [e1, hP₀opt, e2, mul_one]
  have hquad := sub_dotProduct_mulVec_le (.ext hBsym) hBle (K := V)
    (fun y ↦ by linarith [(abs_le.mp (hBabs y)).1]) hv
  -- Step 3: rounding the weights.
  set K₁ := 2 * V * (m * (m + 1) ^ 2 / ε₀) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * K₁ / ε + 8 * V * K₁ / ε ^ 2 + 1)
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 ≤ 4 * K₁ / ε + 8 * V * K₁ / ε ^ 2 := by positivity
    linarith
  set p : Fin m → ℕ := fun i ↦ ⌈(N : ℝ) * w₀ i⌉₊ with hp_def
  have hp1 : ∀ i, 1 ≤ p i := fun i ↦ by
    have : 0 < (N : ℝ) * w₀ i := mul_pos (by linarith) (hw₀pos i)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr this))
  have hpN1 : ∀ i, (N : ℝ) * w₀ i ≤ (p i : ℝ) := fun i ↦ Nat.le_ceil _
  have hpN2 : ∀ i, (p i : ℝ) < N * w₀ i + 1 := fun i ↦
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) (hmax.weight.nonneg i))
  obtain ⟨hdN, hround⟩ :=
    sum_sq_sqrt_div_sub_sqrt_le hmax.weight hε₀ hmin hN1 (fun i ↦ (p i : ℝ)) hpN1 hpN2
  set d : ℕ := ∑ i, p i with hd_def
  have hdR : (d : ℝ) = ∑ i, (p i : ℝ) := by rw [hd_def]; push_cast; rfl
  rw [← hdR] at hdN hround
  have hdpos : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  set q : Fin m → ℝ := fun i ↦ (p i : ℝ) / d with hq_def
  have hqpos : ∀ i, 0 < q i := fun i ↦ div_pos (by exact_mod_cast hp1 i) hdpos
  have hq : IsWeight q := by
    refine ⟨fun i ↦ (hqpos i).le, ?_⟩
    simp only [hq_def, ← sum_div, ← hdR]
    exact div_self hdpos.ne'
  have hsqrtq : ∀ i, √(q i) = sqrtMult p i / √(d : ℝ) := fun i ↦ by
    simp only [hq_def, sqrtMult]
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have hsd : √(d : ℝ) * √(d : ℝ) = d := Real.mul_self_sqrt hdpos.le
  have hsd0 : √(d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdpos).ne'
  have hwmq : ∀ (S : Matrix (Fin m) (Fin m) ℝ) i j,
      weightedSign S q i j = sqrtMult p i * S i j * sqrtMult p j / d := fun S i j ↦ by
    simp only [weightedSign, Matrix.of_apply, hsqrtq]
    rw [show sqrtMult p i / √(d : ℝ) * S i j * (sqrtMult p j / √(d : ℝ)) =
      sqrtMult p i * S i j * sqrtMult p j / (√(d : ℝ) * √(d : ℝ)) by ring, hsd]
  -- Step 4: the optimal configuration for the weights `q`.
  obtain ⟨S', hS', hS'max⟩ := exists_forall_kyFanSumLe_weightedSign_le n q
  obtain ⟨Q, hQ, hQopt⟩ := exists_frobeniusInner_eq_kyFanSumLe n (weightedSign S' q)
  set mb := kyFanSumLe n (weightedSign S' q) with hmb
  have hsignQ := sign_mul_nonneg_of_isMax hS' hqpos hS'max hQ hQopt
  have hcommQ := sum_mul_eq_sum_mul_of_isMaxOn (.ext (IsSignMatrix.weightedSign_comm hS' q)) hQ
    (fun P' hP' ↦ hQopt ▸ frobeniusInner_le_kyFanSumLe _ hP')
  have hmbV : mb ≤ V := hVall S' q hS' hq
  have hmb0 : 0 ≤ mb := kyFanSumLe_nonneg _ _
  have hfq : (fun i ↦ √(q i)) ⬝ᵥ S₀ ⊙ P₀ *ᵥ (fun i ↦ √(q i)) ≤ mb := by
    have e1 : (fun i ↦ √(q i)) ⬝ᵥ S₀ ⊙ P₀ *ᵥ (fun i ↦ √(q i)) =
        frobeniusInner (weightedSign S₀ q) P₀ := by
      simp only [dotProduct_mulVec_self_eq_sum, frobeniusInner, hadamard_apply, weightedSign,
        Matrix.of_apply]
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
      ring
    rw [e1]
    exact (frobeniusInner_le_kyFanSumLe _ hP₀).trans (hS'max S₀ hmax.sign)
  have hgap : V - mb ≤ K₁ / (d : ℝ) ^ 2 := by
    have h1 := hquad (fun i ↦ √(q i))
    have e1 : (fun i ↦ √(q i)) ⬝ᵥ (fun i ↦ √(q i)) = 1 := by
      simp only [dotProduct]
      rw [← hq.sum_eq]
      exact sum_congr rfl fun i _ ↦ Real.mul_self_sqrt (hqpos i).le
    have e2 : (fun i ↦ √(q i) - v i) ⬝ᵥ (fun i ↦ √(q i) - v i) =
        ∑ i, (√((p i : ℝ) / d) - √(w₀ i)) ^ 2 := by
      simp only [dotProduct, hv_def, hq_def, sq]
    rw [e1, e2, mul_one] at h1
    have h2 : (V + V) * ∑ i, (√((p i : ℝ) / d) - √(w₀ i)) ^ 2 ≤
        (V + V) * (m * (m + 1) ^ 2 / (ε₀ * (d : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hround (by linarith)
    have e3 : (V + V) * (m * (m + 1) ^ 2 / (ε₀ * (d : ℝ) ^ 2)) = K₁ / (d : ℝ) ^ 2 := by
      rw [hK₁]
      field_simp
      ring
    linarith
  have hK₁d : K₁ / (d : ℝ) ^ 2 ≤ ε / 4 := by
    have h1 : K₁ / (d : ℝ) ^ 2 ≤ K₁ / d := by
      apply div_le_div_of_nonneg_left hK₁0 hdpos
      nlinarith
    have h2 : 4 * K₁ / ε ≤ d := by
      have : 0 ≤ 8 * V * K₁ / ε ^ 2 := by positivity
      linarith
    have h3 : K₁ / d ≤ ε / 4 := by
      rw [div_le_iff₀ hdpos]
      rw [div_le_iff₀ hε] at h2
      linarith
    linarith
  have hvar_d : 2 * V * K₁ / d ≤ (ε / 2) ^ 2 := by
    have h2 : 8 * V * K₁ / ε ^ 2 ≤ d := by
      have : 0 ≤ 4 * K₁ / ε := by positivity
      linarith
    rw [div_le_iff₀ hdpos]
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  -- Step 5: the blow-up.
  have hXQ : ∀ i j, ∑ k, sqrtMult p i * S' i k * sqrtMult p k * Q k j =
      ∑ k, Q i k * (sqrtMult p k * S' k j * sqrtMult p j) := by
    intro i j
    have h := hcommQ i j
    simp only [hwmq] at h
    have e1 : ∑ k, sqrtMult p i * S' i k * sqrtMult p k / d * Q k j =
        (∑ k, sqrtMult p i * S' i k * sqrtMult p k * Q k j) / d := by
      rw [sum_div]
      refine sum_congr rfl fun k _ ↦ ?_
      ring
    have e2 : ∑ k, Q i k * (sqrtMult p k * S' k j * sqrtMult p j / d) =
        (∑ k, Q i k * (sqrtMult p k * S' k j * sqrtMult p j)) / d := by
      rw [sum_div]
      refine sum_congr rfl fun k _ ↦ ?_
      ring
    rw [e1, e2] at h
    exact (div_left_inj' hdpos.ne').mp h
  have hQabs : ∀ i j, S' i j * Q i j = |Q i j| := fun i j ↦ by
    have h1 : |S' i j * Q i j| = |Q i j| := by rw [abs_mul, hS'.abs_eq, one_mul]
    rw [← h1, abs_of_nonneg (hsignQ i j)]
  have hdmb : ∑ i, ∑ j, sqrtMult p i * sqrtMult p j * |Q i j| = d * mb := by
    rw [← hQopt]
    simp only [frobeniusInner, hwmq, mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [← hQabs i j]
    field_simp
  have hbOP := isStarProjection_blowupProj hp1 hQ.1
  have hcardBI : (Fintype.card (BlowupIndex p) : ℝ) = d := by rw [card_blowupIndex]
  set col : BlowupIndex p → ℝ := fun b ↦ ∑ a, |blowupProj p Q a b| with hcol_def
  have hsumcol : ∑ b, col b = d * mb := by
    simp only [hcol_def]
    rw [sum_sum_abs_blowupProj hp1, hdmb]
  have hsumsq : ∑ b, col b ^ 2 ≤ V ^ 2 * d := by
    simp only [hcol_def]
    rw [sum_sq_sum_abs_blowupProj hp1]
    set G : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j ↦ |Q i j| with hG
    have hGs : ∀ i j, G j i = G i j := fun i j ↦ by simp only [hG, Matrix.of_apply, hQ.1.apply_comm]
    have hGle : ∀ y, y ⬝ᵥ G *ᵥ y ≤ V * (y ⬝ᵥ y) := by
      intro y
      have e : y ⬝ᵥ G *ᵥ y = y ⬝ᵥ S' ⊙ Q *ᵥ y := by
        simp only [dotProduct_mulVec_self_eq_sum, hG, hadamard_apply, Matrix.of_apply, hQabs]
      rw [e]
      exact dotProduct_mulVec_hadamard_le hS' hQ hVall y
    have hGabs := abs_dotProduct_mulVec_le_of_nonneg (fun i j ↦ abs_nonneg (Q i j)) hGle
    have h1 := mulVec_dotProduct_mulVec_le (.ext hGs) hV0 hGabs (sqrtMult p)
    have e1 : ∀ j, (G *ᵥ (sqrtMult p)) j = ∑ i, sqrtMult p i * |Q i j| := fun j ↦ by
      simp only [mulVec_apply_eq_sum, hG, Matrix.of_apply]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [hQ.1.apply_comm j i]
      ring
    have e2 : (sqrtMult p) ⬝ᵥ (sqrtMult p) = d := by
      simp only [dotProduct, sqrtMult_mul_self, hdR]
    rw [e2] at h1
    simp only [dotProduct, e1] at h1
    simpa [sq] using h1
  have hvar : ∑ b, (col b - mb) ^ 2 ≤ (ε / 2) ^ 2 := by
    have e : ∑ b, (col b - mb) ^ 2 =
        ∑ b, col b ^ 2 - 2 * mb * ∑ b, col b + (Fintype.card (BlowupIndex p) : ℝ) * mb ^ 2 := by
      have h0 : ∀ b, (col b - mb) ^ 2 = col b ^ 2 - 2 * mb * col b + mb ^ 2 := fun b ↦ by ring
      rw [sum_congr rfl fun b _ ↦ h0 b, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul]
    rw [e, hsumcol, hcardBI]
    have h1 : V ^ 2 * d - 2 * mb * (d * mb) + d * mb ^ 2 = d * ((V - mb) * (V + mb)) := by ring
    have h2 : (V - mb) * (V + mb) ≤ K₁ / (d : ℝ) ^ 2 * (2 * V) := by
      apply mul_le_mul hgap (by linarith) (by linarith) (by positivity)
    have h3 : (d : ℝ) * (K₁ / (d : ℝ) ^ 2 * (2 * V)) = 2 * V * K₁ / d := by
      field_simp
    calc ∑ b, col b ^ 2 - 2 * mb * (d * mb) + d * mb ^ 2
        ≤ V ^ 2 * d - 2 * mb * (d * mb) + d * mb ^ 2 := by linarith
      _ = d * ((V - mb) * (V + mb)) := h1
      _ ≤ d * (K₁ / (d : ℝ) ^ 2 * (2 * V)) := mul_le_mul_of_nonneg_left h2 hdpos.le
      _ = 2 * V * K₁ / d := h3
      _ ≤ (ε / 2) ^ 2 := hvar_d
  have hcolle : ∀ b, col b ≤ mb + ε / 2 := by
    intro b
    have h1 : (col b - mb) ^ 2 ≤ (ε / 2) ^ 2 :=
      le_trans (single_le_sum (f := fun b ↦ (col b - mb) ^ 2) (fun b _ ↦ sq_nonneg _)
        (mem_univ b)) hvar
    have h2 := abs_le_of_sq_le_sq' h1 (by positivity)
    linarith [h2.2]
  have hmbV' : V - ε / 4 ≤ mb := by linarith
  -- Step 6: trace duality, via `exists_orthProj_of_colSum_le`.
  set A : Matrix (BlowupIndex p) (BlowupIndex p) ℝ :=
    Matrix.of fun a b ↦ blowupSign p S' a b / d with hA
  have hbPP : blowupProj p Q * blowupProj p Q = blowupProj p Q := by
    ext a b
    rw [Matrix.mul_apply]
    exact hbOP.sum_mul_apply a b
  have hAP : A * blowupProj p Q = blowupProj p Q * A := by
    ext a b
    simp only [Matrix.mul_apply, hA, Matrix.of_apply]
    have h := blowupSign_mul_blowupProj hp1 hXQ a b
    have e1 : ∑ c, blowupSign p S' a c / d * blowupProj p Q c b =
        (∑ c, blowupSign p S' a c * blowupProj p Q c b) / d := by
      rw [sum_div]
      refine sum_congr rfl fun c _ ↦ ?_
      ring
    have e2 : ∑ c, blowupProj p Q a c * (blowupSign p S' c b / d) =
        (∑ c, blowupProj p Q a c * blowupSign p S' c b) / d := by
      rw [sum_div]
      refine sum_congr rfl fun c _ ↦ ?_
      ring
    rw [e1, e2, h]
  have htrA : (A * blowupProj p Q).trace = mb := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hA, Matrix.of_apply]
    have e : ∀ a c, blowupSign p S' a c / d * blowupProj p Q c a =
        |blowupProj p Q a c| / d := fun a c ↦ by
      rw [hbOP.apply_comm a c, ← blowupSign_mul_blowupProj_apply hp1 hS' hsignQ a c]
      ring
    simp only [e, ← sum_div]
    rw [sum_comm]
    have : ∑ b, ∑ a, |blowupProj p Q a b| = d * mb := hsumcol
    rw [this]
    field_simp
  have hneBI : Nonempty (BlowupIndex p) := ⟨⟨Classical.arbitrary (Fin m), ⟨0, hp1 _⟩⟩⟩
  obtain ⟨b₀, -, hb₀⟩ := Finset.exists_le_of_sum_le (s := univ) (f := fun _ ↦ mb) (g := col)
    univ_nonempty (by rw [hsumcol, sum_const, card_univ, nsmul_eq_mul, hcardBI])
  refine exists_orthProj_of_colSum_le (P := blowupProj p Q) (A := A) (α := fun _ ↦ 1 / (d : ℝ))
    (lo := maxProjConst ℝ n - ε) (hi := mb + ε / 2) (fun a b ↦ hbOP.apply_comm a b) hbPP ?_ hAP
    ?_ ?_ hcolle ?_ ?_ ⟨b₀, ?_⟩
  · rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [trace_blowupProj hp1]
    exact hQ.2
  · intro a b
    simp only [hA, Matrix.of_apply, blowupSign, abs_div, hS'.abs_eq, Nat.abs_cast]
    exact le_rfl
  · rw [sum_const, card_univ, nsmul_eq_mul, hcardBI]
    rw [mul_one_div_cancel hdpos.ne']
  · linarith
  · rw [htrA]
    linarith
  · have : maxProjConst ℝ n - ε ≤ mb := by linarith
    exact this.trans hb₀

end ProjectionConstants.AlmostMinimal

namespace ProjectionConstants

open WithLp (toLp ofLp)

/-- **Almost minimal orthogonal projections** ([AMOP, Theorem 1.2]). For `n ≥ 1` and `ε > 0`
there are `d` and an `n`-dimensional subspace `E ⊆ ℓ₁^d = PiLp 1 (fun _ : Fin d ↦ ℝ)` such that
the orthogonal projection `P` onto `E` satisfies `λ_ℝ(n) - ε ≤ ‖P‖ ≤ λ(E, ℓ₁^d) + ε`. Here the
orthogonal projection is the projection onto `E` that is self-adjoint for the standard inner
product `⬝ᵥ`, and `‖P‖` is its operator norm on `ℓ₁^d`. -/
theorem exists_almost_minimal_orthogonal_projection (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (E : Submodule ℝ (PiLp 1 fun _ : Fin d ↦ ℝ))
      (P : (PiLp 1 fun _ : Fin d ↦ ℝ) →L[ℝ] PiLp 1 fun _ : Fin d ↦ ℝ),
      Module.finrank ℝ E = n ∧ IsProjectionOnto E P ∧
      (∀ x y, ofLp (P x) ⬝ᵥ ofLp y = ofLp x ⬝ᵥ ofLp (P y)) ∧
      maxProjConst ℝ n - ε ≤ ‖P‖ ∧ ‖P‖ ≤ relProjConst E + ε := by
  obtain ⟨d, P, hPs, hPP, hrank, hlo, hhi⟩ := AlmostMinimal.exists_almost_minimal_orthProj n hn ε hε
  rw [← norm_l1Op] at hlo hhi
  exact ⟨d, l1Sub (LinearMap.range (Matrix.toLin' P)), l1Op P, by rw [finrank_l1Sub, hrank],
    (isMatrixProjOnto_range hPP).l1Op _, dotProduct_l1Op_comm hPs, hlo, hhi⟩

end ProjectionConstants
