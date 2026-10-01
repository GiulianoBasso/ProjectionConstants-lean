/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Analysis.RCLike.Basic
import ProjectionConstants.ForMathlib.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic

/-!
# The recursive Sidelnikov–Welch inequality

For unit vectors `x₁, …, x_N ∈ 𝕂^m` (`𝕂 = ℝ` or `ℂ`) and arbitrary real weights
`w₁, …, w_N`, write `X_k = ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^k`. The recursive Sidelnikov–Welch inequality
[DL26, Theorem 2.1] states that for every `t ≥ 1`,
`X_{2t} ≥ (2t-1)/(m+2t-2) · X_{2t-2}` if `𝕂 = ℝ`, and `X_{2t} ≥ t/(m+t-1) · X_{2t-2}` if
`𝕂 = ℂ`. Iterating it from `X₀ = (∑ᵢ wᵢ)²` gives the weighted Sidelnikov–Welch bound
[DL26, Corollary 2.1] `X_{2t} ≥ c_t(m, 𝕂) (∑ᵢ wᵢ)²` with
`c_t(m, ℝ) = 1·3⋯(2t-1) / (m(m+2)⋯(m+2t-2))` and `c_t(m, ℂ) = 1/C(m+t-1, t)`.

The case `t = 2` is used for the frame bound [DL26, Lemma 3.1] in
`ProjectionConstants.Bounds.FrameBound`.

## Main statements

* `recursive_welch_real`: the division-free form
  `(n+1) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩ⁿ ≤ (m+n) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩ⁿ⁺²` of [DL26, Theorem 2.1] for real
  vectors and every `n ≥ 0` (for even `n` this is `(n+1) Xₙ ≤ (m+n) X_{n+2}`).
* `recursive_welch_complex`: the division-free form `(p+1) X_{2p} ≤ (m+p) X_{2p+2}` of
  [DL26, Theorem 2.1] for complex vectors and every `p ≥ 0`.
* `recursive_welch_real'`, `recursive_welch_complex'`: [DL26, Theorem 2.1] in the form of the
  paper.
* `weighted_welch_real`, `weighted_welch_complex`: the weighted Sidelnikov–Welch bound
  [DL26, Corollary 2.1].
* `welch_real`, `welch_complex`: the case `t = 2`, `3 X₂ ≤ (m+2) X₄` and `2 X₂ ≤ (m+1) X₄`.

## Proof sketch

[DL26] works with the Fischer inner product on homogeneous polynomials. We give a direct tensor
argument instead. In the real case let `T = ∑ᵢ wᵢ xᵢ^{⊗(n+2)}` and `A = ∑ᵢ wᵢ xᵢ^{⊗n}`,
so that `‖T‖² = X_{n+2}` and `‖A‖² = Xₙ` (where, for odd `n`, `X_k` is read without absolute
values). Test `T` against
`Z = ∑_{j=1}^{n+1} δ_{0j} ⊗ A` (the Kronecker delta in the positions `0` and `j`, and `A` in the
remaining ones). Since `‖xᵢ‖ = 1`, every partial trace of `T` is `A`, so `⟨Z, T⟩ = (n+1) ‖A‖²`;
since `A` is symmetric, `‖Z‖² = (n+1)(m+n) ‖A‖²`. Expanding `0 ≤ ‖Z - (m+n) T‖²` gives
`(n+1) Xₙ ≤ (m+n) X_{n+2}`. In the complex case the tensors are
`∑ᵢ wᵢ xᵢ^{⊗(p+1)} ⊗ conj(xᵢ)^{⊗(p+1)}` and the delta pairs the first unconjugated position with
each of the `p + 1` conjugated ones.

## Implementation notes

Vectors in `𝕂^m` are functions `Fin m → 𝕂`, and tensors of order `k` over `𝕂^m` are functions
on the words `Fin k → Fin m`. The complex statements hold for every `RCLike` field `𝕜`.

## References

* [DL26] B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection constants*,
  arXiv:2609.29422.

## Tags

Sidelnikov–Welch bound, equiangular lines, tight frame
-/

open Finset ComplexConjugate

namespace ProjectionConstants

/-! ### Words -/

section Words

variable {M : Type*} [CommMonoid M] {n : ℕ}

private lemma prod_succAbove_eq_prod_erase (f : Fin (n + 1) → M) (p : Fin (n + 1)) :
    ∏ i : Fin n, f (p.succAbove i) = ∏ q ∈ univ.erase p, f q := by
  rw [Fin.univ_succAbove n p, Finset.erase_cons, Finset.prod_map, Fin.coe_succAboveEmb]

/-- Removing one of two equal letters gives the same product. -/
private lemma prod_succAbove_eq_of_eq {f : Fin (n + 1) → M} {j l : Fin (n + 1)} (h : f j = f l) :
    ∏ i : Fin n, f (j.succAbove i) = ∏ i : Fin n, f (l.succAbove i) := by
  rcases eq_or_ne j l with rfl | hjl
  · rfl
  rw [prod_succAbove_eq_prod_erase, prod_succAbove_eq_prod_erase,
    ← Finset.mul_prod_erase (univ.erase j) f (mem_erase.2 ⟨hjl.symm, mem_univ l⟩),
    ← Finset.mul_prod_erase (univ.erase l) f (mem_erase.2 ⟨hjl, mem_univ j⟩), h,
    Finset.erase_right_comm]

variable {m : ℕ}

private lemma prod_insertNth_apply (g : Fin m → M) (p : Fin (n + 1)) (a : Fin m)
    (β : Fin n → Fin m) :
    ∏ i, g (Fin.insertNth (α := fun _ ↦ Fin m) p a β i) = g a * ∏ i, g (β i) := by
  rw [Fin.prod_univ_succAbove _ p]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private lemma prod_cons_apply (g : Fin m → M) (a : Fin m) (β : Fin n → Fin m) :
    ∏ i, g (Fin.cons (α := fun _ ↦ Fin m) a β i) = g a * ∏ i, g (β i) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end Words

section Decompose

variable {R : Type*} [AddCommMonoid R] {m n : ℕ}

/-- Summing over the words `γ` with a prescribed letter `γⱼ = a`. -/
private lemma sum_ite_eq_insertNth (j : Fin (n + 1)) (a : Fin m) (G : (Fin (n + 1) → Fin m) → R) :
    ∑ γ : Fin (n + 1) → Fin m, (if a = γ j then G γ else 0) =
      ∑ β : Fin n → Fin m, G (Fin.insertNth j a β) := by
  rw [← (Fin.insertNthEquiv (fun _ ↦ Fin m) j).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same]
  rw [Finset.sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  rfl

/-- Summing over the words `α` of length `n + 2` with `α₀ = α_{j+1}`. -/
private lemma sum_ite_cons_eq (j : Fin (n + 1)) (F : (Fin (n + 2) → Fin m) → R) :
    ∑ α : Fin (n + 2) → Fin m, (if α 0 = α j.succ then F α else 0) =
      ∑ a, ∑ β : Fin n → Fin m, F (Fin.cons a (Fin.insertNth j a β)) := by
  rw [← (Fin.consEquiv (fun _ ↦ Fin m)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  exact sum_congr rfl fun a _ ↦ sum_ite_eq_insertNth j a _

end Decompose

section Sums

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `∑ₚ (∑ᵢ wᵢ fᵢ(p))² = ∑ᵢⱼ wᵢ wⱼ ∑ₚ fᵢ(p) fⱼ(p)`. -/
private lemma sum_sq_weighted (w : ι → ℝ) (f : ι → κ → ℝ) :
    ∑ p, (∑ i, w i * f i p) * (∑ i, w i * f i p) =
      ∑ i, ∑ j, w i * w j * ∑ p, f i p * f j p := by
  have h1 : ∀ p, (∑ i, w i * f i p) * (∑ i, w i * f i p) =
      ∑ i, ∑ j, w i * w j * (f i p * f j p) := by
    intro p
    rw [Finset.sum_mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  simp_rw [h1, Finset.mul_sum]
  exact Fintype.sum_comm_cycle _

/-- `∑_{α ∈ [m]^k} ∏_q y(α_q) ∏_q z(α_q) = ⟨y, z⟩^k`. -/
private lemma sum_words_prod_mul {R : Type*} [CommSemiring R] {m : ℕ} (y z : Fin m → R) (k : ℕ) :
    ∑ α : Fin k → Fin m, (∏ q, y (α q)) * (∏ q, z (α q)) = (∑ a, y a * z a) ^ k := by
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

end Sums

/-! ### The real case -/

section Real

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **The recursive Sidelnikov–Welch inequality, real case** ([DL26, Theorem 2.1], with
`n = 2t - 2`). For unit vectors `x₁, …, x_N ∈ ℝ^m`, arbitrary real weights `wᵢ` and every
`n ≥ 0`, `(n + 1) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩ⁿ ≤ (m + n) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩ⁿ⁺²`. -/
theorem recursive_welch_real (x : ι → Fin m → ℝ) (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ)
    (n : ℕ) :
    (n + 1) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ n ≤
      (m + n) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (n + 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : IsEmpty ι := ⟨fun i ↦ by simpa using hx i⟩
    simp
  -- `A = ∑ᵢ wᵢ xᵢ^{⊗n}`, `T = ∑ᵢ wᵢ xᵢ^{⊗(n+2)}` and the test tensor `Z = ∑ⱼ δ_{0,j+1} ⊗ A`
  set A : (Fin n → Fin m) → ℝ := fun β ↦ ∑ i, w i * ∏ q, x i (β q) with hA
  set T : (Fin (n + 2) → Fin m) → ℝ := fun α ↦ ∑ i, w i * ∏ q, x i (α q) with hT
  set Z : (Fin (n + 2) → Fin m) → ℝ := fun α ↦ ∑ j : Fin (n + 1),
    if α 0 = α j.succ then A (Fin.removeNth j (Fin.tail α)) else 0 with hZ
  have hAA : ∑ β, A β * A β = ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ n := by
    rw [sum_sq_weighted]
    simp only [sum_words_prod_mul]
  have hTT : ∑ α, T α * T α = ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (n + 2) := by
    rw [sum_sq_weighted]
    simp only [sum_words_prod_mul]
  -- pairing with `Z` only sees the partial traces
  have hpair : ∀ V : (Fin (n + 2) → Fin m) → ℝ, ∑ α, Z α * V α =
      ∑ j : Fin (n + 1), ∑ β, A β * ∑ a, V (Fin.cons a (Fin.insertNth j a β)) := by
    intro V
    simp only [hZ, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_ite_cons_eq]
    simp only [Fin.tail_cons, Fin.removeNth_insertNth]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  -- partial traces of `T` (this uses `‖xᵢ‖ = 1`)
  have hTtr : ∀ (j : Fin (n + 1)) (β : Fin n → Fin m),
      ∑ a, T (Fin.cons a (Fin.insertNth j a β)) = A β := by
    intro j β
    simp only [hT, hA, prod_cons_apply, prod_insertNth_apply]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    calc ∑ a, w i * (x i a * (x i a * ∏ q, x i (β q))) =
          w i * (∏ q, x i (β q)) * ∑ a, x i a ^ 2 := by
          rw [Finset.mul_sum]; exact sum_congr rfl fun a _ ↦ by ring
      _ = w i * ∏ q, x i (β q) := by rw [hx i, mul_one]
  -- `A` is symmetric
  have hsymm : ∀ (γ : Fin (n + 1) → Fin m) (j l : Fin (n + 1)), γ j = γ l →
      A (Fin.removeNth j γ) = A (Fin.removeNth l γ) := by
    intro γ j l h
    simp only [hA, Fin.removeNth_apply]
    exact sum_congr rfl fun i _ ↦ congrArg (w i * ·)
      (prod_succAbove_eq_of_eq (f := fun q ↦ x i (γ q)) (j := j) (l := l) (by simp only [h]))
  -- partial traces of `Z`
  have hZtr : ∀ (l : Fin (n + 1)) (β : Fin n → Fin m),
      ∑ a, Z (Fin.cons a (Fin.insertNth l a β)) = (m + n) * A β := by
    intro l β
    simp only [hZ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
    rw [Finset.sum_comm, Fin.sum_univ_succAbove _ l]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.removeNth_insertNth,
      ite_true, sum_ite_eq', mem_univ]
    have e : ∀ k : Fin n, A (Fin.removeNth (l.succAbove k)
        (Fin.insertNth (α := fun _ ↦ Fin m) l (β k) β)) = A β := by
      intro k
      rw [hsymm _ (l.succAbove k) l (by simp), Fin.removeNth_insertNth]
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the inner products with `Z`
  have hZT : ∑ α, Z α * T α = (n + 1) * ∑ β, A β * A β := by
    rw [hpair]
    simp only [hTtr, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hZZ : ∑ α, Z α * Z α = (n + 1) * (m + n) * ∑ β, A β * A β := by
    rw [hpair]
    simp only [hZtr]
    have e : ∀ β, A β * ((m + n) * A β) = (m + n) * (A β * A β) := fun β ↦ by ring
    simp only [e, ← Finset.mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- `0 ≤ ‖Z - (m + n) T‖²`
  have hnonneg : 0 ≤ ∑ α, (Z α - (m + n) * T α) ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hexp : ∑ α, (Z α - (m + n) * T α) ^ 2 = ∑ α, Z α * Z α -
      2 * (m + n) * ∑ α, Z α * T α + (m + n) ^ 2 * ∑ α, T α * T α := by
    have e : ∀ α, (Z α - (m + n) * T α) ^ 2 = Z α * Z α - 2 * (m + n) * (Z α * T α) +
        (m + n) ^ 2 * (T α * T α) := fun α ↦ by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp, hZZ, hZT, hTT, hAA] at hnonneg
  have hmn : (0 : ℝ) < m + n := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have h : 0 ≤ (m + n) * ((m + n) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (n + 2) -
      (n + 1) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ n) := by linarith
  have := (mul_nonneg_iff_of_pos_left hmn).mp h
  linarith

/-- **The recursive Sidelnikov–Welch inequality, real case**, in the form of
[DL26, Theorem 2.1]: for `t ≥ 1`,
`∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t} ≥ (2t-1)/(m+2t-2) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t-2}`. -/
theorem recursive_welch_real' (hm : 1 ≤ m) (x : ι → Fin m → ℝ)
    (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    (2 * t - 1) / (m + 2 * t - 2) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t - 2) ≤
      ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t) := by
  have h := recursive_welch_real x hx w (2 * t - 2)
  rw [show 2 * t - 2 + 2 = 2 * t by omega] at h
  have hcast : ((2 * t - 2 : ℕ) : ℝ) = 2 * t - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at h
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith

/-- **The weighted Sidelnikov–Welch bound, real case** ([DL26, Corollary 2.1]):
`1·3⋯(2t-1) (∑ᵢ wᵢ)² ≤ m(m+2)⋯(m+2t-2) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t}`. -/
theorem weighted_welch_real (x : ι → Fin m → ℝ) (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ)
    (t : ℕ) :
    (∏ s ∈ range t, (2 * s + 1 : ℝ)) * (∑ i, w i) ^ 2 ≤
      (∏ s ∈ range t, (m + 2 * s : ℝ)) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t) := by
  induction t with
  | zero =>
    simp only [range_zero, prod_empty, one_mul, mul_zero, pow_zero, mul_one]
    rw [sq, Finset.sum_mul_sum]
  | succ t ih =>
    have h := recursive_welch_real x hx w (2 * t)
    rw [show 2 * t + 2 = 2 * (t + 1) by ring] at h
    push_cast at h
    have hP : 0 ≤ ∏ s ∈ range t, (m + 2 * s : ℝ) := prod_nonneg fun s _ ↦ by positivity
    rw [prod_range_succ, prod_range_succ]
    have h1 := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 2 * t + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left h hP
    nlinarith [h1, h2]

/-- **The case `t = 2` of [DL26, Theorem 2.1], real case**:
`3 ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩² ≤ (m + 2) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩⁴`. -/
theorem welch_real (x : ι → Fin m → ℝ) (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ) :
    3 * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ 2 ≤
      (m + 2) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ 4 := by
  have h := recursive_welch_real x hx w 2
  norm_num at h
  exact h

end Real

/-! ### The complex case -/

section Complex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {m : ℕ}

open RCLike

/-- Summing over the pairs of words `(α, γ)` with `α₀ = γⱼ`. -/
private lemma sum_ite_cons_eq_insertNth {R : Type*} [AddCommMonoid R] {p : ℕ} (j : Fin (p + 1))
    (F : (Fin (p + 1) → Fin m) → (Fin (p + 1) → Fin m) → R) :
    ∑ α : Fin (p + 1) → Fin m, ∑ γ : Fin (p + 1) → Fin m, (if α 0 = γ j then F α γ else 0) =
      ∑ a, ∑ α' : Fin p → Fin m, ∑ β : Fin p → Fin m,
        F (Fin.cons a α') (Fin.insertNth j a β) := by
  rw [← (Fin.consEquiv (fun _ ↦ Fin m)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun α' _ ↦ sum_ite_eq_insertNth j a _

omit [Fintype ι] in
/-- `|u - c v|² = |u|² - 2c re(conj u · v) + c² |v|²` for real `c`. -/
private lemma norm_sub_ofReal_mul_sq (u v : 𝕜) (c : ℝ) :
    ‖u - c * v‖ ^ 2 = ‖u‖ ^ 2 - 2 * c * re (conj u * v) + c ^ 2 * ‖v‖ ^ 2 := by
  have hn : ∀ z : 𝕜, ‖z‖ ^ 2 = re (conj z * z) := fun z ↦ by
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have e : conj (u - c * v) * (u - c * v) = conj u * u - (c : 𝕜) * (conj u * v) -
      (c : 𝕜) * conj (conj u * v) + ((c ^ 2 : ℝ) : 𝕜) * (conj v * v) := by
    simp only [map_sub, map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
    push_cast
    ring
  rw [hn, hn u, hn v, e, map_add, map_sub, map_sub, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul,
    RCLike.re_ofReal_mul, RCLike.conj_re]
  ring

/-- `∑ₚ |∑ᵢ wᵢ fᵢ(p)|² = ∑ᵢⱼ wᵢ wⱼ ∑ₚ conj(fᵢ(p)) fⱼ(p)`. -/
private lemma sum_norm_sq_weighted {κ : Type*} [Fintype κ] (w : ι → ℝ) (f : ι → κ → 𝕜) :
    ((∑ p, ‖∑ i, (w i : 𝕜) * f i p‖ ^ 2 : ℝ) : 𝕜) =
      ∑ i, ∑ j, (w i : 𝕜) * w j * ∑ p, conj (f i p) * f j p := by
  push_cast
  have h1 : ∀ p, (‖∑ i, (w i : 𝕜) * f i p‖ : 𝕜) ^ 2 =
      ∑ i, ∑ j, (w i : 𝕜) * w j * (conj (f i p) * f j p) := by
    intro p
    rw [← RCLike.conj_mul, map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    simp only [map_mul, RCLike.conj_ofReal]
    ring
  simp_rw [h1, Finset.mul_sum]
  exact Fintype.sum_comm_cycle _

private lemma sum_words_conj_mul (y z : Fin m → 𝕜) (k : ℕ) :
    ∑ α : Fin k → Fin m, (∏ q, conj (y (α q))) * (∏ q, z (α q)) =
      (∑ a, conj (y a) * z a) ^ k := by
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

/-- `∑_{α,γ} conj(yᵅ conj(y^γ)) zᵅ conj(z^γ) = |⟨y, z⟩|^{2k}` (with `yᵅ = ∏_r y(α_r)`). -/
private lemma sum_word_pairs (y z : Fin m → 𝕜) (k : ℕ) :
    ∑ q : (Fin k → Fin m) × (Fin k → Fin m),
      conj ((∏ r, y (q.1 r)) * conj (∏ r, y (q.2 r))) * ((∏ r, z (q.1 r)) * conj (∏ r, z (q.2 r)))
      = ((‖∑ a, conj (y a) * z a‖ ^ (2 * k) : ℝ) : 𝕜) := by
  rw [Fintype.sum_prod_type]
  have e : ∀ α γ : Fin k → Fin m,
      conj ((∏ r, y (α r)) * conj (∏ r, y (γ r))) * ((∏ r, z (α r)) * conj (∏ r, z (γ r))) =
        ((∏ r, conj (y (α r))) * ∏ r, z (α r)) * ((∏ r, conj (z (γ r))) * ∏ r, y (γ r)) := by
    intro α γ
    simp only [map_mul, RCLike.conj_conj, map_prod]
    ring
  simp only [e, ← Finset.sum_mul_sum]
  rw [sum_words_conj_mul, sum_words_conj_mul]
  have hG : ∑ a, conj (z a) * y a = conj (∑ a, conj (y a) * z a) := by
    rw [map_sum]
    exact sum_congr rfl fun a _ ↦ by simp only [map_mul, RCLike.conj_conj, mul_comm]
  rw [hG, ← mul_pow, RCLike.mul_conj, pow_mul]
  push_cast
  ring

/-- **The recursive Sidelnikov–Welch inequality, complex case** ([DL26, Theorem 2.1], with
`p = t - 1`). For unit vectors `x₁, …, x_N ∈ 𝕜^m`, arbitrary real weights `wᵢ` and every
`p ≥ 0`, `(p + 1) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2p} ≤ (m + p) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2p+2}`. -/
theorem recursive_welch_complex (x : ι → Fin m → 𝕜) (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) (w : ι → ℝ)
    (p : ℕ) :
    (p + 1) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * p) ≤
      (m + p) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * p + 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : IsEmpty ι := ⟨fun i ↦ by simpa using hx i⟩
    simp
  set Y : ℕ → ℝ := fun k ↦ ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * k) with hY
  -- `A = ∑ᵢ wᵢ xᵢ^{⊗p} ⊗ conj(xᵢ)^{⊗p}`, `T` likewise with `p + 1`, and
  -- `Z = ∑ⱼ δ_{0,j} ⊗ A` (pairing the first letter of `α` with the `j`-th letter of `γ`)
  set A : (Fin p → Fin m) → (Fin p → Fin m) → 𝕜 := fun α γ ↦
    ∑ i, (w i : 𝕜) * ((∏ r, x i (α r)) * conj (∏ r, x i (γ r))) with hA
  set T : (Fin (p + 1) → Fin m) → (Fin (p + 1) → Fin m) → 𝕜 := fun α γ ↦
    ∑ i, (w i : 𝕜) * ((∏ r, x i (α r)) * conj (∏ r, x i (γ r))) with hT
  set Z : (Fin (p + 1) → Fin m) → (Fin (p + 1) → Fin m) → 𝕜 := fun α γ ↦
    ∑ j : Fin (p + 1), if α 0 = γ j then A (Fin.tail α) (Fin.removeNth j γ) else 0 with hZ
  -- Gram identities
  have gram : ∀ k : ℕ, ((∑ α : Fin k → Fin m, ∑ γ : Fin k → Fin m,
      ‖∑ i, (w i : 𝕜) * ((∏ r, x i (α r)) * conj (∏ r, x i (γ r)))‖ ^ 2 : ℝ) : 𝕜) =
        ((Y k : ℝ) : 𝕜) := by
    intro k
    have h := sum_norm_sq_weighted w (fun i (q : (Fin k → Fin m) × (Fin k → Fin m)) ↦
      (∏ r, x i (q.1 r)) * conj (∏ r, x i (q.2 r)))
    rw [Fintype.sum_prod_type] at h
    rw [h]
    simp only [sum_word_pairs, hY]
    push_cast
    rfl
  have hAA : ∑ α, ∑ γ, ‖A α γ‖ ^ 2 = Y p := RCLike.ofReal_injective (gram p)
  have hTT : ∑ α, ∑ γ, ‖T α γ‖ ^ 2 = Y (p + 1) := RCLike.ofReal_injective (gram (p + 1))
  -- pairing with `Z` only sees the partial traces
  have hpair : ∀ V : (Fin (p + 1) → Fin m) → (Fin (p + 1) → Fin m) → 𝕜,
      ∑ α, ∑ γ, conj (Z α γ) * V α γ =
        ∑ j : Fin (p + 1), ∑ α', ∑ β,
          conj (A α' β) * ∑ a, V (Fin.cons a α') (Fin.insertNth j a β) := by
    intro V
    simp only [hZ, map_sum, apply_ite (starRingEnd 𝕜), map_zero, Finset.sum_mul, ite_mul,
      zero_mul]
    rw [Fintype.sum_comm_cycle, Fintype.sum_comm_cycle]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_ite_cons_eq_insertNth]
    simp only [Fin.tail_cons, Fin.removeNth_insertNth, Finset.mul_sum]
    rw [Fintype.sum_comm_cycle]
  -- partial traces of `T` (this uses `‖xᵢ‖ = 1`)
  have hTtr : ∀ (j : Fin (p + 1)) (α' β : Fin p → Fin m),
      ∑ a, T (Fin.cons a α') (Fin.insertNth j a β) = A α' β := by
    intro j α' β
    simp only [hT, hA, prod_cons_apply, prod_insertNth_apply, map_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    have h1 : ∑ a, x i a * conj (x i a) = 1 := by
      simp only [RCLike.mul_conj]
      exact_mod_cast hx i
    calc ∑ a, (w i : 𝕜) * ((x i a * ∏ r, x i (α' r)) * (conj (x i a) * conj (∏ r, x i (β r)))) =
          (w i : 𝕜) * ((∏ r, x i (α' r)) * conj (∏ r, x i (β r))) *
            ∑ a, x i a * conj (x i a) := by
          rw [Finset.mul_sum]; exact sum_congr rfl fun a _ ↦ by ring
      _ = _ := by rw [h1, mul_one]
  -- `A` is symmetric in the conjugated letters
  have hsymm : ∀ (α' : Fin p → Fin m) (γ : Fin (p + 1) → Fin m) (j l : Fin (p + 1)),
      γ j = γ l → A α' (Fin.removeNth j γ) = A α' (Fin.removeNth l γ) := by
    intro α' γ j l h
    simp only [hA, Fin.removeNth_apply]
    exact sum_congr rfl fun i _ ↦ congrArg (fun P ↦ (w i : 𝕜) * ((∏ r, x i (α' r)) * conj P))
      (prod_succAbove_eq_of_eq (f := fun q ↦ x i (γ q)) (j := j) (l := l) (by simp only [h]))
  -- partial traces of `Z`
  have hZtr : ∀ (l : Fin (p + 1)) (α' β : Fin p → Fin m),
      ∑ a, Z (Fin.cons a α') (Fin.insertNth l a β) = (m + p) * A α' β := by
    intro l α' β
    simp only [hZ, Fin.cons_zero, Fin.tail_cons]
    rw [Finset.sum_comm, Fin.sum_univ_succAbove _ l]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.removeNth_insertNth,
      ite_true, sum_ite_eq', mem_univ]
    have e : ∀ k : Fin p, A α' (Fin.removeNth (l.succAbove k)
        (Fin.insertNth (α := fun _ ↦ Fin m) l (β k) β)) = A α' β := by
      intro k
      rw [hsymm α' _ (l.succAbove k) l (by simp), Fin.removeNth_insertNth]
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the inner products with `Z`
  have hconjA : ∑ α, ∑ γ, conj (A α γ) * A α γ = ((Y p : ℝ) : 𝕜) := by
    rw [← hAA]
    push_cast
    simp only [RCLike.conj_mul]
  have hZT : ∑ α, ∑ γ, conj (Z α γ) * T α γ = (((p + 1) * Y p : ℝ) : 𝕜) := by
    rw [hpair]
    simp only [hTtr, hconjA, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hZZ : ∑ α, ∑ γ, conj (Z α γ) * Z α γ = (((p + 1) * (m + p) * Y p : ℝ) : 𝕜) := by
    rw [hpair]
    simp only [hZtr]
    have e : ∀ α' β, conj (A α' β) * ((m + p) * A α' β) = (m + p) * (conj (A α' β) * A α' β) :=
      fun α' β ↦ by ring
    simp only [e, ← Finset.mul_sum, hconjA, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- `0 ≤ ‖Z - (m + p) T‖²`
  set c : ℝ := m + p with hc
  have hn : ∀ z : 𝕜, ‖z‖ ^ 2 = re (conj z * z) := fun z ↦ by
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hexp : ∑ α, ∑ γ, ‖Z α γ - c * T α γ‖ ^ 2 =
      (p + 1) * c * Y p - 2 * c * ((p + 1) * Y p) + c ^ 2 * Y (p + 1) := by
    simp only [norm_sub_ofReal_mul_sq, sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
    rw [hTT]
    simp only [hn (Z _ _)]
    have e1 : ∑ α, ∑ γ, re (conj (Z α γ) * Z α γ) = re (∑ α, ∑ γ, conj (Z α γ) * Z α γ) := by
      simp only [map_sum]
    have e2 : ∑ α, ∑ γ, re (conj (Z α γ) * T α γ) = re (∑ α, ∑ γ, conj (Z α γ) * T α γ) := by
      simp only [map_sum]
    rw [e1, e2, hZZ, hZT, RCLike.ofReal_re, RCLike.ofReal_re]
  have hnonneg : 0 ≤ ∑ α, ∑ γ, ‖Z α γ - c * T α γ‖ ^ 2 :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [hexp] at hnonneg
  have hc0 : 0 < c := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    rw [hc]; positivity
  have h : 0 ≤ c * (c * Y (p + 1) - (p + 1) * Y p) := by linarith
  have := (mul_nonneg_iff_of_pos_left hc0).mp h
  have e : 2 * (p + 1) = 2 * p + 2 := by ring
  simp only [hY, e] at this
  linarith

/-- **The recursive Sidelnikov–Welch inequality, complex case**, in the form of
[DL26, Theorem 2.1]: for `t ≥ 1`,
`∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t} ≥ t/(m+t-1) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t-2}`. -/
theorem recursive_welch_complex' (hm : 1 ≤ m) (x : ι → Fin m → 𝕜)
    (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) (w : ι → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    t / (m + t - 1) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t - 2) ≤
      ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t) := by
  obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
  have h := recursive_welch_complex x hx w p
  rw [show 2 * (p + 1) - 2 = 2 * p by omega, show 2 * (p + 1) = 2 * p + 2 by ring]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) ≤ p := by positivity
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith

/-- **The weighted Sidelnikov–Welch bound, complex case** ([DL26, Corollary 2.1]):
`(∑ᵢ wᵢ)² ≤ C(m+t-1, t) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t}`. -/
theorem weighted_welch_complex (x : ι → Fin m → 𝕜) (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1)
    (w : ι → ℝ) (t : ℕ) :
    (∑ i, w i) ^ 2 ≤
      ((m + t - 1).choose t : ℝ) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t) := by
  -- first the product form `t! (∑ wᵢ)² ≤ m(m+1)⋯(m+t-1) X_{2t}`
  have key : ∀ t : ℕ, (∏ s ∈ range t, (s + 1 : ℝ)) * (∑ i, w i) ^ 2 ≤
      (∏ s ∈ range t, (m + s : ℝ)) *
        ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t) := by
    intro t
    induction t with
    | zero =>
      simp only [range_zero, prod_empty, one_mul, mul_zero, pow_zero, mul_one]
      rw [sq, Finset.sum_mul_sum]
    | succ t ih =>
      have h := recursive_welch_complex x hx w t
      rw [show 2 * t + 2 = 2 * (t + 1) by ring] at h
      have hP : 0 ≤ ∏ s ∈ range t, (m + s : ℝ) := prod_nonneg fun s _ ↦ by positivity
      rw [prod_range_succ, prod_range_succ]
      have h1 := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ t + 1 by positivity)
      have h2 := mul_le_mul_of_nonneg_left h hP
      nlinarith [h1, h2]
  have h := key t
  have e1 : ∏ s ∈ range t, (s + 1 : ℝ) = (t.factorial : ℝ) := by
    rw [Nat.factorial_eq_prod_range_add_one]; push_cast; rfl
  have e2 : ∏ s ∈ range t, (m + s : ℝ) = (t.factorial : ℝ) * ((m + t - 1).choose t : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.ascFactorial_eq_factorial_mul_choose', Nat.ascFactorial_eq_prod_range]
    push_cast; rfl
  rw [e1, e2, mul_assoc] at h
  exact le_of_mul_le_mul_left h (by exact_mod_cast t.factorial_pos)

/-- **The case `t = 2` of [DL26, Theorem 2.1], complex case**:
`2 ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|² ≤ (m + 1) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|⁴`. -/
theorem welch_complex (x : ι → Fin m → 𝕜) (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) (w : ι → ℝ) :
    2 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 2 ≤
      (m + 1) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 4 := by
  have h := recursive_welch_complex x hx w 1
  norm_num at h
  exact h

end Complex

end ProjectionConstants
