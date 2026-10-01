/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Real coordinates on Hermitian matrices

The proof of the Bukh–Cox bound ([BC], see `ProjectionConstants.Bounds.BukhCox`) uses that the
Gram matrix of a family of Hermitian `m × m` matrices (for the real pairing `Re tr(XY)`) has rank
at most the real dimension `d` of the space of Hermitian matrices: `d = m(m+1)/2` over `ℝ` and
`d = m²` over `ℂ`.

We encode this by *coordinates*: a map `c : Herm_m → ℝ^Idx` with `Re tr(XY) = ∑ₖ ωₖ c(X)ₖ c(Y)ₖ`
and `Re tr X = ∑ₖ eₖ c(X)ₖ` (`HermCoords`, with weights `ωₖ = weight k`). Then every matrix of the
form `a Re tr(Xᵢ Xⱼ) - b Re tr Xᵢ Re tr Xⱼ` has rank at most `|Idx|` (`HermCoords.rank_le`).

## Main definitions

* `HermCoords 𝕜 m`: real coordinates on the Hermitian `m × m` matrices over `𝕜` in which the real
  trace pairing is diagonal and the trace is linear.
* `HermCoords.full 𝕜 m`: coordinates with `|Idx| = m²` for every `𝕜 = ℝ, ℂ`, using
  `c(X)ₖₗ = Re Xₖₗ + Im Xₖₗ` (the cross terms cancel for Hermitian matrices).
* `HermCoords.real m`: coordinates with `|Idx| = m(m+1)/2` for real symmetric matrices, indexed
  by the pairs `k ≤ l`.

## Main statements

* `HermCoords.rank_le`: the matrix `(a Re tr(Xᵢ Xⱼ) - b Re tr Xᵢ Re tr Xⱼ)ᵢⱼ` has rank at most
  `|Idx|`.
* `HermCoords.card_full`, `HermCoords.card_real`: the numbers of coordinates, `m²` and
  `m(m+1)/2`.

## References

* [BC] B. Bukh, C. Cox, *Nearly orthogonal vectors and small antipodal spherical codes*,
  arXiv:1803.02949.
-/

open Matrix Finset

namespace ProjectionConstants

/-- Real coordinates on Hermitian `m × m` matrices in which the real trace pairing is diagonal
and the trace is linear. -/
structure HermCoords (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) where
  /-- The index set of the coordinates. -/
  Idx : Type
  [fintype : Fintype Idx]
  [decEq : DecidableEq Idx]
  /-- The coordinates. -/
  c : Matrix (Fin m) (Fin m) 𝕜 → Idx → ℝ
  /-- The weights of the pairing. -/
  weight : Idx → ℝ
  /-- The coefficients of the trace. -/
  e : Idx → ℝ
  /-- The real trace pairing is diagonal: `Re tr(XY) = ∑ₖ ωₖ c(X)ₖ c(Y)ₖ`. -/
  re_trace_mul : ∀ X Y : Matrix (Fin m) (Fin m) 𝕜, X.IsHermitian → Y.IsHermitian →
    RCLike.re (X * Y).trace = ∑ k, weight k * c X k * c Y k
  /-- The real trace is linear: `Re tr X = ∑ₖ eₖ c(X)ₖ`. -/
  re_trace : ∀ X : Matrix (Fin m) (Fin m) 𝕜, X.IsHermitian → RCLike.re X.trace = ∑ k, e k * c X k

attribute [instance] HermCoords.fintype HermCoords.decEq

namespace HermCoords

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} (H : HermCoords 𝕜 m)

/-- **Rank bound.** For Hermitian `X₁, …, X_N`, the matrix
`(a Re tr(Xᵢ Xⱼ) - b Re tr Xᵢ Re tr Xⱼ)ᵢⱼ` has rank at most `|Idx|`. -/
theorem rank_le {ι : Type*} [Fintype ι] (X : ι → Matrix (Fin m) (Fin m) 𝕜)
    (hX : ∀ i, (X i).IsHermitian) (a b : ℝ) :
    (Matrix.of fun i j ↦ a * RCLike.re (X i * X j).trace -
      b * RCLike.re (X i).trace * RCLike.re (X j).trace).rank ≤ Fintype.card H.Idx := by
  let C : Matrix H.Idx ι ℝ := Matrix.of fun k i ↦ H.c (X i) k
  let K : Matrix H.Idx H.Idx ℝ := Matrix.of fun k l ↦
    a * (if k = l then H.weight k else 0) - b * H.e k * H.e l
  have hM : (Matrix.of fun i j ↦ a * RCLike.re (X i * X j).trace -
      b * RCLike.re (X i).trace * RCLike.re (X j).trace) = Cᵀ * (K * C) := by
    ext i j
    simp only [of_apply, mul_apply, transpose_apply, C, K, H.re_trace_mul _ _ (hX i) (hX j),
      H.re_trace _ (hX i), H.re_trace _ (hX j)]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      ring
  rw [hM]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width _)

/-! ### Coordinates with `m²` entries -/

/-- `Re (x conj(y)) = Re x Re y + Im x Im y`. -/
lemma re_mul_star_add (x y : 𝕜) :
    RCLike.re (x * star y) = RCLike.re x * RCLike.re y + RCLike.im x * RCLike.im y := by
  simp [RCLike.star_def, RCLike.mul_re]

variable (𝕜 m) in
/-- Coordinates `c(X)ₖₗ = Re Xₖₗ + Im Xₖₗ` on `Fin m × Fin m`: for Hermitian `X, Y` the cross
terms `Re Xₖₗ Im Yₖₗ + Im Xₖₗ Re Yₖₗ` cancel between `(k, l)` and `(l, k)`. -/
noncomputable def full : HermCoords 𝕜 m where
  Idx := Fin m × Fin m
  c X p := RCLike.re (X p.1 p.2) + RCLike.im (X p.1 p.2)
  weight _ := 1
  e p := if p.1 = p.2 then 1 else 0
  re_trace_mul X Y hX hY := by
    have hYs : ∀ k l, Y l k = star (Y k l) := fun k l ↦ by
      conv_lhs => rw [← hY]
      rfl
    have hXs : ∀ k l, X l k = star (X k l) := fun k l ↦ by
      conv_lhs => rw [← hX]
      rfl
    -- `Re tr(XY) = ∑ₖₗ (Re Xₖₗ Re Yₖₗ + Im Xₖₗ Im Yₖₗ)`
    have h1 : RCLike.re (X * Y).trace = ∑ p : Fin m × Fin m,
        (RCLike.re (X p.1 p.2) * RCLike.re (Y p.1 p.2) +
          RCLike.im (X p.1 p.2) * RCLike.im (Y p.1 p.2)) := by
      simp only [Matrix.trace, diag_apply, mul_apply, map_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hYs k l, re_mul_star_add]
    -- the cross terms cancel
    have h2 : ∑ p : Fin m × Fin m, (RCLike.re (X p.1 p.2) * RCLike.im (Y p.1 p.2) +
        RCLike.im (X p.1 p.2) * RCLike.re (Y p.1 p.2)) = 0 := by
      set f : Fin m × Fin m → ℝ := fun p ↦ RCLike.re (X p.1 p.2) * RCLike.im (Y p.1 p.2) +
        RCLike.im (X p.1 p.2) * RCLike.re (Y p.1 p.2)
      have hf : ∀ p : Fin m × Fin m, f p.swap = -f p := by
        intro p
        simp only [f, Prod.fst_swap, Prod.snd_swap, hXs p.1 p.2, hYs p.1 p.2, RCLike.star_def,
          RCLike.conj_re, RCLike.conj_im]
        ring
      have h : ∑ p : Fin m × Fin m, f p = ∑ p : Fin m × Fin m, f p.swap :=
        ((Equiv.prodComm _ _).sum_comp f).symm
      simp only [hf, Finset.sum_neg_distrib] at h
      linarith
    rw [h1]
    rw [show ∑ p : Fin m × Fin m, 1 * (RCLike.re (X p.1 p.2) + RCLike.im (X p.1 p.2)) *
      (RCLike.re (Y p.1 p.2) + RCLike.im (Y p.1 p.2)) =
      ∑ p : Fin m × Fin m, (RCLike.re (X p.1 p.2) * RCLike.re (Y p.1 p.2) +
        RCLike.im (X p.1 p.2) * RCLike.im (Y p.1 p.2)) +
      ∑ p : Fin m × Fin m, (RCLike.re (X p.1 p.2) * RCLike.im (Y p.1 p.2) +
        RCLike.im (X p.1 p.2) * RCLike.re (Y p.1 p.2)) by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun p _ ↦ by ring]
    rw [h2, add_zero]
  re_trace X hX := by
    have him : ∀ k, RCLike.im (X k k) = 0 := fun k ↦ by
      have : X k k = star (X k k) := by
        conv_lhs => rw [← hX]
        rfl
      have h := congrArg RCLike.im this
      rw [RCLike.star_def, RCLike.conj_im] at h
      linarith
    simp only [Matrix.trace, diag_apply, map_sum, Fintype.sum_prod_type, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, him, add_zero]

/-- The coordinates `HermCoords.full 𝕜 m` have `m²` entries. -/
lemma card_full : Fintype.card (full 𝕜 m).Idx = m ^ 2 := by
  have h : Fintype.card (full 𝕜 m).Idx = Fintype.card (Fin m × Fin m) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h]
  simp [sq]

/-! ### Coordinates with `m(m+1)/2` entries for real symmetric matrices -/

variable (m) in
/-- Coordinates `c(X)ₖₗ = Xₖₗ`, `k ≤ l`, for real symmetric matrices, with weights `1` on the
diagonal and `2` off the diagonal. -/
noncomputable def real : HermCoords ℝ m where
  Idx := {p : Fin m × Fin m // p.1 ≤ p.2}
  c X p := X p.1.1 p.1.2
  weight p := if p.1.1 = p.1.2 then 1 else 2
  e p := if p.1.1 = p.1.2 then 1 else 0
  re_trace_mul X Y hX hY := by
    have hYs : ∀ k l, Y l k = Y k l := fun k l ↦ by
      have := congrFun (congrFun hY k) l
      simpa using this
    have hXs : ∀ k l, X l k = X k l := fun k l ↦ by
      have := congrFun (congrFun hX k) l
      simpa using this
    set f : Fin m × Fin m → ℝ := fun p ↦ X p.1 p.2 * Y p.1 p.2
    have hfs : ∀ p, f p.swap = f p := fun p ↦ by simp only [f, Prod.fst_swap, Prod.snd_swap,
      hXs, hYs]
    -- `tr(XY) = ∑ₖₗ Xₖₗ Yₖₗ`
    have h1 : RCLike.re (X * Y).trace = ∑ p : Fin m × Fin m, f p := by
      simp only [RCLike.re_to_real, Matrix.trace, diag_apply, mul_apply, Fintype.sum_prod_type, f]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by rw [hYs]
    -- split into `k < l`, `k = l`, `k > l`
    have h2 : ∑ p : Fin m × Fin m, f p =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2), f p +
          ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 < p.2), f p := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin m × Fin m ↦ p.1 ≤ p.2)]
      congr 1
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hp ⊢
        exact hp
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hp ⊢
        exact hp
      · intro p _; rfl
      · intro p _; rfl
      · intro p _; exact (hfs p).symm
    have h3 : ∑ p : {p : Fin m × Fin m // p.1 ≤ p.2},
        (if p.1.1 = p.1.2 then (1 : ℝ) else 2) * X p.1.1 p.1.2 * Y p.1.1 p.1.2 =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * f p := by
      rw [Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2))
        (p := fun p : Fin m × Fin m ↦ p.1 ≤ p.2) (fun q ↦ by simp)
        (fun p ↦ (if p.1 = p.2 then (1 : ℝ) else 2) * f p)]
      exact Finset.sum_congr rfl fun p _ ↦ by simp only [f]; ring
    have h4 : ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2),
        (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2), f p +
          ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 < p.2), f p := by
      have hsplit : ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
          ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2),
            (f p + if p.1 < p.2 then f p else 0) := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rcases hp.eq_or_lt with h | h
        · simp [h]
        · simp [h, h.ne]; ring
      rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.filter_filter]
      congr 2
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.le, h⟩⟩
    rw [h1, h2]
    change _ = ∑ p : {p : Fin m × Fin m // p.1 ≤ p.2},
      (if p.1.1 = p.1.2 then (1 : ℝ) else 2) * X p.1.1 p.1.2 * Y p.1.1 p.1.2
    rw [h3, h4]
  re_trace X _ := by
    simp only [RCLike.re_to_real, Matrix.trace, diag_apply]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m ↦ p.1 ≤ p.2))
      (p := fun p : Fin m × Fin m ↦ p.1 ≤ p.2) (fun q ↦ by simp)
      (fun p ↦ (if p.1 = p.2 then (1 : ℝ) else 0) * X p.1 p.2)]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
    symm
    refine Finset.sum_nbij' (fun p ↦ p.1) (fun k ↦ (k, k)) ?_ ?_ ?_ ?_ ?_
    · intro p _; simp
    · intro k _; simp
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact Prod.ext rfl hp.2
    · intro k _; rfl
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [hp.2]

/-- The coordinates `HermCoords.real m` have `m(m+1)/2` entries. -/
lemma card_real : Fintype.card (real m).Idx = m * (m + 1) / 2 := by
  have h : Fintype.card (real m).Idx = Fintype.card {p : Fin m × Fin m // p.1 ≤ p.2} :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, ← Fintype.card_congr Sym2.sortEquiv, Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  rw [Nat.add_sub_cancel, mul_comm]

end HermCoords

end ProjectionConstants
