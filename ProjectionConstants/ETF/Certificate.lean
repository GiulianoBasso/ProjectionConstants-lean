/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ETF.Basic

/-!
# Certificates for real equiangular tight frames

To prove that an explicit real equiangular tight frame exists, we give integer vectors
`v₁, …, v_N ∈ ℤⁿ` together with an integer vector `u ∈ ℤⁿ` and integers `normSq`, `innerAbs`,
`a`, `c` such that

* `⟨vᵢ, vᵢ⟩ = normSq` and `⟨vᵢ, vⱼ⟩ = ±innerAbs` for `i ≠ j`,
* `⟨vᵢ, u⟩ = 0` for all `i`,
* `∑ᵢ vᵢ vᵢᵀ = c I - a u uᵀ` (the frame is tight on `u^⊥`),
* `N · normSq = c m`.

Then the matrix `P = (⟨vᵢ, vⱼ⟩ / c)ᵢⱼ` is an ETF projection of rank `m`
(`ETFCertificate.isETFProj`): if `V` is the matrix with rows `vᵢ` and `G = V Vᵀ` is the Gram
matrix, then `G² = V (VᵀV) Vᵀ = c V Vᵀ - a (Vu)(Vu)ᵀ = c G`. Hence there is an equiangular tight
frame of `N` vectors in `ℝ^m` (`ETFCertificate.existsETF`). All conditions are verified by a
Boolean function (`ETFCertificate.check`), which the Lean kernel evaluates for the explicit
certificates of `ProjectionConstants.ETF.Maximal.Certificates`.

## Main definitions

* `Packing.pack B l`: the little-endian base-`B` packing of a list `l` of natural numbers.
* `ETFCertificate`: a certificate, consisting of the shifted frame vectors, the vector `u` and
  the numbers above.
* `ETFCertificate.check`: the Boolean check of all conditions of a certificate.
* `ETFCertificate.proj`: the matrix `P = G / c` of a certificate.

## Main statements

* `Packing.pack_mul_div_mod`: dot products are digits of products of packings.
* `ETFCertificate.isETFProj`: a valid certificate gives an ETF projection.
* `ETFCertificate.existsETF`: a valid certificate gives an equiangular tight frame.

## Implementation notes

The vectors are stored with an offset, `vᵢ = wᵢ - t 𝟙` with `wᵢ ∈ ℕⁿ`, and all inner products
are computed by **packing**: for lists `w, w'` of length `e + 1` with entries at most `M` and
`(e + 1) M² < B`, the dot product `⟨w, w'⟩` is the base-`B` digit of `pack w * pack (reverse w')`
at position `e` (`Packing.pack_mul_div_mod`). One multiplication of big natural numbers replaces
`e + 1` multiplications of small integers, which makes the certificate for the 276 equiangular
lines in `ℝ²³` checkable by the Lean kernel (`decide +kernel`, no `native_decide`).
-/

open Matrix Finset

namespace ProjectionConstants

namespace Packing

/-! ### Packed dot products -/

/-- Little-endian base-`B` packing of a list of natural numbers. -/
def pack (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => a + B * pack B as

/-- The dot product of two lists of natural numbers. -/
def dotN : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => a * b + dotN as bs
  | _, _ => 0

/-- The geometric sum `1 + B + ⋯ + B ^ (n - 1)`. -/
def geom (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + B * geom B n

lemma geom_mul_add {B : ℕ} (hB : 1 ≤ B) : ∀ n, (B - 1) * geom B n + 1 = B ^ n
  | 0 => by simp [geom]
  | n + 1 => by
    have ih := geom_mul_add hB n
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    simp only [Nat.add_sub_cancel, geom] at ih ⊢
    rw [pow_succ, ← ih]
    ring

lemma pack_le {B M : ℕ} : ∀ l : List ℕ, (∀ x ∈ l, x ≤ M) → pack B l ≤ M * geom B l.length
  | [], _ => by simp [pack, geom]
  | a :: as, h => by
    have ha := h a List.mem_cons_self
    have ih := pack_le (B := B) as fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    simp only [pack, List.length_cons, geom]
    calc a + B * pack B as ≤ M + B * (M * geom B as.length) := by gcongr
      _ = M * (1 + B * geom B as.length) := by ring

lemma pack_append_singleton (B b : ℕ) :
    ∀ l : List ℕ, pack B (l ++ [b]) = pack B l + B ^ l.length * b
  | [] => by simp [pack]
  | a :: as => by
    simp only [List.cons_append, pack, pack_append_singleton B b as, List.length_cons, pow_succ]
    ring

lemma dotN_le {M : ℕ} : ∀ w w' : List ℕ, (∀ x ∈ w, x ≤ M) → (∀ x ∈ w', x ≤ M) →
    dotN w w' ≤ w.length * M ^ 2
  | [], _, _, _ => by simp [dotN]
  | _ :: _, [], _, _ => by simp [dotN]
  | a :: as, b :: bs, h, h' => by
    have ih := dotN_le as bs (fun x hx ↦ h x (List.mem_cons_of_mem _ hx))
      (fun x hx ↦ h' x (List.mem_cons_of_mem _ hx))
    have hab : a * b ≤ M ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (h a List.mem_cons_self) (h' b List.mem_cons_self)
    simp only [dotN, List.length_cons]
    rw [add_mul, one_mul, add_comm]
    exact Nat.add_le_add ih hab

/-- The structure of `pack w * pack (reverse w')`: a low part, the digit `⟨w, w'⟩` at position
`n`, and a high part. -/
private lemma pack_mul_aux (B M : ℕ) : ∀ (n : ℕ) (w w' : List ℕ), w.length = n + 1 →
    w'.length = n + 1 → (∀ x ∈ w, x ≤ M) → (∀ x ∈ w', x ≤ M) →
    ∃ L H, pack B w * pack B w'.reverse = L + B ^ n * (dotN w w' + B * H) ∧
      L ≤ n * M ^ 2 * geom B n
  | 0, [a], [b], _, _, _, _ => ⟨0, 0, by simp [pack, dotN], by simp⟩
  | n + 1, a :: u, b :: u', hw, hw', h, h' => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hw hw'
    obtain ⟨L, H, hLH, hL⟩ := pack_mul_aux B M n u u' hw hw'
      (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) (fun x hx ↦ h' x (List.mem_cons_of_mem _ hx))
    have hR := pack_le (B := B) u'.reverse
      (fun x hx ↦ h' x (List.mem_cons_of_mem _ (List.mem_reverse.1 hx)))
    rw [List.length_reverse, hw'] at hR
    have ha := h a List.mem_cons_self
    refine ⟨a * pack B u'.reverse + B * L, H + pack B u * b, ?_, ?_⟩
    · rw [List.reverse_cons, pack_append_singleton, List.length_reverse, hw']
      simp only [pack, dotN]
      calc (a + B * pack B u) * (pack B u'.reverse + B ^ (n + 1) * b)
          = a * pack B u'.reverse + B * (pack B u * pack B u'.reverse) +
            B ^ (n + 1) * (a * b + B * (pack B u * b)) := by ring
        _ = _ := by rw [hLH]; ring
    · have h1 : a * pack B u'.reverse ≤ M ^ 2 * geom B (n + 1) := by
        calc a * pack B u'.reverse ≤ M * (M * geom B (n + 1)) := Nat.mul_le_mul ha hR
          _ = M ^ 2 * geom B (n + 1) := by ring
      have h2 : B * L ≤ n * M ^ 2 * geom B (n + 1) := by
        calc B * L ≤ B * (n * M ^ 2 * geom B n) := Nat.mul_le_mul_left _ hL
          _ = n * M ^ 2 * (B * geom B n) := by ring
          _ ≤ n * M ^ 2 * geom B (n + 1) := by
            apply Nat.mul_le_mul_left; simp only [geom]; omega
      calc a * pack B u'.reverse + B * L ≤ M ^ 2 * geom B (n + 1) + n * M ^ 2 * geom B (n + 1) :=
            Nat.add_le_add h1 h2
        _ = (n + 1) * M ^ 2 * geom B (n + 1) := by ring

/-- **Packed dot product.** If `w, w'` have length `n + 1`, entries at most `M`, and
`(n + 1) M² < B`, then `⟨w, w'⟩` is the `n`-th base-`B` digit of `pack w * pack (reverse w')`. -/
theorem pack_mul_div_mod {B M n : ℕ} {w w' : List ℕ} (hw : w.length = n + 1)
    (hw' : w'.length = n + 1) (h : ∀ x ∈ w, x ≤ M) (h' : ∀ x ∈ w', x ≤ M)
    (hB : (n + 1) * M ^ 2 < B) :
    pack B w * pack B w'.reverse / B ^ n % B = dotN w w' := by
  obtain ⟨L, H, hLH, hL⟩ := pack_mul_aux B M n w w' hw hw' h h'
  have hB1 : 1 ≤ B := by omega
  have hLlt : L < B ^ n := by
    have hg := geom_mul_add hB1 n
    have : n * M ^ 2 ≤ B - 1 := by
      have : n * M ^ 2 ≤ (n + 1) * M ^ 2 := Nat.mul_le_mul_right _ (Nat.le_succ n)
      omega
    calc L ≤ n * M ^ 2 * geom B n := hL
      _ ≤ (B - 1) * geom B n := Nat.mul_le_mul_right _ this
      _ < B ^ n := by omega
  have hD : dotN w w' < B := lt_of_le_of_lt (dotN_le w w' h h') (by rw [hw]; exact hB)
  rw [hLH, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hLlt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hD]

lemma dotN_eq_sum : ∀ {n : ℕ} (a b : List ℕ), a.length = n → b.length = n →
    dotN a b = ∑ k : Fin n, a.getD k 0 * b.getD k 0
  | 0, [], [], _, _ => by simp [dotN]
  | n + 1, x :: a, y :: b, ha, hb => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb
    rw [dotN, dotN_eq_sum a b ha hb, Fin.sum_univ_succ]
    simp

lemma sum_eq_sum_fin : ∀ {n : ℕ} (a : List ℕ), a.length = n → a.sum = ∑ k : Fin n, a.getD k 0
  | 0, [], _ => by simp
  | n + 1, x :: a, ha => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at ha
    rw [List.sum_cons, sum_eq_sum_fin a ha, Fin.sum_univ_succ]
    simp

/-- Inner products of offset vectors `w - t 𝟙`. -/
lemma sum_offset {n : ℕ} (t : ℕ) {w w' : List ℕ} (hw : w.length = n) (hw' : w'.length = n) :
    ∑ k : Fin n, (((w.getD k 0 : ℕ) : ℤ) - t) * ((w'.getD k 0 : ℕ) - t) =
      (dotN w w' : ℤ) - t * w.sum - t * w'.sum + n * t ^ 2 := by
  rw [dotN_eq_sum w w' hw hw', sum_eq_sum_fin w hw, sum_eq_sum_fin w' hw']
  push_cast
  calc ∑ k : Fin n, (((w.getD k 0 : ℕ) : ℤ) - t) * ((w'.getD k 0 : ℕ) - t)
      = ∑ k : Fin n, (((w.getD k 0 : ℕ) : ℤ) * (w'.getD k 0 : ℕ) - t * (w.getD k 0 : ℕ) -
          t * (w'.getD k 0 : ℕ) + t ^ 2) := Finset.sum_congr rfl fun k _ ↦ by ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      simp

/-- `allPairs p l` checks `p a b` for all pairs `a, b` with `a` before `b` in `l`. -/
def allPairs {α : Type*} (p : α → α → Bool) : List α → Bool
  | [] => true
  | a :: as => as.all (p a) && allPairs p as

lemma pairwise_of_allPairs {α : Type*} {p : α → α → Bool} :
    ∀ {l : List α}, allPairs p l = true → l.Pairwise fun a b ↦ p a b = true
  | [], _ => List.Pairwise.nil
  | a :: as, h => by
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwise_of_allPairs h.2)

/-- The data used for packed dot products: the packing, the packing of the reverse, the sum. -/
def packData (B : ℕ) (w : List ℕ) : ℕ × ℕ × ℕ := (pack B w, pack B w.reverse, w.sum)

/-- The packed dot product of lists of length `e + 1`. -/
def pdot (B e : ℕ) (x y : ℕ × ℕ × ℕ) : ℕ := x.1 * y.2.1 / B ^ e % B

lemma pdot_packData {B M e : ℕ} {w w' : List ℕ} (hw : w.length = e + 1)
    (hw' : w'.length = e + 1) (h : ∀ x ∈ w, x ≤ M) (h' : ∀ x ∈ w', x ≤ M)
    (hB : (e + 1) * M ^ 2 < B) : pdot B e (packData B w) (packData B w') = dotN w w' :=
  pack_mul_div_mod hw hw' h h' hB

end Packing

open Packing

/-- A certificate for a real equiangular tight frame. The frame vectors are `wᵢ - t 𝟙 ∈ ℤⁿ`. -/
structure ETFCertificate where
  /-- The ambient dimension. -/
  n : ℕ
  /-- The offset. -/
  t : ℕ
  /-- The shifted frame vectors `wᵢ = vᵢ + t 𝟙`. -/
  ws : List (List ℕ)
  /-- A vector orthogonal to all frame vectors. -/
  u : List ℕ
  /-- The coefficient of `u uᵀ` in the frame operator `c I - a u uᵀ`. -/
  a : ℤ
  /-- The squared norm of the frame vectors. -/
  normSq : ℤ
  /-- The modulus of the off-diagonal inner products. -/
  innerAbs : ℕ
  /-- The frame bound, the coefficient of `I` in the frame operator `c I - a u uᵀ`. -/
  c : ℤ
  /-- A bound for the entries of the `wᵢ` and of `u`. -/
  M : ℕ
  /-- The packing base. -/
  B : ℕ

namespace ETFCertificate

variable (C : ETFCertificate)

/-- The number of vectors. -/
abbrev N : ℕ := C.ws.length

/-- The `k`-th column of the shifted vectors. -/
def col (k : ℕ) : List ℕ := C.ws.map fun w ↦ w.getD k 0

/-- Shape: all vectors have length `n` and entries at most `M`. -/
def checkShape : Bool :=
  C.ws.all (fun w ↦ w.length == C.n && w.all (· ≤ C.M)) &&
    (C.u.length == C.n && C.u.all (· ≤ C.M))

/-- The packing base is large enough: `0 < n`, `0 < N`, `n M² < B` and `N M² < B`. -/
def checkBase : Bool :=
  decide (0 < C.n) && decide (0 < C.N) && decide (C.n * C.M ^ 2 < C.B) &&
    decide (C.N * C.M ^ 2 < C.B)

/-- `⟨vᵢ, vᵢ⟩ = normSq` for all `i`. -/
def checkNorm : Bool :=
  C.ws.all fun w ↦
    (pdot C.B (C.n - 1) (packData C.B w) (packData C.B w) : ℤ) - 2 * C.t * w.sum +
      C.n * C.t ^ 2 == C.normSq

/-- `⟨vᵢ, vⱼ⟩ = ±innerAbs`, in terms of the packed data of `wᵢ` and `wⱼ` (as an identity of
natural numbers). -/
def pairOK (x y : ℕ × ℕ × ℕ) : Bool :=
  pdot C.B (C.n - 1) x y + C.n * C.t ^ 2 == C.innerAbs + C.t * (x.2.2 + y.2.2) ||
    pdot C.B (C.n - 1) x y + C.n * C.t ^ 2 + C.innerAbs == C.t * (x.2.2 + y.2.2)

/-- `⟨vᵢ, vⱼ⟩ = ±innerAbs` for all `i < j`. -/
def checkPairs : Bool := allPairs C.pairOK (C.ws.map (packData C.B))

/-- `⟨vᵢ, u⟩ = 0` for all `i`. -/
def checkKer : Bool :=
  C.ws.all fun w ↦ pdot C.B (C.n - 1) (packData C.B w) (packData C.B C.u) == C.t * C.u.sum

/-- The data of the columns: for each coordinate `k`, the packed data of the `k`-th column of
the shifted vectors and the entry `uₖ`. -/
def colData : List (ℕ × (ℕ × ℕ × ℕ) × ℕ) :=
  (List.range C.n).map fun k ↦ (k, packData C.B (C.col k), C.u.getD k 0)

/-- The `(k, l)` entry of the frame operator is `c δₖₗ - a uₖ uₗ`. -/
def colOK (x y : ℕ × (ℕ × ℕ × ℕ) × ℕ) : Bool :=
  (pdot C.B (C.N - 1) x.2.1 y.2.1 : ℤ) - C.t * (x.2.1.2.2 + y.2.1.2.2) + C.N * C.t ^ 2 ==
    (if x.1 = y.1 then C.c else 0) - C.a * x.2.2 * y.2.2

/-- The frame operator is `c I - a u uᵀ`. -/
def checkFrame : Bool := C.colData.all fun x ↦ C.colData.all fun y ↦ C.colOK x y

/-- All conditions of the certificate. -/
def check : Bool :=
  C.checkShape && C.checkBase && C.checkNorm && C.checkPairs && C.checkKer && C.checkFrame

/-- The frame vectors `vᵢ = wᵢ - t 𝟙`. -/
def vec (i : Fin C.N) (k : Fin C.n) : ℤ := ((C.ws.get i).getD k 0 : ℤ) - C.t

/-- The integer Gram matrix `G = (⟨vᵢ, vⱼ⟩)ᵢⱼ`. -/
def gram (i j : Fin C.N) : ℤ := ∑ k, C.vec i k * C.vec j k

/-- The associated projection `P = G / c`. -/
noncomputable def proj : Matrix (Fin C.N) (Fin C.N) ℝ :=
  Matrix.of fun i j ↦ (C.gram i j : ℝ) / C.c

variable {C}

lemma gram_symm (i j : Fin C.N) : C.gram j i = C.gram i j := by
  simp only [gram, mul_comm]

lemma get_mem (i : Fin C.N) : C.ws.get i ∈ C.ws := List.get_mem _ _

lemma col_getD (k : ℕ) (z : Fin C.N) : (C.col k).getD z 0 = (C.ws.get z).getD k 0 := by
  simp [col, List.getD_eq_getElem?_getD]

lemma col_length (k : ℕ) : (C.col k).length = C.N := by simp [col]

/-- The consequences of a successful check. -/
structure Facts (C : ETFCertificate) : Prop where
  /-- The shifted frame vectors have length `n`. -/
  length_eq : ∀ w ∈ C.ws, w.length = C.n
  /-- The entries of the shifted frame vectors are at most `M`. -/
  bound : ∀ w ∈ C.ws, ∀ x ∈ w, x ≤ C.M
  /-- The vector `u` has length `n`. -/
  u_length_eq : C.u.length = C.n
  /-- The entries of `u` are at most `M`. -/
  u_bound : ∀ x ∈ C.u, x ≤ C.M
  /-- The ambient dimension is positive. -/
  n_pos : 0 < C.n
  /-- There is at least one frame vector. -/
  N_pos : 0 < C.N
  /-- The packing base is large enough for the dot products of rows. -/
  baseRow : C.n * C.M ^ 2 < C.B
  /-- The packing base is large enough for the dot products of columns. -/
  baseCol : C.N * C.M ^ 2 < C.B
  /-- The check of the squared norms succeeds. -/
  norm : C.checkNorm = true
  /-- The check of the off-diagonal inner products succeeds. -/
  pairs : C.checkPairs = true
  /-- The check of the orthogonality to `u` succeeds. -/
  ker : C.checkKer = true
  /-- The check of the frame operator succeeds. -/
  frame : C.checkFrame = true

/-- A successful check gives all the `Facts`. -/
lemma facts_of_check (h : C.check = true) : Facts C := by
  simp only [check, checkShape, checkBase, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, ⟨hul, huM⟩⟩, ⟨⟨⟨hn, hN⟩, hb1⟩, hb2⟩⟩, hnorm⟩, hpairs⟩, hker⟩, hframe⟩ := h
  exact ⟨fun w hw ↦ (hs w hw).1, fun w hw x hx ↦ by simpa using (hs w hw).2 x hx, hul,
    fun x hx ↦ by simpa using huM x hx, hn, hN, hb1, hb2, hnorm, hpairs, hker, hframe⟩

namespace Facts

variable (hC : Facts C)
include hC

/-- The packed dot products of the shifted frame vectors and of `u` are their dot products. -/
lemma pdot_eq {w w' : List ℕ} (hw : w ∈ C.ws ∨ w = C.u) (hw' : w' ∈ C.ws ∨ w' = C.u) :
    pdot C.B (C.n - 1) (packData C.B w) (packData C.B w') = dotN w w' := by
  have hlen : ∀ {v : List ℕ}, v ∈ C.ws ∨ v = C.u → v.length = C.n - 1 + 1 := by
    intro v hv
    rcases hv with hv | rfl
    · rw [hC.length_eq v hv]; have := hC.n_pos; omega
    · rw [hC.u_length_eq]; have := hC.n_pos; omega
  have hbd : ∀ {v : List ℕ}, v ∈ C.ws ∨ v = C.u → ∀ x ∈ v, x ≤ C.M := by
    intro v hv
    rcases hv with hv | rfl
    · exact hC.bound v hv
    · exact hC.u_bound
  refine pdot_packData (hlen hw) (hlen hw') (hbd hw) (hbd hw') ?_
  have := hC.baseRow; have := hC.n_pos
  rwa [Nat.sub_add_cancel (by omega)]

/-- `⟨vᵢ, vⱼ⟩ = ⟨wᵢ, wⱼ⟩ - t ∑ₖ wᵢₖ - t ∑ₖ wⱼₖ + n t²`. -/
lemma gram_eq (i j : Fin C.N) :
    C.gram i j = (dotN (C.ws.get i) (C.ws.get j) : ℤ) - C.t * (C.ws.get i).sum -
      C.t * (C.ws.get j).sum + C.n * C.t ^ 2 :=
  sum_offset C.t (hC.length_eq _ (get_mem i)) (hC.length_eq _ (get_mem j))

/-- `⟨vᵢ, vᵢ⟩ = normSq`. -/
lemma gram_diag (i : Fin C.N) : C.gram i i = C.normSq := by
  have h := hC.norm
  simp only [checkNorm, List.all_eq_true, beq_iff_eq] at h
  have hi := h _ (get_mem i)
  rw [hC.pdot_eq (Or.inl (get_mem i)) (Or.inl (get_mem i))] at hi
  rw [hC.gram_eq, ← hi]
  ring

/-- `⟨vᵢ, vⱼ⟩ = ±innerAbs` for `i ≠ j`. -/
lemma gram_off {i j : Fin C.N} (hij : i ≠ j) :
    C.gram i j = C.innerAbs ∨ C.gram i j = -C.innerAbs := by
  have key : ∀ {i j : Fin C.N}, i < j → C.gram i j = C.innerAbs ∨ C.gram i j = -C.innerAbs := by
    intro i j hlt
    have hp := List.pairwise_iff_get.1 (pairwise_of_allPairs hC.pairs)
    have hij : C.pairOK (packData C.B (C.ws.get i)) (packData C.B (C.ws.get j)) = true := by
      have := hp ⟨i, by simp⟩ ⟨j, by simp⟩ hlt
      simpa using this
    simp only [pairOK, Bool.or_eq_true, beq_iff_eq] at hij
    rw [hC.pdot_eq (Or.inl (get_mem i)) (Or.inl (get_mem j))] at hij
    rw [hC.gram_eq]
    simp only [packData] at hij
    rcases hij with h | h
    · left
      have h' : (dotN (C.ws.get i) (C.ws.get j) : ℤ) + C.n * C.t ^ 2 =
          C.innerAbs + C.t * (((C.ws.get i).sum : ℕ) + ((C.ws.get j).sum : ℕ) : ℤ) := by
        exact_mod_cast h
      linear_combination h'
    · right
      have h' : (dotN (C.ws.get i) (C.ws.get j) : ℤ) + C.n * C.t ^ 2 + C.innerAbs =
          C.t * (((C.ws.get i).sum : ℕ) + ((C.ws.get j).sum : ℕ) : ℤ) := by
        exact_mod_cast h
      linear_combination h'
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · rw [← gram_symm]; exact key h

/-- `⟨vᵢ, u⟩ = 0`. -/
lemma vec_orthogonal_u (i : Fin C.N) : ∑ k : Fin C.n, C.vec i k * (C.u.getD k 0 : ℤ) = 0 := by
  have h := hC.ker
  simp only [checkKer, List.all_eq_true, beq_iff_eq] at h
  have hi := h _ (get_mem i)
  rw [hC.pdot_eq (Or.inl (get_mem i)) (Or.inr rfl)] at hi
  have hi' : (dotN (C.ws.get i) C.u : ℤ) = C.t * C.u.sum := by exact_mod_cast hi
  simp only [vec]
  rw [dotN_eq_sum _ _ (hC.length_eq _ (get_mem i)) hC.u_length_eq,
    sum_eq_sum_fin _ hC.u_length_eq] at hi'
  push_cast at hi'
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hi']
  ring

lemma col_bound (k : ℕ) : ∀ x ∈ C.col k, x ≤ C.M := by
  intro x hx
  simp only [col, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  simp only [List.getD_eq_getElem?_getD]
  cases hk : w[k]? with
  | none => simp
  | some y => exact hC.bound w hw y (List.mem_of_getElem? hk)

/-- The frame operator: `∑ᵢ vᵢₖ vᵢₗ = c δₖₗ - a uₖ uₗ`. -/
lemma frame_apply (k l : Fin C.n) :
    ∑ z : Fin C.N, C.vec z k * C.vec z l =
      (if k = l then C.c else 0) - C.a * (C.u.getD k 0 : ℤ) * (C.u.getD l 0 : ℤ) := by
  have h := hC.frame
  simp only [checkFrame, List.all_eq_true] at h
  have hmem : ∀ k : Fin C.n, ((k : ℕ), packData C.B (C.col k), C.u.getD k 0) ∈ C.colData :=
    fun k ↦ List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩
  have hkl := h _ (hmem k) _ (hmem l)
  simp only [colOK, beq_iff_eq] at hkl
  have hcols : ∀ k : ℕ, (C.col k).length = C.N - 1 + 1 := by
    intro k; rw [col_length]; have := hC.N_pos; omega
  have hB : (C.N - 1 + 1) * C.M ^ 2 < C.B := by
    have := hC.baseCol; have := hC.N_pos
    rwa [Nat.sub_add_cancel (by omega)]
  rw [pdot_packData (hcols k) (hcols l) (hC.col_bound k) (hC.col_bound l) hB] at hkl
  have hoff := sum_offset (n := C.N) C.t (col_length k) (col_length l)
  simp only [col_getD] at hoff
  simp only [packData, Fin.val_inj] at hkl
  simp only [vec]
  rw [hoff, ← hkl]
  ring

/-- `G² = c G`. -/
lemma gram_sq (i j : Fin C.N) : ∑ z, C.gram i z * C.gram z j = C.c * C.gram i j := by
  set U : Fin C.n → ℤ := fun k ↦ (C.u.getD k 0 : ℤ) with hU
  have e1 : ∀ z, C.gram i z * C.gram z j =
      ∑ k, ∑ l, (C.vec i k * C.vec j l) * (C.vec z k * C.vec z l) := by
    intro z
    rw [gram, gram, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  have e2 : ∑ z, C.gram i z * C.gram z j =
      ∑ k, ∑ l, (C.vec i k * C.vec j l) * ((if k = l then C.c else 0) - C.a * U k * U l) := by
    calc ∑ z, C.gram i z * C.gram z j
        = ∑ z, ∑ k, ∑ l, (C.vec i k * C.vec j l) * (C.vec z k * C.vec z l) :=
          Finset.sum_congr rfl fun z _ ↦ e1 z
      _ = ∑ k, ∑ z, ∑ l, (C.vec i k * C.vec j l) * (C.vec z k * C.vec z l) := Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ z, (C.vec i k * C.vec j l) * (C.vec z k * C.vec z l) :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
      _ = ∑ k, ∑ l, (C.vec i k * C.vec j l) * ∑ z, C.vec z k * C.vec z l := by
          simp only [Finset.mul_sum]
      _ = _ := by simp only [hC.frame_apply, hU]
  have hsplit : ∀ k l, (C.vec i k * C.vec j l) * ((if k = l then C.c else 0) - C.a * U k * U l) =
      (if k = l then C.vec i k * C.vec j l * C.c else 0) -
        C.a * (C.vec i k * U k) * (C.vec j l * U l) := by
    intro k l; split_ifs <;> ring
  have hzero : ∑ k, ∑ l, C.a * (C.vec i k * U k) * (C.vec j l * U l) = 0 := by
    simp only [← Finset.mul_sum, hU, hC.vec_orthogonal_u j, mul_zero, Finset.sum_const_zero]
  rw [e2]
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hzero, sub_zero, gram, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

end Facts

/-- **A valid certificate gives an ETF projection.** If `C.check` holds, `c > 0` and
`N · normSq = c m`, then `P = G / c` is an ETF projection of rank `m`. -/
theorem isETFProj (h : C.check = true) {m : ℕ} (hc : 0 < C.c)
    (hm : (C.N : ℤ) * C.normSq = C.c * m) : IsETFProj m C.proj := by
  have hC := facts_of_check h
  have hc' : (C.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hmR : (C.N : ℝ) * C.normSq = C.c * m := by exact_mod_cast hm
  have hN : (C.N : ℝ) ≠ 0 := by exact_mod_cast hC.N_pos.ne'
  refine ⟨⟨.of_conjTranspose_eq ?_ ?_, ?_⟩, ?_, ⟨(C.innerAbs : ℝ) / C.c, fun i j hij ↦ ?_⟩⟩
  · ext i j
    simp [proj, gram_symm]
  · ext i j
    simp only [proj, mul_apply, of_apply]
    have hR : ∑ z, (C.gram i z : ℝ) * C.gram z j = C.c * C.gram i j := by
      exact_mod_cast hC.gram_sq i j
    rw [show ∑ z, (C.gram i z : ℝ) / C.c * ((C.gram z j : ℝ) / C.c) =
      (∑ z, (C.gram i z : ℝ) * C.gram z j) / C.c ^ 2 by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun z _ ↦ by ring, hR]
    field_simp
  · simp only [Matrix.trace, diag_apply, proj, of_apply, hC.gram_diag, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc, hmR]
    field_simp
  · intro i
    simp only [proj, of_apply, hC.gram_diag, Fintype.card_fin]
    field_simp
    linarith
  · simp only [proj, of_apply, Real.norm_eq_abs, abs_div]
    rw [abs_of_pos (show (0 : ℝ) < C.c by exact_mod_cast hc)]
    rcases hC.gram_off hij with h | h <;> simp [h]

/-- A valid certificate gives an equiangular tight frame of `N` vectors in `ℝ^m`. -/
theorem existsETF (h : C.check = true) {m : ℕ} (hm0 : m ≠ 0) (hc : 0 < C.c)
    (hm : (C.N : ℤ) * C.normSq = C.c * m) : ExistsETF ℝ m C.N :=
  (isETFProj h hc hm).exists_isETF hm0

end ETFCertificate

end ProjectionConstants
