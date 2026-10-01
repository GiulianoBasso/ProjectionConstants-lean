/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.TwoGraph

/-!
# Sign matrices without cliques and cocliques of order four

In Step 4 of the proof of [JFA-E, Theorem A], the classification of `K₄`-free two-graphs by
Frankl and Füredi is used. This file replaces it by a direct argument (`exists_embedding_A6`).

Suppose that the two-graph `[S]` has no clique of order `4` and no coclique of order `4`, i.e. no
four indices on which `S` is switching equivalent to the all-ones matrix (Steps 1 and 3 of
[JFA-E]). Then every `4`-set contains exactly two coherent triples. Switch at a vertex `a` of a
coherent triple `{a, b, c}`, so that row `a` becomes `1`, and let `x ~ y` if the switched entry is
`-1`. This graph has no triangle (`K₄`), no independent `3`-set (coclique), no induced `2K₂`
(`K₄`) and no induced `C₄` (coclique). Hence, on the vertices other than `a`, it is an induced
subgraph of the `5`-cycle `1–4–3–2–5–1` of `A₆`: `b ↦ 1`, `c ↦ 4`, and every further vertex goes
to `5`, `3` or `2` according as it is adjacent to `b`, to `c`, or to neither. So `S` is, up to
switching and relabelling, a principal submatrix of `A₆`.

## Main statements

* `exists_embedding_A6`: a sign matrix without cliques and cocliques of order `4` that has a
  coherent triple is, up to switching and relabelling, a principal submatrix of `A₆`.
* `A6_apply_comm`, `A6_apply_self`: `A₆` is symmetric with ones on the diagonal.

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A₆` is symmetric. -/
lemma A6_apply_comm (k l : Fin 6) : A6 l k = A6 k l := by
  fin_cases k <;> fin_cases l <;> simp [A6]

/-- The diagonal entries of `A₆` are `1`. -/
lemma A6_apply_self (k : Fin 6) : A6 k k = 1 := by
  fin_cases k <;> simp [A6]

private lemma A6_zero_apply (k : Fin 6) : A6 0 k = 1 := by
  fin_cases k <;> simp [A6]

section

variable {S T : Matrix ι ι ℝ} {ε : ι → ℝ}

omit [DecidableEq ι] [Fintype ι] in
/-- A `4`-set on which `S` is switching equivalent to `J` contradicts `hcoc`. -/
private lemma false_of_switch_eq_one
    (hcoc : ∀ (c : Fin 4 → ι), Function.Injective c → ∀ ε : ι → ℝ,
      (∀ a b, S (c a) (c b) = ε (c a) * ε (c b)) → False)
    (hST : ∀ x y, S x y = ε x * ε y * T x y) (c : Fin 4 → ι) (hc : Function.Injective c)
    (δ : Fin 4 → ℝ) (hδ : ∀ m n, δ m * δ n * T (c m) (c n) = 1)
    (hTd : ∀ m, T (c m) (c m) = 1) : False := by
  apply hcoc c hc (fun x ↦ ε x * Function.extend c δ 1 x)
  intro m n
  simp only [hc.extend_apply]
  have hm : δ m * δ m = 1 := by have := hδ m m; rwa [hTd, mul_one] at this
  have hn : δ n * δ n = 1 := by have := hδ n n; rwa [hTd, mul_one] at this
  have hT : T (c m) (c n) = δ m * δ n := by
    have := hδ m n
    linear_combination (δ m * δ n) * this - T (c m) (c n) * δ n * δ n * hm - T (c m) (c n) * hn
  rw [hST, hT]
  ring

omit [DecidableEq ι] [Fintype ι] in
/-- Four points all of whose triples are coherent (for `T`) contradict `K₄`-freeness. -/
private lemma false_of_coherent_four (hK4 : K4Free S) (hST : ∀ x y, S x y = ε x * ε y * T x y)
    (hε : ∀ x, ε x * ε x = 1) {p q r s : ι} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1 : T p q * T p r * T q r = -1) (h2 : T p q * T p s * T q s = -1)
    (h3 : T p r * T p s * T r s = -1) (h4 : T q r * T q s * T r s = -1) : False := by
  have hcoh : ∀ x y z, T x y * T x z * T y z = -1 → IsCoherentTriple S x y z := by
    intro x y z h
    unfold IsCoherentTriple
    rw [hST, hST, hST]
    have e : ε x * ε y * T x y * (ε x * ε z * T x z) * (ε y * ε z * T y z) =
        (ε x * ε x) * (ε y * ε y) * (ε z * ε z) * (T x y * T x z * T y z) := by ring
    rw [e, hε, hε, hε, h]
    norm_num
  exact hK4 p q r s hpq hpr hps hqr hqs hrs
    ⟨hcoh _ _ _ h1, hcoh _ _ _ h2, hcoh _ _ _ h3, hcoh _ _ _ h4⟩

end

omit [DecidableEq ι] [Fintype ι] in
private lemma injective_vec_four {p q r s : ι} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    Function.Injective (![p, q, r, s] : Fin 4 → ι) := by
  intro m n h
  fin_cases m <;> fin_cases n <;> simp at h ⊢ <;> simp_all

omit [DecidableEq ι] [Fintype ι] in
/-- **Step 4 of the proof of [JFA-E, Theorem A], without the classification of Frankl and
Füredi.** If `[S]` has no clique and no coclique of order `4`, and a coherent triple, then `S` is,
up to switching and relabelling, a principal submatrix of `A₆`. -/
theorem exists_embedding_A6 {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) (hK4 : K4Free S)
    (hcoc : ∀ (c : Fin 4 → ι), Function.Injective c → ∀ ε : ι → ℝ,
      (∀ a b, S (c a) (c b) = ε (c a) * ε (c b)) → False)
    (hcoh : HasCoherentTriple S) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∃ φ : ι → Fin 6, Function.Injective φ ∧
      ∀ i j, S i j = ε i * ε j * A6 (φ i) (φ j) := by
  classical
  obtain ⟨a, b, c, habc⟩ := hcoh
  unfold IsCoherentTriple at habc
  have hsq := hS.mul_self_eq
  have hab : a ≠ b := by
    rintro rfl; rw [hS.diag, one_mul, hsq] at habc; norm_num at habc
  have hac : a ≠ c := by
    rintro rfl; rw [hS.diag, mul_one, hS.symm, hsq] at habc; norm_num at habc
  have hbc : b ≠ c := by
    rintro rfl; rw [mul_assoc, hS.diag, mul_one, hsq] at habc; norm_num at habc
  -- switch at `a`
  set ε : ι → ℝ := fun x ↦ S a x with hεdef
  have hε : ∀ x, ε x = 1 ∨ ε x = -1 := fun x ↦ hS.pm a x
  have hεε : ∀ x, ε x * ε x = 1 := fun x ↦ hsq a x
  set T : Matrix ι ι ℝ := fun x y ↦ ε x * ε y * S x y with hTdef
  have hTpm : ∀ x y, T x y = 1 ∨ T x y = -1 := by
    intro x y
    simp only [hTdef]
    rcases hε x with h1 | h1 <;> rcases hε y with h2 | h2 <;> rcases hS.pm x y with h3 | h3 <;>
      simp [h1, h2, h3]
  have hTs : ∀ x y, T y x = T x y := by
    intro x y; simp only [hTdef, hS.symm y x]; ring
  have hTd : ∀ x, T x x = 1 := by
    intro x; simp only [hTdef, hS.diag, mul_one]; exact hεε x
  have hTa : ∀ y, T a y = 1 := by
    intro y; simp only [hTdef, hεdef, hS.diag, one_mul]; exact hsq a y
  have hTbc : T b c = -1 := by simp only [hTdef, hεdef]; linarith
  have hST : ∀ x y, S x y = ε x * ε y * T x y := by
    intro x y; simp only [hTdef]
    linear_combination (-(S x y)) * ε y * ε y * hεε x - S x y * hεε y
  -- the forbidden configurations of the graph `x ~ y ⟺ T x y = -1`
  have tri : ∀ x y z, x ≠ a → y ≠ a → z ≠ a → x ≠ y → x ≠ z → y ≠ z →
      T x y = -1 → T x z = -1 → T y z = -1 → False := by
    intro x y z hxa hya hza hxy hxz hyz h1 h2 h3
    refine false_of_coherent_four hK4 hST hεε (Ne.symm hxa) (Ne.symm hya) (Ne.symm hza) hxy hxz hyz
      ?_ ?_ ?_ ?_
    · rw [hTa, hTa, h1]; norm_num
    · rw [hTa, hTa, h2]; norm_num
    · rw [hTa, hTa, h3]; norm_num
    · rw [h1, h2, h3]; norm_num
  have hTa' : ∀ y, T y a = 1 := fun y ↦ by rw [hTs]; exact hTa y
  have ind : ∀ x y z, x ≠ a → y ≠ a → z ≠ a → x ≠ y → x ≠ z → y ≠ z →
      T x y = 1 → T x z = 1 → T y z = 1 → False := by
    intro x y z hxa hya hza hxy hxz hyz h1 h2 h3
    have h1' : T y x = 1 := by rw [hTs]; exact h1
    have h2' : T z x = 1 := by rw [hTs]; exact h2
    have h3' : T z y = 1 := by rw [hTs]; exact h3
    refine false_of_switch_eq_one hcoc hST _
      (injective_vec_four (Ne.symm hxa) (Ne.symm hya) (Ne.symm hza) hxy hxz hyz)
      (fun _ ↦ 1) (fun m n ↦ ?_) (fun m ↦ hTd _)
    fin_cases m <;> fin_cases n <;> simp [hTa, hTa', hTd, h1, h2, h3, h1', h2', h3']
  have twoK2 : ∀ x y z w, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
      T x y = -1 → T z w = -1 → T x z = 1 → T x w = 1 → T y z = 1 → T y w = 1 → False := by
    intro x y z w hxy hxz hxw hyz hyw hzw h1 h2 h3 h4 h5 h6
    refine false_of_coherent_four hK4 hST hεε hxy hxz hxw hyz hyw hzw ?_ ?_ ?_ ?_
    · rw [h1, h3, h5]; norm_num
    · rw [h1, h4, h6]; norm_num
    · rw [h3, h4, h2]; norm_num
    · rw [h5, h6, h2]; norm_num
  have fourC : ∀ x y z w, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
      T x y = -1 → T y z = -1 → T z w = -1 → T w x = -1 → T x z = 1 → T y w = 1 → False := by
    intro x y z w hxy hxz hxw hyz hyw hzw h1 h2 h3 h4 h5 h6
    have h1' : T y x = -1 := by rw [hTs]; exact h1
    have h2' : T z y = -1 := by rw [hTs]; exact h2
    have h3' : T w z = -1 := by rw [hTs]; exact h3
    have h4' : T x w = -1 := by rw [hTs]; exact h4
    have h5' : T z x = 1 := by rw [hTs]; exact h5
    have h6' : T w y = 1 := by rw [hTs]; exact h6
    refine false_of_switch_eq_one hcoc hST _ (injective_vec_four hxy hxz hxw hyz hyw hzw)
      ![1, -1, 1, -1] (fun m n ↦ ?_) (fun m ↦ hTd _)
    fin_cases m <;> fin_cases n <;> simp [hTd, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6']
  have h1ne : (1 : ℝ) ≠ -1 := by norm_num
  -- the embedding
  set φ : ι → Fin 6 := fun z ↦ if z = a then 0 else if z = b then 1 else if z = c then 4
    else if T z b = -1 then 5 else if T z c = -1 then 3 else 2 with hφdef
  -- the six kinds of vertices
  have kind : ∀ z, (z = a ∧ φ z = 0) ∨ (z = b ∧ φ z = 1) ∨ (z = c ∧ φ z = 4) ∨
      (z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ T z b = -1 ∧ T z c = 1 ∧ φ z = 5) ∨
      (z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ T z b = 1 ∧ T z c = -1 ∧ φ z = 3) ∨
      (z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ T z b = 1 ∧ T z c = 1 ∧ φ z = 2) := by
    intro z
    by_cases hza : z = a
    · left; exact ⟨hza, by simp [hφdef, hza]⟩
    by_cases hzb : z = b
    · right; left; exact ⟨hzb, by simp [hφdef, hzb, hab.symm]⟩
    by_cases hzc : z = c
    · right; right; left; exact ⟨hzc, by simp [hφdef, hzc, hac.symm, hbc.symm]⟩
    right; right; right
    rcases hTpm z b with hb1 | hb1
    · rcases hTpm z c with hc1 | hc1
      · right; right
        exact ⟨hza, hzb, hzc, hb1, hc1, by simp [hφdef, hza, hzb, hzc, hb1, hc1, h1ne]⟩
      · right; left
        exact ⟨hza, hzb, hzc, hb1, hc1, by simp [hφdef, hza, hzb, hzc, hb1, hc1, h1ne]⟩
    · left
      have hc1 : T z c = 1 := by
        rcases hTpm z c with h | h
        · exact h
        · exact (tri b c z hab.symm hac.symm hza hbc (Ne.symm hzb) (Ne.symm hzc) hTbc
            (by rw [hTs]; exact hb1) (by rw [hTs]; exact h)).elim
      exact ⟨hza, hzb, hzc, hb1, hc1, by simp [hφdef, hza, hzb, hzc, hb1]⟩
  -- two distinct vertices of the same kind outside `{a, b, c}` are impossible
  have same : ∀ x y, x ≠ y → x ≠ a → x ≠ b → x ≠ c → y ≠ a → y ≠ b → y ≠ c →
      T x b = T y b → T x c = T y c → False := by
    intro x y hxy hxa hxb hxc hya hyb hyc hb hc
    rcases hTpm x b with hxb1 | hxb1
    · rcases hTpm x c with hxc1 | hxc1
      · -- kind 2: both non-adjacent to `b` and `c`
        rcases hTpm x y with h | h
        · exact ind b x y hab.symm hxa hya (Ne.symm hxb) (Ne.symm hyb) hxy
            (by rw [hTs]; exact hxb1) (by rw [hTs, ← hb]; exact hxb1) h
        · exact twoK2 b c x y hbc (Ne.symm hxb) (Ne.symm hyb) (Ne.symm hxc) (Ne.symm hyc) hxy
            hTbc h (by rw [hTs]; exact hxb1) (by rw [hTs, ← hb]; exact hxb1)
            (by rw [hTs]; exact hxc1) (by rw [hTs, ← hc]; exact hxc1)
      · -- kind 3: both adjacent to `c` only
        rcases hTpm x y with h | h
        · exact ind b x y hab.symm hxa hya (Ne.symm hxb) (Ne.symm hyb) hxy
            (by rw [hTs]; exact hxb1) (by rw [hTs, ← hb]; exact hxb1) h
        · exact tri c x y hac.symm hxa hya (Ne.symm hxc) (Ne.symm hyc) hxy
            (by rw [hTs]; exact hxc1) (by rw [hTs, ← hc]; exact hxc1) h
    · -- kind 5: both adjacent to `b`, hence not to `c`
      have hxc1 : T x c = 1 := by
        rcases hTpm x c with h | h
        · exact h
        · exact (tri b c x hab.symm hac.symm hxa hbc (Ne.symm hxb) (Ne.symm hxc) hTbc
            (by rw [hTs]; exact hxb1) (by rw [hTs]; exact h)).elim
      rcases hTpm x y with h | h
      · exact ind c x y hac.symm hxa hya (Ne.symm hxc) (Ne.symm hyc) hxy
          (by rw [hTs]; exact hxc1) (by rw [hTs, ← hc]; exact hxc1) h
      · exact tri b x y hab.symm hxa hya (Ne.symm hxb) (Ne.symm hyb) hxy
          (by rw [hTs]; exact hxb1) (by rw [hTs, ← hb]; exact hxb1) h
  -- two vertices outside `{a, b, c}`
  have other : ∀ x y, x ≠ y → x ≠ a → x ≠ b → x ≠ c → y ≠ a → y ≠ b → y ≠ c →
      T x y = A6 (φ x) (φ y) := by
    intro x y hxy hxa hxb hxc hya hyb hyc
    have hsame := same x y hxy hxa hxb hxc hya hyb hyc
    have hyx : y ≠ x := Ne.symm hxy
    rcases kind x with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hxb1, hxc1, hx⟩ |
        ⟨-, -, -, hxb1, hxc1, hx⟩ | ⟨-, -, -, hxb1, hxc1, hx⟩
    · exact absurd h hxa
    · exact absurd h hxb
    · exact absurd h hxc
    · -- `x` of kind 5
      rcases kind y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩ |
          ⟨-, -, -, hyb1, hyc1, hy⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩
      · exact absurd h hya
      · exact absurd h hyb
      · exact absurd h hyc
      · exact (hsame (hxb1.trans hyb1.symm) (hxc1.trans hyc1.symm)).elim
      · -- (5, 3): no induced `C₄` `b - c - y - x - b`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · rw [h]; simp [A6]
        · have e1 : T c y = -1 := by rw [hTs]; exact hyc1
          have e2 : T y x = -1 := by rw [hTs]; exact h
          have e3 : T b y = 1 := by rw [hTs]; exact hyb1
          have e4 : T c x = 1 := by rw [hTs]; exact hxc1
          exact (fourC b c y x hbc (Ne.symm hyb) (Ne.symm hxb) (Ne.symm hyc) (Ne.symm hxc) hyx
            hTbc e1 e2 hxb1 e3 e4).elim
      · -- (5, 2): no independent triple `{c, x, y}`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · have e1 : T c x = 1 := by rw [hTs]; exact hxc1
          have e2 : T c y = 1 := by rw [hTs]; exact hyc1
          exact (ind c x y hac.symm hxa hya (Ne.symm hxc) (Ne.symm hyc) hxy e1 e2 h).elim
        · rw [h]; simp [A6]
    · -- `x` of kind 3
      rcases kind y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩ |
          ⟨-, -, -, hyb1, hyc1, hy⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩
      · exact absurd h hya
      · exact absurd h hyb
      · exact absurd h hyc
      · -- (3, 5): no induced `C₄` `b - c - x - y - b`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · rw [h]; simp [A6]
        · have e1 : T c x = -1 := by rw [hTs]; exact hxc1
          have e3 : T b x = 1 := by rw [hTs]; exact hxb1
          have e4 : T c y = 1 := by rw [hTs]; exact hyc1
          exact (fourC b c x y hbc (Ne.symm hxb) (Ne.symm hyb) (Ne.symm hxc) (Ne.symm hyc) hxy
            hTbc e1 h hyb1 e3 e4).elim
      · exact (hsame (hxb1.trans hyb1.symm) (hxc1.trans hyc1.symm)).elim
      · -- (3, 2): no independent triple `{b, x, y}`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · have e1 : T b x = 1 := by rw [hTs]; exact hxb1
          have e2 : T b y = 1 := by rw [hTs]; exact hyb1
          exact (ind b x y hab.symm hxa hya (Ne.symm hxb) (Ne.symm hyb) hxy e1 e2 h).elim
        · rw [h]; simp [A6]
    · -- `x` of kind 2
      rcases kind y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩ |
          ⟨-, -, -, hyb1, hyc1, hy⟩ | ⟨-, -, -, hyb1, hyc1, hy⟩
      · exact absurd h hya
      · exact absurd h hyb
      · exact absurd h hyc
      · -- (2, 5): no independent triple `{c, x, y}`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · have e1 : T c x = 1 := by rw [hTs]; exact hxc1
          have e2 : T c y = 1 := by rw [hTs]; exact hyc1
          exact (ind c x y hac.symm hxa hya (Ne.symm hxc) (Ne.symm hyc) hxy e1 e2 h).elim
        · rw [h]; simp [A6]
      · -- (2, 3): no independent triple `{b, x, y}`
        rw [hx, hy]
        rcases hTpm x y with h | h
        · have e1 : T b x = 1 := by rw [hTs]; exact hxb1
          have e2 : T b y = 1 := by rw [hTs]; exact hyb1
          exact (ind b x y hab.symm hxa hya (Ne.symm hxb) (Ne.symm hyb) hxy e1 e2 h).elim
        · rw [h]; simp [A6]
      · exact (hsame (hxb1.trans hyb1.symm) (hxc1.trans hyc1.symm)).elim
  have hφa : φ a = 0 := by simp [hφdef]
  have hφb : φ b = 1 := by simp [hφdef, hab.symm]
  have hφc : φ c = 4 := by simp [hφdef, hac.symm, hbc.symm]
  -- the embedding preserves the switched entries
  have key : ∀ x y, T x y = A6 (φ x) (φ y) := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy, hTd, A6_apply_self]
    by_cases hxa : x = a
    · rw [hxa, hTa, hφa, A6_zero_apply]
    by_cases hya : y = a
    · rw [hya, hTa', hφa, A6_apply_comm, A6_zero_apply]
    by_cases hxb : x = b
    · by_cases hyc : y = c
      · rw [hxb, hyc, hTbc, hφb, hφc]; simp [A6]
      have hyb : y ≠ b := fun h ↦ hxy (hxb.trans h.symm)
      rw [hxb, hTs, hφb]
      rcases kind y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hyb1, -, hy⟩ |
          ⟨-, -, -, hyb1, -, hy⟩ | ⟨-, -, -, hyb1, -, hy⟩
      · exact absurd h hya
      · exact absurd h hyb
      · exact absurd h hyc
      all_goals rw [hyb1, hy]; simp [A6]
    by_cases hxc : x = c
    · by_cases hyb : y = b
      · rw [hxc, hyb, hTs, hTbc, hφb, hφc]; simp [A6]
      have hyc : y ≠ c := fun h ↦ hxy (hxc.trans h.symm)
      rw [hxc, hTs, hφc]
      rcases kind y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, hyc1, hy⟩ |
          ⟨-, -, -, -, hyc1, hy⟩ | ⟨-, -, -, -, hyc1, hy⟩
      · exact absurd h hya
      · exact absurd h hyb
      · exact absurd h hyc
      all_goals rw [hyc1, hy]; simp [A6]
    by_cases hyb : y = b
    · rw [hyb, hφb]
      rcases kind x with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hxb1, -, hx⟩ |
          ⟨-, -, -, hxb1, -, hx⟩ | ⟨-, -, -, hxb1, -, hx⟩
      · exact absurd h hxa
      · exact absurd h hxb
      · exact absurd h hxc
      all_goals rw [hxb1, hx]; simp [A6]
    by_cases hyc : y = c
    · rw [hyc, hφc]
      rcases kind x with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, hxc1, hx⟩ |
          ⟨-, -, -, -, hxc1, hx⟩ | ⟨-, -, -, -, hxc1, hx⟩
      · exact absurd h hxa
      · exact absurd h hxb
      · exact absurd h hxc
      all_goals rw [hxc1, hx]; simp [A6]
    exact other x y hxy hxa hxb hxc hya hyb hyc
  -- injectivity
  have hinj : Function.Injective φ := by
    intro x y hφxy
    by_contra hxy
    rcases kind x with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ | ⟨hx, hx'⟩ | ⟨hxa, hxb, hxc, hxb1, hxc1, hx'⟩ |
        ⟨hxa, hxb, hxc, hxb1, hxc1, hx'⟩ | ⟨hxa, hxb, hxc, hxb1, hxc1, hx'⟩ <;>
      rcases kind y with ⟨hy, hy'⟩ | ⟨hy, hy'⟩ | ⟨hy, hy'⟩ | ⟨hya, hyb, hyc, hyb1, hyc1, hy'⟩ |
        ⟨hya, hyb, hyc, hyb1, hyc1, hy'⟩ | ⟨hya, hyb, hyc, hyb1, hyc1, hy'⟩ <;>
      rw [hx', hy'] at hφxy <;> simp at hφxy
    all_goals first
      | exact hxy (hx.trans hy.symm)
      | exact same x y hxy hxa hxb hxc hya hyb hyc (hxb1.trans hyb1.symm) (hxc1.trans hyc1.symm)
  refine ⟨ε, hε, φ, hinj, fun i j ↦ ?_⟩
  rw [hST, key]

end ProjectionConstants.GrunbaumConjecture
