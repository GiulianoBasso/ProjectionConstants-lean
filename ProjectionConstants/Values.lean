/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Bounds.Gerzon
import ProjectionConstants.ETF.Maximal.Certificates
import ProjectionConstants.ETF.Maximal.Seidel
import ProjectionConstants.Invariant.Polygon

/-!
# Exact values of maximal projection constants

By [DL, Theorem 2.3] (`maxProjConst_real_eq_delta`, `maxProjConst_complex_eq_delta` in
`ProjectionConstants.Bounds.Gerzon`), `λ_ℝ(m) = δ_{m, m(m+1)/2}` as soon as there is a maximal
real ETF in `ℝ^m`, and `λ_ℂ(m) = δ_{m, m²}` as soon as there is a SIC (a maximal ETF) in `ℂ^m`.
With the explicit maximal ETFs of `ProjectionConstants.ETF.Maximal.Certificates` and
`ProjectionConstants.ETF.Maximal.Seidel` this gives the values of [DL, Theorems 2.4 and 2.5].

SICs are known for `m ∈ {1, …, 17, 19, 24, 28, 35, 48}`, among others. We construct them for
`m = 1, 2, 3`, which gives `λ_ℂ(1) = 1`, `λ_ℂ(2) = (1 + √3)/2` and `λ_ℂ(3) = 5/3`
unconditionally. For the remaining dimensions the SICs are known from the literature (exact
solutions of large degree) and are not constructed here.

## Main definitions

* `ZaunerConjecture`: Zauner's conjecture, there is a SIC in `ℂ^m` for every `m ≥ 1`.
* `DeregowskaLewandowskaConjecture`: [DL, Conjecture 2.1], `λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m`
  for every `m ≥ 1`.

## Main statements

* `maxProjConst_real_two`, `maxProjConst_real_three`, `maxProjConst_real_seven`,
  `maxProjConst_real_twentyThree`: [DL, Theorem 2.4], `λ_ℝ(2) = 4/3` (Grünbaum's conjecture),
  `λ_ℝ(3) = (1 + √5)/2`, `λ_ℝ(7) = 5/2` and `λ_ℝ(23) = 14/3`; moreover `λ_ℝ(1) = 1`
  (`maxProjConst_real_one`). A second proof of `λ_ℝ(2) = 4/3` is
  `ProjectionConstants.GrunbaumConjecture.maxProjConst_real_two`.
* `absProjConst_regularPolygon_three_eq_maxProjConst`, `exists_absProjConst_eq_maxProjConst_two`:
  the value `λ_ℝ(2) = 4/3` is attained by the plane whose unit ball is a regular hexagon, as
  conjectured by Grünbaum [G, §6].
* `maxProjConst_complex_eq_of_sic`: [DL, Theorem 2.5], `λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m`
  whenever a SIC exists in `ℂ^m`.
* `maxProjConst_complex_one`, `maxProjConst_complex_two`, `maxProjConst_complex_three`:
  `λ_ℂ(1) = 1`, `λ_ℂ(2) = (1 + √3)/2` and `λ_ℂ(3) = 5/3`.
* `deregowskaLewandowskaConjecture_of_zaunerConjecture`: Zauner's conjecture implies
  [DL, Conjecture 2.1].

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.
-/

namespace ProjectionConstants

open MaximalETF

private lemma sqrt_eq_of_eq_sq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : √a = b := by
  rw [h, Real.sqrt_sq hb]

/-! ### The real case -/

/-- `λ_ℝ(1) = 1`. -/
theorem maxProjConst_real_one : maxProjConst ℝ 1 = 1 := by
  rw [maxProjConst_real_eq_delta le_rfl (existsETF_one ℝ), delta]
  norm_num

/-- **Grünbaum's conjecture** ([DL, Theorem 2.4]). `λ_ℝ(2) = 4/3`. -/
theorem maxProjConst_real_two : maxProjConst ℝ 2 = 4 / 3 := by
  rw [maxProjConst_real_eq_delta (by norm_num) existsETF_two, delta]
  norm_num

/-- **The regular hexagon is extremal** (Grünbaum's conjecture in the form of [G, §6]): the
maximal projection constant of planes, `λ_ℝ(2) = 4/3`, is attained by the plane whose unit ball is
a regular hexagon. -/
theorem absProjConst_regularPolygon_three_eq_maxProjConst :
    absProjConst ℝ (regularPolygon 3) = maxProjConst ℝ 2 := by
  rw [absProjConst_regularPolygon_three, maxProjConst_real_two]

/-- The supremum defining `λ_ℝ(2)` is attained (by the regular hexagon plane). -/
theorem exists_absProjConst_eq_maxProjConst_two :
    ∃ Y : FinDimNormedSpace ℝ 2, absProjConst ℝ Y.carrier = maxProjConst ℝ 2 :=
  ⟨⟨regularPolygon 3, finrank_regularPolygon 3 (by norm_num)⟩,
    absProjConst_regularPolygon_three_eq_maxProjConst⟩

/-- `λ_ℝ(3) = (1 + √5)/2` ([DL, Theorem 2.4]). -/
theorem maxProjConst_real_three : maxProjConst ℝ 3 = (1 + √5) / 2 := by
  rw [maxProjConst_real_eq_delta (by norm_num) existsETF_three_real, delta]
  norm_num
  ring

/-- `λ_ℝ(7) = 5/2` ([DL, Theorem 2.4]). -/
theorem maxProjConst_real_seven : maxProjConst ℝ 7 = 5 / 2 := by
  rw [maxProjConst_real_eq_delta (by norm_num) existsETF_seven, delta]
  norm_num
  rw [sqrt_eq_of_eq_sq (b := 9) (by norm_num) (by norm_num)]
  norm_num

/-- `λ_ℝ(23) = 14/3` ([DL, Theorem 2.4]). -/
theorem maxProjConst_real_twentyThree : maxProjConst ℝ 23 = 14 / 3 := by
  rw [maxProjConst_real_eq_delta (by norm_num) existsETF_twentyThree, delta]
  norm_num
  rw [sqrt_eq_of_eq_sq (b := 55) (by norm_num) (by norm_num)]
  norm_num

/-! ### The complex case -/

/-- **`λ_ℂ(m)` in the presence of a SIC** ([DL, Theorem 2.5]). If there is a SIC (a maximal ETF
of `m²` vectors) in `ℂ^m`, then `λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m`. SICs are known to exist for
`m ∈ {1, …, 17, 19, 24, 28, 35, 48}`, among others. -/
theorem maxProjConst_complex_eq_of_sic {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℂ m (m ^ 2)) :
    maxProjConst ℂ m = (1 + (m - 1) * √(m + 1)) / m := by
  rw [maxProjConst_complex_eq_delta hm h, delta_eq_bukhCoxComplex hm, bukhCoxComplex]
  ring

/-- `λ_ℂ(1) = 1` ([DL, Theorem 2.5] for `m = 1`). -/
theorem maxProjConst_complex_one : maxProjConst ℂ 1 = 1 := by
  rw [maxProjConst_complex_eq_of_sic le_rfl (existsETF_one ℂ)]
  norm_num

/-- `λ_ℂ(2) = (1 + √3)/2` ([DL, Theorem 2.5] for `m = 2`). -/
theorem maxProjConst_complex_two : maxProjConst ℂ 2 = (1 + √3) / 2 := by
  rw [maxProjConst_complex_eq_of_sic (by norm_num) existsETF_two_complex]
  norm_num

/-- `λ_ℂ(3) = 5/3` ([DL, Theorem 2.5] for `m = 3`). -/
theorem maxProjConst_complex_three : maxProjConst ℂ 3 = 5 / 3 := by
  rw [maxProjConst_complex_eq_of_sic (by norm_num) existsETF_three_complex]
  norm_num
  rw [sqrt_eq_of_eq_sq (b := 2) (by norm_num) (by norm_num)]
  norm_num

/-! ### The conjecture of Deręgowska and Lewandowska -/

/-- **Zauner's conjecture**: there is a SIC, an equiangular tight frame of `m²` vectors in `ℂ^m`,
for every `m ≥ 1`. -/
def ZaunerConjecture : Prop := ∀ m : ℕ, 1 ≤ m → ExistsETF ℂ m (m ^ 2)

/-- **The conjecture of Deręgowska and Lewandowska** ([DL, Conjecture 2.1]):
`λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m` for every `m ≥ 1`. -/
def DeregowskaLewandowskaConjecture : Prop :=
  ∀ m : ℕ, 1 ≤ m → maxProjConst ℂ m = (1 + (m - 1) * √(m + 1)) / m

/-- Zauner's conjecture implies the conjecture of Deręgowska and Lewandowska
([DL, Conjecture 2.1]). -/
theorem deregowskaLewandowskaConjecture_of_zaunerConjecture (h : ZaunerConjecture) :
    DeregowskaLewandowskaConjecture :=
  fun m hm ↦ maxProjConst_complex_eq_of_sic hm (h m hm)

end ProjectionConstants
