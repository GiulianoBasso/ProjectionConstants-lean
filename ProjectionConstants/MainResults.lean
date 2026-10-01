/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.Mono
import ProjectionConstants.Values
import ProjectionConstants.Bounds.KLLEquality
import ProjectionConstants.FourSix.Main
import ProjectionConstants.Euclidean.Values
import ProjectionConstants.Stabilization.Main
import ProjectionConstants.Complementary.Main
import ProjectionConstants.Fourier.DiscAlgebra

/-!
# Main results

This file restates the main theorems of the library in elementary terms, so that the statements
can be checked against the literature without unfolding the definitions of the library. Every
theorem here is a thin wrapper around the theorem of the same name (up to the namespace
`ProjectionConstants.MainResults`) proved elsewhere in the library.

Every statement depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`
(see `scripts/CheckAxioms.lean`). The certificates for the explicit equiangular tight frames and
for the sums of squares in the proof of `λ_ℝ(4, 6) = 5/3` are checked by the kernel
(`decide +kernel`, no `native_decide`).

## Notation

| literature                | Lean                                   |
|---------------------------|----------------------------------------|
| `λ(Y, X)`                 | `relProjConst Y`                       |
| `λ(Y)`                    | `absProjConst 𝕜 Y`                     |
| `λ_𝕜(m)`                  | `maxProjConst 𝕜 m`                     |
| `λ_𝕜(m, N)`               | `maxRelProjConst 𝕜 m N`                |
| `μ_𝕜(m, N)`               | `quasiRelConst 𝕜 (Fin N) m`            |
| `μ_𝕜(m)`                  | `quasiMaxConst 𝕜 m`                    |
| `δ_{m,N}`                 | `delta m N`                            |
| `ETF(m, N)` exists        | `ExistsETF 𝕜 m N`                      |
| `Π(n, d)` ([JFA])         | `maxRelProjConst ℝ n d`                |
| `Π_n` ([JFA], [AMOP])     | `maxProjConst ℝ n`                     |
| `ℓ₁^d`                    | `PiLp 1 (fun _ : Fin d ↦ ℝ)`           |
| `ℓ₂ⁿ(𝕜)`                  | `EuclideanSpace 𝕜 (Fin n)`             |
| `ℓ∞^N`                    | `Fin N → 𝕜`                            |
| regular `2N`-gon plane    | `regularPolygon N`                     |
| `C(𝕋)`, `𝕋 = ℝ/Tℤ`        | `C(AddCircle T, ℂ)`                    |
| `𝒯ₙ`                      | `trigPoly T n`                         |
| `Sₙ`                      | `fourierPartialSum T n`                |
| `Lₙ`                      | `lebesgueConst T n`                    |
| `C_N(𝕋)`                  | `spectralSubspace T N`                 |
| `A(𝕋)`                    | `discAlgebra T`                        |

## Main statements

Foundations and the results of [DL]:

* `maxProjConst_eq_iSup_maxRelProjConst`: `λ_𝕜(m) = sup_N λ_𝕜(m, N)`.
* `absProjConst_le_sqrt`: the bound `λ(Y) ≤ √m` of Kadec and Snobar [KS].
* `maxRelProjConst_eq_sSup_parseval`: the formula of Chalmers and Lewicki [CL], in the form of
  [DL, Theorem 1.1].
* `maxRelProjConst_le_delta`, `existsETF_tfae`: the bound of König, Lewis and Lin [KLL] and its
  equality case [DL, Theorem 1.2].
* `quasiRelConst_real_le`, `quasiRelConst_complex_le`: the bounds of [DL, Theorem 2.1], after
  Bukh and Cox [BC].
* `maxProjConst_eq_quasiMaxConst`: `λ_𝕜(m) = μ_𝕜(m)` [DL, Theorem 2.2].
* `maxProjConst_real_le_delta`, `maxProjConst_real_eq_delta`, `maxProjConst_complex_le_delta`,
  `maxProjConst_complex_eq_delta`: upper bounds for `λ_𝕜(m)`, attained in the presence of maximal
  equiangular tight frames [DL, Theorem 2.3].
* `maxProjConst_real_values`: `λ_ℝ(m)` for `m = 2, 3, 7, 23` [DL, Theorem 2.4].
* `maxProjConst_complex_eq_of_sic`, `maxProjConst_complex_values`: `λ_ℂ(m)` in the presence of a
  SIC, and for `m = 1, 2, 3` [DL, Theorem 2.5].
* `maxProjConst_complex_eq_of_zaunerConjecture`: Zauner's conjecture implies
  [DL, Conjecture 2.1].

Sign matrices, the results of [JFA] and [AMOP]:

* `maxProjConst_real_eq_sSup`: the formula of Chalmers and Lewicki with sign matrices
  [JFA, Theorem 2.1].
* `isGreatest_signMatrixValues_two`: `Π₂ = 4/3` ([JFA], with the corrected proof of [JFA-E]);
  this gives a second proof of Grünbaum's conjecture `λ_ℝ(2) = 4/3`, first proved in [CL]
  (`GrunbaumConjecture.maxProjConst_real_two`).
* `maxRelProjConst_four_six`, `maxRelProjConst_five_six`: `Π(4, 6) = Π(5, 6) = 5/3`
  [JFA, §4.4], [JFA-E].
* `exists_almost_minimal_orthogonal_projection`: almost minimal orthogonal projections
  [AMOP, Theorem 1.2].
* `strictMono_maxProjConst_real`, `maxProjConst_real_add_le_succ`: `λ_ℝ(n)` is strictly
  increasing (a folklore result), here with an explicit gap.

Stabilization, the results of [KMMP]:

* `maxRelProjConst_eq_maxProjConst`: `λ_ℝ(r, n) = λ_ℝ(r)` for `n ≥ 2^r C(r+1, 2)`
  [KMMP, Theorem 1.3].
* `exists_weightedAbsSum_eq_maxProjConst`: the supremum defining `λ_ℝ(r)` is attained.

Sidelnikov–Welch bounds and complementary dimensions, the results of [DL26]:

* `recursive_welch_real`, `recursive_welch_complex`: the recursive Sidelnikov–Welch inequality
  [DL26, Theorem 2.1].
* `weighted_welch_real`, `weighted_welch_complex`: the weighted Sidelnikov–Welch bound
  [DL26, Corollary 2.1].
* `weightedAbsSum_gram_le_real`, `weightedAbsSum_gram_le_complex`: a frame bound
  [DL26, Lemma 3.1].
* `maxRelProjConst_compl_real`, `maxRelProjConst_compl_complex`, `maxRelProjConst_hyperplane`,
  `maxRelProjConst_compl_values`: complementary dimensions [DL26, Theorem 3.1].

The results of Grünbaum [G] on polyhedral spaces:

* `absProjConst_congr`, `absProjConst_eq_relProjConst`: `λ` is an isometric invariant, and
  `λ(Y) = λ(Y, ℓ∞^N)` for subspaces `Y ⊆ ℓ∞^N` [G, §1].
* `absProjConst_le_mul_norm_mul_norm`, `absProjConst_le_mul_of_le_of_le`: the Lipschitz estimate
  for the Banach–Mazur distance [G, §3, Lemma].
* `absProjConst_range_circulant`: idempotent circulant matrices are minimal projections.
* `absProjConst_l1`, `absProjConst_l1_odd_eq_even`: `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`
  [G, Theorem 3], and `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)`.
* `absProjConst_regularPolygon`, `absProjConst_regularPolygon_of_even`,
  `absProjConst_regularPolygon_of_odd`, `absProjConst_regularPolygon_two_pow`,
  `absProjConst_regularPolygon_values`: the planes whose unit ball is a regular polygon
  [G, Theorem 1 and §3].
* `absProjConst_regularPolygon_three_eq_maxProjConst`, `absProjConst_le_four_thirds`: the regular
  hexagon attains `λ_ℝ(2) = 4/3`; in particular `λ(Y) ≤ 4/3 < 3/2` for every real plane `Y`, which
  sharpens [G, Theorem 5].

Euclidean spaces:

* `absProjConst_euclideanSpace_eq`: `λ(ℓ₂ⁿ)` as a spherical mean [G], [R], [DGMMM, §1].
* `absProjConst_euclideanSpace_real`, `absProjConst_euclideanSpace_complex`,
  `absProjConst_euclideanSpace_values`: the formulas of Grünbaum [G] and Rutovitz [R].
* `absProjConst_euclideanSpace_real_eq_grunbaum`: the same formula in the form of
  [G, Theorem 4] (Grünbaum proved the upper bound, Rutovitz equality).
* `absProjConst_euclideanSpace_real_odd`: `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹) = (2m + 1) C(2m, m) / 4ᵐ`
  [G, §5, Remark].

Invariant subspaces, the results of Rudin [Ru] and their classical applications on the circle:

* `exists_isProjectionOnto_isEquivariant`: **Rudin's averaging theorem** [Ru, Theorem 1], with
  the uniform bound [Ru, (4)] and the estimate `‖Q‖ ≤ M² ‖P‖`.
* `relProjConst_eq_norm`: **Rudin's principle**: a unique equivariant projection onto a
  finite-dimensional invariant subspace is minimal.
* `relProjConst_trigPoly`: the theorem of Lozinskiĭ and Kharshiladze (see [DGMMM, §1]):
  `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖ = Lₙ`.
* `relProjConst_trigPoly_values`, `relProjConst_trigPoly_bounds`,
  `tendsto_relProjConst_trigPoly_atTop`: `λ(𝒯₀) = 1`, `λ(𝒯₁) = 1/3 + 2√3/π`, and
  `(4/π²) log (n + 1) ≤ λ(𝒯ₙ, C(𝕋)) ≤ 1 + log (2n + 1)`.
* `exists_not_bddAbove_of_isProjectionOnto`: **Kharshiladze–Lozinskiĭ**: no sequence of
  projections onto `𝒯ₙ` converges strongly to the identity of `C(𝕋)`.
* `exists_not_bddAbove_fourierPartialSum_apply_zero`: **du Bois-Reymond**: the Fourier series of
  some continuous function diverges at `0`.
* `exists_isProjectionOnto_spectralSubspace_iff`,
  `exists_isProjectionOnto_spectralSubspace_of_periodic`: [Ru, Theorem 2 and §4] for `C(𝕋)`,
  reduced to Fourier multipliers, and its "if" part.
* `not_exists_isProjectionOnto_discAlgebra`: the disc algebra is not complemented in `C(𝕋)`
  [Ru, §4].

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [CL] B. L. Chalmers, G. Lewicki, *A proof of the Grünbaum conjecture*.
* [KLL] H. König, D. R. Lewis, P.-K. Lin, *Finite dimensional projection constants*,
  Studia Math. 75 (1983).
* [BC] B. Bukh, C. Cox, *Nearly orthogonal vectors and small antipodal spherical codes*,
  arXiv:1803.02949.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866; [JFA-E] G. Basso, *Erratum to "Computation of maximal projection
  constants"*, arXiv:2402.06672.
* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.
* [DL26] B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection constants*,
  arXiv:2609.29422.
* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.
* [R] D. Rutovitz, *Some parameters associated with finite-dimensional Banach spaces*,
  J. London Math. Soc. 40 (1965).
* [DGMMM] A. Defant, D. Galicer, M. Mansilla, M. Mastyło, S. Muro, *Projection constants for
  spaces of multivariate polynomials*, arXiv:2208.06467.
* [KS] M. I. Kadec, M. G. Snobar, *Some functionals over a compact Minkowski space*,
  Math. Notes 10 (1971).
* [Ru] W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962),
  429–432.
-/

open Matrix
open WithLp (ofLp)

namespace ProjectionConstants.MainResults

section General

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### Foundations -/

/-- `λ_𝕜(m) = sup_N λ_𝕜(m, N)`: every `m`-dimensional space embeds almost isometrically into
some `ℓ∞^N`. -/
theorem maxProjConst_eq_iSup_maxRelProjConst (m : ℕ) :
    maxProjConst 𝕜 m = ⨆ N, maxRelProjConst 𝕜 m N :=
  ProjectionConstants.maxProjConst_eq_iSup_maxRelProjConst m

/-- **Kadec–Snobar.** `λ(Y) ≤ √m` for every `m`-dimensional normed space `Y`. -/
theorem absProjConst_le_sqrt (Y : Type) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] {m : ℕ} (hY : Module.finrank 𝕜 Y = m) : absProjConst 𝕜 Y ≤ √m :=
  ProjectionConstants.absProjConst_le_sqrt Y hY

/-! ### The formula of Chalmers and Lewicki and the bound of König, Lewis and Lin -/

/-- **The formula of Chalmers and Lewicki** ([DL, Theorem 1.1]). `λ_𝕜(m, N)` is the supremum of
`∑ᵢⱼ tᵢ tⱼ |(Uᴴ U)ᵢⱼ|` over `t ∈ ℝ^N` with `t ≥ 0` and `‖t‖₂ = 1` and over `U ∈ 𝕜^{m×N}` with
`U Uᴴ = I_m`. -/
theorem maxRelProjConst_eq_sSup_parseval (m N : ℕ) :
    maxRelProjConst 𝕜 m N = sSup {x | ∃ (t : Fin N → ℝ) (U : Matrix (Fin m) (Fin N) 𝕜),
      (∀ i, 0 ≤ t i) ∧ ∑ i, t i ^ 2 = 1 ∧ U * Uᴴ = 1 ∧
        x = ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖} :=
  ProjectionConstants.maxRelProjConst_eq_sSup_parseval m N

/-- **The bound of König, Lewis and Lin** ([DL, Theorem 1.2]). `λ_𝕜(m, N) ≤ δ_{m,N}` for
`m ≥ 1`. -/
theorem maxRelProjConst_le_delta {m N : ℕ} (hm : 1 ≤ m) :
    maxRelProjConst 𝕜 m N ≤ delta m N :=
  ProjectionConstants.maxRelProjConst_le_delta (by omega)

/-- **The equality case of the bound of König, Lewis and Lin** ([DL, Theorem 1.2]). For
`1 ≤ m ≤ N`, the following are equivalent: (i) there is an equiangular tight frame of `N` vectors
in `𝕜^m`; (ii) `μ_𝕜(m, N) = δ_{m,N}`; (iii) `λ_𝕜(m, N) = δ_{m,N}`. -/
theorem existsETF_tfae {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    List.TFAE [ExistsETF 𝕜 m N, quasiRelConst 𝕜 (Fin N) m = delta m N,
      maxRelProjConst 𝕜 m N = delta m N] :=
  ProjectionConstants.existsETF_tfae hm hmN

/-! ### Quasimaximal projection constants -/

/-- **Quasimaximal and maximal projection constants agree** ([DL, Theorem 2.2]).
`λ_𝕜(m) = μ_𝕜(m)`. -/
theorem maxProjConst_eq_quasiMaxConst (m : ℕ) : maxProjConst 𝕜 m = quasiMaxConst 𝕜 m :=
  ProjectionConstants.maxProjConst_eq_quasiMaxConst m

end General

/-- **The bound of Bukh and Cox, real case** ([DL, Theorem 2.1]).
`μ_ℝ(m, N) ≤ 2/(m+1) · (1 + (m-1)/2 · √(m+2))`. -/
theorem quasiRelConst_real_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    quasiRelConst ℝ (Fin N) m ≤ 2 / (m + 1) * (1 + (m - 1) / 2 * √(m + 2)) := by
  have h := quasiRelConst_real_le_delta hm N
  rwa [delta_eq_bukhCoxReal hm] at h

/-- **The bound of Bukh and Cox, complex case** ([DL, Theorem 2.1]).
`μ_ℂ(m, N) ≤ 1/m · (1 + (m-1) √(m+1))`. -/
theorem quasiRelConst_complex_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    quasiRelConst ℂ (Fin N) m ≤ 1 / m * (1 + (m - 1) * √(m + 1)) := by
  have h := quasiRelConst_complex_le_delta (𝕜 := ℂ) hm N
  rwa [delta_eq_bukhCoxComplex hm] at h

/-- **An upper bound for `λ_ℝ(m)`** ([DL, Theorem 2.3]). `λ_ℝ(m) ≤ δ_{m, m(m+1)/2}`. -/
theorem maxProjConst_real_le_delta {m : ℕ} (hm : 1 ≤ m) :
    maxProjConst ℝ m ≤ delta m (m * (m + 1) / 2) :=
  ProjectionConstants.maxProjConst_real_le_delta hm

/-- **The equality case for real maximal ETFs** ([DL, Theorem 2.3]). If there is a maximal
equiangular tight frame in `ℝ^m`, that is, an `ETF(m, m(m+1)/2)`, then
`λ_ℝ(m) = δ_{m, m(m+1)/2}`. -/
theorem maxProjConst_real_eq_delta {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℝ m (m * (m + 1) / 2)) :
    maxProjConst ℝ m = delta m (m * (m + 1) / 2) :=
  ProjectionConstants.maxProjConst_real_eq_delta hm h

/-- **An upper bound for `λ_ℂ(m)`** ([DL, Theorem 2.3]). `λ_ℂ(m) ≤ δ_{m, m²}`. -/
theorem maxProjConst_complex_le_delta {m : ℕ} (hm : 1 ≤ m) :
    maxProjConst ℂ m ≤ delta m (m ^ 2) :=
  ProjectionConstants.maxProjConst_complex_le_delta hm

/-- **The equality case for complex maximal ETFs** ([DL, Theorem 2.3]). If there is a maximal
equiangular tight frame in `ℂ^m` (a SIC), that is, an `ETF(m, m²)`, then `λ_ℂ(m) = δ_{m, m²}`. -/
theorem maxProjConst_complex_eq_delta {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℂ m (m ^ 2)) :
    maxProjConst ℂ m = delta m (m ^ 2) :=
  ProjectionConstants.maxProjConst_complex_eq_delta hm h

/-! ### Explicit values -/

/-- **Explicit values of `λ_ℝ(m)`** ([DL, Theorem 2.4]). `λ_ℝ(2) = 4/3` (Grünbaum's conjecture),
`λ_ℝ(3) = (1 + √5)/2`, `λ_ℝ(7) = 5/2` and `λ_ℝ(23) = 14/3`. -/
theorem maxProjConst_real_values :
    maxProjConst ℝ 2 = 4 / 3 ∧ maxProjConst ℝ 3 = (1 + √5) / 2 ∧
      maxProjConst ℝ 7 = 5 / 2 ∧ maxProjConst ℝ 23 = 14 / 3 :=
  ⟨maxProjConst_real_two, maxProjConst_real_three, maxProjConst_real_seven,
    maxProjConst_real_twentyThree⟩

/-- **`λ_ℂ(m)` in the presence of a SIC** ([DL, Theorem 2.5]).
`λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m` whenever there is a SIC in `ℂ^m`, that is, an `ETF(m, m²)`
(these are known for `m ∈ {1, …, 17, 19, 24, 28, 35, 48}`, among others). -/
theorem maxProjConst_complex_eq_of_sic {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℂ m (m ^ 2)) :
    maxProjConst ℂ m = (1 + (m - 1) * √(m + 1)) / m :=
  ProjectionConstants.maxProjConst_complex_eq_of_sic hm h

/-- **Explicit values of `λ_ℂ(m)`** ([DL, Theorem 2.5]) for `m = 1, 2, 3`, where the SICs are
constructed explicitly. -/
theorem maxProjConst_complex_values :
    maxProjConst ℂ 1 = 1 ∧ maxProjConst ℂ 2 = (1 + √3) / 2 ∧ maxProjConst ℂ 3 = 5 / 3 :=
  ⟨maxProjConst_complex_one, maxProjConst_complex_two, maxProjConst_complex_three⟩

/-- **Zauner's conjecture implies the conjecture of Deręgowska and Lewandowska**
([DL, Conjecture 2.1]): if there is a SIC in `ℂ^m` for every `m ≥ 1`, then
`λ_ℂ(m) = (1 + (m - 1)√(m + 1))/m` for every `m ≥ 1`. -/
theorem maxProjConst_complex_eq_of_zaunerConjecture (h : ZaunerConjecture) {m : ℕ}
    (hm : 1 ≤ m) : maxProjConst ℂ m = (1 + (m - 1) * √(m + 1)) / m :=
  deregowskaLewandowskaConjecture_of_zaunerConjecture h m hm

/-! ### Sign matrices -/

/-- **The formula of Chalmers and Lewicki with sign matrices** ([JFA, Theorem 2.1]).
`λ_ℝ(n) = sup {kyFanSum n (√D S √D) : S ∈ 𝒮_d, D ∈ 𝒟_d, d ∈ ℕ}`, where `kyFanSum n A` is the
sum of the `n` largest eigenvalues of `A`, `𝒮_d` is the set of symmetric `d × d` sign matrices
with ones on the diagonal and `𝒟_d` is the set of diagonal matrices of weights. -/
theorem maxProjConst_real_eq_sSup {n : ℕ} (hn : 1 ≤ n) :
    maxProjConst ℝ n = sSup (signMatrixValues n) :=
  ProjectionConstants.maxProjConst_real_eq_sSup hn

/-- **`Π₂ = 4/3`** ([JFA] with the corrected proof of its erratum [JFA-E]): over all `d`, all sign
matrices `S` and all weights `w`, the maximum of `kyFanSum 2 (√D S √D)`, the sum of the two
largest eigenvalues, is `4/3`. Together with `maxProjConst_real_eq_sSup`, this gives a second
proof of Grünbaum's conjecture `λ_ℝ(2) = 4/3` (`GrunbaumConjecture.maxProjConst_real_two`),
independent of the proof of [DL]. -/
theorem isGreatest_signMatrixValues_two : IsGreatest (signMatrixValues 2) (4 / 3) :=
  ProjectionConstants.isGreatest_signMatrixValues_two

/-- **`Π(4, 6) = 5/3`** ([JFA, §4.4], with the corrected proof of its erratum [JFA-E]): the
maximal relative projection constant of four-dimensional subspaces of `ℓ∞⁶` is `5/3`. -/
theorem maxRelProjConst_four_six : maxRelProjConst ℝ 4 6 = 5 / 3 :=
  ProjectionConstants.maxRelProjConst_four_six

/-- `Π(5, 6) = 5/3`, a by-product of the proof of `Π(4, 6) = 5/3`. -/
theorem maxRelProjConst_five_six : maxRelProjConst ℝ 5 6 = 5 / 3 :=
  ProjectionConstants.maxRelProjConst_five_six

/-- **Almost minimal orthogonal projections** ([AMOP, Theorem 1.2]). For `n ≥ 1` and `ε > 0`
there are `d` and an `n`-dimensional subspace `E ⊆ ℓ₁^d` whose orthogonal projection `P` (the
projection onto `E` that is self-adjoint for the standard inner product) satisfies
`λ_ℝ(n) - ε ≤ ‖P‖ ≤ λ(E, ℓ₁^d) + ε`. -/
theorem exists_almost_minimal_orthogonal_projection {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (E : Submodule ℝ (PiLp 1 fun _ : Fin d ↦ ℝ))
      (P : (PiLp 1 fun _ : Fin d ↦ ℝ) →L[ℝ] PiLp 1 fun _ : Fin d ↦ ℝ),
      Module.finrank ℝ E = n ∧ IsProjectionOnto E P ∧
      (∀ x y, ofLp (P x) ⬝ᵥ ofLp y = ofLp x ⬝ᵥ ofLp (P y)) ∧
      maxProjConst ℝ n - ε ≤ ‖P‖ ∧ ‖P‖ ≤ relProjConst E + ε :=
  ProjectionConstants.exists_almost_minimal_orthogonal_projection n hn ε hε

/-- **Strict monotonicity** (folklore). The maximal projection constants `λ_ℝ(n)`, `n ≥ 1`,
are strictly increasing. -/
theorem strictMono_maxProjConst_real : StrictMono fun n : ℕ ↦ maxProjConst ℝ (n + 1) :=
  ProjectionConstants.strictMono_maxProjConst_real

/-- **Quantitative strict monotonicity**, an explicit form of the folklore result.
`λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)` for
`k ≥ 2`. -/
theorem maxProjConst_real_add_le_succ {k : ℕ} (hk : 2 ≤ k) :
    maxProjConst ℝ k + 1 / (51200 * (k : ℝ) ^ 3) ≤ maxProjConst ℝ (k + 1) :=
  ProjectionConstants.maxProjConst_real_add_le_succ hk

/-! ### Stabilization -/

/-- **Stabilization** ([KMMP, Theorem 1.3], answering a question of Basso). The maximal relative
projection constants stabilize: `λ_ℝ(r, n) = λ_ℝ(r)` for all `n ≥ 2^r C(r+1, 2)`. In the notation
of [JFA], `Π(r, n) = Π_r` for these `n`. -/
theorem maxRelProjConst_eq_maxProjConst {r n : ℕ} (hn : 2 ^ r * (r + 1).choose 2 ≤ n) :
    maxRelProjConst ℝ r n = maxProjConst ℝ r :=
  ProjectionConstants.maxRelProjConst_eq_maxProjConst hn

/-- **The supremum defining `λ_ℝ(r)` is attained** ([KMMP]). Some unit weight `t` and orthogonal
projection `P` of rank `r` on `ℝ^N`, `N = 2^r C(r+1, 2)`, satisfy `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = λ_ℝ(r)`. -/
theorem exists_weightedAbsSum_eq_maxProjConst {r : ℕ} (hr : 1 ≤ r) :
    ∃ (t : Fin (2 ^ r * (r + 1).choose 2) → ℝ)
      (P : Matrix (Fin (2 ^ r * (r + 1).choose 2)) (Fin (2 ^ r * (r + 1).choose 2)) ℝ),
      IsUnitWeight t ∧ P ∈ orthProjs ℝ (Fin (2 ^ r * (r + 1).choose 2)) r ∧
        weightedAbsSum t P = maxProjConst ℝ r :=
  ProjectionConstants.exists_weightedAbsSum_eq_maxProjConst hr

/-! ### The recursive Sidelnikov–Welch inequality and complementary dimensions -/

/-- **The recursive Sidelnikov–Welch inequality, real case** ([DL26, Theorem 2.1]). For unit
vectors `x₁, …, x_N ∈ ℝ^m`, real weights `wᵢ` and `t ≥ 1`,
`∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t} ≥ (2t-1)/(m+2t-2) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t-2}`. -/
theorem recursive_welch_real {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (x : ι → Fin m → ℝ) (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    (2 * t - 1) / (m + 2 * t - 2) * ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t - 2) ≤
      ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t) :=
  recursive_welch_real' hm x hx w ht

open ComplexConjugate in
/-- **The recursive Sidelnikov–Welch inequality, complex case** ([DL26, Theorem 2.1]). For unit
vectors `x₁, …, x_N ∈ ℂ^m`, real weights `wᵢ` and `t ≥ 1`,
`∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t} ≥ t/(m+t-1) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t-2}`. -/
theorem recursive_welch_complex {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    (x : ι → Fin m → ℂ) (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) (w : ι → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    t / (m + t - 1) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t - 2) ≤
      ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t) :=
  recursive_welch_complex' hm x hx w ht

/-- **The weighted Sidelnikov–Welch bound, real case** ([DL26, Corollary 2.1]). For unit vectors
`x₁, …, x_N ∈ ℝ^m` and real weights `wᵢ`,
`1·3⋯(2t-1) (∑ᵢ wᵢ)² ≤ m(m+2)⋯(m+2t-2) ∑ᵢⱼ wᵢ wⱼ ⟨xᵢ, xⱼ⟩^{2t}`. -/
theorem weighted_welch_real {ι : Type} [Fintype ι] {m : ℕ} (x : ι → Fin m → ℝ)
    (hx : ∀ i, ∑ a, x i a ^ 2 = 1) (w : ι → ℝ) (t : ℕ) :
    (∏ s ∈ Finset.range t, (2 * s + 1 : ℝ)) * (∑ i, w i) ^ 2 ≤
      (∏ s ∈ Finset.range t, (m + 2 * s : ℝ)) *
        ∑ i, ∑ j, w i * w j * (∑ a, x i a * x j a) ^ (2 * t) :=
  ProjectionConstants.weighted_welch_real x hx w t

open ComplexConjugate in
/-- **The weighted Sidelnikov–Welch bound, complex case** ([DL26, Corollary 2.1]). For unit
vectors `x₁, …, x_N ∈ ℂ^m` and real weights `wᵢ`,
`(∑ᵢ wᵢ)² ≤ C(m+t-1, t) ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^{2t}`. -/
theorem weighted_welch_complex {ι : Type} [Fintype ι] {m : ℕ} (x : ι → Fin m → ℂ)
    (hx : ∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) (w : ι → ℝ) (t : ℕ) :
    (∑ i, w i) ^ 2 ≤
      ((m + t - 1).choose t : ℝ) * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ (2 * t) :=
  ProjectionConstants.weighted_welch_complex x hx w t

/-- **A frame bound, real case** ([DL26, Lemma 3.1]). If `U ∈ ℝ^{m×N}` satisfies `U Uᵀ = I` and
`t ∈ ℝ^N` satisfies `t ≥ 0` and `‖t‖₂ ≤ 1`, then
`∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ (2 + (m-1)√(m+2)) / (2(m+1)²) · (m + 2 + S²)`, where `uᵢ` are the columns
of `U` and `S = ∑ᵢ tᵢ ‖uᵢ‖`. -/
theorem weightedAbsSum_gram_le_real {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    {U : Matrix (Fin m) ι ℝ} (hU : U * Uᴴ = 1) {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖ ≤ (2 + (m - 1) * √(m + 2)) / (2 * (m + 1) ^ 2) *
      (m + 2 + (∑ i, t i * √(∑ k, ‖U k i‖ ^ 2)) ^ 2) :=
  ProjectionConstants.weightedAbsSum_gram_le_real hm hU ht0 ht1

/-- **A frame bound, complex case** ([DL26, Lemma 3.1]). If `U ∈ ℂ^{m×N}` satisfies `U U* = I`
and `t ∈ ℝ^N` satisfies `t ≥ 0` and `‖t‖₂ ≤ 1`, then
`∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ √(m+1)/2 + (1 + (m/2 - 1)√(m+1)) / m² · S²`, where `uᵢ` are the columns
of `U` and `S = ∑ᵢ tᵢ ‖uᵢ‖`. -/
theorem weightedAbsSum_gram_le_complex {ι : Type} [Fintype ι] {m : ℕ} (hm : 1 ≤ m)
    {U : Matrix (Fin m) ι ℂ} (hU : U * Uᴴ = 1) {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖ ≤ √(m + 1) / 2 +
      (1 + (m / 2 - 1) * √(m + 1)) / m ^ 2 * (∑ i, t i * √(∑ k, ‖U k i‖ ^ 2)) ^ 2 :=
  ProjectionConstants.weightedAbsSum_gram_le_complex hm hU ht0 ht1

/-- **Complementary dimensions, real case** ([DL26, Theorem 3.1]). If `ℝ^m`, `m ≥ 2`, admits a
maximal equiangular tight frame (of `M = m(m+1)/2` vectors), then for every `k ≥ 1`,
`λ_ℝ(kM - m, kM) = μ_ℝ(kM - m, kM) = λ_ℝ(m) - 2m/(kM) + 1`. -/
theorem maxRelProjConst_compl_real {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hM : M = m * (m + 1) / 2) (h : ExistsETF ℝ m M) :
    maxRelProjConst ℝ (k * M - m) (k * M) = maxProjConst ℝ m - 2 * m / (k * M) + 1 ∧
      quasiRelConst ℝ (Fin (k * M)) (k * M - m) = maxProjConst ℝ m - 2 * m / (k * M) + 1 :=
  ⟨ProjectionConstants.maxRelProjConst_compl_real hm hk hM h, quasiRelConst_compl_real hm hk hM h⟩

/-- **Complementary dimensions, complex case** ([DL26, Theorem 3.1]). If `ℂ^m`, `m ≥ 2`, admits a
maximal equiangular tight frame (a SIC, of `M = m²` vectors), then for every `k ≥ 1`,
`λ_ℂ(kM - m, kM) = μ_ℂ(kM - m, kM) = λ_ℂ(m) - 2m/(kM) + 1`. -/
theorem maxRelProjConst_compl_complex {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (hM : M = m ^ 2)
    (h : ExistsETF ℂ m M) :
    maxRelProjConst ℂ (k * M - m) (k * M) = maxProjConst ℂ m - 2 * m / (k * M) + 1 ∧
      quasiRelConst ℂ (Fin (k * M)) (k * M - m) = maxProjConst ℂ m - 2 * m / (k * M) + 1 :=
  ⟨ProjectionConstants.maxRelProjConst_compl_complex hm hk hM h,
    quasiRelConst_compl_complex hm hk hM h⟩

/-- **Hyperplanes**, the case `m = 1` of the formula of [DL26, Theorem 3.1]:
`λ_𝕜(N - 1, N) = 2 - 2/N` for `N ≥ 1`. For `N = 6` this is `Π(5, 6) = 5/3`. -/
theorem maxRelProjConst_hyperplane {𝕜 : Type} [RCLike 𝕜] {N : ℕ} (hN : 1 ≤ N) :
    maxRelProjConst 𝕜 (N - 1) N = 2 - 2 / N :=
  ProjectionConstants.maxRelProjConst_hyperplane hN

/-- **Complementary dimensions, explicit values** ([DL26]), from the maximal ETFs in `ℝ²`, `ℝ³`,
`ℝ⁷`, `ℝ²³`, `ℂ²` and `ℂ³`: for every `k ≥ 1`,
`λ_ℝ(3k-2, 3k) = 7/3 - 4/(3k)`, `λ_ℝ(6k-3, 6k) = (3+√5)/2 - 1/k`,
`λ_ℝ(28k-7, 28k) = 7/2 - 1/(2k)`, `λ_ℝ(276k-23, 276k) = 17/3 - 1/(6k)`,
`λ_ℂ(4k-2, 4k) = (3+√3)/2 - 1/k` and `λ_ℂ(9k-3, 9k) = 8/3 - 2/(3k)`. -/
theorem maxRelProjConst_compl_values {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℝ (3 * k - 2) (3 * k) = 7 / 3 - 4 / (3 * k) ∧
      maxRelProjConst ℝ (6 * k - 3) (6 * k) = (3 + √5) / 2 - 1 / k ∧
      maxRelProjConst ℝ (28 * k - 7) (28 * k) = 7 / 2 - 1 / (2 * k) ∧
      maxRelProjConst ℝ (276 * k - 23) (276 * k) = 17 / 3 - 1 / (6 * k) ∧
      maxRelProjConst ℂ (4 * k - 2) (4 * k) = (3 + √3) / 2 - 1 / k ∧
      maxRelProjConst ℂ (9 * k - 3) (9 * k) = 8 / 3 - 2 / (3 * k) :=
  ⟨maxRelProjConst_compl_real_two hk, maxRelProjConst_compl_real_three hk,
    maxRelProjConst_compl_real_seven hk, maxRelProjConst_compl_real_twentyThree hk,
    maxRelProjConst_compl_complex_two hk, maxRelProjConst_compl_complex_three hk⟩

/-! ### Invariance, the extension property of `ℓ∞`, and the Banach–Mazur distance -/

/-- Isometric normed spaces have the same projection constant. -/
theorem absProjConst_congr {𝕜 : Type} [RCLike 𝕜] {X Y : Type} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (e : X ≃ₗᵢ[𝕜] Y) :
    absProjConst 𝕜 X = absProjConst 𝕜 Y :=
  e.absProjConst_eq

/-- `λ(Y) = λ(Y, ℓ∞^N)` for every subspace `Y ⊆ ℓ∞^N`, because `ℓ∞^N` has the extension property
[G, §1]. -/
theorem absProjConst_eq_relProjConst {𝕜 : Type} [RCLike 𝕜] {N : ℕ}
    (Y : Submodule 𝕜 (Fin N → 𝕜)) : absProjConst 𝕜 Y = relProjConst Y :=
  absProjConst_eq_relProjConst_pi Y

/-- **Grünbaum's lemma** [G, §3]: `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)` for every isomorphism `T : X → Y` of
finite-dimensional normed spaces; that is, `λ` is Lipschitz with respect to the logarithm of the
Banach–Mazur distance. -/
theorem absProjConst_le_mul_norm_mul_norm {𝕜 : Type} [RCLike 𝕜] {X Y : Type}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 X] (T : X ≃L[𝕜] Y) :
    absProjConst 𝕜 Y ≤ ‖(T : X →L[𝕜] Y)‖ * ‖(T.symm : Y →L[𝕜] X)‖ * absProjConst 𝕜 X :=
  T.absProjConst_le

/-- **Grünbaum's lemma** [G, §3] in its original form: for two norms `‖·‖₁ ≤ ‖·‖₂ ≤ μ ‖·‖₁` on the
same space, `λ(X₂) ≤ μ λ(X₁)` and `λ(X₁) ≤ μ λ(X₂)`. (Here `T` identifies `X₁` with `X₂`.) -/
theorem absProjConst_le_mul_of_le_of_le {𝕜 : Type} [RCLike 𝕜] {X Y : Type}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 X] (T : X ≃ₗ[𝕜] Y) {μ : ℝ} (h₁ : ∀ x, ‖x‖ ≤ ‖T x‖)
    (h₂ : ∀ x, ‖T x‖ ≤ μ * ‖x‖) :
    absProjConst 𝕜 Y ≤ μ * absProjConst 𝕜 X ∧ absProjConst 𝕜 X ≤ μ * absProjConst 𝕜 Y :=
  ProjectionConstants.absProjConst_le_mul_of_le_of_le T h₁ h₂

/-! ### Minimal circulant projections: `ℓ₁ⁿ` and the regular polygons -/

/-- **Idempotent circulant matrices are minimal projections**: if `G` is a finite abelian group
and `P = (v (g - h))_{g,h}` is idempotent, then `λ(range P) = λ(range P, ℓ∞(G)) = ∑_g |v g|`, the
norm of `P` on `ℓ∞(G)`. -/
theorem absProjConst_range_circulant {𝕜 : Type} [RCLike 𝕜] {G : Type} [AddCommGroup G]
    [Fintype G] [DecidableEq G] {v : G → 𝕜} (hv : circulant v * circulant v = circulant v) :
    absProjConst 𝕜 (LinearMap.range (circulant v).toLin') = ∑ g, ‖v g‖ ∧
      relProjConst (LinearMap.range (circulant v).toLin') = ∑ g, ‖v g‖ :=
  ⟨ProjectionConstants.absProjConst_range_circulant hv, relProjConst_range_circulant hv⟩

/-- **Grünbaum's formula** [G, Theorem 3]: `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`. -/
theorem absProjConst_l1 (n : ℕ) :
    absProjConst ℝ (PiLp 1 fun _ : Fin n ↦ ℝ) = n * (n - 1).choose ((n - 1) / 2) / 2 ^ (n - 1) :=
  ProjectionConstants.absProjConst_l1 n

/-- [G, §4, Remark]: `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)`. -/
theorem absProjConst_l1_odd_eq_even (m : ℕ) :
    absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 1) ↦ ℝ) =
      absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 2) ↦ ℝ) :=
  ProjectionConstants.absProjConst_l1_odd_eq_even m

open Real in
/-- **The regular polygons.** For `N ≥ 2` the plane `regularPolygon N ⊆ ℓ∞(ℤ/2N)` spanned by
`(cos(kπ/N))_k` and `(sin(kπ/N))_k`, whose unit ball is a regular `2N`-gon, has projection constant
`(2/N) ∑_{k<N} |cos(kπ/N)|`. -/
theorem absProjConst_regularPolygon (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    Module.finrank ℝ (regularPolygon N) = 2 ∧
      absProjConst ℝ (regularPolygon N) = 2 / N * ∑ k ∈ Finset.range N, |cos (k * π / N)| :=
  ⟨finrank_regularPolygon N hN, ProjectionConstants.absProjConst_regularPolygon N hN⟩

open Real in
/-- The regular `2N`-gon, `N ≥ 2` even: `λ = (2/N) cot(π/2N)`. -/
theorem absProjConst_regularPolygon_of_even (N : ℕ) [NeZero N] (hN : 2 ≤ N) (he : Even N) :
    absProjConst ℝ (regularPolygon N) = 2 / N * cot (π / (2 * N)) :=
  ProjectionConstants.absProjConst_regularPolygon_of_even N hN he

open Real in
/-- The regular `2N`-gon, `N ≥ 3` odd: `λ = 2 / (N sin(π/2N))`. -/
theorem absProjConst_regularPolygon_of_odd (N : ℕ) [NeZero N] (hN : 2 ≤ N) (ho : Odd N) :
    absProjConst ℝ (regularPolygon N) = 2 / (N * sin (π / (2 * N))) :=
  ProjectionConstants.absProjConst_regularPolygon_of_odd N hN ho

open Real in
/-- **Grünbaum's theorem** [G, Theorem 1]: for `n ≥ 2`, the plane whose unit ball is a regular
`2ⁿ`-gon has projection constant `2²⁻ⁿ cot(2⁻ⁿπ)`. -/
theorem absProjConst_regularPolygon_two_pow (n : ℕ) (hn : 2 ≤ n) :
    absProjConst ℝ (regularPolygon (2 ^ (n - 1))) = 4 / 2 ^ n * cot (π / 2 ^ n) :=
  ProjectionConstants.absProjConst_regularPolygon_two_pow n hn

/-- The square, the regular hexagon [G, §3, Remark (ii)] and the regular octagon have projection
constants `1`, `4/3` and `(1 + √2)/2`. -/
theorem absProjConst_regularPolygon_values :
    absProjConst ℝ (regularPolygon 2) = 1 ∧ absProjConst ℝ (regularPolygon 3) = 4 / 3 ∧
      absProjConst ℝ (regularPolygon 4) = (1 + √2) / 2 :=
  ⟨absProjConst_regularPolygon_two, absProjConst_regularPolygon_three,
    absProjConst_regularPolygon_four⟩

/-- **The regular hexagon is extremal** (Grünbaum's conjecture in the form of [G, §6], proved in
[CL]): `λ(regularPolygon 3) = λ_ℝ(2)`, so the supremum defining `λ_ℝ(2) = 4/3` is attained. -/
theorem absProjConst_regularPolygon_three_eq_maxProjConst :
    absProjConst ℝ (regularPolygon 3) = maxProjConst ℝ 2 :=
  ProjectionConstants.absProjConst_regularPolygon_three_eq_maxProjConst

/-- `λ(Y) ≤ 4/3` for every two-dimensional real normed space `Y`. This sharpens the bound
`λ(Y) < 3/2` of [G, Theorem 5]. -/
theorem absProjConst_le_four_thirds (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hY : Module.finrank ℝ Y = 2) : absProjConst ℝ Y ≤ 4 / 3 := by
  have : FiniteDimensional ℝ Y := Module.finite_of_finrank_pos (by omega)
  exact (absProjConst_le_maxProjConst Y hY).trans_eq maxProjConst_real_two

/-! ### The projection constants of Euclidean spaces -/

open MeasureTheory Metric in
open scoped InnerProductSpace in
/-- **The projection constant of `ℓ₂ⁿ` as a spherical mean** ([G], [R]; see [DGMMM, §1]):
`λ(ℓ₂ⁿ(𝕜)) = n ∫ |⟪u, e⟫| dν(u) / ν(S)` for every finite measure `ν ≠ 0` on the unit sphere `S`
that is invariant under the linear isometries, and every unit vector `e`. -/
theorem absProjConst_euclideanSpace_eq {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {n : ℕ} (hn : 1 ≤ n) {ν : Measure (sphere (0 : EuclideanSpace 𝕜 (Fin n)) 1)}
    [IsFiniteMeasure ν] (hν : Euclidean.IsInvariant 𝕜 ν) (hν0 : ν ≠ 0)
    {e : EuclideanSpace 𝕜 (Fin n)} (he : ‖e‖ = 1) :
    absProjConst 𝕜 (EuclideanSpace 𝕜 (Fin n)) =
      n * (∫ u, ‖⟪(u : EuclideanSpace 𝕜 (Fin n)), e⟫_𝕜‖ ∂ν) / ν.real Set.univ :=
  haveI : NeZero n := ⟨by omega⟩
  ProjectionConstants.absProjConst_euclideanSpace_eq hν hν0 he

open Real in
/-- **Grünbaum's formula** [G]: `λ(ℓ₂ⁿ(ℝ)) = 2 Γ(n/2 + 1) / (√π Γ((n+1)/2))`. -/
theorem absProjConst_euclideanSpace_real {n : ℕ} (hn : 1 ≤ n) :
    absProjConst ℝ (EuclideanSpace ℝ (Fin n)) =
      2 * Gamma (n / 2 + 1) / (√π * Gamma ((n + 1) / 2)) :=
  haveI : NeZero n := ⟨by omega⟩
  ProjectionConstants.absProjConst_euclideanSpace_real n

open Real Nat in
/-- **Rutovitz's formula** [R]: `λ(ℓ₂ⁿ(ℂ)) = (√π / 2) n! / Γ(n + 1/2)`. -/
theorem absProjConst_euclideanSpace_complex {n : ℕ} (hn : 1 ≤ n) :
    absProjConst ℂ (EuclideanSpace ℂ (Fin n)) = √π / 2 * n ! / Gamma (n + 1 / 2) :=
  haveI : NeZero n := ⟨by omega⟩
  ProjectionConstants.absProjConst_euclideanSpace_complex n

open Real in
/-- `λ(ℓ₂²(ℝ)) = 4/π`, `λ(ℓ₂³(ℝ)) = 3/2` and `λ(ℓ₂²(ℂ)) = 4/3`. -/
theorem absProjConst_euclideanSpace_values :
    absProjConst ℝ (EuclideanSpace ℝ (Fin 2)) = 4 / π ∧
      absProjConst ℝ (EuclideanSpace ℝ (Fin 3)) = 3 / 2 ∧
      absProjConst ℂ (EuclideanSpace ℂ (Fin 2)) = 4 / 3 :=
  ⟨absProjConst_euclideanSpace_real_two, absProjConst_euclideanSpace_real_three,
    absProjConst_euclideanSpace_complex_two⟩

open Real in
/-- **Grünbaum's form** of the formula [G, Theorem 4]: `λ(ℓ₂ⁿ(ℝ)) = n Γ(n/2) / (√π Γ((n+1)/2))`.
Grünbaum proved the upper bound and conjectured equality; equality is due to Rutovitz [R]. -/
theorem absProjConst_euclideanSpace_real_eq_grunbaum {n : ℕ} (hn : 1 ≤ n) :
    absProjConst ℝ (EuclideanSpace ℝ (Fin n)) = n * Gamma (n / 2) / (√π * Gamma ((n + 1) / 2)) :=
  haveI : NeZero n := ⟨by omega⟩
  ProjectionConstants.absProjConst_euclideanSpace_real_eq_grunbaum n

/-- [G, §5, Remark] with [R]: `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹) = (2m + 1) C(2m, m) / 4ᵐ`. -/
theorem absProjConst_euclideanSpace_real_odd (m : ℕ) :
    absProjConst ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) =
        (2 * m + 1) * (2 * m).choose m / 4 ^ m ∧
      absProjConst ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) =
        absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 1) ↦ ℝ) :=
  ⟨ProjectionConstants.absProjConst_euclideanSpace_real_odd m,
    absProjConst_euclideanSpace_real_odd_eq_l1 m⟩

/-! ### Invariant subspaces: Rudin's averaging theorem and the circle -/

/-- **Rudin's averaging theorem** [Ru, Theorem 1]. Let a compact group `G` act continuously on a
normed space `X` by bounded operators `ρ g`, and let `Y ⊆ X` be a complete `G`-invariant subspace.
Then `sup_g ‖ρ g‖ < ∞` [Ru, (4)]; and if `‖ρ g‖ ≤ M` for all `g`, then for every projection `P` of
`X` onto `Y` there is a projection `Q` onto `Y` that commutes with every `ρ g`, with
`‖Q‖ ≤ M² ‖P‖`. -/
theorem exists_isProjectionOnto_isEquivariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    {ρ : G → X →L[𝕜] X} (hρ : IsRepresentation ρ) (hc : Continuous fun p : G × X ↦ ρ p.1 p.2)
    {Y : Submodule 𝕜 X} [CompleteSpace Y] (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) :
    (∃ M, ∀ g, ‖ρ g‖ ≤ M) ∧ ∀ M, (∀ g, ‖ρ g‖ ≤ M) → ∀ P, IsProjectionOnto Y P →
      ∃ Q, IsProjectionOnto Y Q ∧ IsEquivariant ρ Q ∧ ‖Q‖ ≤ M ^ 2 * ‖P‖ := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have := isProbabilityMeasure_haarMeasure_top (G := G)
  exact ⟨hρ.exists_forall_norm_le fun x ↦ hc.comp (continuous_id.prodMk continuous_const),
    fun M hM P hP ↦ hρ.exists_isProjectionOnto_isEquivariant (MeasureTheory.Measure.haarMeasure ⊤)
      hc hM hY hP⟩

/-- **Rudin's principle** [Ru]: let a compact group act continuously on `X` by contractions, let
`Y ⊆ X` be a finite-dimensional invariant subspace, and let `P₀` be the only projection onto `Y`
that commutes with the action. Then `P₀` is a minimal projection: `λ(Y, X) = ‖P₀‖`. -/
theorem relProjConst_eq_norm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] {ρ : G → X →L[𝕜] X} (hρ : IsRepresentation ρ)
    (hc : Continuous fun p : G × X ↦ ρ p.1 p.2) (hiso : ∀ g x, ‖ρ g x‖ ≤ ‖x‖)
    {Y : Submodule 𝕜 X} [FiniteDimensional 𝕜 Y] (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    {P₀ : X →L[𝕜] X} (hP₀ : IsProjectionOnto Y P₀)
    (huniq : ∀ Q, IsProjectionOnto Y Q → IsEquivariant ρ Q → Q = P₀) :
    relProjConst Y = ‖P₀‖ := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  exact hρ.relProjConst_eq_norm hc hiso hY hP₀ huniq

open Real in
/-- **Lozinskiĭ–Kharshiladze** (see [DGMMM, §1]), via Rudin's averaging [Ru, §4]: on the circle
`𝕋 = ℝ/Tℤ`, the Fourier partial sum operator `Sₙ` is a minimal projection of `C(𝕋)` onto the space
`𝒯ₙ` of trigonometric polynomials of degree at most `n`, and
`λ(𝒯ₙ, C(𝕋)) = Lₙ = T⁻¹ ∫_0^T |∑_{|k| ≤ n} e^{2πikx/T}| dx`. -/
theorem relProjConst_trigPoly (T : ℝ) [Fact (0 < T)] (n : ℕ) :
    relProjConst (trigPoly T n) = ‖fourierPartialSum T n‖ ∧
      relProjConst (trigPoly T n) = T⁻¹ * ∫ x in (0 : ℝ)..T,
        ‖∑ k ∈ Finset.Icc (-(n : ℤ)) n, Complex.exp (2 * π * Complex.I * k * x / T)‖ := by
  refine ⟨by rw [ProjectionConstants.relProjConst_trigPoly, norm_fourierPartialSum], ?_⟩
  rw [ProjectionConstants.relProjConst_trigPoly, lebesgueConst_eq_intervalIntegral n 0, zero_add]
  refine congrArg (T⁻¹ * ·) (intervalIntegral.integral_congr fun x _ ↦ ?_)
  simp only [dirichletKernel_apply, fourier_coe_apply]

open Real in
/-- `λ(𝒯₀, C(𝕋)) = 1` and `λ(𝒯₁, C(𝕋)) = 1/3 + 2√3/π ≈ 1.436`. -/
theorem relProjConst_trigPoly_values (T : ℝ) [Fact (0 < T)] :
    relProjConst (trigPoly T 0) = 1 ∧ relProjConst (trigPoly T 1) = 1 / 3 + 2 * √3 / π :=
  ⟨relProjConst_trigPoly_zero, relProjConst_trigPoly_one⟩

open Real in
/-- The projection constants of the trigonometric polynomials grow logarithmically:
`(4/π²) log (n + 1) ≤ λ(𝒯ₙ, C(𝕋)) ≤ 1 + log (2n + 1)`. -/
theorem relProjConst_trigPoly_bounds (T : ℝ) [Fact (0 < T)] (n : ℕ) :
    4 / π ^ 2 * log (n + 1) ≤ relProjConst (trigPoly T n) ∧
      relProjConst (trigPoly T n) ≤ 1 + log (2 * n + 1) := by
  rw [ProjectionConstants.relProjConst_trigPoly]
  exact ⟨four_div_pi_sq_mul_log_le_lebesgueConst n, lebesgueConst_le_one_add_log n⟩

open Filter in
/-- `λ(𝒯ₙ, C(𝕋)) → ∞`. -/
theorem tendsto_relProjConst_trigPoly_atTop (T : ℝ) [Fact (0 < T)] :
    Tendsto (fun n ↦ relProjConst (trigPoly T n)) atTop atTop :=
  ProjectionConstants.tendsto_relProjConst_trigPoly_atTop

open Filter Topology in
/-- **Kharshiladze–Lozinskiĭ**: for every sequence of projections `Pₙ` of `C(𝕋)` onto `𝒯ₙ` there
is a continuous function `f` such that `‖Pₙ f‖` is unbounded; in particular `Pₙ f ↛ f`. -/
theorem exists_not_bddAbove_of_isProjectionOnto (T : ℝ) [Fact (0 < T)]
    {P : ℕ → C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hP : ∀ n, IsProjectionOnto (trigPoly T n) (P n)) :
    ∃ f : C(AddCircle T, ℂ), ¬BddAbove (Set.range fun n ↦ ‖P n f‖) ∧
      ¬Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by
  obtain ⟨f, hf⟩ := ProjectionConstants.exists_not_bddAbove_of_isProjectionOnto hP
  exact ⟨f, hf, fun h ↦ hf h.norm.bddAbove_range⟩

/-- **du Bois-Reymond**: there is a continuous function `f` on the circle whose Fourier series
diverges at `0`: the partial sums `∑_{|k| ≤ n} f̂(k)` are unbounded. -/
theorem exists_not_bddAbove_fourierPartialSum_apply_zero (T : ℝ) [Fact (0 < T)] :
    ∃ f : C(AddCircle T, ℂ),
      ¬BddAbove (Set.range fun n : ℕ ↦ ‖∑ k ∈ Finset.Icc (-(n : ℤ)) n, fourierCoeff f k‖) := by
  obtain ⟨f, hf⟩ := ProjectionConstants.exists_not_bddAbove_fourierPartialSum_apply_zero (T := T)
  refine ⟨f, ?_⟩
  convert hf using 5 with n
  rw [fourierPartialSum_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ContinuousMap.smul_apply, fourier_eval_zero, smul_eq_mul, mul_one]

/-- **Rudin's theorem on the invariant subspaces of `C(𝕋)`** [Ru, Theorem 2 and §4], reduced to
Fourier multipliers: for `N ⊆ ℤ`, the space `C_N(𝕋) = {f ∈ C(𝕋) : f̂(k) = 0 for k ∉ N}` is
complemented in `C(𝕋)` if and only if there is a bounded operator `Q` on `C(𝕋)` with `Q eₖ = eₖ`
for `k ∈ N` and `Q eₖ = 0` for `k ∉ N`. -/
theorem exists_isProjectionOnto_spectralSubspace_iff (T : ℝ) [Fact (0 < T)] (N : Set ℤ) :
    (∃ P, IsProjectionOnto (spectralSubspace T N) P) ↔
      ∃ Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ),
        ∀ k, Q (fourier k) = N.indicator fourier k :=
  ProjectionConstants.exists_isProjectionOnto_spectralSubspace_iff N

/-- [Ru, Theorem 2 and §4], "if" part: if `N ⊆ ℤ` differs from a set of period `p` in finitely
many places, then `C_N(𝕋)` is complemented in `C(𝕋)`. -/
theorem exists_isProjectionOnto_spectralSubspace_of_periodic (T : ℝ) [Fact (0 < T)]
    {N N' : Set ℤ} {p : ℕ} (hp : 0 < p) (hN : ∀ k : ℤ, k + p ∈ N ↔ k ∈ N)
    (hfin : (symmDiff N N').Finite) : ∃ P, IsProjectionOnto (spectralSubspace T N') P :=
  ProjectionConstants.exists_isProjectionOnto_spectralSubspace_of_periodic hp hN hfin

/-- **The disc algebra is not complemented in `C(𝕋)`** [Ru, §4] (for `H¹ ⊆ L¹`, this is Newman's
theorem): there is no bounded projection of `C(𝕋)` onto
`A(𝕋) = {f ∈ C(𝕋) : f̂(k) = 0 for k < 0}`. -/
theorem not_exists_isProjectionOnto_discAlgebra (T : ℝ) [Fact (0 < T)] :
    ¬∃ P : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ),
      (∀ (f : C(AddCircle T, ℂ)) (k : ℤ), k < 0 → fourierCoeff (P f) k = 0) ∧
        ∀ f : C(AddCircle T, ℂ), (∀ k : ℤ, k < 0 → fourierCoeff f k = 0) → P f = f := by
  rintro ⟨P, hP₁, hP₂⟩
  exact ProjectionConstants.not_exists_isProjectionOnto_discAlgebra
    ⟨P, fun f k hk ↦ hP₁ f k (not_le.1 hk), fun f hf ↦ hP₂ f fun k hk ↦ hf k (not_le.2 hk)⟩

end ProjectionConstants.MainResults
