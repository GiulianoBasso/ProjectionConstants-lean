# ProjectionConstants

![build](https://github.com/GiulianoBasso/ProjectionConstants-lean/actions/workflows/build.yml/badge.svg)

A Lean 4 / Mathlib library on projection constants of finite-dimensional normed spaces. It
formalizes the main results on projection constants of

* **[DL]** B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454,


* **[JFA]** G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  with the corrected proofs of `Π₂ = 4/3` and `Π(4, 6) = 5/3` from its erratum **[JFA-E]**
  (arXiv:2402.06672);


* **[AMOP]** G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698: the main
  theorem (Theorem 1.2); the library also proves the folklore result that `λ_ℝ(n)` is strictly
  increasing, with the explicit gap `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)`;

* **[KMMP]** H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200: `λ_ℝ(r, n) = λ_ℝ(r)` for all `n ≥ 2^r C(r+1, 2)`;

* **[G]** B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465:
  all results. Theorem 1 (the planes whose unit ball is a regular `2ⁿ`-gon, generalized to all
  regular `2N`-gons, with the hexagon `λ = 4/3` of the remark in §3), Theorem 3
  (`λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹` and `λ(ℓ₁²ᵐ⁻¹) = λ(ℓ₁²ᵐ)`), the lemma of §3 (`λ` is
  Lipschitz for the Banach–Mazur distance), Theorems 2 and 4 on Euclidean spaces (with equality in
  Theorem 4, due to **[R]** D. Rutovitz, *Some parameters associated with finite-dimensional
  Banach spaces*, J. London Math. Soc. 40 (1965)) and the remark `λ(ℓ₂²ᵐ⁻¹(ℝ)) = λ(ℓ₁²ᵐ⁻¹)` of
  §5. Theorem 5 is superseded by the bound of Kadec and Snobar and by `λ_ℝ(2) = 4/3`, both in the
  library, and Grünbaum's conjecture of §6 (the hexagon is extremal) is proved. The Euclidean
  formulas `λ(ℓ₂ⁿ(ℝ)) = 2 Γ(n/2 + 1) / (√π Γ((n+1)/2))` and `λ(ℓ₂ⁿ(ℂ)) = (√π/2) n! / Γ(n + 1/2)`
  are proved via the spherical-mean formula `λ(ℓ₂ⁿ) = n ∫_S |⟪u, e⟫| dσ(u)` as presented in
  **[DGMMM]** A. Defant, D. Galicer, M. Mansilla, M. Mastyło, S. Muro, *Projection constants for
  spaces of multivariate polynomials*, arXiv:2208.06467;

* **[DL26]** B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection
  constants*, arXiv:2609.29422: the recursive Sidelnikov–Welch inequality, and
  `λ_𝕂(kM - m, kM) = λ_𝕂(m) - 2m/(kM) + 1` whenever `𝕂^m` admits a maximal equiangular tight
  frame of `M` vectors;

* **[Ru]** W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962),
  429–432: Theorem 1 (averaging over a compact group, with the uniform bound (4) and the estimate
  `‖Q‖ ≤ M² ‖P‖`), its finite version and Rudin's principle (a unique equivariant projection is
  minimal), and the case `C(𝕋)` of §4: Theorem 2 reduced to Fourier multipliers, its "if" part
  (periodic sets up to finitely many places), and the theorem that the disc algebra is not
  complemented in `C(𝕋)`. With it come the classical results on the trigonometric polynomials
  `𝒯ₙ ⊆ C(𝕋)`: the theorem of Lozinskiĭ and Kharshiladze `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖ = Lₙ` (the Lebesgue
  constant), `λ(𝒯₁, C(𝕋)) = 1/3 + 2√3/π`, `(4/π²) log (n + 1) ≤ Lₙ ≤ 1 + log (2n + 1)`, the
  theorem of Kharshiladze and Lozinskiĭ that no sequence of projections onto `𝒯ₙ` converges
  strongly, and du Bois-Reymond's continuous function with a divergent Fourier series.

Everything is proved from the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
no `sorry`, no `native_decide`. The explicit frames (for example the 276 equiangular lines in
`ℝ²³`), the classification of the two-graphs on six vertices and the sums-of-squares certificates
for `Π(4, 6)` are verified by the Lean kernel.

The code follows the Mathlib conventions: Mathlib naming, `fun x ↦ …`, module docstrings in the
Mathlib format, lines of at most 100 characters, docstrings on all definitions, and it builds
without any warning under Mathlib's standard linter set (`weak.linter.mathlibStandardSet`);
`#lint` passes. Mathlib notions are used wherever they exist (e.g. `IsStarProjection` for
orthogonal projection matrices, `Matrix.IsSymm`, `Matrix.PosSemidef`, `Matrix.IsHermitian`).
General lemmas that do not depend on the rest of the library are collected in `ForMathlib/`.

`diagram/dependency-tree.html` is a radial dependency diagram of the library.

## Authorship

The Lean code in this repository was written by Claude, an AI
model developed by Anthropic (model identifiers claude-opus-5-5 and claude-fable-5-1), in sessions
guided by Giuliano Basso. He chose the statements to formalize, built the project, ran the axiom
check in `scripts/CheckAxioms.lean` and compared the statements in `ProjectionConstants/Main.lean` with the
errata. 




## Building

```
lake exe cache get   # download the Mathlib build cache
lake build
```

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (see `lean-toolchain` and `lakefile.toml`).

Checks:

```
lake env lean scripts/CheckAxioms.lean               # axioms of the main results
lake env lean scripts/CertificateNegativeTests.lean  # corrupted certificates and tables are rejected
```

## Layout

The folders are organized by topic. All declarations live in the namespace
`ProjectionConstants`, except the general lemmas of `ForMathlib/` (Mathlib namespaces).

| Folder / file | Content |
|---|---|
| `ForMathlib/` | General lemmas: sums over finite types, elementary real inequalities, real dot products, star projections of matrices (`IsStarProjection`), `(Tr A)² ≤ rank A · ∑ᵢⱼ Aᵢⱼ²` |
| `Basic`, `Injective`, `Linfty`, `L1`, `Reduction` | `λ(Y, X)`, `λ(Y)`, `λ_𝕜(m)` for normed spaces; the extension property of `ℓ∞^N` and `ℓ∞(Γ)`, `λ(Y) = λ(Y, ℓ∞^N)`, isometric invariance and Grünbaum's Banach–Mazur estimate (`Injective`); matrix projections on `ℓ∞^N` (row sums) and `ℓ₁^N` (column sums); the reduction of `λ_𝕜(m)` to subspaces of `ℓ∞^N` (ε-nets, Hahn–Banach) |
| `Matrix/` | Orthogonal projection matrices and Parseval frames (`OrthProj`); commutation of maximizers on the Grassmannian (`Commute`); coordinates on Hermitian matrices (`HermCoords`); sign matrices and weights (`SignMatrix`); Ky Fan sums and Ky Fan's maximum principle (`KyFan/`) |
| `ChalmersLewicki/` | The formula of Chalmers and Lewicki (Sion's minimax theorem for the upper bound, trace duality for the lower bound); Kadec–Snobar `λ(Y) ≤ √m`; the formula in terms of sign matrices |
| `Quasimaximal` | Quasimaximal projection constants and `λ_𝕜(m) = μ_𝕜(m)` ([DL, Theorem 2.2]) |
| `Invariant/` | [Ru]: Rudin's averaging theorem for compact and finite groups, and Rudin's principle (`Rudin`). [G]: idempotent circulant matrices on a finite abelian group are minimal projections (`Circulant`); `λ(ℓ₁ⁿ)` via the Rademacher functions on `(ℤ/2)ⁿ` (`L1`); the planes whose unit ball is a regular `2N`-gon (`Polygon`) |
| `Fourier/` | The circle `𝕋 = AddCircle T`: translations, Fourier coefficients and partial sums, the Dirichlet kernel, Lozinskiĭ–Kharshiladze `λ(𝒯ₙ, C(𝕋)) = Lₙ` (`Trigonometric`); the growth of the Lebesgue constants, `L₁`, Kharshiladze–Lozinskiĭ and du Bois-Reymond (`Lebesgue`); [Ru, Theorem 2] for `C(𝕋)` and the disc algebra (`DiscAlgebra`) |
| `ETF/` | Equiangular tight frames; a kernel-checked certificate format (`Certificate`); explicit maximal ETFs (`Maximal/`: integer certificates for `m = 2, 7, 23`, Seidel matrices for the icosahedron and the SICs in `ℂ²` and `ℂ³`) |
| `Bounds/` | The bound of König, Lewis and Lin and its equality case (`KLL`, `KLLEquality`), the bound of Bukh and Cox (`BukhCox`), the bounds at the Gerzon bounds (`Gerzon`), the recursive Sidelnikov–Welch inequality (`Welch`), a frame bound (`FrameBound`) |
| `Values` | `λ_ℝ(m)` for `m = 2, 3, 7, 23`, `λ_ℂ(m)` given a SIC and for `m = 1, 2, 3`, Zauner's conjecture; the regular hexagon attains `λ_ℝ(2)` |
| `GrunbaumConjecture/` | [JFA] with [JFA-E]: `Π₂ = 4/3` (a second proof of `λ_ℝ(2) = 4/3`), via sign patterns of maximizers, two-graphs, the matrix `A₆`, and the characteristic polynomial of the weighted pentagon `R₅` |
| `FourSix/` | [JFA, §4.4] with [JFA-E]: `Π(4, 6) = Π(5, 6) = 5/3`, with sums-of-squares certificates and a kernel-checked treatment of all sixteen two-graphs on six vertices |
| `AlmostMinimal/` | [AMOP]: almost minimal orthogonal projections; the folklore strict monotonicity of `λ_ℝ(n)`, with an explicit gap (`Mono`) |
| `Stabilization/` | [KMMP]: first-order conditions of maximizers (`Maximizer`), reweighting inside a sign class (`Reweight`), Carathéodory's theorem for cones (`Caratheodory`), and `λ_ℝ(r, n) = λ_ℝ(r)` for `n ≥ 2^r C(r+1, 2)` (`Main`) |
| `Euclidean/` | [G], [R]: invariant measures on the sphere and the symmetry lemma (`Sphere`); the lower bound through `C(S, 𝕜)` (`LowerBound`); the upper bound by discretization, signed cyclic shifts and Hahn–Banach (`UpperBound`); `λ(𝕜ⁿ) = n ∫ |⟪u, e⟫| dν / ν(S)` (`Formula`); polar coordinates (`Polar`); the Gamma-function closed forms and `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹)` (`Values`) |
| `Complementary/` | [DL26]: complementary projections and repeated frames (`Complement`); complementary dimensions and the explicit families (`Main`) |
| `MainResults` | The main theorems, restated in elementary terms, with the corresponding results of the literature |
| `scripts/` | Axiom check, negative tests for the certificates, the generator of the diagram |

## Notation

| literature | Lean |
|---|---|
| `λ(Y, X)` | `relProjConst Y` |
| `λ(Y)` | `absProjConst 𝕜 Y` |
| `λ_𝕜(m)`, `Π_m` of [JFA] and [AMOP] (`𝕜 = ℝ`) | `maxProjConst 𝕜 m` |
| `λ_𝕜(m, N)`, `Π(m, N)` of [JFA] (`𝕜 = ℝ`) | `maxRelProjConst 𝕜 m N` |
| `μ_𝕜(m, N)`, `μ_𝕜(m)` | `quasiRelConst 𝕜 (Fin N) m`, `quasiMaxConst 𝕜 m` |
| `δ_{m,N}` | `delta m N` |
| an ETF(m, N) exists | `ExistsETF 𝕜 m N` |
| orthogonal projection matrix, of rank `m` | `IsStarProjection P`, `P ∈ orthProjs 𝕜 ι m` |
| `∑ᵢⱼ tᵢ tⱼ \|Pᵢⱼ\|` | `weightedAbsSum t P` |
| sign matrices, weights, `√D S √D` | `IsSignMatrix S`, `IsWeight w`, `weightedSign S w` |
| sum of the `n` largest eigenvalues of `A` | `kyFanSum n A` |
| `ℓ₁^d`, `λ(E, ℓ₁^d)` | `PiLp 1 (fun _ : Fin d ↦ ℝ)`, `relProjConst (l1Sub E)` |
| `ℓ₂ⁿ(𝕜)` | `EuclideanSpace 𝕜 (Fin n)` |
| `ℓ∞^N`, `ℓ∞(G)` | `Fin N → 𝕜`, `G → 𝕜` (Mathlib's sup norm) |
| the plane whose unit ball is a regular `2N`-gon | `regularPolygon N` (a plane in `ℓ∞(ℤ/2N)`) |
| circulant (group) matrix `(v(g - h))_{g,h}` | `Matrix.circulant v` |
| a representation `g ↦ ρ g` of `G` on `X`; `Q` commutes with all `ρ g` | `IsRepresentation ρ` (`IsAddRepresentation ρ`); `IsEquivariant ρ Q` |
| `C(𝕋)` with `𝕋 = ℝ/Tℤ`, the characters `eₖ(x) = e^{2πikx/T}`, translations `f ↦ f(· - y)` | `C(AddCircle T, ℂ)`, `fourier k`, `circleTranslate y` |
| `𝒯ₙ`, `Sₙ f = ∑_{\|k\| ≤ n} f̂(k) eₖ`, `Dₙ`, `Lₙ = ∫_𝕋 \|Dₙ\|` | `trigPoly T n`, `fourierPartialSum T n`, `dirichletKernel T n`, `lebesgueConst T n` |
| `C_N(𝕋) = {f : f̂ = 0 off N}`, the disc algebra `A(𝕋) = C_ℕ(𝕋)` | `spectralSubspace T N`, `discAlgebra T` |

## Main results (`ProjectionConstants.MainResults`)

| Result | Reference | Lean |
|---|---|---|
| `λ_𝕜(m) = sup_N λ_𝕜(m, N)` | | `maxProjConst_eq_iSup_maxRelProjConst` |
| Kadec–Snobar `λ(Y) ≤ √m` | | `absProjConst_le_sqrt` |
| The formula of Chalmers and Lewicki | [DL, Thm 1.1] | `maxRelProjConst_eq_sSup_parseval` |
| The KLL bound; ETF ⇔ `μ = δ` ⇔ `λ = δ` | [DL, Thm 1.2] | `maxRelProjConst_le_delta`, `existsETF_tfae` |
| The Bukh–Cox bounds, real and complex | [DL, Thm 2.1] | `quasiRelConst_real_le`, `quasiRelConst_complex_le` |
| `λ = μ` | [DL, Thm 2.2] | `maxProjConst_eq_quasiMaxConst` |
| Upper bounds, equality for maximal ETFs | [DL, Thm 2.3] | `maxProjConst_real_le_delta`, `maxProjConst_real_eq_delta`, `maxProjConst_complex_le_delta`, `maxProjConst_complex_eq_delta` |
| `λ_ℝ(2) = 4/3`, `λ_ℝ(3) = (1+√5)/2`, `λ_ℝ(7) = 5/2`, `λ_ℝ(23) = 14/3` | [DL, Thm 2.4] | `maxProjConst_real_values` |
| `λ_ℂ(m) = (1 + (m-1)√(m+1))/m` given a SIC in `ℂ^m`; unconditional for `m = 1, 2, 3` | [DL, Thm 2.5] | `maxProjConst_complex_eq_of_sic`, `maxProjConst_complex_values` |
| Zauner's conjecture implies [DL, Conjecture 2.1] | [DL] | `maxProjConst_complex_eq_of_zaunerConjecture` |
| The formula of Chalmers and Lewicki with sign matrices | [JFA, Thm 2.1] | `maxProjConst_real_eq_sSup` |
| `Π₂ = 4/3`, and a second proof of `λ_ℝ(2) = 4/3` | [JFA], [JFA-E] | `isGreatest_signMatrixValues_two`, `ProjectionConstants.GrunbaumConjecture.maxProjConst_real_two` |
| `Π(4, 6) = 5/3`; by-product `Π(5, 6) = 5/3` | [JFA, §4.4], [JFA-E] | `maxRelProjConst_four_six`, `maxRelProjConst_five_six` |
| Almost minimal orthogonal projections, for `E ⊆ ℓ₁^d = PiLp 1 _` | [AMOP, Thm 1.2] | `exists_almost_minimal_orthogonal_projection` |
| `λ_ℝ(n)` is strictly increasing; explicit gap `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k+1)` | folklore | `strictMono_maxProjConst_real`, `maxProjConst_real_add_le_succ` |
| Stabilization: `λ_ℝ(r, n) = λ_ℝ(r)` for `n ≥ 2^r C(r+1, 2)`; the supremum defining `λ_ℝ(r)` is attained | [KMMP, Thm 1.3] | `maxRelProjConst_eq_maxProjConst`, `exists_weightedAbsSum_eq_maxProjConst` |
| Recursive Sidelnikov–Welch inequality: `X_{2t} ≥ (2t-1)/(m+2t-2) X_{2t-2}` over `ℝ`, `X_{2t} ≥ t/(m+t-1) X_{2t-2}` over `ℂ`, where `X_k = ∑ᵢⱼ wᵢwⱼ\|⟨xᵢ, xⱼ⟩\|^k` | [DL26, Thm 2.1] | `recursive_welch_real`, `recursive_welch_complex` |
| Weighted Sidelnikov–Welch bound | [DL26, Cor 2.1] | `weighted_welch_real`, `weighted_welch_complex` |
| A frame bound for Parseval frames | [DL26, Lemma 3.1] | `weightedAbsSum_gram_le_real`, `weightedAbsSum_gram_le_complex` |
| Complementary dimensions: `λ_𝕂(kM - m, kM) = λ_𝕂(m) - 2m/(kM) + 1` given a maximal ETF in `𝕂^m`, attained with equal weights | [DL26, Thm 3.1] | `maxRelProjConst_compl_real`, `maxRelProjConst_compl_complex` |
| Hyperplanes: `λ_𝕂(N-1, N) = 2 - 2/N` | [DL26] | `maxRelProjConst_hyperplane` |
| `λ_ℝ(3k-2, 3k) = 7/3 - 4/(3k)`, `λ_ℝ(6k-3, 6k) = (3+√5)/2 - 1/k`, `λ_ℝ(28k-7, 28k) = 7/2 - 1/(2k)`, `λ_ℝ(276k-23, 276k) = 17/3 - 1/(6k)`, `λ_ℂ(4k-2, 4k) = (3+√3)/2 - 1/k`, `λ_ℂ(9k-3, 9k) = 8/3 - 2/(3k)` | [DL26] | `maxRelProjConst_compl_values` |
| `λ(ℓ₂ⁿ(𝕜)) = n ∫ \|⟪u, e⟫\| dν(u) / ν(S)` for every invariant finite measure `ν ≠ 0` on the sphere | [G], [R], [DGMMM] | `absProjConst_euclideanSpace_eq` |
| Grünbaum: `λ(ℓ₂ⁿ(ℝ)) = 2 Γ(n/2 + 1) / (√π Γ((n+1)/2))`; Rutovitz: `λ(ℓ₂ⁿ(ℂ)) = (√π/2) n! / Γ(n + 1/2)` | [G], [R] | `absProjConst_euclideanSpace_real`, `absProjConst_euclideanSpace_complex` |
| `λ(ℓ₂²(ℝ)) = 4/π`, `λ(ℓ₂³(ℝ)) = 3/2`, `λ(ℓ₂²(ℂ)) = 4/3` | [G, Thm 2] | `absProjConst_euclideanSpace_values` |
| `λ(ℓ₂ⁿ(ℝ)) = n Γ(n/2) / (√π Γ((n+1)/2))` (Grünbaum: `≤`; Rutovitz: `=`) | [G, Thm 4], [R] | `absProjConst_euclideanSpace_real_eq_grunbaum` |
| `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹) = (2m+1) C(2m, m) / 4ᵐ` | [G, §5], [R] | `absProjConst_euclideanSpace_real_odd` |
| `λ` is an isometric invariant; `λ(Y) = λ(Y, ℓ∞^N)` for `Y ⊆ ℓ∞^N` | [G, §1] | `absProjConst_congr`, `absProjConst_eq_relProjConst` |
| Banach–Mazur: `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)`; for norms `‖·‖₁ ≤ ‖·‖₂ ≤ μ ‖·‖₁`, `λ(X₂) ≤ μ λ(X₁)` | [G, §3, Lemma] | `absProjConst_le_mul_norm_mul_norm`, `absProjConst_le_mul_of_le_of_le` |
| Idempotent circulant matrices `P = (v(g-h))` are minimal: `λ(range P) = ∑_g \|v g\|` | | `absProjConst_range_circulant` |
| `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`; `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)` | [G, Thm 3] | `absProjConst_l1`, `absProjConst_l1_odd_eq_even` |
| Regular `2N`-gon plane: `λ = (2/N) ∑_{k<N} \|cos(kπ/N)\|`, `= (2/N) cot(π/2N)` (`N` even), `= 2/(N sin(π/2N))` (`N` odd) | [G, Thm 1] | `absProjConst_regularPolygon`, `absProjConst_regularPolygon_of_even`, `absProjConst_regularPolygon_of_odd` |
| Regular `2ⁿ`-gon: `λ = 2²⁻ⁿ cot(2⁻ⁿπ)`; square, hexagon, octagon: `1`, `4/3`, `(1+√2)/2` | [G, Thm 1, §3] | `absProjConst_regularPolygon_two_pow`, `absProjConst_regularPolygon_values` |
| The hexagon attains `λ_ℝ(2) = 4/3`; `λ(Y) ≤ 4/3 < 3/2` for real planes | [G, §6, Thm 5], [CL] | `absProjConst_regularPolygon_three_eq_maxProjConst`, `absProjConst_le_four_thirds` |
| Rudin's averaging theorem: `sup_g ‖ρ g‖ = M < ∞`, and an equivariant projection `Q` with `‖Q‖ ≤ M² ‖P‖` | [Ru, Thm 1, (4)] | `exists_isProjectionOnto_isEquivariant` |
| Rudin's principle: a unique equivariant projection `P₀` onto a finite-dimensional invariant subspace has `λ(Y, X) = ‖P₀‖` | [Ru] | `relProjConst_eq_norm` |
| Lozinskiĭ–Kharshiladze: `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖ = Lₙ = T⁻¹ ∫_0^T \|∑_{\|k\| ≤ n} e^{2πikx/T}\| dx` | [DGMMM, §1], [Ru, §4] | `relProjConst_trigPoly` |
| `λ(𝒯₀, C(𝕋)) = 1`, `λ(𝒯₁, C(𝕋)) = 1/3 + 2√3/π`; `(4/π²) log (n+1) ≤ λ(𝒯ₙ, C(𝕋)) ≤ 1 + log (2n+1)`, so `λ(𝒯ₙ, C(𝕋)) → ∞` | | `relProjConst_trigPoly_values`, `relProjConst_trigPoly_bounds`, `tendsto_relProjConst_trigPoly_atTop` |
| Kharshiladze–Lozinskiĭ: for projections `Pₙ` onto `𝒯ₙ`, some `f ∈ C(𝕋)` has `sup ‖Pₙ f‖ = ∞` | [DGMMM, §1] | `exists_not_bddAbove_of_isProjectionOnto` |
| du Bois-Reymond: a continuous function whose Fourier series diverges at `0` | | `exists_not_bddAbove_fourierPartialSum_apply_zero` |
| `C_N(𝕋)` is complemented ⇔ `1_N` is a bounded Fourier multiplier; if `N` is periodic up to finitely many places, it is complemented | [Ru, Thm 2, §4] | `exists_isProjectionOnto_spectralSubspace_iff`, `exists_isProjectionOnto_spectralSubspace_of_periodic` |
| The disc algebra `{f ∈ C(𝕋) : f̂(k) = 0 for k < 0}` is not complemented in `C(𝕋)` | [Ru, §4] | `not_exists_isProjectionOnto_discAlgebra` |

## Notes on the proofs

* **The formula of Chalmers and Lewicki** ([DL, Theorem 1.1]). The upper bound
  `λ(Y, ℓ∞^N) ≤ sup ∑ tᵢtⱼ|Pᵢⱼ|` applies Mathlib's Sion minimax theorem to projections onto `Y`
  and probability vectors. The lower bound uses a maximizer, a first-order condition on the
  Grassmannian (`commute_of_isMaxOn`) and trace duality.
* **Quasimaximal constants** ([DL, Theorem 2.2]) blow up rational weights (`nᵢ` copies of the
  `i`-th coordinate) and use the density of the rationals.
* **The bound of Bukh and Cox** ([DL, Theorem 2.1]): coordinates on Hermitian matrices, the rank
  of a Gram matrix, and `(Tr A)² ≤ rank A · ∑ᵢⱼ Aᵢⱼ²`.
* **The equality case of the KLL bound** ([DL, Theorem 1.2]). The three Cauchy–Schwarz
  inequalities of the proof become equalities. If the diagonal is not constant, this forces
  `N = m + 1` and a negative proportionality constant, a contradiction.
* **Maximal ETFs.** An integer certificate lists the vectors `vᵢ` (with an offset), a vector `u`
  orthogonal to all of them, and constants with `∑ vᵢvᵢᵀ = cI - a uuᵀ`. All inner products are
  computed by *packing*: `⟨w, w'⟩` is one base-`B` digit of `pack w · pack (reverse w')`
  (`Packing.pack_mul_div_mod`). So the 37 950 inner products of the 276 lines cost one
  big-number multiplication each, and the kernel checks the certificate in about 15 seconds.
* **`Π₂ = 4/3`** (`GrunbaumConjecture/`, [JFA-E]). By the formula with sign matrices, `Π₂` is
  the supremum of `kyFanSum 2 (√D S √D)`. A maximizer has the strict sign pattern of vectors in the plane, has
  no zero weight, no `K₄` and no coclique of order `4`; instead of the Frankl–Füredi
  classification, a direct argument shows that it is, up to switching and relabelling, a
  principal submatrix of `A₆`. `A₆` itself is excluded ([JFA-E, Lemma D]), and the
  characteristic polynomial of `√D R₅ √D` gives `kyFanSum 2 (√D R₅ √D) ≤ 4/3`
  ([JFA-E, Proposition F]).
* **`Π(4, 6) = 5/3`** (`FourSix/`). The erratum proves `M₁ ≤ 5/3` by a certificate: a positive
  semidefinite `C` with diagonal `2/3` and `A1 + C ⪰ 0` gives
  `kyFanSum 4 (√D A1 √D) ≤ Tr(√D (A1 + C) √D) = ∑ⱼ dⱼ (1 + Cⱼⱼ) = 5/3`
  (`FourSix.frobeniusInner_weightedSign_le_of_certificate`). `kyFanSum_four_weightedSign_A1_le`
  uses exactly the `C` of the erratum (six unit vectors in `ℝ²`, entries in `ℚ(√3)`); the
  positive definiteness of `A1 + C` is checked through its `LDLᵀ` factorization. The same
  argument, with rational matrices `C`, gives `M₂ ≤ 5/3` (replacing Lieb–Siedentop concavity, the
  symmetrization lemma, the cubic estimate and the Lagrange multipliers of the paper) and the
  upper bound in `M₃ = 5/3`. The reduction to `A1, A2, A3` (via `Π(3, 6) < 5/3`,
  `Π(5, 6) ≤ 5/3` and the classification of Bussemaker–Mathon–Seidel) is replaced by a direct
  treatment of all sixteen two-graphs on six vertices: after switching, a sign matrix is one of
  `1024` normalized patterns, and a table, checked by the kernel, relates each of them to one of
  sixteen representatives. Since the certificate argument bounds `Tr(√D A √D P)` for projections
  of every rank, it also gives `Π(5, 6) = 5/3`.
* **`ℓ₁`.** `norm_l1Op` identifies the operator norm on `ℓ₁^N = PiLp 1 _` with the maximal
  column sum (`colSumNorm`), and `relProjConst_l1Sub` expresses `λ(Y, ℓ₁^N)` through matrix
  projections. So [AMOP, Theorem 1.2] is stated for subspaces of `PiLp 1 (fun _ : Fin d ↦ ℝ)`.
* **Strict monotonicity** (`AlmostMinimal/Mono`), a folklore result. Splitting indices of a
  configuration `(w, P)` (two copies with half the weight and opposite signs in a new direction) gives a configuration of
  rank `k + 1`; a bound for heavy indices and a uniform gain `θ³/100`, `θ = 1/(8k)`, give
  `λ_ℝ(k) + 1/(51200 k³) ≤ λ_ℝ(k + 1)`.
* **Stabilization** (`Stabilization/`, [KMMP]). Take a maximizer `(t, U)` of the
  Chalmers–Lewicki quantity for `λ(r, n)` (`U Uᵀ = I_r`, columns `uᵢ ∈ ℝ^r`). Two first-order
  conditions hold: `tᵢ ∑ⱼ tⱼ |⟨uᵢ, uⱼ⟩| = λ tᵢ²` (perturb `tᵢ`), and `λ tᵢ² = ⟨uᵢ, H uᵢ⟩` for a
  fixed matrix `H` (from `M P = P M` with `M = (tᵢ tⱼ sgn⟨uᵢ, uⱼ⟩)`, the commutation lemma for
  maximizers on the Grassmannian). Split the indices into the `2^r` classes of sign patterns of
  the `uᵢ`; inside a class all `⟨uᵢ, uⱼ⟩ ≥ 0`. By Carathéodory's theorem for cones in the
  `C(r+1, 2)`-dimensional space of symmetric matrices, `∑_{i ∈ C} uᵢ uᵢᵀ = ∑_{i ∈ C} cᵢ uᵢ uᵢᵀ`
  with at most `C(r+1, 2)` nonzero `cᵢ ≥ 0`. Replacing `(tᵢ, uᵢ)` by `√cᵢ (tᵢ, uᵢ)` keeps the
  constraints (by the two conditions) and does not decrease the value (the change is
  `‖∑_{i ∈ C} (cᵢ - 1) tᵢ uᵢ‖² ≥ 0`). After all classes, at most `2^r C(r+1, 2)` indices remain.
* **Euclidean spaces** (`Euclidean/`). Let `ν ≠ 0` be a finite measure on the unit sphere `S`
  of `E = 𝕜ⁿ` that is invariant under the linear isometries, and `c = ∫ |⟪u, e⟫| dν / ν(S)`.
  *Symmetry lemma*: `∫ φ(⟪y, u⟫) u dν(u)` is a multiple of `y` (it is fixed by the reflections
  fixing `y`), with a factor independent of `y` (the isometries act transitively on `S`).
  *Lower bound*: `x ↦ ⟪·, x⟫` embeds `E` isometrically into `C(S, 𝕜)`. For a projection `P`
  onto its image, the test functions `ψ(⟪·, u⟫)`, `ψ` a smoothed sign, have norm `≤ 1`; averaging
  `Re ⟪u, P(ψ(⟪·, u⟫))⟫ ≤ ‖P‖` over `u` (Bochner integrals in `C(S, 𝕜)`) and the symmetry lemma
  give `‖P‖ ≥ n c`. *Upper bound*: for any superspace `X ⊇ E`, approximate `ν / ν(S)` by a
  finitely supported probability measure on `S` (simple functions), symmetrize it under the
  `n 2ⁿ` signed cyclic shifts `(gx)ᵢ = ±x_{i+s}` (a tight frame: `∑_g ⟪gz, x⟫ gz = 2ⁿ ‖z‖² x`),
  and extend the functionals `⟪yₖ, ·⟫` to `X` by Hahn–Banach; `P ξ = n ∑ₖ wₖ gₖ(ξ) yₖ` is a
  projection onto `E` of norm `≤ n (c + ε)`. *Values*: the surface measure `μ.toSphere` of a
  Haar measure is invariant (linear isometries have `|det| = 1`), and polar coordinates with the
  Gaussian `e^{-‖x‖²}` give `c = (∫ |x₁| e^{-‖x‖²} / ∫ e^{-‖x‖²}) Γ(dn/2) / Γ((dn+1)/2)` with
  `d = dim_ℝ 𝕜`; by Fubini the ratio of Gaussian integrals is `Γ((d+1)/2) / Γ(d/2)`.
* **Grünbaum's computations** (`Injective`, `Invariant/`, [G]). `ℓ∞^N` and `ℓ∞(Γ)` have the
  extension property (Hahn–Banach in each coordinate), so `λ(Y) = λ(Y, ℓ∞^N)` for `Y ⊆ ℓ∞^N`, and
  embedding `X` isometrically into `ℓ∞(X)` gives Grünbaum's lemma `λ(Y) ≤ ‖T‖ ‖T⁻¹‖ λ(X)`. Let
  `G` be a finite abelian group and `P = (v(g - h))_{g,h}` an idempotent circulant matrix. Its
  norm on `ℓ∞(G)` is `∑_g |v g|` (every row is a permutation of `v`), and trace duality with the
  circulant matrix `A = (sgn v(h - g) / |G|)_{g,h}`, which commutes with `P`, shows that no
  projection onto `range P` has smaller norm. Grünbaum proves minimality directly, by summing the
  constraints over the extreme points of the unit ball. For `ℓ₁ⁿ`, `G = (ℤ/2)ⁿ` and `P` is the
  orthogonal projection onto the span of the Rademacher functions `rᵢ(a) = (-1)^{aᵢ}`, which is
  isometric to `ℓ₁ⁿ`; the value `2⁻ⁿ ∑ₖ C(n, k) |n - 2k|` is evaluated by telescoping. For the
  regular `2N`-gon, `G = ℤ/2N` and `P = (cos((j - k)π/N) / N)`; the closed forms come from
  `2 sin(α/2) ∑_{j<M} cos(jα + β) = sin((M - 1/2)α + β) + sin(α/2 - β)`. Grünbaum treats
  `N = 2ⁿ⁻¹` with `N` functionals; here all `N ≥ 2` are covered.
* **Rudin's averaging theorem** (`Invariant/Rudin`, [Ru]). The sets `{g : ‖ρ g‖ ≤ k}` are closed
  and cover the compact group `G`, so by Baire one of them has interior, and finitely many
  translates of the interior cover `G`. The average `Q x = ∫ ρ g (P (ρ g⁻¹ x)) dg` is a Bochner
  integral in the complete subspace `Y`, so `X` need not be complete. The argument is proved once
  for an abstract averaging scheme without group structure and then specialized to multiplicative
  and additive groups, to the normalized Haar measure, and to finite groups
  (`Q = |G|⁻¹ ∑_g ρ g ∘ P ∘ ρ g⁻¹`). If `G` acts by contractions, `‖Q‖ ≤ ‖P‖`, which gives Rudin's
  principle.
* **Trigonometric polynomials** (`Fourier/`). An operator `Q` on `C(𝕋)` that commutes with the
  translations satisfies `(Q eₖ)(0) = (τ_y Q eₖ)(y) = e₋ₖ(y) (Q eₖ)(y)`, so `Q eₖ = (Q eₖ)(0) eₖ`.
  Hence the only equivariant projection onto `𝒯ₙ` is `Sₙ` (both agree on the characters, whose
  span is dense by Stone–Weierstrass), and `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖`. `Sₙ f(x) = ∫ Dₙ(x - t) f(t) dt`
  gives `‖Sₙ‖ ≤ Lₙ`; testing the functional `f ↦ Sₙ f(0)` with `conj(Dₙ) / max(|Dₙ|, δ)` gives
  `‖f ↦ Sₙ f(0)‖ ≥ Lₙ`. The closed form `|sin(πx/T)| |Dₙ(x)| = |sin((2n+1)πx/T)|` comes from the
  geometric sum `Dₙ = e₋ₙ ∑_{j ≤ 2n} e₁ʲ` and `|e^{iθ} - 1| = 2 |sin(θ/2)|`. Then `sin t ≤ t` on
  the intervals `[(j-1)T/(2n+1), jT/(2n+1)]` gives `Lₙ ≥ (4/π²) Hₙ ≥ (4/π²) log (n+1)`, and
  `|Dₙ| ≤ 2n + 1` together with Jordan's inequality gives `Lₙ ≤ 1 + log (2n+1)`. Since
  `‖Pₙ‖ ≥ Lₙ → ∞` for projections `Pₙ` onto `𝒯ₙ`, and `‖f ↦ Sₙ f(0)‖ = Lₙ`, the theorems of
  Kharshiladze–Lozinskiĭ and du Bois-Reymond follow from the Banach–Steinhaus theorem.
* **Invariant subspaces of `C(𝕋)`** (`Fourier/DiscAlgebra`, [Ru, Theorem 2 and §4]). A projection
  onto `C_N(𝕋)` can be averaged to an equivariant one, which maps `eₖ` to `1_N(k) eₖ`; conversely,
  such a multiplier is a projection onto `C_N(𝕋)`, because continuous functions are determined by
  their Fourier coefficients (via `L²`). For `N` of period `p`, the multiplier is
  `∑_{r ∈ N ∩ [0, p)} p⁻¹ ∑_{m<p} eᵣ(mT/p) τ_{mT/p}` (orthogonality of the characters of `ℤ/p`);
  finite modifications add rank-one operators `f ↦ f̂(k) eₖ`. For the disc algebra (`N = ℕ`), a
  multiplier `Q` with symbol `1_ℕ` would give `Sₙ = e₋ₙ Q eₙ - eₙ₊₁ Q e₋₍ₙ₊₁₎` and
  `Lₙ = ‖Sₙ‖ ≤ 2 ‖Q‖`, contradicting `Lₙ → ∞`.
* **The recursive Sidelnikov–Welch inequality** (`Bounds/Welch`, [DL26, §2]). The paper uses the
  Fischer inner product on homogeneous polynomials; the formalization uses tensors on words
  `Fin k → Fin m`. With `T = ∑ᵢ wᵢ xᵢ^{⊗(n+2)}`, `A = ∑ᵢ wᵢ xᵢ^{⊗n}` and the test tensor
  `Z = ∑_{j=1}^{n+1} δ_{0j} ⊗ A`, the unit norms give `⟨Z, T⟩ = (n+1)‖A‖²` and the symmetry of
  `A` gives `‖Z‖² = (n+1)(m+n)‖A‖²`; `0 ≤ ‖Z - (m+n)T‖²` is then `(n+1) Xₙ ≤ (m+n) X_{n+2}`,
  i.e. [DL26, Theorem 2.1] for `n = 2t - 2`. In the complex case the delta pairs the first
  unconjugated position with each conjugated one. Iterating gives [DL26, Corollary 2.1].
* **Complementary dimensions** (`Complementary/`, [DL26, §3]). For a projection `P` of rank
  `N - m`, `1 - P = U* U` with `U U* = I_m`, and
  `∑ tᵢtⱼ|Pᵢⱼ| = 1 - 2∑ tᵢ²‖uᵢ‖² + ∑ tᵢtⱼ|⟨uᵢ, uⱼ⟩|`; [DL26, Lemma 3.1] (the case `t = 2` of the
  recursive inequality, applied to the normalized columns) bounds the last sum. The lower bound
  comes from the complement of the `k`-fold repetition `(1/k) Jₖ ⊗ P₀` of an optimal frame. For
  `k = 1` the formalization uses the König–Lewis–Lin bound `λ(M-m, M) ≤ δ_{M-m,M}` and the
  identity `δ_{M-m,M} = δ_{m,M} + 1 - 2m/M` instead of the case analysis of the paper, which
  relies on the classification of the dimensions of real maximal ETFs (in particular on their
  nonexistence in `ℝ⁴`); the remaining exception `(m, k) = (2, 2)` is `λ_ℝ(4, 6) = 5/3`.

## Scope and open ends

* [DL, Theorem 2.5] for `m ≥ 4` takes the existence of a SIC in `ℂ^m` as a hypothesis. The known
  SICs in the dimensions listed in [DL] involve algebraic numbers of large degree and are not
  constructed here.
* The statement of [DL26, Theorem 3.1] that the extremal frames for `k ≥ 2` are biangular is not
  formalized (the formalization shows that equal weights are optimal).
* [Ru]: the "only if" part of Theorem 2 rests on Helson's theorem on idempotent measures (only
  periodic sets, up to finitely many places, have indicator functions that are Fourier–Stieltjes
  transforms), which is not formalized; the reduction to bounded multipliers and the case of the
  disc algebra are. The `L¹` versions (Theorem 2 for `L¹(𝕋)`, Newman's theorem that `H¹` is not
  complemented in `L¹`) and the extension of §4 to compact abelian groups (Cohen) are not
  formalized.
* The theorem of Lozinskiĭ and Kharshiladze is proved for the relative constant `λ(𝒯ₙ, C(𝕋))`.
  It equals the absolute projection constant `λ(𝒯ₙ)` of [DGMMM], because `C(𝕋)**` is a
  `1`-injective space; this is not formalized. The asymptotics `Lₙ = (4/π²) log n + O(1)` are formalized only through the bounds
  `(4/π²) log (n+1) ≤ Lₙ ≤ 1 + log (2n+1)`.
* In [JFA, §4.4], `M₂ ≤ 5/3` is proved with calculus (Lieb–Siedentop, Lemmas 4.4 and 4.5,
  Lagrange multipliers). This argument is not formalized; `kyFanSum_four_weightedSign_A2_le`
  uses a certificate instead. The classification of Bussemaker–Mathon–Seidel and the signature
  argument are likewise replaced by the kernel-checked table.

## The dependency diagram

`diagram/dependency-tree.html` is generated from the compiled library:

```
scripts/diagram/build.sh
```

This exports all declarations and their dependencies (`scripts/DepGraph.lean`), arranges them
as a radial tree (`scripts/diagram/make_tree.py`) and writes the page
(`scripts/diagram/build_page.py`). Intermediate files go to `.lake/diagram/`.


## License

Apache 2.0, see `LICENSE`.
