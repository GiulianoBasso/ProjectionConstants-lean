/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Invariant.Rudin
import ProjectionConstants.ChalmersLewicki.LowerBound
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The projection constant of the trigonometric polynomials

Let `𝒯ₙ ⊆ C(𝕋)` be the space of trigonometric polynomials `∑_{|k| ≤ n} cₖ eₖ` of degree at most
`n` on the circle `𝕋 = AddCircle T`, where `eₖ(x) = exp(2πikx/T)`, with the sup norm. The
**theorem of Lozinskiĭ and Kharshiladze** (see [DGMMM, §1]) states that the Fourier partial sum
operator `Sₙ f = ∑_{|k| ≤ n} f̂(k) eₖ` is a minimal projection of `C(𝕋)` onto `𝒯ₙ`, so that

  `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖ = Lₙ = ∫_𝕋 |Dₙ(t)| dt`,

the `n`-th **Lebesgue constant**, where `Dₙ = ∑_{|k| ≤ n} eₖ` is the Dirichlet kernel and `dt` is
the normalized Haar measure.

This is the standard application of Rudin's averaging theorem [Ru, §4]: the circle acts on `C(𝕋)`
by translations `(τ_y f)(x) = f(x - y)`, continuously and isometrically, and `𝒯ₙ` is invariant.
An operator `Q` that commutes with the translations maps each character `eₖ` to a multiple of
itself. If `Q` is a projection onto `𝒯ₙ`, then `Q eₖ = eₖ` for `|k| ≤ n` and `Q eₖ = 0` otherwise,
and since the trigonometric polynomials are dense, `Q = Sₙ`. By Rudin's principle
(`IsAddRepresentation.relProjConst_eq_norm`), `λ(𝒯ₙ, C(𝕋)) = ‖Sₙ‖`. Finally,
`Sₙ f(x) = ∫ Dₙ(x - t) f(t) dt` gives `‖Sₙ‖ ≤ Lₙ`, and testing with continuous approximations of
the phase of `Dₙ` gives `|Sₙ f(0)| ≥ (Lₙ - δ) ‖f‖` for every `δ > 0`.

The growth of `Lₙ` is studied in `ProjectionConstants.Fourier.Lebesgue`.

## Main definitions

* `circleTranslate y`: the translation `f ↦ f(· - y)` on `C(AddCircle T, ℂ)`.
* `trigPoly T n`: the trigonometric polynomials of degree at most `n`.
* `fourierCoeffCLM k`: the `k`-th Fourier coefficient as a continuous linear functional.
* `fourierPartialSum T n`: the Fourier partial sum operator `Sₙ`.
* `dirichletKernel T n`: the Dirichlet kernel `Dₙ = ∑_{|k| ≤ n} eₖ`.
* `lebesgueConst T n`: the Lebesgue constant `Lₙ = ∫ |Dₙ|`.

## Main statements

* `IsEquivariant.apply_fourier_eq_smul`: an operator that commutes with the translations maps
  every character to a multiple of itself.
* `IsProjectionOnto.eq_fourierPartialSum`: `Sₙ` is the only projection onto `𝒯ₙ` that commutes
  with the translations.
* `norm_fourierPartialSum`: `‖Sₙ‖ = Lₙ`; in fact already `‖f ↦ Sₙ f(0)‖ = Lₙ`
  (`norm_evalCLM_comp_fourierPartialSum`).
* `relProjConst_trigPoly`: **Lozinskiĭ–Kharshiladze**, `λ(𝒯ₙ, C(𝕋)) = Lₙ`.

## References

* [Ru] W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962), 429–432.
* [DGMMM] A. Defant, D. Galicer, M. Mansilla, M. Mastyło, S. Muro, *Projection constants for
  spaces of multivariate polynomials*, arXiv:2208.06467.

## Tags

projection constant, trigonometric polynomials, Lebesgue constant, Dirichlet kernel, Fourier
series, minimal projection
-/

open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

noncomputable section

namespace ProjectionConstants

variable {T : ℝ}

/-! ### Characters -/

/-- The characters are multiplicative: `eₖ(x + y) = eₖ(x) eₖ(y)`. -/
lemma fourier_apply_add (k : ℤ) (x y : AddCircle T) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

/-- `eₖ(-x) = e₋ₖ(x)`. -/
lemma fourier_apply_neg (k : ℤ) (x : AddCircle T) : fourier k (-x) = fourier (-k) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

/-- `eₖ(x - y) = eₖ(x) e₋ₖ(y)`. -/
lemma fourier_apply_sub (k : ℤ) (x y : AddCircle T) :
    fourier k (x - y) = fourier k x * fourier (-k) y := by
  rw [sub_eq_add_neg, fourier_apply_add, fourier_apply_neg]

/-- `|eₖ(x)| = 1`. -/
lemma norm_fourier_apply (k : ℤ) (x : AddCircle T) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- `eₖ(-x) eₖ(x) = 1`. -/
lemma fourier_neg_apply_mul_fourier_apply (k : ℤ) (x : AddCircle T) :
    fourier (-k) x * fourier k x = 1 := by
  rw [← fourier_add, neg_add_cancel, fourier_zero]

variable [hT : Fact (0 < T)]

/-- Continuous functions on the circle are integrable for the normalized Haar measure. -/
lemma _root_.Continuous.integrable_haarAddCircle {E : Type*} [NormedAddCommGroup E]
    {g : AddCircle T → E} (hg : Continuous g) : Integrable g haarAddCircle :=
  hg.integrable_of_hasCompactSupport (.of_compactSpace g)

/-- The characters span a dense subspace of `C(𝕋)`. -/
lemma dense_span_fourier :
    Dense (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.2 span_fourier_closure_eq_top

/-- Two continuous linear maps on `C(𝕋)` that agree on the characters are equal. -/
lemma _root_.ContinuousLinearMap.ext_fourier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : C(AddCircle T, ℂ) →L[ℂ] E} (h : ∀ k, f (fourier k) = g (fourier k)) : f = g :=
  ContinuousLinearMap.ext_on dense_span_fourier (by rintro _ ⟨k, rfl⟩; exact h k)

/-! ### Translations -/

/-- Translation by `y`: `(circleTranslate y f)(x) = f(x - y)`. -/
def circleTranslate (y : AddCircle T) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.comp ⟨fun x ↦ x - y, continuous_sub_right y⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun f ↦ by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x ↦ f.norm_coe_le_norm _

@[simp] lemma circleTranslate_apply (y : AddCircle T) (f : C(AddCircle T, ℂ)) (x : AddCircle T) :
    circleTranslate y f x = f (x - y) := rfl

/-- Translations are contractions (indeed isometries). -/
lemma norm_circleTranslate_apply_le (y : AddCircle T) (f : C(AddCircle T, ℂ)) :
    ‖circleTranslate y f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun _ ↦ f.norm_coe_le_norm _

/-- The translations form a representation of the circle. -/
lemma isAddRepresentation_circleTranslate :
    IsAddRepresentation (circleTranslate (T := T)) where
  map_zero := by ext f x; simp
  map_add y z := by ext f x; simp [sub_add_eq_sub_sub]

/-- The translation action `(y, f) ↦ f(· - y)` is jointly continuous. -/
lemma continuous_circleTranslate :
    Continuous fun p : AddCircle T × C(AddCircle T, ℂ) ↦ circleTranslate p.1 p.2 := by
  let φ : C(AddCircle T × AddCircle T, AddCircle T) := ⟨fun p ↦ p.2 - p.1, by fun_prop⟩
  exact ContinuousMap.continuous_comp'.comp ((φ.curry.continuous.comp continuous_fst).prodMk
    continuous_snd)

/-- `τ_y eₖ = e₋ₖ(y) eₖ`: the characters are eigenvectors of the translations. -/
lemma circleTranslate_fourier (y : AddCircle T) (k : ℤ) :
    circleTranslate y (fourier k) = fourier (-k) y • fourier k := by
  ext x
  simp only [circleTranslate_apply, ContinuousMap.smul_apply, smul_eq_mul, fourier_apply_sub]
  ring

/-- An operator that commutes with the translations maps every character to a multiple of itself:
`Q eₖ = (Q eₖ)(0) • eₖ`, because `(Q eₖ)(0) = (τ_y Q eₖ)(y) = (Q τ_y eₖ)(y) = e₋ₖ(y) (Q eₖ)(y)`. -/
lemma IsEquivariant.apply_fourier_eq_smul {Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)}
    (hQ : IsEquivariant circleTranslate Q) (k : ℤ) :
    Q (fourier k) = Q (fourier k) 0 • fourier k := by
  ext y
  have h := congrArg (fun R : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) ↦ R (fourier k) y) (hQ y)
  simp only [ContinuousLinearMap.comp_apply, circleTranslate_apply, sub_self,
    circleTranslate_fourier, map_smul, ContinuousMap.smul_apply, smul_eq_mul] at h
  rw [ContinuousMap.smul_apply, smul_eq_mul, h, mul_comm (fourier (-k) y), mul_assoc,
    fourier_neg_apply_mul_fourier_apply, mul_one]

/-! ### Fourier coefficients -/

/-- The `k`-th Fourier coefficient `f ↦ f̂(k)`, a continuous linear functional of norm at most
`1` on `C(AddCircle T, ℂ)`. -/
def fourierCoeffCLM (k : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ fourierCoeff f k
      map_add' := fun f g ↦ by
        rw [ContinuousMap.coe_add, fourierCoeff.add f.continuous.integrable_haarAddCircle
          g.continuous.integrable_haarAddCircle, Pi.add_apply]
      map_smul' := fun c f ↦ by
        rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, RingHom.id_apply] } 1 fun f ↦ by
    rw [one_mul]
    have h := norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := T))
      (f := fun t ↦ fourier (-k) t • f t) (C := ‖f‖) (Filter.Eventually.of_forall fun t ↦ by
        rw [norm_smul, norm_fourier_apply, one_mul]
        exact f.norm_coe_le_norm t)
    rwa [probReal_univ, mul_one] at h

@[simp] lemma fourierCoeffCLM_apply (k : ℤ) (f : C(AddCircle T, ℂ)) :
    fourierCoeffCLM k f = fourierCoeff f k := rfl

/-- `(τ_y f)^(k) = e₋ₖ(y) f̂(k)`. -/
lemma fourierCoeff_circleTranslate (y : AddCircle T) (f : C(AddCircle T, ℂ)) (k : ℤ) :
    fourierCoeff (circleTranslate y f) k = fourier (-k) y * fourierCoeff f k := by
  simp only [fourierCoeff, circleTranslate_apply]
  have h := integral_sub_right_eq_self (μ := haarAddCircle)
    (fun s ↦ fourier (-k) (s + y) • f s) y
  simp only [sub_add_cancel] at h
  rw [h]
  simp only [fourier_apply_add, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext t
  ring

/-! ### Trigonometric polynomials and Fourier partial sums -/

variable (T) in
/-- The trigonometric polynomials `∑_{|k| ≤ n} cₖ eₖ` of degree at most `n`. -/
def trigPoly (n : ℕ) : Submodule ℂ C(AddCircle T, ℂ) :=
  Submodule.span ℂ (fourier '' Set.Icc (-(n : ℤ)) n)

instance (n : ℕ) : FiniteDimensional ℂ (trigPoly T n) :=
  FiniteDimensional.span_of_finite ℂ ((Set.finite_Icc _ _).image _)

omit hT in
lemma fourier_mem_trigPoly {n : ℕ} {k : ℤ} (hk : k ∈ Icc (-(n : ℤ)) n) :
    fourier k ∈ trigPoly T n :=
  Submodule.subset_span ⟨k, by simpa using hk, rfl⟩

/-- The trigonometric polynomials are invariant under translations. -/
lemma circleTranslate_mem_trigPoly {n : ℕ} (y : AddCircle T) {f : C(AddCircle T, ℂ)}
    (hf : f ∈ trigPoly T n) : circleTranslate y f ∈ trigPoly T n := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    rw [circleTranslate_fourier]
    exact Submodule.smul_mem _ _ (fourier_mem_trigPoly (by simpa using hk))
  | zero => simp
  | add f g _ _ hf hg => simpa using add_mem hf hg
  | smul c f _ hf => simpa using Submodule.smul_mem _ c hf

variable (T) in
/-- The Fourier partial sum operator `Sₙ f = ∑_{|k| ≤ n} f̂(k) eₖ`. -/
def fourierPartialSum (n : ℕ) : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ) :=
  ∑ k ∈ Icc (-(n : ℤ)) n, (fourierCoeffCLM k).smulRight (fourier k)

lemma fourierPartialSum_apply (n : ℕ) (f : C(AddCircle T, ℂ)) :
    fourierPartialSum T n f = ∑ k ∈ Icc (-(n : ℤ)) n, fourierCoeff f k • fourier k := by
  simp [fourierPartialSum]

/-- `Sₙ eⱼ = eⱼ` for `|j| ≤ n`, and `Sₙ eⱼ = 0` otherwise. -/
lemma fourierPartialSum_fourier (n : ℕ) (j : ℤ) :
    fourierPartialSum T n (fourier j) = if j ∈ Icc (-(n : ℤ)) n then fourier j else 0 := by
  rw [fourierPartialSum_apply]
  simp only [fourierCoeff_fourier, Pi.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']

/-- `Sₙ` is a projection onto `𝒯ₙ`. -/
lemma isProjectionOnto_fourierPartialSum (n : ℕ) :
    IsProjectionOnto (trigPoly T n) (fourierPartialSum T n) := by
  refine ⟨fun f ↦ ?_, fun g hg ↦ ?_⟩
  · rw [fourierPartialSum_apply]
    exact Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ (fourier_mem_trigPoly hk)
  · induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      rw [fourierPartialSum_fourier, ite_eq_left (by simpa using hk)]
    | zero => simp
    | add f g _ _ hf hg => simp [hf, hg]
    | smul c f _ hf => simp [hf]

/-- **The equivariant projection is unique**: every projection onto `𝒯ₙ` that commutes with the
translations is the Fourier partial sum operator `Sₙ`. -/
theorem IsProjectionOnto.eq_fourierPartialSum {n : ℕ}
    {Q : C(AddCircle T, ℂ) →L[ℂ] C(AddCircle T, ℂ)} (hQ : IsProjectionOnto (trigPoly T n) Q)
    (hQe : IsEquivariant circleTranslate Q) : Q = fourierPartialSum T n := by
  refine ContinuousLinearMap.ext_fourier fun k ↦ ?_
  rw [fourierPartialSum_fourier]
  split_ifs with hk
  · exact hQ.map_id _ (fourier_mem_trigPoly hk)
  -- `Q eₖ` is a multiple of `eₖ` that lies in `𝒯ₙ`, so `Q eₖ = Sₙ (Q eₖ) = 0`
  rw [← (isProjectionOnto_fourierPartialSum n).map_id _ (hQ.mem (fourier k)),
    hQe.apply_fourier_eq_smul k, map_smul, fourierPartialSum_fourier, ite_eq_right hk, smul_zero]

/-! ### The Dirichlet kernel and the Lebesgue constants -/

variable (T) in
/-- The Dirichlet kernel `Dₙ = ∑_{|k| ≤ n} eₖ`. -/
def dirichletKernel (n : ℕ) : C(AddCircle T, ℂ) :=
  ∑ k ∈ Icc (-(n : ℤ)) n, fourier k

variable (T) in
/-- The Lebesgue constant `Lₙ = ∫ |Dₙ(t)| dt`, with the normalized Haar measure. -/
def lebesgueConst (n : ℕ) : ℝ :=
  ∫ t, ‖dirichletKernel T n t‖ ∂haarAddCircle

omit hT in
lemma dirichletKernel_apply (n : ℕ) (x : AddCircle T) :
    dirichletKernel T n x = ∑ k ∈ Icc (-(n : ℤ)) n, fourier k x := by
  simp [dirichletKernel]

omit hT in
/-- The Dirichlet kernel is even. -/
lemma dirichletKernel_neg (n : ℕ) (x : AddCircle T) :
    dirichletKernel T n (-x) = dirichletKernel T n x := by
  simp only [dirichletKernel_apply, fourier_apply_neg]
  refine Finset.sum_nbij' (fun k ↦ -k) (fun k ↦ -k) (fun k hk ↦ ?_) (fun k hk ↦ ?_)
    (fun k _ ↦ neg_neg k) (fun k _ ↦ neg_neg k) fun k _ ↦ rfl
  · simp only [Finset.mem_Icc] at hk ⊢
    omega
  · simp only [Finset.mem_Icc] at hk ⊢
    omega

/-- The Fourier partial sums are convolutions with the Dirichlet kernel:
`Sₙ f(x) = ∫ Dₙ(x - t) f(t) dt`. -/
lemma fourierPartialSum_apply_eq_integral (n : ℕ) (f : C(AddCircle T, ℂ)) (x : AddCircle T) :
    fourierPartialSum T n f x = ∫ t, dirichletKernel T n (x - t) * f t ∂haarAddCircle := by
  rw [fourierPartialSum_apply]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, dirichletKernel_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ ↦ (by fun_prop : Continuous _).integrable_haarAddCircle]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [fourierCoeff, ← integral_mul_const]
  congr 1
  ext t
  rw [fourier_apply_sub, smul_eq_mul]
  ring

/-- `∫ |Dₙ(x - t)| dt = Lₙ`. -/
lemma integral_norm_dirichletKernel_sub (n : ℕ) (x : AddCircle T) :
    ∫ t, ‖dirichletKernel T n (x - t)‖ ∂haarAddCircle = lebesgueConst T n := by
  have h : ∀ t, dirichletKernel T n (x - t) = dirichletKernel T n (t - x) := fun t ↦ by
    rw [← dirichletKernel_neg, neg_sub]
  simp only [h]
  exact integral_sub_right_eq_self (fun t ↦ ‖dirichletKernel T n t‖) x

/-- `‖Sₙ‖ ≤ Lₙ`. -/
lemma norm_fourierPartialSum_le (n : ℕ) : ‖fourierPartialSum T n‖ ≤ lebesgueConst T n := by
  have hL : 0 ≤ lebesgueConst T n := integral_nonneg fun _ ↦ norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun f ↦ ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ ?_
  rw [fourierPartialSum_apply_eq_integral]
  have hi : Integrable (fun t ↦ ‖dirichletKernel T n (x - t)‖ * ‖f‖) haarAddCircle :=
    (by fun_prop : Continuous _).integrable_haarAddCircle
  calc ‖∫ t, dirichletKernel T n (x - t) * f t ∂haarAddCircle‖
      ≤ ∫ t, ‖dirichletKernel T n (x - t) * f t‖ ∂haarAddCircle :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖dirichletKernel T n (x - t)‖ * ‖f‖ ∂haarAddCircle := by
        refine integral_mono ((by fun_prop : Continuous _).integrable_haarAddCircle) hi fun t ↦ ?_
        rw [norm_mul]
        gcongr
        exact f.norm_coe_le_norm t
    _ = lebesgueConst T n * ‖f‖ := by
        rw [integral_mul_const, integral_norm_dirichletKernel_sub]

/-- Evaluation at a point is a functional of norm at most `1` on `C(𝕋)`. -/
lemma norm_evalCLM_le (x : AddCircle T) :
    ‖(ContinuousMap.evalCLM ℂ x : C(AddCircle T, ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa using f.norm_coe_le_norm x

/-- `Lₙ ≤ ‖f ↦ Sₙ f(0)‖`: test `Sₙ` at `0` with the continuous approximations
`conj(Dₙ) / max(|Dₙ|, δ)` of the phase of `Dₙ`. -/
lemma lebesgueConst_le_norm_evalCLM_comp (n : ℕ) :
    lebesgueConst T n ≤ ‖(ContinuousMap.evalCLM ℂ 0).comp (fourierPartialSum T n)‖ := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set D := dirichletKernel T n
  let f : C(AddCircle T, ℂ) :=
    ⟨fun t ↦ conj (clampSign δ (D t)), (Complex.continuous_conj.comp
      ((continuous_clampSign hδ).comp D.continuous))⟩
  have hf : ‖f‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 fun t ↦ by
    simpa [f] using norm_clampSign_le hδ (D t)
  have hcont : Continuous fun t ↦ ‖D t‖ ^ 2 / max ‖D t‖ δ :=
    (D.continuous.norm.pow 2).div (D.continuous.norm.max continuous_const) fun t ↦
      (lt_of_lt_of_le hδ (le_max_right _ _)).ne'
  -- the value of `Sₙ f` at `0`
  have h₀ : fourierPartialSum T n f 0 =
      ((∫ t, ‖D t‖ ^ 2 / max ‖D t‖ δ ∂haarAddCircle : ℝ) : ℂ) := by
    rw [fourierPartialSum_apply_eq_integral, ← integral_complex_ofReal]
    congr 1
    ext t
    rw [zero_sub, dirichletKernel_neg, mul_comm]
    exact conj_clampSign_mul δ (D t)
  have hlow : lebesgueConst T n - δ ≤ ∫ t, ‖D t‖ ^ 2 / max ‖D t‖ δ ∂haarAddCircle := by
    have h := integral_mono (by fun_prop : Continuous fun t ↦ ‖D t‖ - δ).integrable_haarAddCircle
      hcont.integrable_haarAddCircle fun t ↦ sub_le_sq_div_max hδ (norm_nonneg (D t))
    rwa [integral_sub (by fun_prop : Continuous _).integrable_haarAddCircle
      (integrable_const δ), integral_const, probReal_univ, one_smul] at h
  have hI : 0 ≤ ∫ t, ‖D t‖ ^ 2 / max ‖D t‖ δ ∂haarAddCircle :=
    integral_nonneg fun t ↦ by positivity
  set S := (ContinuousMap.evalCLM ℂ 0).comp (fourierPartialSum T n)
  calc lebesgueConst T n ≤ ∫ t, ‖D t‖ ^ 2 / max ‖D t‖ δ ∂haarAddCircle + δ := by linarith
    _ = ‖S f‖ + δ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply, h₀, Complex.norm_real,
          Real.norm_of_nonneg hI]
    _ ≤ ‖S‖ * ‖f‖ + δ := by
        gcongr
        exact S.le_opNorm f
    _ ≤ ‖S‖ + δ := by
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) hf

/-- The norm of the functional `f ↦ Sₙ f(0)` on `C(𝕋)` is the Lebesgue constant. -/
theorem norm_evalCLM_comp_fourierPartialSum (n : ℕ) :
    ‖(ContinuousMap.evalCLM ℂ 0).comp (fourierPartialSum T n)‖ = lebesgueConst T n := by
  refine le_antisymm ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
    (lebesgueConst_le_norm_evalCLM_comp n)
  calc _ ≤ 1 * ‖fourierPartialSum T n‖ := by gcongr; exact norm_evalCLM_le 0
    _ ≤ lebesgueConst T n := by rw [one_mul]; exact norm_fourierPartialSum_le n

/-- The norm of the Fourier partial sum operator on `C(𝕋)` is the Lebesgue constant:
`‖Sₙ‖ = Lₙ`. -/
theorem norm_fourierPartialSum (n : ℕ) : ‖fourierPartialSum T n‖ = lebesgueConst T n := by
  refine le_antisymm (norm_fourierPartialSum_le n) ?_
  calc lebesgueConst T n = ‖(ContinuousMap.evalCLM ℂ 0).comp (fourierPartialSum T n)‖ :=
        (norm_evalCLM_comp_fourierPartialSum n).symm
    _ ≤ 1 * ‖fourierPartialSum T n‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact norm_evalCLM_le 0)
    _ = ‖fourierPartialSum T n‖ := one_mul _

/-! ### The theorem of Lozinskiĭ and Kharshiladze -/

/-- **Lozinskiĭ–Kharshiladze**: the Fourier partial sum operator is a minimal projection onto the
trigonometric polynomials of degree at most `n`, and `λ(𝒯ₙ, C(𝕋)) = Lₙ`. The proof is Rudin's
averaging argument (`IsAddRepresentation.relProjConst_eq_norm`). -/
theorem relProjConst_trigPoly (n : ℕ) : relProjConst (trigPoly T n) = lebesgueConst T n := by
  rw [isAddRepresentation_circleTranslate.relProjConst_eq_norm continuous_circleTranslate
    norm_circleTranslate_apply_le (fun y _ hf ↦ circleTranslate_mem_trigPoly y hf)
    (isProjectionOnto_fourierPartialSum n) fun Q hQ hQe ↦ hQ.eq_fourierPartialSum hQe,
    norm_fourierPartialSum]

end ProjectionConstants
