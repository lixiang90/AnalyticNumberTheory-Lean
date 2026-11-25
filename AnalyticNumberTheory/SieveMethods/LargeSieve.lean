import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletLFunctions.GaussSums
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ZetaValues

/-!
# The Large Sieve

This file develops the analytic and arithmetic large sieve inequalities and their classical
applications in analytic number theory:

- Gallagher's Sobolev inequality (`gallagher_sobolev_pointwise`, `gallagher_sobolev_midpoint`,
  `gallagher_sobolev_sq_midpoint`) and Gallagher's Fourier-band Sobolev large sieve
  (`gallagher_large_sieve`).
- Finite-dimensional duality principle for matrices / bilinear forms
  (`duality_iff_bilinear_iff_dual`, `duality_sSup_eq`).
- Uniform-spacing Hilbert inequalities on `ℝ` and modulo `1` (`hilbert_inequality_real`,
  `hilbert_inequality_sin_pi`) via the Hermitian spectral theorem and the Mittag-Leffler series
  for cotangent.
- Sharp analytic large sieve inequality `∑_r ‖S(α_r)‖^2 ≤ (N - 1 + δ⁻¹) ∑ |a_n|^2`
  (`analytic_large_sieve`, `analytic_large_sieve_add_inv`), Farey-point spacing, and Rényi's
  prime-modulus variance bound.
- Arithmetic large sieve inequalities (`arithmetic_large_sieve_squarefree`,
  `arithmetic_large_sieve_sifted`, `character_large_sieve`), and Brun–Titchmarsh prime bounds
  via both the large sieve and Selberg's `Λ²` upper-bound sieve.
-/

noncomputable section

open Complex Real Finset MeasureTheory Filter
open scoped Topology Matrix ArithmeticFunction.Moebius Classical InnerProductSpace
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.PrimeDistribution
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.SieveMethods

/-! ### Additive Character and Distance to the Nearest Integer -/

section AdditiveCharacterAndSpacing

/-- Standard additive character `e(α) = exp(2πi α)` on `ℝ`. -/
def e (α : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * α * Complex.I)

/-- Periodicity `e (α + 1) = e α`. -/
@[simp]
theorem e_add_one (α : ℝ) : e (α + 1) = e α := by
  unfold e
  have h : 2 * Real.pi * ((α + 1 : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * (α : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Integer-shift invariance `e (α + k) = e α` for `k : ℤ`. -/
@[simp]
theorem e_add_int (α : ℝ) (k : ℤ) : e (α + k) = e α := by
  unfold e
  have h : 2 * Real.pi * ((α + k : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * (α : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `e 0 = 1`. -/
@[simp]
theorem e_zero : e 0 = 1 := by
  simp [e]

/-- `e (α + β) = e α * e β`. -/
theorem e_add (α β : ℝ) : e (α + β) = e α * e β := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e (-α) = star (e α)`. -/
theorem e_neg (α : ℝ) : e (-α) = star (e α) := by
  unfold e
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `e (-α) = (e α)⁻¹`. -/
theorem e_neg_eq_inv (α : ℝ) : e (-α) = (e α)⁻¹ := by
  unfold e
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- Every value of `e α` has norm `1`. -/
@[simp]
theorem norm_e (α : ℝ) : ‖e α‖ = 1 := by
  have h : 2 * Real.pi * (α : ℂ) * Complex.I = (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e, h, Complex.norm_exp_ofReal_mul_I]

/-- `e α * star (e α) = 1`. -/
@[simp]
theorem e_mul_star_e (α : ℝ) : e α * star (e α) = 1 := by
  rw [← e_neg, ← e_add, add_neg_cancel, e_zero]

/-- Derivative of `t ↦ e (c * t)` is `2πi c * e (c * t)`. -/
theorem hasDerivAt_e_mul (c t : ℝ) :
    HasDerivAt (fun u : ℝ => e (c * u)) ((2 * Real.pi * c * Complex.I) * e (c * t)) t := by
  unfold e
  have hlin : HasDerivAt (fun u : ℝ => 2 * (Real.pi : ℂ) * ((c * u : ℝ) : ℂ) * Complex.I)
      (2 * Real.pi * c * Complex.I) t := by
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) * (u : ℂ))
        (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) t := by
      simpa using h1.const_mul (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I)
    have hfun : (fun u : ℝ => (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) * (u : ℂ)) =
        fun u : ℝ => 2 * (Real.pi : ℂ) * ((c * u : ℝ) : ℂ) * Complex.I := by
      ext u
      push_cast
      ring
    rw [hfun] at h2
    exact h2
  have hexp := (Complex.hasDerivAt_exp _).scomp t hlin
  refine hexp.congr_deriv ?_
  simp only [smul_eq_mul]

/-- Orthogonality of `e (m * u)` on `[0, 1]` for `m : ℤ`. -/
theorem integral_e_int_mul (m : ℤ) :
    ∫ u in (0 : ℝ)..1, e (m * u) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp
  · have hm0 : (2 * Real.pi * (m : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, hm, Complex.I_ne_zero]
    have hd : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => e (m * t) / (2 * Real.pi * (m : ℂ) * Complex.I))
          (e (m * u)) u := by
      intro u _
      have h := (hasDerivAt_e_mul (m : ℝ) u).div_const (2 * Real.pi * (m : ℂ) * Complex.I)
      refine h.congr_deriv ?_
      push_cast
      field_simp [hm0]
    have hint : IntervalIntegrable (fun u : ℝ => e (m * u)) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      unfold e
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    have h1 : e ((m : ℝ) * 1) = 1 := by
      rw [mul_one, show (m : ℝ) = 0 + (m : ℝ) by ring, e_add_int, e_zero]
    have h0 : e ((m : ℝ) * 0) = 1 := by simp
    rw [h1, h0, sub_self]

/-- Period-`1` translation invariance of interval integrals of length `1`. -/
theorem integral_add_one_eq_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Function.Periodic f 1) (a : ℝ) :
    ∫ u in a..(a + 1), f u = ∫ u in (0 : ℝ)..1, f u := by
  simpa using hf.intervalIntegral_add_eq a 0

/-- Distance from a real number `α` to the nearest integer: `‖α‖ = |α - round α|`. -/
def distToInt (α : ℝ) : ℝ :=
  |α - round α|

/-- `distToInt α` is nonnegative. -/
theorem distToInt_nonneg (α : ℝ) : 0 ≤ distToInt α :=
  abs_nonneg _

/-- `distToInt α ≤ 1 / 2` for all `α : ℝ`. -/
theorem distToInt_le_half (α : ℝ) : distToInt α ≤ 1 / 2 :=
  abs_sub_round α

/-- `distToInt α` is at most `|α - k|` for every integer `k`. -/
theorem distToInt_le_abs_sub (α : ℝ) (k : ℤ) : distToInt α ≤ |α - k| :=
  round_le α k

/-- `distToInt α = |α|` whenever `|α| ≤ 1 / 2`. -/
theorem distToInt_eq_abs_of_abs_le_half {α : ℝ} (hα : |α| ≤ 1 / 2) :
    distToInt α = |α| := by
  have h1 : distToInt α ≤ |α| := by simpa using distToInt_le_abs_sub α 0
  have h2 : |α| ≤ distToInt α := by
    rcases eq_or_ne (round α) 0 with hr | hr
    · simp [distToInt, hr]
    · have hge1 : (1 : ℝ) ≤ |(round α : ℝ)| := by exact_mod_cast Int.one_le_abs hr
      have htri : (1 : ℝ) ≤ |α| + |α - round α| := by
        calc
          (1 : ℝ) ≤ |(round α : ℝ)| := hge1
          _ = |α - (α - round α)| := by ring_nf
          _ ≤ |α| + |α - round α| := abs_sub _ _
      change |α| ≤ |α - round α|
      linarith
  exact le_antisymm h1 h2

/-- `distToInt` is symmetric: `distToInt (-α) = distToInt α`. -/
theorem distToInt_neg (α : ℝ) : distToInt (-α) = distToInt α := by
  refine le_antisymm ?_ ?_
  · calc
      distToInt (-α) ≤ |-α - ((-round α : ℤ) : ℝ)| := distToInt_le_abs_sub (-α) (-round α)
      _ = |-(α - round α)| := by push_cast; ring_nf
      _ = distToInt α := abs_neg _
  · calc
      distToInt α ≤ |α - ((-round (-α) : ℤ) : ℝ)| := distToInt_le_abs_sub α (-round (-α))
      _ = |-((-α) - round (-α))| := by push_cast; ring_nf
      _ = distToInt (-α) := abs_neg _

/-- `distToInt` is periodic of period `1` (invariant under integer shifts). -/
@[simp]
theorem distToInt_add_intCast (α : ℝ) (k : ℤ) : distToInt (α + k) = distToInt α := by
  refine le_antisymm ?_ ?_
  · calc
      distToInt (α + k) ≤ |(α + k) - ((round α + k : ℤ) : ℝ)| :=
        distToInt_le_abs_sub (α + k) (round α + k)
      _ = |α - round α| := by push_cast; ring_nf
      _ = distToInt α := rfl
  · calc
      distToInt α ≤ |α - ((round (α + k) - k : ℤ) : ℝ)| :=
        distToInt_le_abs_sub α (round (α + k) - k)
      _ = |(α + k) - round (α + k)| := by push_cast; ring_nf
      _ = distToInt (α + k) := rfl

/-- Triangle inequality for `distToInt`. -/
theorem distToInt_add_le (α β : ℝ) : distToInt (α + β) ≤ distToInt α + distToInt β := by
  calc
    distToInt (α + β) ≤ |(α + β) - ((round α + round β : ℤ) : ℝ)| :=
      distToInt_le_abs_sub (α + β) (round α + round β)
    _ = |(α - round α) + (β - round β)| := by push_cast; ring_nf
    _ ≤ |α - round α| + |β - round β| := abs_add_le _ _
    _ = distToInt α + distToInt β := rfl

/-- `distToInt α = 0` if and only if `α` is an integer. -/
theorem distToInt_eq_zero_iff (α : ℝ) : distToInt α = 0 ↔ ∃ k : ℤ, α = k := by
  constructor
  · intro h
    refine ⟨round α, ?_⟩
    exact sub_eq_zero.mp (abs_eq_zero.mp h)
  · rintro ⟨k, rfl⟩
    exact le_antisymm (by simpa using distToInt_le_abs_sub (k : ℝ) k) (distToInt_nonneg _)

/-- Predicate expressing that a finite family `α : κ → ℝ` indexed by `J : Finset κ` is
`δ`-well-spaced modulo `1` (with `0 < δ ≤ 1`). -/
def WellSpacedModOne {κ : Type*} (J : Finset κ) (α : κ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ distToInt (α r - α s)

/-- If `J` has at least `2` elements and `α` is `δ`-well-spaced mod `1`, then `δ ≤ 1 / 2`. -/
theorem WellSpacedModOne.le_half_of_two_le {κ : Type*} {J : Finset κ} {α : κ → ℝ} {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (hJ : 2 ≤ J.card) : δ ≤ 1 / 2 := by
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  exact (hws.2.2 r hr s hs hrs).trans (distToInt_le_half _)

/-- Any family satisfying `0 < δ ≤ 1/2` and `δ ≤ distToInt (α r - α s)` is `WellSpacedModOne`. -/
theorem wellSpacedModOne_of_le_half {κ : Type*} {J : Finset κ} {α : κ → ℝ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδh : δ ≤ 1 / 2)
    (hsp : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ distToInt (α r - α s)) :
    WellSpacedModOne J α δ :=
  ⟨hδ0, hδh.trans (by norm_num), hsp⟩

/-- Trigonometric polynomial `S(α) = ∑_{M < n ≤ M + N} a_n e(α n)`. -/
def trigPoly (a : ℕ → ℂ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc M (M + N), a n * e (α * n)

end AdditiveCharacterAndSpacing

/-! ### Gallagher's Sobolev Inequality and Fourier-Band Large Sieve -/

section GallagherSobolev

private theorem intervalIntegrable_finset_sum_local {ι E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {f : ι → ℝ → E} {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume a b := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem intervalIntegral_finset_sum_local {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : ι → ℝ → E} {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ u in a..b, ∑ i ∈ s, f i u = ∑ i ∈ s, ∫ u in a..b, f i u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hfi : IntervalIntegrable (f i) volume a b := hf i (Finset.mem_insert_self i s)
    have hfs : IntervalIntegrable (fun u => ∑ j ∈ s, f j u) volume a b :=
      intervalIntegrable_finset_sum_local fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi]
    rw [intervalIntegral.integral_add hfi hfs, ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

private theorem integral_mul_sub_deriv_eq {f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc a b)) (c : ℝ) :
    ∫ u in a..b, ((u - c : ℝ) : ℂ) * f' u =
      ((b - c : ℝ) : ℂ) * f b - ((a - c : ℝ) : ℂ) * f a - ∫ u in a..b, f u := by
  let G : ℝ → ℂ := fun u => ((u - c : ℝ) : ℂ) * f u
  have hf_cont : ContinuousOn f (Set.Icc a b) := fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hG_deriv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt G (f u + ((u - c : ℝ) : ℂ) * f' u) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hlin : HasDerivAt (fun t : ℝ => ((t - c : ℝ) : ℂ)) 1 u := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa using h1.sub_const (c : ℂ)
    have hmul := hlin.mul (hdiff u hu)
    refine hmul.congr_deriv ?_
    ring
  have hG'_cont : ContinuousOn (fun u => f u + ((u - c : ℝ) : ℂ) * f' u) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hf_cont.add ((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousOn.mul hf'_cont)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv hG'_cont.intervalIntegrable
  have hint1 : IntervalIntegrable f volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hab]
  have hint2 : IntervalIntegrable (fun u => ((u - c : ℝ) : ℂ) * f' u) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousOn.mul hf'_cont
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  dsimp [G] at hftc
  linear_combination hftc

/-- Gallagher's Sobolev identity on `[a, b]` (`a < b`) for `x ∈ [a, b]`:
`f x = (b - a)⁻¹ * ∫_a^b f(u) du + ∫_x^b ((u - b)/(b - a)) f'(u) du + ∫_a^x ((u - a)/(b - a)) f'(u) du`. -/
theorem sobolev_identity_interval {f f' : ℝ → ℂ} {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hdiff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc a b)) :
    f x = (((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u) +
      (∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u) +
      (∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u) := by
  have hax : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hba : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hab).ne'
  have h1 := integral_mul_sub_deriv_eq hxb
    (fun t ht => hdiff t ⟨hax.trans ht.1, ht.2⟩)
    (hf'_cont.mono (Set.Icc_subset_Icc_left hax)) b
  have h2 := integral_mul_sub_deriv_eq hax
    (fun t ht => hdiff t ⟨ht.1, ht.2.trans hxb⟩)
    (hf'_cont.mono (Set.Icc_subset_Icc_right hxb)) a
  have hf_int_ax : IntervalIntegrable f volume a x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hax]
    exact fun t ht => (hdiff t ⟨ht.1, ht.2.trans hxb⟩).continuousAt.continuousWithinAt
  have hf_int_xb : IntervalIntegrable f volume x b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxb]
    exact fun t ht => (hdiff t ⟨hax.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hf_int_ax hf_int_xb
  have hr1 : ∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u =
      (((b - a)⁻¹ : ℝ) : ℂ) * ∫ u in x..b, ((u - b : ℝ) : ℂ) * f' u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    ring
  have hr2 : ∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u =
      (((b - a)⁻¹ : ℝ) : ℂ) * ∫ u in a..x, ((u - a : ℝ) : ℂ) * f' u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    ring
  rw [hr1, hr2, h1, h2]
  have hinv : ((b - a : ℝ) : ℂ) * (((b - a)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sub_pos.mpr hab).ne', Complex.ofReal_one]
  apply mul_left_cancel₀ hba
  calc
    ((b - a : ℝ) : ℂ) * f x
        = (∫ u in a..x, f u) + (∫ u in x..b, f u) +
            (-((x - b : ℝ) : ℂ) * f x - ∫ u in x..b, f u) +
            (((x - a : ℝ) : ℂ) * f x - ∫ u in a..x, f u) := by
          push_cast; ring
    _ = (∫ u in a..b, f u) +
            (((b - b : ℝ) : ℂ) * f b - ((x - b : ℝ) : ℂ) * f x - ∫ u in x..b, f u) +
            (((x - a : ℝ) : ℂ) * f x - ((a - a : ℝ) : ℂ) * f a - ∫ u in a..x, f u) := by
          rw [hsplit]
          simp only [sub_self, Complex.ofReal_zero, zero_mul, zero_sub, sub_zero]
          push_cast; ring
    _ = ((b - a : ℝ) : ℂ) *
          ((((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u) +
            (((b - a)⁻¹ : ℝ) : ℂ) *
              (((b - b : ℝ) : ℂ) * f b - ((x - b : ℝ) : ℂ) * f x - ∫ u in x..b, f u) +
            (((b - a)⁻¹ : ℝ) : ℂ) *
              (((x - a : ℝ) : ℂ) * f x - ((a - a : ℝ) : ℂ) * f a - ∫ u in a..x, f u)) := by
          rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, hinv, one_mul,
            one_mul, one_mul]

/-- Gallagher's pointwise Sobolev inequality on `[a, b]` (`a < b`):
for `x ∈ [a, b]`, `‖f x‖ ≤ (b - a)⁻¹ * ∫_a^b ‖f(u)‖ du + ∫_a^b ‖f'(u)‖ du`. -/
theorem gallagher_sobolev_pointwise {f f' : ℝ → ℂ} {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hdiff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc a b)) :
    ‖f x‖ ≤ (b - a)⁻¹ * (∫ u in a..b, ‖f u‖) + ∫ u in a..b, ‖f' u‖ := by
  have hid := sobolev_identity_interval hab hx hdiff hf'_cont
  have hax : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  have hint_f'1 : IntervalIntegrable (fun u => ‖f' u‖) volume a x :=
    (ContinuousOn.norm (hf'_cont.mono (Set.Icc_subset_Icc_right hxb))).intervalIntegrable_of_Icc hax
  have hint_f'2 : IntervalIntegrable (fun u => ‖f' u‖) volume x b :=
    (ContinuousOn.norm (hf'_cont.mono (Set.Icc_subset_Icc_left hax))).intervalIntegrable_of_Icc hxb
  have h1 : ‖(((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u)‖ ≤
      (b - a)⁻¹ * (∫ u in a..b, ‖f u‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hba_pos.le)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm hab.le) (inv_nonneg.mpr hba_pos.le)
  have h2 : ‖∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u‖ ≤ ∫ u in x..b, ‖f' u‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hxb).trans ?_
    refine intervalIntegral.integral_mono_on hxb ?_ hint_f'2 fun u hu => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxb]
      exact ((Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn.mul
        (hf'_cont.mono (Set.Icc_subset_Icc_left hax))).norm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hba_pos]
      have hle1 : |u - b| / (b - a) ≤ 1 := by
        rw [div_le_one hba_pos, abs_sub_le_iff]
        exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
      simpa using mul_le_mul_of_nonneg_right hle1 (norm_nonneg (f' u))
  have h3 : ‖∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u‖ ≤ ∫ u in a..x, ‖f' u‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hax).trans ?_
    refine intervalIntegral.integral_mono_on hax ?_ hint_f'1 fun u hu => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hax]
      exact ((Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn.mul
        (hf'_cont.mono (Set.Icc_subset_Icc_right hxb))).norm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hba_pos]
      have hle1 : |u - a| / (b - a) ≤ 1 := by
        rw [div_le_one hba_pos, abs_sub_le_iff]
        exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
      simpa using mul_le_mul_of_nonneg_right hle1 (norm_nonneg (f' u))
  have hsum_f' : (∫ u in a..x, ‖f' u‖) + ∫ u in x..b, ‖f' u‖ = ∫ u in a..b, ‖f' u‖ :=
    intervalIntegral.integral_add_adjacent_intervals hint_f'1 hint_f'2
  have htri : ‖f x‖ ≤
      ‖(((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u)‖ +
        ‖∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u‖ +
        ‖∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u‖ := by
    rw [hid]
    have htri1 := norm_add_le
      ((((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u) +
        ∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u)
      (∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u)
    have htri2 := norm_add_le
      ((((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u))
      (∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u)
    linarith
  linarith [htri, h1, h2, h3, hsum_f']

/-- Gallagher's midpoint Sobolev inequality on `[a, b]` (`a < b`):
`‖f ((a + b) / 2)‖ ≤ (b - a)⁻¹ * ∫_a^b ‖f(u)‖ du + (1 / 2) * ∫_a^b ‖f'(u)‖ du`. -/
theorem gallagher_sobolev_midpoint {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hdiff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc a b)) :
    ‖f ((a + b) / 2)‖ ≤ (b - a)⁻¹ * (∫ u in a..b, ‖f u‖) + (1 / 2) * ∫ u in a..b, ‖f' u‖ := by
  let x : ℝ := (a + b) / 2
  have hax : a ≤ x := by dsimp [x]; linarith
  have hxb : x ≤ b := by dsimp [x]; linarith
  have hx : x ∈ Set.Icc a b := ⟨hax, hxb⟩
  have hid := sobolev_identity_interval hab hx hdiff hf'_cont
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  have hint_f'1 : IntervalIntegrable (fun u => (1 / 2 : ℝ) * ‖f' u‖) volume a x :=
    ((ContinuousOn.norm (hf'_cont.mono (Set.Icc_subset_Icc_right hxb))).const_mul (1 / 2)).intervalIntegrable_of_Icc hax
  have hint_f'2 : IntervalIntegrable (fun u => (1 / 2 : ℝ) * ‖f' u‖) volume x b :=
    ((ContinuousOn.norm (hf'_cont.mono (Set.Icc_subset_Icc_left hax))).const_mul (1 / 2)).intervalIntegrable_of_Icc hxb
  have h1 : ‖(((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u)‖ ≤
      (b - a)⁻¹ * (∫ u in a..b, ‖f u‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hba_pos.le)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm hab.le) (inv_nonneg.mpr hba_pos.le)
  have h2 : ‖∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u‖ ≤
      ∫ u in x..b, (1 / 2 : ℝ) * ‖f' u‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hxb).trans ?_
    refine intervalIntegral.integral_mono_on hxb ?_ hint_f'2 fun u hu => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxb]
      exact ((Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn.mul
        (hf'_cont.mono (Set.Icc_subset_Icc_left hax))).norm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hba_pos]
      have hle : |u - b| / (b - a) ≤ 1 / 2 := by
        rw [div_le_iff₀ hba_pos, abs_sub_le_iff]
        have hu1 : x ≤ u := hu.1
        have hu2 : u ≤ b := hu.2
        constructor <;> dsimp [x] at hu1 <;> linarith
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg (f' u))
  have h3 : ‖∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u‖ ≤
      ∫ u in a..x, (1 / 2 : ℝ) * ‖f' u‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hax).trans ?_
    refine intervalIntegral.integral_mono_on hax ?_ hint_f'1 fun u hu => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hax]
      exact ((Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn.mul
        (hf'_cont.mono (Set.Icc_subset_Icc_right hxb))).norm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hba_pos]
      have hle : |u - a| / (b - a) ≤ 1 / 2 := by
        rw [div_le_iff₀ hba_pos, abs_sub_le_iff]
        have hu1 : a ≤ u := hu.1
        have hu2 : u ≤ x := hu.2
        constructor <;> dsimp [x] at hu2 <;> linarith
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg (f' u))
  have hsum_f' : (∫ u in a..x, (1 / 2 : ℝ) * ‖f' u‖) + ∫ u in x..b, (1 / 2 : ℝ) * ‖f' u‖ =
      (1 / 2 : ℝ) * ∫ u in a..b, ‖f' u‖ := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint_f'1 hint_f'2,
      intervalIntegral.integral_const_mul]
  have htri : ‖f x‖ ≤
      ‖(((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u)‖ +
        ‖∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u‖ +
        ‖∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u‖ := by
    rw [hid]
    have htri1 := norm_add_le
      ((((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u) +
        ∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u)
      (∫ u in a..x, (((u - a) / (b - a) : ℝ) : ℂ) * f' u)
    have htri2 := norm_add_le
      ((((b - a)⁻¹ : ℝ) : ℂ) * (∫ u in a..b, f u))
      (∫ u in x..b, (((u - b) / (b - a) : ℝ) : ℂ) * f' u)
    linarith
  linarith [htri, h1, h2, h3, hsum_f']

/-- Centered version of Gallagher's `L²` Sobolev inequality (`δ > 0`):
`‖f x‖ ^ 2 ≤ δ⁻¹ * ∫_{x - δ/2}^{x + δ/2} ‖f(u)‖^2 du + ∫_{x - δ/2}^{x + δ/2} ‖f(u)‖ * ‖f'(u)‖ du`. -/
theorem gallagher_sobolev_sq_midpoint {f f' : ℝ → ℂ} {x δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ t ∈ Set.Icc (x - δ / 2) (x + δ / 2), HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc (x - δ / 2) (x + δ / 2))) :
    ‖f x‖ ^ 2 ≤ δ⁻¹ * (∫ u in (x - δ / 2)..(x + δ / 2), ‖f u‖ ^ 2) +
      ∫ u in (x - δ / 2)..(x + δ / 2), ‖f u‖ * ‖f' u‖ := by
  let a := x - δ / 2
  let b := x + δ / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hmid : (a + b) / 2 = x := by dsimp [a, b]; ring
  have hba : b - a = δ := by dsimp [a, b]; ring
  let g : ℝ → ℂ := fun u => ((‖f u‖ ^ 2 : ℝ) : ℂ)
  let g' : ℝ → ℂ := fun u => ((2 * (star (f u) * f' u).re : ℝ) : ℂ)
  have hg_diff : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    have hft := hdiff t ht
    have hstar : HasDerivAt (fun u => star (f u)) (star (f' t)) t := hft.star
    have hprod : HasDerivAt (fun u => star (f u) * f u)
        (star (f' t) * f t + star (f t) * f' t) t := hstar.mul hft
    have hre : HasDerivAt (fun u => (star (f u) * f u).re)
        (star (f' t) * f t + star (f t) * f' t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hprod
    have hfun : (fun u => (‖f u‖ ^ 2 : ℝ)) = fun u => (star (f u) * f u).re := by
      ext u
      have h : star (f u) * f u = ((‖f u‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h, Complex.ofReal_re]
    have hderiv_val : (star (f' t) * f t + star (f t) * f' t).re =
        2 * (star (f t) * f' t).re := by
      have hconj : star (f' t) * f t = star (star (f t) * f' t) := by
        simp [mul_comm]
      rw [hconj, Complex.add_re, Complex.star_def, Complex.conj_re]
      ring
    rw [← hfun, hderiv_val] at hre
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hre
  have hf_cont : ContinuousOn f (Set.Icc a b) := fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hg'_cont : ContinuousOn g' (Set.Icc a b) := by
    have hre_cont : ContinuousOn (fun u => 2 * (star (f u) * f' u).re) (Set.Icc a b) :=
      continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
        ((continuous_star.comp_continuousOn hf_cont).mul hf'_cont))
    exact Complex.continuous_ofReal.comp_continuousOn hre_cont
  have hmid_ineq := gallagher_sobolev_midpoint hab hg_diff hg'_cont
  rw [hmid, hba] at hmid_ineq
  have hnorm_g : ∀ u, ‖g u‖ = ‖f u‖ ^ 2 := fun u => by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hnorm_g' : ∀ u, ‖g' u‖ ≤ 2 * (‖f u‖ * ‖f' u‖) := fun u => by
    dsimp [g']
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos two_pos]
    calc
      2 * |(star (f u) * f' u).re| ≤ 2 * ‖star (f u) * f' u‖ := by
        gcongr; exact Complex.abs_re_le_norm _
      _ = 2 * (‖f u‖ * ‖f' u‖) := by rw [norm_mul, norm_star]
  rw [hnorm_g] at hmid_ineq
  simp_rw [hnorm_g] at hmid_ineq
  have hint_g' : IntervalIntegrable (fun u => ‖g' u‖) volume a b :=
    (ContinuousOn.norm hg'_cont).intervalIntegrable_of_Icc hab.le
  have hint_ff' : IntervalIntegrable (fun u => 2 * (‖f u‖ * ‖f' u‖)) volume a b :=
    ((hf_cont.norm.mul hf'_cont.norm).const_mul 2).intervalIntegrable_of_Icc hab.le
  have hint_mono : ∫ u in a..b, ‖g' u‖ ≤ 2 * ∫ u in a..b, ‖f u‖ * ‖f' u‖ := by
    calc
      ∫ u in a..b, ‖g' u‖ ≤ ∫ u in a..b, 2 * (‖f u‖ * ‖f' u‖) :=
        intervalIntegral.integral_mono_on hab.le hint_g' hint_ff' fun u _ => hnorm_g' u
      _ = 2 * ∫ u in a..b, ‖f u‖ * ‖f' u‖ := intervalIntegral.integral_const_mul _ _
  calc
    ‖f x‖ ^ 2 ≤ δ⁻¹ * (∫ u in a..b, ‖f u‖ ^ 2) + (1 / 2) * ∫ u in a..b, ‖g' u‖ := hmid_ineq
    _ ≤ δ⁻¹ * (∫ u in a..b, ‖f u‖ ^ 2) + (1 / 2) * (2 * ∫ u in a..b, ‖f u‖ * ‖f' u‖) := by
        gcongr
    _ = δ⁻¹ * (∫ u in a..b, ‖f u‖ ^ 2) + ∫ u in a..b, ‖f u‖ * ‖f' u‖ := by ring

private theorem continuous_distToInt_sub (x : ℝ) :
    Continuous fun u : ℝ => distToInt (u - x) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds u hε] with v hv
  have hv' : |v - u| < ε := by simpa [Real.dist_eq] using Metric.mem_ball.mp hv
  change |distToInt (v - x) - distToInt (u - x)| < ε
  have h1 : distToInt (v - x) ≤ distToInt (u - x) + |v - u| := by
    have hsub : v - x = (u - x) + (v - u) := by ring
    calc
      distToInt (v - x) ≤ distToInt (u - x) + distToInt (v - u) := by
        rw [hsub]; exact distToInt_add_le _ _
      _ ≤ distToInt (u - x) + |v - u| := by
        gcongr; simpa using distToInt_le_abs_sub (v - u) 0
  have h2 : distToInt (u - x) ≤ distToInt (v - x) + |v - u| := by
    have hsub : u - x = (v - x) + (u - v) := by ring
    calc
      distToInt (u - x) ≤ distToInt (v - x) + distToInt (u - v) := by
        rw [hsub]; exact distToInt_add_le _ _
      _ ≤ distToInt (v - x) + |u - v| := by
        gcongr; simpa using distToInt_le_abs_sub (u - v) 0
      _ = distToInt (v - x) + |v - u| := by rw [abs_sub_comm]
  rw [abs_sub_lt_iff]
  exact ⟨by linarith [hv', h1], by linarith [hv', h2]⟩

private theorem integral_periodic_indicator_distToInt_lt {F : ℝ → ℝ}
    (hF_per : Function.Periodic F 1) (hF_int : IntervalIntegrable F volume 0 1)
    {x δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ u in (x - δ / 2)..(x + δ / 2), F u =
      ∫ u in (0 : ℝ)..1, Set.indicator {u : ℝ | distToInt (u - x) < δ / 2} F u := by
  let S := {u : ℝ | distToInt (u - x) < δ / 2}
  let g : ℝ → ℝ := S.indicator F
  have hS_per : ∀ u, u + 1 ∈ S ↔ u ∈ S := by
    intro u
    simp only [S, Set.mem_ofPred_eq]
    have h : (u + 1) - x = (u - x) + (1 : ℤ) := by push_cast; ring
    rw [h, distToInt_add_intCast]
  have hg_per : Function.Periodic g 1 := by
    intro u
    by_cases hu : u ∈ S
    · have hu1 : u + 1 ∈ S := (hS_per u).mpr hu
      simp [g, hu, hu1, hF_per u]
    · have hu1 : u + 1 ∉ S := fun h => hu ((hS_per u).mp h)
      simp [g, hu, hu1]
  have ha_le : x - 1 / 2 ≤ x - δ / 2 := by linarith
  have hb_le : x + δ / 2 ≤ x + 1 / 2 := by linarith
  have hmid_le : x - δ / 2 ≤ x + δ / 2 := by linarith
  have hF_int_full : IntervalIntegrable F volume (x - 1 / 2) (x + 1 / 2) :=
    hF_per.intervalIntegrable₀ one_ne_zero hF_int (x - 1 / 2) (x + 1 / 2)
  have hS_meas : MeasurableSet S :=
    (isOpen_Iio : IsOpen (Set.Iio (δ / 2))).measurableSet.preimage (continuous_distToInt_sub x).measurable
  have hg_int_full : IntervalIntegrable g volume (x - 1 / 2) (x + 1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hF_int_full ⊢
    exact hF_int_full.indicator hS_meas
  have hg_1 : IntervalIntegrable g volume (x - 1 / 2) (x - δ / 2) :=
    hg_int_full.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨ha_le, by linarith⟩)))
  have hg_2 : IntervalIntegrable g volume (x - δ / 2) (x + δ / 2) :=
    hg_int_full.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨ha_le, by linarith⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hb_le⟩)))
  have hg_3 : IntervalIntegrable g volume (x + δ / 2) (x + 1 / 2) :=
    hg_int_full.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hb_le⟩))
      Set.right_mem_uIcc)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hg_1.trans hg_2) hg_3
  rw [← intervalIntegral.integral_add_adjacent_intervals hg_1 hg_2] at hsplit
  have hzero1 : ∫ u in (x - 1 / 2)..(x - δ / 2), g u = 0 := by
    rw [intervalIntegral.integral_of_le ha_le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have hnot : u ∉ S := by
      simp only [S, Set.mem_ofPred_eq, not_lt]
      have habs : |u - x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [distToInt_eq_abs_of_abs_le_half habs, abs_of_nonpos (by linarith [hu.2])]
      linarith [hu.2]
    simp [g, hnot]
  have hzero3 : ∫ u in (x + δ / 2)..(x + 1 / 2), g u = 0 := by
    rw [intervalIntegral.integral_of_le hb_le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have hnot : u ∉ S := by
      simp only [S, Set.mem_ofPred_eq, not_lt]
      have habs : |u - x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [distToInt_eq_abs_of_abs_le_half habs, abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.1]
    simp [g, hnot]
  have hmid_eq : ∫ u in (x - δ / 2)..(x + δ / 2), g u = ∫ u in (x - δ / 2)..(x + δ / 2), F u := by
    rw [intervalIntegral.integral_of_le hmid_le, intervalIntegral.integral_of_le hmid_le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hin : u ∈ S := by
      simp only [S, Set.mem_ofPred_eq]
      have habs : |u - x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [distToInt_eq_abs_of_abs_le_half habs, abs_lt]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp [g, hin]
  have hper_eq := integral_add_one_eq_of_periodic g hg_per (x - 1 / 2)
  have heq_end : (x - 1 / 2) + 1 = x + 1 / 2 := by ring
  rw [heq_end] at hper_eq
  calc
    ∫ u in (x - δ / 2)..(x + δ / 2), F u
        = ∫ u in (x - δ / 2)..(x + δ / 2), g u := hmid_eq.symm
    _ = ∫ u in (x - 1 / 2)..(x + 1 / 2), g u := by linarith
    _ = ∫ u in (0 : ℝ)..1, g u := hper_eq

private theorem sum_integral_wellSpaced_le {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) {F : ℝ → ℝ} (hF_nonneg : ∀ u, 0 ≤ F u)
    (hF_per : Function.Periodic F 1) (hF_int : IntervalIntegrable F volume 0 1) :
    ∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), F u ≤ ∫ u in (0 : ℝ)..1, F u := by
  let S : κ → Set ℝ := fun r => {u : ℝ | distToInt (u - α r) < δ / 2}
  have hcongr : ∀ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), F u =
      ∫ u in (0 : ℝ)..1, (S r).indicator F u := fun r _ =>
    integral_periodic_indicator_distToInt_lt hF_per hF_int hws.1 hws.2.1
  rw [Finset.sum_congr rfl hcongr]
  have hint_ind : ∀ r ∈ J, IntervalIntegrable ((S r).indicator F) volume 0 1 := by
    intro r _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hF_int ⊢
    have hS_meas : MeasurableSet (S r) :=
      (isOpen_Iio : IsOpen (Set.Iio (δ / 2))).measurableSet.preimage
        (continuous_distToInt_sub (α r)).measurable
    exact hF_int.indicator hS_meas
  rw [← intervalIntegral_finset_sum_local hint_ind]
  refine intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_finset_sum_local hint_ind) hF_int fun u _ => ?_
  have hdisj : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → ¬ (u ∈ S r ∧ u ∈ S s) := by
    intro r hr s hs hrs ⟨hur, hus⟩
    have h1 := hws.2.2 r hr s hs hrs
    have htri : distToInt (α r - α s) ≤ distToInt (u - α r) + distToInt (u - α s) := by
      have hdiff : α r - α s = (u - α s) + -(u - α r) := by ring
      rw [hdiff]
      calc
        distToInt ((u - α s) + -(u - α r))
            ≤ distToInt (u - α s) + distToInt (-(u - α r)) := distToInt_add_le _ _
        _ = distToInt (u - α r) + distToInt (u - α s) := by rw [distToInt_neg, add_comm]
    dsimp [S] at hur hus
    linarith [hur, hus]
  by_cases hmem : ∃ r ∈ J, u ∈ S r
  · obtain ⟨r₀, hr₀, hu₀⟩ := hmem
    have huniq : ∀ r ∈ J, r ≠ r₀ → u ∉ S r := fun r hr hne hur =>
      hdisj r hr r₀ hr₀ hne ⟨hur, hu₀⟩
    rw [Finset.sum_eq_single r₀]
    · simp [hu₀]
    · intro r hr hne
      simp [huniq r hr hne]
    · intro hnot
      exact absurd hr₀ hnot
  · push Not at hmem
    have hzero : ∑ r ∈ J, (S r).indicator F u = 0 :=
      Finset.sum_eq_zero fun r hr => by simp [hmem r hr]
    rw [hzero]
    exact hF_nonneg u

private theorem integral_norm_sq_trigPoly_shift (a : ℕ → ℂ) (M N : ℕ) (K : ℤ) :
    ∫ u in (0 : ℝ)..1, ‖∑ n ∈ Finset.Ioc M (M + N), a n * e (u * (n + K : ℤ))‖ ^ 2 =
      ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let S := Finset.Ioc M (M + N)
  have hnorm_sq : ∀ u : ℝ,
      ((‖∑ n ∈ S, a n * e (u * ((n + K : ℤ) : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u) := by
    intro u
    let w := ∑ n ∈ S, a n * e (u * ((n + K : ℤ) : ℝ))
    have hw : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [hw]
    dsimp [w]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, ← Complex.star_def, ← e_neg]
    have hexp : e (u * ((m + K : ℤ) : ℝ)) * e (-(u * ((n + K : ℤ) : ℝ))) =
        e (((m : ℤ) - (n : ℤ)) * u) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    calc
      a m * e (u * ((m + K : ℤ) : ℝ)) * (star (a n) * e (-(u * ((n + K : ℤ) : ℝ))))
          = a m * star (a n) * (e (u * ((m + K : ℤ) : ℝ)) * e (-(u * ((n + K : ℤ) : ℝ)))) := by
            ring
      _ = a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u) := by rw [hexp]
  have hint_term : ∀ m n : ℕ, IntervalIntegrable
      (fun u : ℝ => a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u)) volume 0 1 := by
    intro m n
    refine Continuous.intervalIntegrable ?_ 0 1
    unfold e
    fun_prop
  have hint_inner : ∀ m ∈ S, IntervalIntegrable
      (fun u : ℝ => ∑ n ∈ S, a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u)) volume 0 1 :=
    fun m _ => intervalIntegrable_finset_sum_local fun n _ => hint_term m n
  have hc_int : ((∫ u in (0 : ℝ)..1, ‖∑ n ∈ S, a n * e (u * ((n + K : ℤ) : ℝ))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ n ∈ S, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    have h1 : ∫ u in (0 : ℝ)..1, ((‖∑ n ∈ S, a n * e (u * ((n + K : ℤ) : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        ∫ u in (0 : ℝ)..1, ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u) :=
      intervalIntegral.integral_congr fun u _ => hnorm_sq u
    rw [h1, intervalIntegral_finset_sum_local hint_inner]
    have h2 : ∑ m ∈ S, ∫ u in (0 : ℝ)..1, ∑ n ∈ S, a m * star (a n) * e (((m : ℤ) - (n : ℤ)) * u) =
        ∑ m ∈ S, ∑ n ∈ S, a m * star (a n) * ∫ u in (0 : ℝ)..1, e (((m : ℤ) - (n : ℤ)) * u) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral_finset_sum_local (fun n _ => hint_term m n)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    rw [h2]
    have hint_mn : ∀ m n : ℕ,
        ∫ u in (0 : ℝ)..1, e ((((m : ℤ) : ℝ) - ((n : ℤ) : ℝ)) * u) = if m = n then 1 else 0 := by
      intro m n
      rw [show ((m : ℤ) : ℝ) - ((n : ℤ) : ℝ) = (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) by push_cast; ring,
        integral_e_int_mul]
      simp [sub_eq_zero]
    simp_rw [hint_mn]
    push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m]
    · simp only [↓reduceIte, mul_one, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow]
    · intro n _ hnm
      simp [Ne.symm hnm]
    · intro hnot
      exact absurd hm hnot
  exact Complex.ofReal_injective hc_int

private theorem integral_norm_sq_deriv_trigPoly_shift (a : ℕ → ℂ) (M N : ℕ) (K : ℤ) :
    ∫ u in (0 : ℝ)..1,
        ‖∑ n ∈ Finset.Ioc M (M + N),
          a n * (2 * Real.pi * ((n + K : ℤ) : ℝ) * Complex.I) * e (u * (n + K : ℤ))‖ ^ 2 =
      ∑ n ∈ Finset.Ioc M (M + N), (2 * Real.pi * ((n + K : ℤ) : ℝ)) ^ 2 * ‖a n‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => a n * (2 * Real.pi * ((n + K : ℤ) : ℝ) * Complex.I)
  have h := integral_norm_sq_trigPoly_shift b M N K
  rw [h]
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp [b]
  rw [norm_mul]
  have hnorm' : ‖2 * (Real.pi : ℂ) * ((n + K : ℤ) : ℂ) * Complex.I‖ =
      |2 * Real.pi * ((n + K : ℤ) : ℝ)| := by
    have hrew : (2 * (Real.pi : ℂ) * ((n + K : ℤ) : ℂ) * Complex.I) =
        ((2 * Real.pi * ((n + K : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hrew, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm', mul_pow, sq_abs, mul_comm]

/-- **Gallagher's Sobolev Large Sieve**:
for any finite `δ`-well-spaced family `α` mod `1` (`0 < δ ≤ 1`),
`∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤ (Real.pi * N + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2`. -/
theorem gallagher_large_sieve {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (a : ℕ → ℂ) (M N : ℕ) :
    ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trigPoly]
  let K : ℤ := -(M : ℤ) - ((N - 1) / 2 : ℕ) - 1
  let f : ℝ → ℂ := fun u => ∑ n ∈ Finset.Ioc M (M + N), a n * e (u * ((n + K : ℤ) : ℝ))
  let f' : ℝ → ℂ := fun u => ∑ n ∈ Finset.Ioc M (M + N),
    a n * (2 * Real.pi * ((n + K : ℤ) : ℝ) * Complex.I) * e (u * ((n + K : ℤ) : ℝ))
  have hf_eq_norm : ∀ u : ℝ, ‖f u‖ = ‖trigPoly a M N u‖ := by
    intro u
    have hshift : f u = e (u * (K : ℝ)) * trigPoly a M N u := by
      dsimp [f, trigPoly]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have he : e (u * (K : ℝ)) * e (u * (n : ℝ)) = e (u * ((n + K : ℤ) : ℝ)) := by
        rw [← e_add]
        congr 1
        push_cast
        ring
      calc
        a n * e (u * ((n + K : ℤ) : ℝ))
            = a n * (e (u * (K : ℝ)) * e (u * (n : ℝ))) := by rw [he]
        _ = e (u * (K : ℝ)) * (a n * e (u * (n : ℝ))) := by ring
    rw [hshift, norm_mul, norm_e, one_mul]
  have hf_per : Function.Periodic f 1 := by
    intro u
    dsimp [f]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h : (u + 1) * ((n + K : ℤ) : ℝ) = u * ((n + K : ℤ) : ℝ) + (n + K : ℤ) := by
      push_cast; ring
    rw [h, e_add_int]
  have hf'_per : Function.Periodic f' 1 := by
    intro u
    dsimp [f']
    refine Finset.sum_congr rfl fun n _ => ?_
    have h : (u + 1) * ((n + K : ℤ) : ℝ) = u * ((n + K : ℤ) : ℝ) + (n + K : ℤ) := by
      push_cast; ring
    rw [h, e_add_int]
  have hf_diff : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    have hterm : ∀ n ∈ Finset.Ioc M (M + N),
        HasDerivAt (fun u : ℝ => a n * e (u * ((n + K : ℤ) : ℝ)))
          (a n * (2 * Real.pi * ((n + K : ℤ) : ℝ) * Complex.I) * e (t * ((n + K : ℤ) : ℝ))) t := by
      intro n _
      have he := hasDerivAt_e_mul ((n + K : ℤ) : ℝ) t
      have he' : HasDerivAt (fun u : ℝ => e (u * ((n + K : ℤ) : ℝ)))
          ((2 * Real.pi * ((n + K : ℤ) : ℝ) * Complex.I) * e (t * ((n + K : ℤ) : ℝ))) t := by
        simpa only [mul_comm _ ((n + K : ℤ) : ℝ)] using he
      exact (he'.const_mul (a n)).congr_deriv (by ring)
    simpa only [f, f'] using HasDerivAt.fun_sum hterm
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf_diff t).continuousAt
  have hf'_cont : Continuous f' := by
    dsimp [f', e]
    fun_prop
  have hsob : ∀ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      δ⁻¹ * (∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ ^ 2) +
        ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ * ‖f' u‖ := by
    intro r _
    rw [← hf_eq_norm (α r)]
    exact gallagher_sobolev_sq_midpoint hws.1 (fun t _ => hf_diff t) hf'_cont.continuousOn
  have hF1_per : Function.Periodic (fun u => ‖f u‖ ^ 2) 1 := fun u => by simp [hf_per u]
  have hF2_per : Function.Periodic (fun u => ‖f u‖ * ‖f' u‖) 1 := fun u => by
    simp [hf_per u, hf'_per u]
  have hF1_int : IntervalIntegrable (fun u => ‖f u‖ ^ 2) volume 0 1 :=
    (hf_cont.norm.pow 2).intervalIntegrable 0 1
  have hF2_int : IntervalIntegrable (fun u => ‖f u‖ * ‖f' u‖) volume 0 1 :=
    (hf_cont.norm.mul hf'_cont.norm).intervalIntegrable 0 1
  have hsum_sob : ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      δ⁻¹ * (∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ ^ 2) +
        ∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ * ‖f' u‖ := by
    calc
      ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2
          ≤ ∑ r ∈ J, (δ⁻¹ * (∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ ^ 2) +
              ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ * ‖f' u‖) := Finset.sum_le_sum hsob
      _ = δ⁻¹ * (∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ ^ 2) +
            ∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ * ‖f' u‖ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  have h1 := sum_integral_wellSpaced_le J α hws (fun u => sq_nonneg _) hF1_per hF1_int
  have h2 := sum_integral_wellSpaced_le J α hws (fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hF2_per hF2_int
  have hcs : ∫ u in (0 : ℝ)..1, ‖f u‖ * ‖f' u‖ ≤
      Real.sqrt (∫ u in (0 : ℝ)..1, ‖f u‖ ^ 2) * Real.sqrt (∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2) := by
    have hint_sq1 : IntervalIntegrable (fun u => ‖f u‖ ^ 2) volume 0 1 := hF1_int
    have hint_sq2 : IntervalIntegrable (fun u => ‖f' u‖ ^ 2) volume 0 1 :=
      (hf'_cont.norm.pow 2).intervalIntegrable 0 1
    let A := ∫ u in (0 : ℝ)..1, ‖f u‖ ^ 2
    let B := ∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2
    let C := ∫ u in (0 : ℝ)..1, ‖f u‖ * ‖f' u‖
    have hA : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one fun u _ => sq_nonneg _
    have hB : 0 ≤ B := intervalIntegral.integral_nonneg zero_le_one fun u _ => sq_nonneg _
    have hC : 0 ≤ C := intervalIntegral.integral_nonneg zero_le_one fun u _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B := by
      intro t
      have hnn : 0 ≤ ∫ u in (0 : ℝ)..1, (t * ‖f u‖ - ‖f' u‖) ^ 2 :=
        intervalIntegral.integral_nonneg zero_le_one fun u _ => sq_nonneg _
      have hexp : ∫ u in (0 : ℝ)..1, (t * ‖f u‖ - ‖f' u‖) ^ 2 = t ^ 2 * A - 2 * t * C + B := by
        have hid : ∀ u, (t * ‖f u‖ - ‖f' u‖) ^ 2 =
            t ^ 2 * ‖f u‖ ^ 2 - 2 * t * (‖f u‖ * ‖f' u‖) + ‖f' u‖ ^ 2 := fun u => by ring
        simp_rw [hid]
        rw [intervalIntegral.integral_add ((hint_sq1.const_mul (t ^ 2)).sub (hF2_int.const_mul (2 * t)))
          hint_sq2,
          intervalIntegral.integral_sub (hint_sq1.const_mul (t ^ 2)) (hF2_int.const_mul (2 * t)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      linarith
    have hC_sq : C ^ 2 ≤ A * B := by
      rcases eq_or_lt_of_le hA with hA0 | hApos
      · have hC0 : C = 0 := by
          by_contra hCne
          have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCne)
          have hq' := hquad ((B + 1) / (2 * C))
          rw [← hA0, mul_zero, zero_sub] at hq'
          have hcalc : -2 * ((B + 1) / (2 * C)) * C + B = -1 := by
            field_simp [hCpos.ne']
            ring
          linarith
        rw [hC0, ← hA0]
        norm_num
      · have hq := hquad (C / A)
        have hcalc : (C / A) ^ 2 * A - 2 * (C / A) * C + B = (A * B - C ^ 2) / A := by
          field_simp [hApos.ne']
          ring
        rw [hcalc, div_nonneg_iff] at hq
        rcases hq with ⟨h1', _⟩ | ⟨_, h2'⟩
        · linarith
        · linarith
    calc
      C = Real.sqrt (C ^ 2) := (Real.sqrt_sq hC).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hC_sq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  have hI1 : ∫ u in (0 : ℝ)..1, ‖f u‖ ^ 2 = ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
    integral_norm_sq_trigPoly_shift a M N K
  have hI2 : ∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2 =
      ∑ n ∈ Finset.Ioc M (M + N), (2 * Real.pi * ((n + K : ℤ) : ℝ)) ^ 2 * ‖a n‖ ^ 2 :=
    integral_norm_sq_deriv_trigPoly_shift a M N K
  have hbound_K : ∀ n ∈ Finset.Ioc M (M + N), |((n + K : ℤ) : ℝ)| ≤ (N : ℝ) / 2 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hdiv : 2 * ((N - 1) / 2) ≤ N - 1 := Nat.mul_div_le (N - 1) 2
    have hdiv2 : N - 1 ≤ 2 * ((N - 1) / 2) + 1 := by omega
    rw [abs_le]
    constructor
    · have h1' : -(N : ℤ) ≤ 2 * ((n : ℤ) + K) := by
        dsimp [K]
        omega
      have h1R : -(N : ℝ) ≤ 2 * ((n + K : ℤ) : ℝ) := by exact_mod_cast h1'
      linarith
    · have h2' : 2 * ((n : ℤ) + K) ≤ (N : ℤ) := by
        dsimp [K]
        omega
      have h2R : 2 * ((n + K : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2'
      linarith
  have hI2_le : ∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2 ≤
      (Real.pi * (N : ℝ)) ^ 2 * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
    rw [hI2, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have habs : |2 * Real.pi * ((n + K : ℤ) : ℝ)| ≤ Real.pi * (N : ℝ) := by
      rw [abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]
      have hnK := hbound_K n hn
      calc
        2 * Real.pi * |((n + K : ℤ) : ℝ)| ≤ 2 * Real.pi * ((N : ℝ) / 2) := by
          gcongr
        _ = Real.pi * (N : ℝ) := by ring
    calc
      (2 * Real.pi * ((n + K : ℤ) : ℝ)) ^ 2 = |2 * Real.pi * ((n + K : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.pi * (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
  let S2 : ℝ := ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2
  have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt_I2 : Real.sqrt (∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2) ≤ Real.pi * (N : ℝ) * Real.sqrt S2 := by
    calc
      Real.sqrt (∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2)
          ≤ Real.sqrt ((Real.pi * (N : ℝ)) ^ 2 * S2) := Real.sqrt_le_sqrt hI2_le
      _ = Real.sqrt ((Real.pi * (N : ℝ)) ^ 2) * Real.sqrt S2 := Real.sqrt_mul (sq_nonneg _) _
      _ = Real.pi * (N : ℝ) * Real.sqrt S2 := by
          rw [Real.sqrt_sq (by positivity)]
  have h2_bound : ∫ u in (0 : ℝ)..1, ‖f u‖ * ‖f' u‖ ≤ Real.pi * (N : ℝ) * S2 := by
    calc
      ∫ u in (0 : ℝ)..1, ‖f u‖ * ‖f' u‖
          ≤ Real.sqrt S2 * Real.sqrt (∫ u in (0 : ℝ)..1, ‖f' u‖ ^ 2) := by rwa [hI1] at hcs
      _ ≤ Real.sqrt S2 * (Real.pi * (N : ℝ) * Real.sqrt S2) := by
          gcongr
      _ = Real.pi * (N : ℝ) * (Real.sqrt S2 * Real.sqrt S2) := by ring
      _ = Real.pi * (N : ℝ) * S2 := by rw [Real.mul_self_sqrt hS2_nn]
  calc
    ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2
        ≤ δ⁻¹ * (∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ ^ 2) +
            ∑ r ∈ J, ∫ u in (α r - δ / 2)..(α r + δ / 2), ‖f u‖ * ‖f' u‖ := hsum_sob
    _ ≤ δ⁻¹ * (∫ u in (0 : ℝ)..1, ‖f u‖ ^ 2) + ∫ u in (0 : ℝ)..1, ‖f u‖ * ‖f' u‖ := by
        gcongr; exact (inv_pos.mpr hws.1).le
    _ ≤ δ⁻¹ * S2 + Real.pi * (N : ℝ) * S2 := by
        rw [hI1]; gcongr
    _ = (Real.pi * (N : ℝ) + δ⁻¹) * S2 := by ring

end GallagherSobolev

/-! ### Finite-Dimensional Duality Principle -/

section DualityPrinciple

/-- **Finite-dimensional duality principle** (equivalence of operator norm, bilinear form, and
adjoint operator norm bounds): for any finite index sets `I : Finset ι`, `J : Finset κ`, matrix
`c : κ → ι → ℂ`, and `0 ≤ D`, the three `L²` bounds are equivalent. -/
theorem duality_iff_bilinear_iff_dual {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (c : κ → ι → ℂ) {D : ℝ} (hD : 0 ≤ D) :
    ((∀ a : ι → ℂ, ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤ D * ∑ n ∈ I, ‖a n‖ ^ 2) ↔
      (∀ (a : ι → ℂ) (b : κ → ℂ),
        ‖∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n‖ ^ 2 ≤
          D * (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2))) ∧
    ((∀ (a : ι → ℂ) (b : κ → ℂ),
        ‖∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n‖ ^ 2 ≤
          D * (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2)) ↔
      (∀ b : κ → ℂ, ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ D * ∑ r ∈ J, ‖b r‖ ^ 2)) := by
  have h12 :
      (∀ a : ι → ℂ, ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤ D * ∑ n ∈ I, ‖a n‖ ^ 2) ↔
        (∀ (a : ι → ℂ) (b : κ → ℂ),
          ‖∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n‖ ^ 2 ≤
            D * (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2)) := by
    constructor
    · intro hI a b
      have hrewrite : ∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n =
          ∑ r ∈ J, (∑ n ∈ I, a n * c r n) * star (b r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
      rw [hrewrite]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq J
        (fun r => ‖∑ n ∈ I, a n * c r n‖) (fun r => ‖b r‖)
      have hnorm : ‖∑ r ∈ J, (∑ n ∈ I, a n * c r n) * star (b r)‖ ≤
          ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ * ‖b r‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [norm_mul, norm_star]
      have hsq : ‖∑ r ∈ J, (∑ n ∈ I, a n * c r n) * star (b r)‖ ^ 2 ≤
          (∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ * ‖b r‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      calc
        ‖∑ r ∈ J, (∑ n ∈ I, a n * c r n) * star (b r)‖ ^ 2
            ≤ (∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2) := hsq.trans hcs
        _ ≤ (D * ∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2) := by
            gcongr
            exact hI a
    · intro hII a
      let b : κ → ℂ := fun r => ∑ n ∈ I, a n * c r n
      have hspec := hII a b
      have hrew : ∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n =
          ((∑ r ∈ J, ‖b r‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun r _ => ?_
        have h1 : ∑ n ∈ I, a n * star (b r) * c r n = b r * star (b r) := by
          dsimp [b]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
        rw [h1, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [hrew, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hspec
      let S := ∑ r ∈ J, ‖b r‖ ^ 2
      change S ^ 2 ≤ D * (∑ n ∈ I, ‖a n‖ ^ 2) * S at hspec
      have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rcases eq_or_lt_of_le hSnn with hS0 | hSpos
      · change S ≤ D * ∑ n ∈ I, ‖a n‖ ^ 2
        rw [← hS0]
        exact mul_nonneg hD (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      · change S ≤ D * ∑ n ∈ I, ‖a n‖ ^ 2
        nlinarith
  have h23 :
      (∀ (a : ι → ℂ) (b : κ → ℂ),
          ‖∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n‖ ^ 2 ≤
            D * (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2)) ↔
        (∀ b : κ → ℂ, ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ D * ∑ r ∈ J, ‖b r‖ ^ 2) := by
    constructor
    · intro hII b
      let a : ι → ℂ := fun n => star (∑ r ∈ J, b r * c r n)
      have hspec := hII a (fun r => star (b r))
      have ha_norm : ∑ n ∈ I, ‖a n‖ ^ 2 = ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp [a]
        simp only [Complex.norm_conj]
      have hb_norm : ∑ r ∈ J, ‖star (b r)‖ ^ 2 = ∑ r ∈ J, ‖b r‖ ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [Complex.star_def, Complex.norm_conj]
      have hrew : ∑ r ∈ J, ∑ n ∈ I, a n * star (star (b r)) * c r n =
          ((∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 : ℝ) : ℂ) := by
        rw [Finset.sum_comm]
        push_cast
        refine Finset.sum_congr rfl fun n _ => ?_
        have h1 : ∑ r ∈ J, a n * star (star (b r)) * c r n =
            star (∑ r ∈ J, b r * c r n) * (∑ r ∈ J, b r * c r n) := by
          dsimp [a]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [Complex.conj_conj]
          ring
        rw [h1, mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.ofReal_pow]
      rw [hrew, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        ha_norm, hb_norm] at hspec
      let S := ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2
      change S ^ 2 ≤ D * S * ∑ r ∈ J, ‖b r‖ ^ 2 at hspec
      have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rcases eq_or_lt_of_le hSnn with hS0 | hSpos
      · change S ≤ D * ∑ r ∈ J, ‖b r‖ ^ 2
        rw [← hS0]
        exact mul_nonneg hD (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      · change S ≤ D * ∑ r ∈ J, ‖b r‖ ^ 2
        nlinarith
    · intro hIII a b
      have hrewrite : ∑ r ∈ J, ∑ n ∈ I, a n * star (b r) * c r n =
          ∑ n ∈ I, a n * (∑ r ∈ J, star (b r) * c r n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [hrewrite]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
        (fun n => ‖a n‖) (fun n => ‖∑ r ∈ J, star (b r) * c r n‖)
      have hnorm : ‖∑ n ∈ I, a n * (∑ r ∈ J, star (b r) * c r n)‖ ≤
          ∑ n ∈ I, ‖a n‖ * ‖∑ r ∈ J, star (b r) * c r n‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul]
      have hsq : ‖∑ n ∈ I, a n * (∑ r ∈ J, star (b r) * c r n)‖ ^ 2 ≤
          (∑ n ∈ I, ‖a n‖ * ‖∑ r ∈ J, star (b r) * c r n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hb_star := hIII (fun r => star (b r))
      have hb_norm : ∑ r ∈ J, ‖star (b r)‖ ^ 2 = ∑ r ∈ J, ‖b r‖ ^ 2 :=
        Finset.sum_congr rfl fun r _ => by simp only [Complex.star_def, Complex.norm_conj]
      rw [hb_norm] at hb_star
      calc
        ‖∑ n ∈ I, a n * (∑ r ∈ J, star (b r) * c r n)‖ ^ 2
            ≤ (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ n ∈ I, ‖∑ r ∈ J, star (b r) * c r n‖ ^ 2) := hsq.trans hcs
        _ ≤ (∑ n ∈ I, ‖a n‖ ^ 2) * (D * ∑ r ∈ J, ‖b r‖ ^ 2) := by
            gcongr
        _ = D * (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ r ∈ J, ‖b r‖ ^ 2) := by ring
  exact ⟨h12, h23⟩

/-- Equivalence between operator norm bound `∑_r ‖∑_n a_n c_{r,n}‖² ≤ D ∑_n ‖a_n‖²` and its dual
`∑_n ‖∑_r b_r c_{r,n}‖² ≤ D ∑_r ‖b_r‖²` for `0 ≤ D`. -/
theorem duality_iff {ι κ : Type*} (I : Finset ι) (J : Finset κ) (c : κ → ι → ℂ)
    {D : ℝ} (hD : 0 ≤ D) :
    (∀ a : ι → ℂ, ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤ D * ∑ n ∈ I, ‖a n‖ ^ 2) ↔
      (∀ b : κ → ℂ, ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ D * ∑ r ∈ J, ‖b r‖ ^ 2) :=
  (duality_iff_bilinear_iff_dual I J c hD).1.trans (duality_iff_bilinear_iff_dual I J c hD).2

/-- Supremum form of the finite-dimensional duality principle:
`sup_{‖b‖ ≤ 1} ∑_n ‖∑_r b_r c_{r,n}‖² = sup_{‖a‖ ≤ 1} ∑_r ‖∑_n a_n c_{r,n}‖²`. -/
theorem duality_sSup_eq {ι κ : Type*} (I : Finset ι) (J : Finset κ) (c : κ → ι → ℂ) :
    sSup {x : ℝ | ∃ b : κ → ℂ, ∑ r ∈ J, ‖b r‖ ^ 2 ≤ 1 ∧
        x = ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2} =
      sSup {y : ℝ | ∃ a : ι → ℂ, ∑ n ∈ I, ‖a n‖ ^ 2 ≤ 1 ∧
        y = ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2} := by
  let S₁ : Set ℝ := {x : ℝ | ∃ b : κ → ℂ, ∑ r ∈ J, ‖b r‖ ^ 2 ≤ 1 ∧
    x = ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2}
  let S₂ : Set ℝ := {y : ℝ | ∃ a : ι → ℂ, ∑ n ∈ I, ‖a n‖ ^ 2 ≤ 1 ∧
    y = ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2}
  have hS₁_ne : S₁.Nonempty := ⟨0, fun _ => 0, by simp, by simp⟩
  have hS₂_ne : S₂.Nonempty := ⟨0, fun _ => 0, by simp, by simp⟩
  let M : ℝ := ∑ r ∈ J, ∑ n ∈ I, ‖c r n‖ ^ 2
  have hS₁_bdd : BddAbove S₁ := by
    refine ⟨M, ?_⟩
    rintro x ⟨b, hb, rfl⟩
    have hterm : ∀ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤
        (∑ r ∈ J, ‖b r‖ ^ 2) * (∑ r ∈ J, ‖c r n‖ ^ 2) := by
      intro n _
      have hnorm : ‖∑ r ∈ J, b r * c r n‖ ≤ ∑ r ∈ J, ‖b r‖ * ‖c r n‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => (norm_mul _ _).le)
      calc
        ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ (∑ r ∈ J, ‖b r‖ * ‖c r n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ ≤ (∑ r ∈ J, ‖b r‖ ^ 2) * (∑ r ∈ J, ‖c r n‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq J (fun r => ‖b r‖) (fun r => ‖c r n‖)
    calc
      ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2
          ≤ ∑ n ∈ I, (∑ r ∈ J, ‖b r‖ ^ 2) * (∑ r ∈ J, ‖c r n‖ ^ 2) := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ I, 1 * (∑ r ∈ J, ‖c r n‖ ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = M := by
          simp only [one_mul, M]
          exact Finset.sum_comm
  have hS₂_bdd : BddAbove S₂ := by
    refine ⟨M, ?_⟩
    rintro y ⟨a, ha, rfl⟩
    have hterm : ∀ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤
        (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ n ∈ I, ‖c r n‖ ^ 2) := by
      intro r _
      have hnorm : ‖∑ n ∈ I, a n * c r n‖ ≤ ∑ n ∈ I, ‖a n‖ * ‖c r n‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_mul _ _).le)
      calc
        ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤ (∑ n ∈ I, ‖a n‖ * ‖c r n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ ≤ (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ n ∈ I, ‖c r n‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖a n‖) (fun n => ‖c r n‖)
    calc
      ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2
          ≤ ∑ r ∈ J, (∑ n ∈ I, ‖a n‖ ^ 2) * (∑ n ∈ I, ‖c r n‖ ^ 2) := Finset.sum_le_sum hterm
      _ ≤ ∑ r ∈ J, 1 * (∑ n ∈ I, ‖c r n‖ ^ 2) := by
          refine Finset.sum_le_sum fun r _ => ?_
          exact mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = M := by simp [M]
  have hS₁_nn : 0 ≤ sSup S₁ := le_csSup hS₁_bdd ⟨fun _ => 0, by simp, by simp⟩
  have hS₂_nn : 0 ≤ sSup S₂ := le_csSup hS₂_bdd ⟨fun _ => 0, by simp, by simp⟩
  have hbound₂ : ∀ a : ι → ℂ, ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 ≤ sSup S₂ * ∑ n ∈ I, ‖a n‖ ^ 2 := by
    intro a
    let N := ∑ n ∈ I, ‖a n‖ ^ 2
    have hNnn : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases eq_or_lt_of_le hNnn with hN0 | hNpos
    · have ha0 : ∀ n ∈ I, a n = 0 := by
        intro n hn
        have hle : ‖a n‖ ^ 2 ≤ N :=
          Finset.single_le_sum (fun m _ => sq_nonneg ‖a m‖) hn
        have h0 : ‖a n‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
      have hzero : ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun r _ => by
          have hs0 : ∑ n ∈ I, a n * c r n = 0 :=
            Finset.sum_eq_zero fun n hn => by simp [ha0 n hn]
          simp [hs0]
      change _ ≤ sSup S₂ * N
      rw [hzero, ← hN0, mul_zero]
    · let a' : ι → ℂ := fun n => ((1 / Real.sqrt N : ℝ) : ℂ) * a n
      have ha'_norm : ∑ n ∈ I, ‖a' n‖ ^ 2 ≤ 1 := by
        have hsum : ∑ n ∈ I, ‖a' n‖ ^ 2 = N⁻¹ * N := by
          calc
            ∑ n ∈ I, ‖a' n‖ ^ 2 = ∑ n ∈ I, (1 / Real.sqrt N) ^ 2 * ‖a n‖ ^ 2 := by
              refine Finset.sum_congr rfl fun n _ => ?_
              dsimp [a']
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
            _ = (1 / Real.sqrt N) ^ 2 * N := by rw [← Finset.mul_sum]
            _ = N⁻¹ * N := by
              rw [div_pow, one_pow, Real.sq_sqrt hNpos.le, one_div]
        rw [hsum, inv_mul_cancel₀ hNpos.ne']
      have hmem : (∑ r ∈ J, ‖∑ n ∈ I, a' n * c r n‖ ^ 2) ∈ S₂ := ⟨a', ha'_norm, rfl⟩
      have hle := le_csSup hS₂_bdd hmem
      have heq : ∑ r ∈ J, ‖∑ n ∈ I, a' n * c r n‖ ^ 2 =
          N⁻¹ * ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 := by
        calc
          ∑ r ∈ J, ‖∑ n ∈ I, a' n * c r n‖ ^ 2
              = ∑ r ∈ J, (1 / Real.sqrt N) ^ 2 * ‖∑ n ∈ I, a n * c r n‖ ^ 2 := by
                refine Finset.sum_congr rfl fun r _ => ?_
                have hfac : ∑ n ∈ I, a' n * c r n =
                    ((1 / Real.sqrt N : ℝ) : ℂ) * ∑ n ∈ I, a n * c r n := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun n _ => by dsimp [a']; ring
                rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
          _ = (1 / Real.sqrt N) ^ 2 * ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 := by
                rw [← Finset.mul_sum]
          _ = N⁻¹ * ∑ r ∈ J, ‖∑ n ∈ I, a n * c r n‖ ^ 2 := by
                rw [div_pow, one_pow, Real.sq_sqrt hNpos.le, one_div]
      rw [heq, inv_mul_le_iff₀ hNpos, mul_comm N (sSup S₂)] at hle
      exact hle
  have hbound₁ : ∀ b : κ → ℂ, ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ sSup S₁ * ∑ r ∈ J, ‖b r‖ ^ 2 := by
    intro b
    let N := ∑ r ∈ J, ‖b r‖ ^ 2
    have hNnn : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases eq_or_lt_of_le hNnn with hN0 | hNpos
    · have hb0 : ∀ r ∈ J, b r = 0 := by
        intro r hr
        have hle : ‖b r‖ ^ 2 ≤ N :=
          Finset.single_le_sum (fun m _ => sq_nonneg ‖b m‖) hr
        have h0 : ‖b r‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
      have hzero : ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun n _ => by
          have hs0 : ∑ r ∈ J, b r * c r n = 0 :=
            Finset.sum_eq_zero fun r hr => by simp [hb0 r hr]
          simp [hs0]
      change _ ≤ sSup S₁ * N
      rw [hzero, ← hN0, mul_zero]
    · let b' : κ → ℂ := fun r => ((1 / Real.sqrt N : ℝ) : ℂ) * b r
      have hb'_norm : ∑ r ∈ J, ‖b' r‖ ^ 2 ≤ 1 := by
        have hsum : ∑ r ∈ J, ‖b' r‖ ^ 2 = N⁻¹ * N := by
          calc
            ∑ r ∈ J, ‖b' r‖ ^ 2 = ∑ r ∈ J, (1 / Real.sqrt N) ^ 2 * ‖b r‖ ^ 2 := by
              refine Finset.sum_congr rfl fun r _ => ?_
              dsimp [b']
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
            _ = (1 / Real.sqrt N) ^ 2 * N := by rw [← Finset.mul_sum]
            _ = N⁻¹ * N := by
              rw [div_pow, one_pow, Real.sq_sqrt hNpos.le, one_div]
        rw [hsum, inv_mul_cancel₀ hNpos.ne']
      have hmem : (∑ n ∈ I, ‖∑ r ∈ J, b' r * c r n‖ ^ 2) ∈ S₁ := ⟨b', hb'_norm, rfl⟩
      have hle := le_csSup hS₁_bdd hmem
      have heq : ∑ n ∈ I, ‖∑ r ∈ J, b' r * c r n‖ ^ 2 =
          N⁻¹ * ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 := by
        calc
          ∑ n ∈ I, ‖∑ r ∈ J, b' r * c r n‖ ^ 2
              = ∑ n ∈ I, (1 / Real.sqrt N) ^ 2 * ‖∑ r ∈ J, b r * c r n‖ ^ 2 := by
                refine Finset.sum_congr rfl fun n _ => ?_
                have hfac : ∑ r ∈ J, b' r * c r n =
                    ((1 / Real.sqrt N : ℝ) : ℂ) * ∑ r ∈ J, b r * c r n := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun r _ => by dsimp [b']; ring
                rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
          _ = (1 / Real.sqrt N) ^ 2 * ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 := by
                rw [← Finset.mul_sum]
          _ = N⁻¹ * ∑ n ∈ I, ‖∑ r ∈ J, b r * c r n‖ ^ 2 := by
                rw [div_pow, one_pow, Real.sq_sqrt hNpos.le, one_div]
      rw [heq, inv_mul_le_iff₀ hNpos, mul_comm N (sSup S₁)] at hle
      exact hle
  have h1_le_2 : sSup S₁ ≤ sSup S₂ := by
    refine csSup_le hS₁_ne ?_
    rintro x ⟨b, hb, rfl⟩
    have hdual := ((duality_iff I J c hS₂_nn).mp hbound₂) b
    exact hdual.trans (mul_le_of_le_one_right hS₂_nn hb)
  have h2_le_1 : sSup S₂ ≤ sSup S₁ := by
    refine csSup_le hS₂_ne ?_
    rintro y ⟨a, ha, rfl⟩
    have hdual := ((duality_iff I J c hS₁_nn).mpr hbound₁) a
    exact hdual.trans (mul_le_of_le_one_right hS₁_nn ha)
  exact le_antisymm h1_le_2 h2_le_1

end DualityPrinciple

/-! ### Hilbert's Inequality and Sharp Analytic Large Sieve -/

section HilbertAndAnalyticLargeSieve

private theorem sum_inv_sq_spaced_le {R : ℕ} {x : Fin R → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hx : ∀ i j : Fin R, i < j → δ ≤ x j - x i) (s : Fin R) :
    ∑ r : Fin R, (if r = s then 0 else (x r - x s)⁻¹ ^ 2) ≤ Real.pi ^ 2 * δ⁻¹ ^ 2 / 3 := by
  have hgap : ∀ i j : Fin R, i ≤ j → (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * δ ≤ x j - x i := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | _
    · simp
    · have hind : ∀ d : ℕ, ∀ (a b : Fin R), (b : ℕ) = (a : ℕ) + d → (d : ℝ) * δ ≤ x b - x a := by
        intro d
        induction d with
        | zero =>
          intro a b hab
          have : a = b := Fin.ext (by omega)
          subst this; simp
        | succ d ih =>
          intro a b hab
          have hm_lt : (a : ℕ) + d < R := by omega
          let m : Fin R := ⟨(a : ℕ) + d, hm_lt⟩
          have hm1 : (d : ℝ) * δ ≤ x m - x a := ih a m rfl
          have hm2 : δ ≤ x b - x m := hx m b (Fin.mk_lt_mk.mpr (by omega))
          push_cast
          linarith
      have hdiff : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by
        have : (i : ℕ) ≤ (j : ℕ) := hij
        omega
      exact hind ((j : ℕ) - (i : ℕ)) i j hdiff
  have hterm_le : ∀ r : Fin R,
      (if r = s then (0 : ℝ) else (x r - x s)⁻¹ ^ 2) ≤
        if r = s then 0 else δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ := by
    intro r
    split_ifs with hrs
    · exact le_rfl
    · have hne : (r : ℕ) ≠ (s : ℕ) := fun h => hrs (Fin.ext h)
      have hdist : (Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) * δ ≤ |x r - x s| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : r ≤ s := Fin.le_def.mpr hlt.le
          have hg := hgap r s hle
          have hab : Int.natAbs ((r : ℤ) - (s : ℤ)) = (s : ℕ) - (r : ℕ) := by omega
          have hnonneg : 0 ≤ x s - x r := by
            have h0 : 0 ≤ (((s : ℕ) - (r : ℕ) : ℕ) : ℝ) * δ := by positivity
            linarith
          rw [hab, abs_sub_comm, abs_of_nonneg hnonneg]
          exact hg
        · have hle : s ≤ r := Fin.le_def.mpr hgt.le
          have hg := hgap s r hle
          have hab : Int.natAbs ((r : ℤ) - (s : ℤ)) = (r : ℕ) - (s : ℕ) := by omega
          have hnonneg : 0 ≤ x r - x s := by
            have h0 : 0 ≤ (((r : ℕ) - (s : ℕ) : ℕ) : ℝ) * δ := by positivity
            linarith
          rw [hab, abs_of_nonneg hnonneg]
          exact hg
      have hnat_pos : 0 < Int.natAbs ((r : ℤ) - (s : ℤ)) := Int.natAbs_pos.mpr (by omega)
      have hk_pos : (0 : ℝ) < Int.natAbs ((r : ℤ) - (s : ℤ)) := Nat.cast_pos.mpr hnat_pos
      have hprod_pos : 0 < (Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) * δ := mul_pos hk_pos hδ
      have hinv_le : |x r - x s|⁻¹ ≤ δ⁻¹ * (Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ)⁻¹ := by
        rw [← mul_inv_rev]
        exact inv_anti₀ hprod_pos hdist
      calc
        (x r - x s)⁻¹ ^ 2 = |x r - x s|⁻¹ ^ 2 := by rw [← abs_inv, sq_abs]
        _ ≤ (δ⁻¹ * (Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ)⁻¹) ^ 2 :=
            pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) hinv_le 2
        _ = δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ := by
            rw [mul_pow, inv_pow, inv_pow]
  have hsplit : ∑ r : Fin R, (if r = s then (0 : ℝ) else δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹) ≤
      2 * δ⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ := by
    have hlt_eq : ∑ r ∈ Finset.univ.filter (· < s),
        ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ =
        ∑ k ∈ Finset.Icc 1 (s : ℕ), ((k : ℝ) ^ 2)⁻¹ := by
      refine Finset.sum_bij (fun r _ => (s : ℕ) - (r : ℕ)) ?_ ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr
        simp only [Finset.mem_Icc]
        omega
      · intro r₁ hr₁ r₂ hr₂ h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr₁ hr₂
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨⟨(s : ℕ) - k, by omega⟩, ?_, by simp; omega⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        omega
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr
        have hab : Int.natAbs ((r : ℤ) - (s : ℤ)) = (s : ℕ) - (r : ℕ) := by omega
        rw [hab]
    have hgt_eq : ∑ r ∈ Finset.univ.filter (s < ·),
        ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ =
        ∑ k ∈ Finset.Icc 1 (R - 1 - (s : ℕ)), ((k : ℝ) ^ 2)⁻¹ := by
      refine Finset.sum_bij (fun r _ => (r : ℕ) - (s : ℕ)) ?_ ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr
        simp only [Finset.mem_Icc]
        have hrlt : (r : ℕ) < R := r.isLt
        omega
      · intro r₁ hr₁ r₂ hr₂ h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr₁ hr₂
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        have hslt : (s : ℕ) < R := s.isLt
        refine ⟨⟨(s : ℕ) + k, by omega⟩, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        omega
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hr
        have hab : Int.natAbs ((r : ℤ) - (s : ℤ)) = (r : ℕ) - (s : ℕ) := by omega
        rw [hab]
    have hlt : ∑ r ∈ Finset.univ.filter (· < s),
        ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ ≤ ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ := by
      rw [hlt_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.le_of_lt s.isLt)) (fun _ _ _ => by positivity)
    have hgt : ∑ r ∈ Finset.univ.filter (s < ·),
        ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ ≤ ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ := by
      rw [hgt_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega)) (fun _ _ _ => by positivity)
    have hpart : (Finset.univ : Finset (Fin R)) =
        insert s (Finset.univ.filter (· < s) ∪ Finset.univ.filter (s < ·)) := by
      ext r
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, true_and,
        true_iff]
      rcases lt_trichotomy r s with hlt | rfl | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hgt)
    have hnot1 : s ∉ Finset.univ.filter (· < s) ∪ Finset.univ.filter (s < ·) := by simp
    have hdisj : Disjoint (Finset.univ.filter (· < s)) (Finset.univ.filter (s < ·)) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Finset.mem_filter] at hr1 hr2
      exact lt_asymm hr1.2 hr2.2
    calc
      ∑ r : Fin R, (if r = s then (0 : ℝ) else δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹)
          = ∑ r ∈ Finset.univ.filter (· < s), δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ +
              ∑ r ∈ Finset.univ.filter (s < ·), δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ := by
            conv_lhs => rw [hpart, Finset.sum_insert hnot1, Finset.sum_union hdisj]
            simp only [↓reduceIte, zero_add]
            congr 1
            · refine Finset.sum_congr rfl fun r hr => ?_
              have hne : r ≠ s := (Finset.mem_filter.mp hr).2.ne
              simp [hne]
            · refine Finset.sum_congr rfl fun r hr => ?_
              have hne : r ≠ s := (Finset.mem_filter.mp hr).2.ne'
              simp [hne]
      _ = δ⁻¹ ^ 2 * (∑ r ∈ Finset.univ.filter (· < s), ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹ +
            ∑ r ∈ Finset.univ.filter (s < ·), ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
      _ ≤ δ⁻¹ ^ 2 * (∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ + ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹) := by
            gcongr
      _ = 2 * δ⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ := by ring
  have hzeta2 : ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    have hsum_le : ∑ k ∈ Finset.Icc 1 R, (1 : ℝ) / (k : ℝ) ^ 2 ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
      hasSum_zeta_two.summable.sum_le_tsum (Finset.Icc 1 R) fun n _ => by positivity
    rw [hasSum_zeta_two.tsum_eq] at hsum_le
    simpa [one_div] using hsum_le
  calc
    ∑ r : Fin R, (if r = s then (0 : ℝ) else (x r - x s)⁻¹ ^ 2)
        ≤ ∑ r : Fin R, (if r = s then (0 : ℝ) else δ⁻¹ ^ 2 * ((Int.natAbs ((r : ℤ) - (s : ℤ)) : ℝ) ^ 2)⁻¹) :=
          Finset.sum_le_sum fun r _ => hterm_le r
    _ ≤ 2 * δ⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 R, ((k : ℝ) ^ 2)⁻¹ := hsplit
    _ ≤ 2 * δ⁻¹ ^ 2 * (Real.pi ^ 2 / 6) := by gcongr
    _ = Real.pi ^ 2 * δ⁻¹ ^ 2 / 3 := by ring

/-- **Montgomery–Vaughan / Hilbert's inequality on `ℝ`**:
if `x : Fin R → ℝ` satisfies `x j - x i ≥ δ > 0` for all `i < j`, then for any `u : Fin R → ℂ`,
`‖∑ r, ∑ s, (if r = s then 0 else u r * star (u s) / (x r - x s))‖ ≤ π * δ⁻¹ * ∑ r, ‖u r‖ ^ 2`. -/
theorem hilbert_inequality_real {R : ℕ} {x : Fin R → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hx : ∀ i j : Fin R, i < j → δ ≤ x j - x i) (u : Fin R → ℂ) :
    ‖∑ r : Fin R, ∑ s : Fin R,
        (if r = s then (0 : ℂ) else u r * star (u s) / ((x r - x s : ℝ) : ℂ))‖ ≤
      Real.pi * δ⁻¹ * ∑ r : Fin R, ‖u r‖ ^ 2 := by
  let A : Matrix (Fin R) (Fin R) ℂ := fun r s =>
    if r = s then 0 else -Complex.I / ((x r - x s : ℝ) : ℂ)
  have hA : A.IsHermitian := by
    ext r s
    rw [Matrix.conjTranspose_apply]
    dsimp [A]
    by_cases hrs : r = s
    · subst hrs
      simp
    · simp only [hrs, Ne.symm hrs, ↓reduceIte, map_div₀, map_neg,
        Complex.conj_I, neg_neg, Complex.conj_ofReal]
      have hne : ((x r : ℂ) - (x s : ℂ)) ≠ 0 := by
        have hneR : x r ≠ x s := by
          rcases lt_or_gt_of_ne hrs with h | h
          · linarith [hx r s h]
          · linarith [hx s r h]
        exact_mod_cast sub_ne_zero.mpr hneR
      have hne' : ((x s : ℂ) - (x r : ℂ)) ≠ 0 := by
        have : ((x s : ℂ) - (x r : ℂ)) = -((x r : ℂ) - (x s : ℂ)) := by ring
        rw [this]
        exact neg_ne_zero.mpr hne
      push_cast
      field_simp [hne, hne']
      ring
  have heig_bd : ∀ j : Fin R, |hA.eigenvalues j| ≤ Real.pi * δ⁻¹ := by
    intro j
    let lam : ℝ := hA.eigenvalues j
    let v : Fin R → ℂ := ⇑(hA.eigenvectorBasis j)
    have hv_norm : ∑ r : Fin R, ‖v r‖ ^ 2 = 1 := by
      have h1 : ‖hA.eigenvectorBasis j‖ ^ 2 = 1 := by
        rw [hA.eigenvectorBasis.orthonormal.1 j, one_pow]
      have h2 := EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis j)
      rw [h1] at h2
      exact h2.symm
    have hv_eig : A *ᵥ v = (lam : ℂ) • v := by
      simpa [v, lam, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis j
    have hv_coord : ∀ r : Fin R,
        ∑ s : Fin R, (if s = r then (0 : ℂ) else v s / ((x r - x s : ℝ) : ℂ)) =
          Complex.I * (lam : ℂ) * v r := by
      intro r
      have hrow := congrFun hv_eig r
      simp only [Matrix.mulVec, dotProduct, A, Pi.smul_apply, smul_eq_mul] at hrow
      have hmul := congrArg (Complex.I * ·) hrow
      rw [Finset.mul_sum] at hmul
      calc
        ∑ s : Fin R, (if s = r then (0 : ℂ) else v s / ((x r - x s : ℝ) : ℂ))
            = ∑ s : Fin R, Complex.I * ((if r = s then (0 : ℂ) else -Complex.I / ((x r - x s : ℝ) : ℂ)) * v s) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              by_cases hsr : s = r
              · simp [hsr]
              · simp only [hsr, Ne.symm hsr, ↓reduceIte]
                ring_nf
                rw [Complex.I_sq]
                ring
        _ = Complex.I * ((lam : ℂ) * v r) := hmul
        _ = Complex.I * (lam : ℂ) * v r := by ring
    have hlam_sq : ((lam ^ 2 : ℝ) : ℂ) =
        ∑ r : Fin R,
          (∑ s : Fin R, (if s = r then (0 : ℂ) else v s / ((x r - x s : ℝ) : ℂ))) *
          (∑ t : Fin R, (if t = r then (0 : ℂ) else star (v t) / ((x r - x t : ℝ) : ℂ))) := by
      have h1 : ((lam ^ 2 : ℝ) : ℂ) =
          ∑ r : Fin R, ((‖(lam : ℂ) * v r‖ ^ 2 : ℝ) : ℂ) := by
        have hr : ∑ r : Fin R, ‖(lam : ℂ) * v r‖ ^ 2 = lam ^ 2 * ∑ r : Fin R, ‖v r‖ ^ 2 := by
          simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
        rw [hv_norm, mul_one] at hr
        have hsumC : ((∑ r : Fin R, ‖(lam : ℂ) * v r‖ ^ 2 : ℝ) : ℂ) =
            ∑ r : Fin R, ((‖(lam : ℂ) * v r‖ ^ 2 : ℝ) : ℂ) := Complex.ofReal_sum _ _
        rw [← hsumC, hr]
      rw [h1]
      refine Finset.sum_congr rfl fun r _ => ?_
      have h2 : ((‖(lam : ℂ) * v r‖ ^ 2 : ℝ) : ℂ) =
          (Complex.I * (lam : ℂ) * v r) * star (Complex.I * (lam : ℂ) * v r) := by
        have hn : ‖Complex.I * (lam : ℂ) * v r‖ = ‖(lam : ℂ) * v r‖ := by
          rw [mul_assoc, norm_mul, Complex.norm_I, one_mul]
        rw [← hn, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [h2, ← hv_coord r, star_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp
    have hsum_expand :
        ∑ r : Fin R,
          (∑ s : Fin R, (if s = r then (0 : ℂ) else v s / ((x r - x s : ℝ) : ℂ))) *
          (∑ t : Fin R, (if t = r then (0 : ℂ) else star (v t) / ((x r - x t : ℝ) : ℂ))) =
        ∑ s : Fin R, ((‖v s‖ ^ 2 : ℝ) : ℂ) *
            ∑ r : Fin R, (if r = s then (0 : ℂ) else (((x r - x s)⁻¹ ^ 2 : ℝ) : ℂ)) +
          ∑ s : Fin R, ∑ t : Fin R,
            if s = t then 0 else
              v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
                ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                  ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) := by
      have hexp1 : ∀ r : Fin R,
          (∑ s : Fin R, (if s = r then (0 : ℂ) else v s / ((x r - x s : ℝ) : ℂ))) *
          (∑ t : Fin R, (if t = r then (0 : ℂ) else star (v t) / ((x r - x t : ℝ) : ℂ))) =
          ∑ s : Fin R, ∑ t : Fin R,
            if r = s ∨ r = t then 0 else
              v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹) := by
        intro r
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hsr : s = r <;> by_cases htr : t = r
        · simp [hsr, htr]
        · simp [hsr, htr]
        · simp [hsr, htr]
        · simp only [hsr, htr, Ne.symm hsr, Ne.symm htr, or_self, ↓reduceIte]
          ring
      simp_rw [hexp1]
      rw [Finset.sum_comm]
      have hswap2 : (∑ s : Fin R, ∑ r : Fin R, ∑ t : Fin R,
          if r = s ∨ r = t then (0 : ℂ) else
            v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹)) =
          ∑ s : Fin R, ∑ t : Fin R, ∑ r : Fin R,
            if r = s ∨ r = t then (0 : ℂ) else
              v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
      rw [hswap2]
      -- Split s = t and s ≠ t
      have hsplit_st : ∀ s : Fin R,
          (∑ t : Fin R, ∑ r : Fin R,
            if r = s ∨ r = t then (0 : ℂ) else
              v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹)) =
          ((‖v s‖ ^ 2 : ℝ) : ℂ) *
              ∑ r : Fin R, (if r = s then (0 : ℂ) else (((x r - x s)⁻¹ ^ 2 : ℝ) : ℂ)) +
            ∑ t : Fin R, if s = t then 0 else
              v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
                ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                  ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) := by
        intro s
        have hdiag_t :
            (∑ r : Fin R, if r = s ∨ r = s then (0 : ℂ) else
              v s * star (v s) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x s : ℝ) : ℂ)⁻¹)) =
            ((‖v s‖ ^ 2 : ℝ) : ℂ) *
              ∑ r : Fin R, (if r = s then (0 : ℂ) else (((x r - x s)⁻¹ ^ 2 : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hrs : r = s
          · simp [hrs]
          · simp only [hrs, or_self, ↓reduceIte, RCLike.star_def, Complex.mul_conj,
              Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Complex.ofReal_inv]
            ring
        have hoff_t : ∀ t : Fin R, s ≠ t →
            (∑ r : Fin R, if r = s ∨ r = t then (0 : ℂ) else
              v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹)) =
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) := by
          intro t hst
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hcond : r = s ∨ r = t
          · simp [hcond]
          · simp only [hcond, ↓reduceIte]
            rw [not_or] at hcond
            have h1 : ((x r - x s : ℝ) : ℂ) ≠ 0 := by
              have hne : x r ≠ x s := by
                rcases lt_or_gt_of_ne hcond.1 with h | h <;> linarith [hx _ _ h]
              exact_mod_cast sub_ne_zero.mpr hne
            have h2 : ((x r - x t : ℝ) : ℂ) ≠ 0 := by
              have hne : x r ≠ x t := by
                rcases lt_or_gt_of_ne hcond.2 with h | h <;> linarith [hx _ _ h]
              exact_mod_cast sub_ne_zero.mpr hne
            have h3 : ((x s - x t : ℝ) : ℂ) ≠ 0 := by
              have hne : x s ≠ x t := by
                rcases lt_or_gt_of_ne hst with h | h <;> linarith [hx _ _ h]
              exact_mod_cast sub_ne_zero.mpr hne
            push_cast at h1 h2 h3 ⊢
            field_simp [h1, h2, h3]
            ring
        calc
          (∑ t : Fin R, ∑ r : Fin R,
              if r = s ∨ r = t then (0 : ℂ) else
                v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹))
              = (∑ r : Fin R, if r = s ∨ r = s then (0 : ℂ) else
                  v s * star (v s) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x s : ℝ) : ℂ)⁻¹)) +
                ∑ t ∈ Finset.univ.erase s, ∑ r : Fin R,
                  if r = s ∨ r = t then (0 : ℂ) else
                    v s * star (v t) * (((x r - x s : ℝ) : ℂ)⁻¹ * ((x r - x t : ℝ) : ℂ)⁻¹) := by
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
          _ = ((‖v s‖ ^ 2 : ℝ) : ℂ) *
                ∑ r : Fin R, (if r = s then (0 : ℂ) else (((x r - x s)⁻¹ ^ 2 : ℝ) : ℂ)) +
              ∑ t : Fin R, if s = t then 0 else
                v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
                  ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                    ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) := by
                rw [hdiag_t]
                congr 1
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
                simp only [ite_true, zero_add]
                refine Finset.sum_congr rfl fun t ht => ?_
                have hst : s ≠ t := (Finset.mem_erase.mp ht).1.symm
                simp only [hst, ↓reduceIte]
                exact hoff_t t hst
      simp_rw [hsplit_st, Finset.sum_add_distrib]
    have hinner_split : ∀ s t : Fin R, s ≠ t →
        ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
            ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) =
          (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) -
            (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) +
            2 * ((x s - x t : ℝ) : ℂ)⁻¹ := by
      intro s t hst
      have hs_val : (∑ r : Fin R, if r = s ∨ r = t then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) =
          (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) -
            ((x t - x s : ℝ) : ℂ)⁻¹ := by
        have h1 : ∀ r : Fin R,
            (if r = s ∨ r = t then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) =
              (if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) -
                (if r = t then ((x t - x s : ℝ) : ℂ)⁻¹ else 0) := by
          intro r
          by_cases hrs : r = s <;> by_cases hrt : r = t
          · exact absurd (hrs.symm.trans hrt) hst
          · simp [hrs, hst]
          · simp [hrt, hst.symm]
          · simp [hrs, hrt]
        simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
        simp
      have ht_val : (∑ r : Fin R, if r = s ∨ r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) =
          (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) -
            ((x s - x t : ℝ) : ℂ)⁻¹ := by
        have h1 : ∀ r : Fin R,
            (if r = s ∨ r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) =
              (if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) -
                (if r = s then ((x s - x t : ℝ) : ℂ)⁻¹ else 0) := by
          intro r
          by_cases hrs : r = s <;> by_cases hrt : r = t
          · exact absurd (hrs.symm.trans hrt) hst
          · simp [hrs, hst]
          · simp [hrt, hst.symm]
          · simp [hrs, hrt]
        simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
        simp
      have hterm_sub : ∀ r : Fin R,
          (if r = s ∨ r = t then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹) =
          (if r = s ∨ r = t then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) -
          (if r = s ∨ r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) := fun r => by
        split_ifs <;> simp
      simp_rw [hterm_sub, Finset.sum_sub_distrib, hs_val, ht_val]
      have hneg_inv : ((x t - x s : ℝ) : ℂ)⁻¹ = -((x s - x t : ℝ) : ℂ)⁻¹ := by
        rw [show (x t - x s : ℝ) = -(x s - x t) by ring, Complex.ofReal_neg, inv_neg]
      rw [hneg_inv]
      ring
    have hoff_cancel :
        (∑ s : Fin R, ∑ t : Fin R,
          if s = t then (0 : ℂ) else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹)) =
        2 * ∑ s : Fin R, ∑ t : Fin R,
          if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ) := by
      have hrew : ∀ s t : Fin R,
          (if s = t then (0 : ℂ) else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              ∑ r : Fin R, (if r = s ∨ r = t then (0 : ℂ) else
                ((x r - x s : ℝ) : ℂ)⁻¹ - ((x r - x t : ℝ) : ℂ)⁻¹)) =
          (if s = t then 0 else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹)) -
          (if s = t then 0 else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹)) +
          (if s = t then 0 else
            2 * (v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ))) := by
        intro s t
        by_cases hst : s = t
        · simp [hst]
        · simp only [hst, ↓reduceIte, hinner_split s t hst, Complex.ofReal_pow, Complex.ofReal_inv]
          ring
      simp_rw [hrew, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h34 :
          (∑ s : Fin R, ∑ t : Fin R, if s = t then (0 : ℂ) else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹)) =
          (∑ s : Fin R, ∑ t : Fin R, if s = t then (0 : ℂ) else
            v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
              (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹)) := by
        have hS3 :
            (∑ s : Fin R, ∑ t : Fin R, if s = t then (0 : ℂ) else
              v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
                (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹)) =
            -Complex.I * (lam : ℂ) * ∑ s : Fin R, ((‖v s‖ ^ 2 : ℝ) : ℂ) *
              (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) := by
          calc
            _ = ∑ s : Fin R, v s * (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) *
                  (∑ t : Fin R, if t = s then (0 : ℂ) else star (v t) / ((x s - x t : ℝ) : ℂ)) := by
                refine Finset.sum_congr rfl fun s _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun t _ => ?_
                by_cases hst : s = t
                · simp [hst]
                · simp only [hst, Ne.symm hst, ↓reduceIte]; ring
            _ = ∑ s : Fin R, v s * (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) *
                  (-Complex.I * (lam : ℂ) * star (v s)) := by
                refine Finset.sum_congr rfl fun s _ => ?_
                have hstar := congrArg star (hv_coord s)
                rw [star_sum] at hstar
                have hstar_eq : (∑ t : Fin R, if t = s then (0 : ℂ) else star (v t) / ((x s - x t : ℝ) : ℂ)) =
                    ∑ t : Fin R, star (if t = s then (0 : ℂ) else v t / ((x s - x t : ℝ) : ℂ)) := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  split_ifs <;> simp
                rw [hstar_eq, hstar]
                simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
            _ = -Complex.I * (lam : ℂ) * ∑ s : Fin R, ((‖v s‖ ^ 2 : ℝ) : ℂ) *
                  (∑ r : Fin R, if r = s then (0 : ℂ) else ((x r - x s : ℝ) : ℂ)⁻¹) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun s _ => ?_
                have hvsq : v s * star (v s) = ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
                  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
                rw [← hvsq]
                ring
        have hS4 :
            (∑ s : Fin R, ∑ t : Fin R, if s = t then (0 : ℂ) else
              v s * star (v t) / ((x s - x t : ℝ) : ℂ) *
                (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹)) =
            -Complex.I * (lam : ℂ) * ∑ t : Fin R, ((‖v t‖ ^ 2 : ℝ) : ℂ) *
              (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) := by
          rw [Finset.sum_comm]
          calc
            _ = ∑ t : Fin R, star (v t) * (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) *
                  (∑ s : Fin R, if s = t then (0 : ℂ) else v s / ((x s - x t : ℝ) : ℂ)) := by
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun s _ => ?_
                by_cases hst : s = t
                · simp [hst]
                · simp only [hst, ↓reduceIte]; ring
            _ = ∑ t : Fin R, star (v t) * (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) *
                  (-Complex.I * (lam : ℂ) * v t) := by
                refine Finset.sum_congr rfl fun t _ => ?_
                have hneg : (∑ s : Fin R, if s = t then (0 : ℂ) else v s / ((x s - x t : ℝ) : ℂ)) =
                    -(∑ s : Fin R, if s = t then (0 : ℂ) else v s / ((x t - x s : ℝ) : ℂ)) := by
                  rw [← Finset.sum_neg_distrib]
                  refine Finset.sum_congr rfl fun s _ => ?_
                  split_ifs with hst
                  · simp
                  · rw [show (x s - x t : ℝ) = -(x t - x s) by ring, Complex.ofReal_neg, div_neg]
                rw [hneg, hv_coord t]
                ring
            _ = -Complex.I * (lam : ℂ) * ∑ t : Fin R, ((‖v t‖ ^ 2 : ℝ) : ℂ) *
                  (∑ r : Fin R, if r = t then (0 : ℂ) else ((x r - x t : ℝ) : ℂ)⁻¹) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun t _ => ?_
                have hvsq : v t * star (v t) = ((‖v t‖ ^ 2 : ℝ) : ℂ) := by
                  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
                rw [← hvsq]
                ring
        rw [hS3, hS4]
      rw [h34, sub_self, zero_add, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> ring
    have hlam_eq := hlam_sq.trans hsum_expand
    rw [hoff_cancel] at hlam_eq
    let S1 : ℝ := ∑ s : Fin R, ‖v s‖ ^ 2 *
      ∑ r : Fin R, (if r = s then (0 : ℝ) else (x r - x s)⁻¹ ^ 2)
    have hS1_eq : ((S1 : ℝ) : ℂ) =
        ∑ s : Fin R, ((‖v s‖ ^ 2 : ℝ) : ℂ) *
          ∑ r : Fin R, (if r = s then (0 : ℂ) else (((x r - x s)⁻¹ ^ 2 : ℝ) : ℂ)) := by
      dsimp [S1]
      push_cast
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp
    have hS5_norm : ‖∑ s : Fin R, ∑ t : Fin R,
        if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ)‖ ≤ S1 := by
      calc
        ‖∑ s : Fin R, ∑ t : Fin R,
            if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ)‖
            ≤ ∑ s : Fin R, ∑ t : Fin R,
                ‖if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ)‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => norm_sum_le _ _)
        _ ≤ ∑ s : Fin R, ∑ t : Fin R,
              (if s = t then (0 : ℝ) else ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) * (x s - x t)⁻¹ ^ 2) := by
            refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
            by_cases hst : s = t
            · simp [hst]
            · simp only [hst, ↓reduceIte, norm_mul, norm_star, Complex.norm_real,
                Real.norm_of_nonneg (sq_nonneg _)]
              have ham : ‖v s‖ * ‖v t‖ ≤ (‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2 := by
                nlinarith [sq_nonneg (‖v s‖ - ‖v t‖)]
              exact mul_le_mul_of_nonneg_right ham (sq_nonneg _)
        _ = (1 / 2 : ℝ) * (∑ s : Fin R, ‖v s‖ ^ 2 *
                ∑ t : Fin R, (if t = s then (0 : ℝ) else (x t - x s)⁻¹ ^ 2)) +
              (1 / 2 : ℝ) * (∑ t : Fin R, ‖v t‖ ^ 2 *
                ∑ s : Fin R, (if s = t then (0 : ℝ) else (x s - x t)⁻¹ ^ 2)) := by
            have hhalf : ∀ s t : Fin R,
                (if s = t then (0 : ℝ) else ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) * (x s - x t)⁻¹ ^ 2) =
                (1 / 2 : ℝ) * (‖v s‖ ^ 2 * (if t = s then (0 : ℝ) else (x t - x s)⁻¹ ^ 2)) +
                (1 / 2 : ℝ) * (‖v t‖ ^ 2 * (if s = t then (0 : ℝ) else (x s - x t)⁻¹ ^ 2)) := by
              intro s t
              by_cases hst : s = t
              · simp [hst]
              · simp only [hst, Ne.symm hst, ↓reduceIte]
                have hsq : (x t - x s)⁻¹ ^ 2 = (x s - x t)⁻¹ ^ 2 := by
                  rw [show x t - x s = -(x s - x t) by ring, inv_neg, neg_sq]
                rw [hsq]
                ring
            simp_rw [hhalf, Finset.sum_add_distrib]
            congr 1
            · simp_rw [← Finset.mul_sum]
            · rw [Finset.sum_comm]
              simp_rw [← Finset.mul_sum]
        _ = S1 := by dsimp [S1]; ring
    have hS1_le : S1 ≤ Real.pi ^ 2 * δ⁻¹ ^ 2 / 3 := by
      calc
        S1 ≤ ∑ s : Fin R, ‖v s‖ ^ 2 * (Real.pi ^ 2 * δ⁻¹ ^ 2 / 3) := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact mul_le_mul_of_nonneg_left (sum_inv_sq_spaced_le hδ hx s) (sq_nonneg _)
        _ = (∑ s : Fin R, ‖v s‖ ^ 2) * (Real.pi ^ 2 * δ⁻¹ ^ 2 / 3) := by rw [← Finset.sum_mul]
        _ = Real.pi ^ 2 * δ⁻¹ ^ 2 / 3 := by rw [hv_norm, one_mul]
    have hlam_norm : lam ^ 2 ≤ 3 * S1 := by
      have hnorm_eq := congrArg norm hlam_eq
      rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg lam), ← hS1_eq] at hnorm_eq
      calc
        lam ^ 2 ≤ ‖((S1 : ℝ) : ℂ)‖ + ‖2 * ∑ s : Fin R, ∑ t : Fin R,
            if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ)‖ :=
          hnorm_eq.le.trans (norm_add_le _ _)
        _ = S1 + 2 * ‖∑ s : Fin R, ∑ t : Fin R,
            if s = t then (0 : ℂ) else v s * star (v t) * (((x s - x t)⁻¹ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun s _ =>
            mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun t _ => by split_ifs <;> positivity)),
            norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
        _ ≤ S1 + 2 * S1 := by gcongr
        _ = 3 * S1 := by ring
    have hlam_sq_le : lam ^ 2 ≤ (Real.pi * δ⁻¹) ^ 2 := by
      calc
        lam ^ 2 ≤ 3 * S1 := hlam_norm
        _ ≤ 3 * (Real.pi ^ 2 * δ⁻¹ ^ 2 / 3) := by gcongr
        _ = (Real.pi * δ⁻¹) ^ 2 := by ring
    have hpi_nn : 0 ≤ Real.pi * δ⁻¹ := mul_nonneg Real.pi_pos.le (inv_pos.mpr hδ).le
    rw [← abs_of_nonneg hpi_nn]
    exact sq_le_sq.mp (by simpa [sq_abs] using hlam_sq_le)
  -- Express bilinear form in the orthonormal eigenvector basis
  let b := hA.eigenvectorBasis
  let uVec : EuclideanSpace ℂ (Fin R) := WithLp.toLp 2 u
  have hinner_eq :
      ⟪uVec, Matrix.toEuclideanLin A uVec⟫_ℂ =
        -Complex.I * ∑ r : Fin R, ∑ s : Fin R,
          (if r = s then (0 : ℂ) else star (u r) * u s / ((x r - x s : ℝ) : ℂ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, uVec, WithLp.ofLp_toLp, dotProduct, Matrix.mulVec]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [A]
    split_ifs <;> ring
  have hspec_sum :
      ⟪uVec, Matrix.toEuclideanLin A uVec⟫_ℂ =
        ∑ j : Fin R, ((hA.eigenvalues j : ℝ) : ℂ) * ((‖⟪b j, uVec⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    have hu_exp : uVec = ∑ j : Fin R, ⟪b j, uVec⟫_ℂ • b j := (b.sum_repr' uVec).symm
    have hAu : Matrix.toEuclideanLin A uVec =
        ∑ j : Fin R, (⟪b j, uVec⟫_ℂ * (hA.eigenvalues j : ℂ)) • b j := by
      calc
        Matrix.toEuclideanLin A uVec
            = Matrix.toEuclideanLin A (∑ j : Fin R, ⟪b j, uVec⟫_ℂ • b j) := by rw [← hu_exp]
        _ = ∑ j : Fin R, ⟪b j, uVec⟫_ℂ • Matrix.toEuclideanLin A (b j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => map_smul _ _ _
        _ = ∑ j : Fin R, (⟪b j, uVec⟫_ℂ * (hA.eigenvalues j : ℂ)) • b j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have heig : Matrix.toEuclideanLin A (b j) = (hA.eigenvalues j : ℂ) • b j := by
              ext k
              have hmv := congrFun (hA.mulVec_eigenvectorBasis j) k
              simpa [Matrix.toLpLin_apply, b, RCLike.real_smul_eq_coe_smul] using hmv
            rw [heig, smul_smul]
    rw [hAu, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    have h1 : ⟪uVec, b j⟫_ℂ = star ⟪b j, uVec⟫_ℂ := by
      simp
    have h2 : star ⟪b j, uVec⟫_ℂ * ⟪b j, uVec⟫_ℂ = ((‖⟪b j, uVec⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow]
    calc
      (⟪b j, uVec⟫_ℂ * (hA.eigenvalues j : ℂ)) * ⟪uVec, b j⟫_ℂ
          = (hA.eigenvalues j : ℂ) * (star ⟪b j, uVec⟫_ℂ * ⟪b j, uVec⟫_ℂ) := by
            rw [h1]; ring
      _ = ((hA.eigenvalues j : ℝ) : ℂ) * ((‖⟪b j, uVec⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by rw [h2]
  have hnorm_parseval : ∑ j : Fin R, ‖⟪b j, uVec⟫_ℂ‖ ^ 2 = ∑ r : Fin R, ‖u r‖ ^ 2 := by
    have h1 : ∑ j : Fin R, ‖⟪b j, uVec⟫_ℂ‖ ^ 2 = ‖uVec‖ ^ 2 :=
      b.sum_sq_norm_inner_right uVec
    have h2 : ‖uVec‖ ^ 2 = ∑ r : Fin R, ‖u r‖ ^ 2 := by
      simpa [uVec] using EuclideanSpace.norm_sq_eq uVec
    exact h1.trans h2
  have hstar_sum :
      ‖∑ r : Fin R, ∑ s : Fin R,
          (if r = s then (0 : ℂ) else u r * star (u s) / ((x r - x s : ℝ) : ℂ))‖ =
        ‖⟪uVec, Matrix.toEuclideanLin A uVec⟫_ℂ‖ := by
    rw [hinner_eq, norm_mul, norm_neg, Complex.norm_I, one_mul]
    rw [← norm_star]
    congr 1
    rw [star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [hstar_sum, hspec_sum]
  calc
    ‖∑ j : Fin R, ((hA.eigenvalues j : ℝ) : ℂ) * ((‖⟪b j, uVec⟫_ℂ‖ ^ 2 : ℝ) : ℂ)‖
        ≤ ∑ j : Fin R, ‖((hA.eigenvalues j : ℝ) : ℂ) * ((‖⟪b j, uVec⟫_ℂ‖ ^ 2 : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
    _ = ∑ j : Fin R, |hA.eigenvalues j| * ‖⟪b j, uVec⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ ∑ j : Fin R, (Real.pi * δ⁻¹) * ‖⟪b j, uVec⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (heig_bd j) (sq_nonneg _)
    _ = Real.pi * δ⁻¹ * ∑ j : Fin R, ‖⟪b j, uVec⟫_ℂ‖ ^ 2 := by rw [← Finset.mul_sum]
    _ = Real.pi * δ⁻¹ * ∑ r : Fin R, ‖u r‖ ^ 2 := by rw [hnorm_parseval]

/-! ### Cesàro Limit, Hilbert's Inequality on ℝ / ℤ, and the Sharp Analytic Large Sieve -/

private theorem cesaro_tendsto_complex {s : ℕ → ℂ} {L : ℂ}
    (hs : Filter.Tendsto s Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun K : ℕ => (((2 * K + 1 : ℕ) : ℂ))⁻¹ * ∑ M ∈ Finset.range (2 * K + 1), s M)
      Filter.atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hs ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hs (ε / 2) (by positivity)
  let B : ℝ := ∑ M ∈ Finset.range N0, ‖s M - L‖
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨K0, hK0⟩ := exists_nat_gt (B / ε)
  refine ⟨max N0 K0, fun K hK => ?_⟩
  have hK_K0 : K0 ≤ K := (le_max_right N0 K0).trans hK
  have hK_N0 : N0 ≤ 2 * K + 1 := by omega
  let D : ℝ := (2 * K + 1 : ℕ)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hdiff : (((2 * K + 1 : ℕ) : ℂ))⁻¹ * ∑ M ∈ Finset.range (2 * K + 1), s M - L =
      ((D : ℂ)⁻¹) * ∑ M ∈ Finset.range (2 * K + 1), (s M - L) := by
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD_pos.ne'
    have hDE : ((2 * K + 1 : ℕ) : ℂ) = (D : ℂ) := by simp [D]
    have hcard : ((Finset.range (2 * K + 1)).card : ℂ) = (D : ℂ) := by
      simp [D]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hDE]
    field_simp [hDc]
  rw [dist_eq_norm, hdiff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hD_pos.le]
  have hsplit : ∑ M ∈ Finset.range (2 * K + 1), ‖s M - L‖ =
      B + ∑ M ∈ Finset.Ico N0 (2 * K + 1), ‖s M - L‖ := by
    rw [← Finset.sum_range_add_sum_Ico (fun M => ‖s M - L‖) hK_N0]
  have hnorm_sum : ‖∑ M ∈ Finset.range (2 * K + 1), (s M - L)‖ ≤
      ∑ M ∈ Finset.range (2 * K + 1), ‖s M - L‖ := norm_sum_le _ _
  have htail : ∑ M ∈ Finset.Ico N0 (2 * K + 1), ‖s M - L‖ ≤ D * (ε / 2) := by
    calc
      ∑ M ∈ Finset.Ico N0 (2 * K + 1), ‖s M - L‖
          ≤ ∑ _M ∈ Finset.Ico N0 (2 * K + 1), (ε / 2) := by
            refine Finset.sum_le_sum fun M hM => ?_
            have hMge : N0 ≤ M := (Finset.mem_Ico.mp hM).1
            exact le_of_lt (by simpa [dist_eq_norm] using hN0 M hMge)
      _ = (((2 * K + 1 - N0 : ℕ) : ℝ)) * (ε / 2) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ D * (ε / 2) := by
            have hle : ((2 * K + 1 - N0 : ℕ) : ℝ) ≤ D := by
              dsimp [D]; exact_mod_cast Nat.sub_le (2 * K + 1) N0
            exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hB_lt : B < D * (ε / 2) := by
    have hK0_lt : B / ε < K0 := hK0
    have hK_lt : B / ε < (K : ℝ) := hK0_lt.trans_le (by exact_mod_cast hK_K0)
    have hB_lt' : B < K * ε := (div_lt_iff₀ hε).mp hK_lt
    have hKD : K * ε ≤ D * (ε / 2) := by
      dsimp [D]
      push_cast
      nlinarith
    exact hB_lt'.trans_le hKD
  calc
    (D⁻¹) * ‖∑ M ∈ Finset.range (2 * K + 1), (s M - L)‖
        ≤ D⁻¹ * (B + D * (ε / 2)) := by
          gcongr
          exact hnorm_sum.trans (hsplit.symm ▸ add_le_add (le_refl B) htail)
    _ < D⁻¹ * (D * (ε / 2) + D * (ε / 2)) := by gcongr
    _ = ε := by field_simp [hD_pos.ne']; ring

private theorem zpow_neg_one_pow_neg (m : ℤ) : ((-1 : ℂ) ^ (-m)) = (-1 : ℂ) ^ m := by
  rw [zpow_neg]
  have h : (-1 : ℂ) ^ m = 1 ∨ (-1 : ℂ) ^ m = -1 := by
    rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      rw [← two_mul, zpow_mul]
      norm_num
    · right
      rw [zpow_add₀ (by norm_num), zpow_mul, zpow_one]
      norm_num
  rcases h with h1 | h2
  · rw [h1, inv_one]
  · rw [h2]; norm_num

private theorem sum_Icc_sub_eq_cesaro (f : ℤ → ℂ) (K : ℕ) :
    ∑ k1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ k2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f (k1 - k2) =
      ∑ M ∈ Finset.range (2 * K + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m := by
  have h1 :
      ∑ k1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ k2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f (k1 - k2) =
        ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
          (((2 * K + 1 - m.natAbs : ℕ) : ℂ)) * f m := by
    let S := Finset.Icc (-(K : ℤ)) (K : ℤ)
    have hcard : ∀ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
        (S.filter fun k1 => k1 - m ∈ S).card = 2 * K + 1 - m.natAbs := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hmabs : m.natAbs ≤ 2 * K := by omega
      have heq : S.filter (fun k1 => k1 - m ∈ S) =
          Finset.Icc (max (-(K : ℤ)) (m - (K : ℤ))) (min (K : ℤ) ((K : ℤ) + m)) := by
        ext x
        simp only [Finset.mem_filter, S, Finset.mem_Icc, le_min_iff, max_le_iff]
        omega
      rw [heq, Int.card_Icc]
      omega
    have hrhs_expand :
        ∑ k1 ∈ S, ∑ k2 ∈ S, f (k1 - k2) =
          ∑ k1 ∈ S, ∑ k2 ∈ S,
            ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
              (if k1 - k2 = m then f m else 0) := by
      refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
      rw [Finset.sum_eq_single (k1 - k2)]
      · simp
      · intro m _ hm
        simp [hm.symm]
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_Icc] at hk1 hk2 ⊢
        omega
    rw [hrhs_expand]
    calc
      ∑ k1 ∈ S, ∑ k2 ∈ S, ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
          (if k1 - k2 = m then f m else 0)
          = ∑ k1 ∈ S, ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
              ∑ k2 ∈ S, (if k1 - k2 = m then f m else 0) := by
            refine Finset.sum_congr rfl fun k1 _ => Finset.sum_comm
      _ = ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
            ∑ k1 ∈ S, ∑ k2 ∈ S, (if k1 - k2 = m then f m else 0) := Finset.sum_comm
      _ = ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
            (((2 * K + 1 - m.natAbs : ℕ) : ℂ)) * f m := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hinner : ∑ k1 ∈ S, ∑ k2 ∈ S, (if k1 - k2 = m then f m else 0) =
                ∑ k1 ∈ S, (if k1 - m ∈ S then f m else 0) := by
              refine Finset.sum_congr rfl fun k1 _ => ?_
              by_cases hmem : k1 - m ∈ S
              · simp only [hmem, ↓reduceIte]
                rw [Finset.sum_eq_single (k1 - m)]
                · simp
                · intro k2 _ hk2
                  simp [show k1 - k2 ≠ m by omega]
                · intro hnot
                  exact absurd hmem hnot
              · simp only [hmem, ↓reduceIte]
                refine Finset.sum_eq_zero fun k2 hk2 => ?_
                have hne : k1 - k2 ≠ m := by
                  intro heq
                  apply hmem
                  have : k1 - m = k2 := by omega
                  rwa [this]
                simp [hne]
            rw [hinner, ← Finset.sum_filter, Finset.sum_const, hcard m hm, nsmul_eq_mul]
  have h2 :
      ∑ M ∈ Finset.range (2 * K + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m =
        ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
          (((2 * K + 1 - m.natAbs : ℕ) : ℂ)) * f m := by
    have hsplit :
        ∑ M ∈ Finset.range (2 * K + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m =
          ∑ M ∈ Finset.range (2 * K + 1),
            ∑ m ∈ Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ),
              (if m.natAbs ≤ M then f m else 0) := by
      refine Finset.sum_congr rfl fun M hM => ?_
      have hMle : M ≤ 2 * K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
      have hsub : Finset.Icc (-(M : ℤ)) (M : ℤ) ⊆
          Finset.Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ) := by
        intro m hm
        rw [Finset.mem_Icc] at hm ⊢
        omega
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hmabs : m.natAbs ≤ 2 * K := by omega
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    have hfc : ((Finset.range (2 * K + 1)).filter fun M => m.natAbs ≤ M) =
        Finset.Ico m.natAbs (2 * K + 1) := by
      ext M
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfc, Nat.card_Ico, nsmul_eq_mul]
  exact h1.trans h2.symm

private theorem tendsto_sum_neg_one_pow_div {t : ℝ} (ht : ∀ k : ℤ, t ≠ (k : ℝ)) :
    Filter.Tendsto
      (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (-1 : ℂ) ^ m / ((t : ℂ) + (m : ℂ)))
      Filter.atTop (𝓝 ((Real.pi / Real.sin (Real.pi * t) : ℝ) : ℂ)) := by
  have ht2_mem : ((t / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [Complex.intCast_re, Complex.ofReal_re] at hre
    exact ht (2 * n) (by push_cast; linarith)
  have ht12_mem : (((t + 1) / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [Complex.intCast_re, Complex.ofReal_re] at hre
    exact ht (2 * n - 1) (by push_cast; linarith)
  have hcot_even := (summable_cotTerm ht2_mem).hasSum.tendsto_sum_nat
  have hcot_odd := (summable_cotTerm ht12_mem).hasSum.tendsto_sum_nat
  rw [← cot_series_rep' ht2_mem] at hcot_even
  rw [← cot_series_rep' ht12_mem] at hcot_odd
  have ht_ne : ∀ k : ℤ, (t : ℂ) + (k : ℂ) ≠ 0 := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.ofReal_re, Complex.intCast_re, Complex.zero_re] at hre
    exact ht (-k) (by push_cast; linarith)
  have hsum_even : ∀ N : ℕ,
      (1 / 2 : ℂ) * (1 / ((t / 2 : ℝ) : ℂ) + ∑ j ∈ Finset.range N, cotTerm ((t / 2 : ℝ) : ℂ) j) =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k : ℤ) : ℂ)) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero, neg_zero,
        Finset.Icc_self, Finset.sum_singleton, mul_zero, Int.cast_zero]
      have h0 : (t : ℂ) ≠ 0 := by simpa using ht_ne 0
      push_cast; field_simp [h0]
    | succ N ih =>
      have hterm_e : (1 / 2 : ℂ) * cotTerm ((t / 2 : ℝ) : ℂ) N =
          (1 : ℂ) / ((t : ℂ) + ((2 * (-((N + 1 : ℕ) : ℤ)) : ℤ) : ℂ)) +
            (1 : ℂ) / ((t : ℂ) + ((2 * ((N + 1 : ℕ) : ℤ) : ℤ) : ℂ)) := by
        dsimp [cotTerm]
        simp only [one_div, mul_add]
        rw [← mul_inv, ← mul_inv]
        congr 1 <;> congr 1 <;> [push_cast; push_cast] <;> ring
      have hIcc : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
          insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [Finset.sum_range_succ, ← add_assoc, mul_add, ih, hterm_e, hIcc, Finset.sum_insert,
        Finset.sum_insert]
      · push_cast; ring
      · simp only [Finset.mem_Icc]; omega
      · simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hsum_odd : ∀ N : ℕ,
      (1 / 2 : ℂ) * (1 / (((t + 1) / 2 : ℝ) : ℂ) +
          ∑ j ∈ Finset.range N, cotTerm (((t + 1) / 2 : ℝ) : ℂ) j) =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k + 1 : ℤ) : ℂ)) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero, neg_zero,
        Finset.Icc_self, Finset.sum_singleton, mul_zero, zero_add, Int.cast_one]
      have h1 : (t : ℂ) + 1 ≠ 0 := by simpa using ht_ne 1
      have h1' : (((t + 1) / 2 : ℝ) : ℂ) ≠ 0 := by
        intro h0; apply h1; push_cast at h0; linear_combination 2 * h0
      push_cast; field_simp [h1, h1']
    | succ N ih =>
      have hterm_o : (1 / 2 : ℂ) * cotTerm (((t + 1) / 2 : ℝ) : ℂ) N =
          (1 : ℂ) / ((t : ℂ) + ((2 * (-((N + 1 : ℕ) : ℤ)) + 1 : ℤ) : ℂ)) +
            (1 : ℂ) / ((t : ℂ) + ((2 * ((N + 1 : ℕ) : ℤ) + 1 : ℤ) : ℂ)) := by
        dsimp [cotTerm]
        simp only [one_div, mul_add]
        rw [← mul_inv, ← mul_inv]
        congr 1 <;> congr 1 <;> [push_cast; push_cast] <;> ring
      have hIcc : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
          insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [Finset.sum_range_succ, ← add_assoc, mul_add, ih, hterm_o, hIcc, Finset.sum_insert,
        Finset.sum_insert]
      · push_cast; ring
      · simp only [Finset.mem_Icc]; omega
      · simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  let L : ℂ := ((Real.pi / Real.sin (Real.pi * t) : ℝ) : ℂ)
  have hlim_eq :
      (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))) -
        (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ))) = L := by
    have hsin_nz : Real.sin (Real.pi * t) ≠ 0 := by
      intro h0
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨k, hk⟩ := h0
      have hk' : k * Real.pi = Real.pi * (k : ℝ) := mul_comm _ _
      exact ht k (mul_left_cancel₀ Real.pi_ne_zero (by linarith))
    have hth : (Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ) =
        (Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ) + (Real.pi : ℂ) / 2 := by
      push_cast; ring
    have hsin2 : Complex.sin ((Real.pi : ℂ) * (t : ℂ)) =
        2 * Complex.sin ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) *
          Complex.cos ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) := by
      have := Complex.sin_two_mul ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))
      convert this using 2
      push_cast; ring
    have hsin_th : Complex.sin ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      apply hsin_nz
      have hc0 : Complex.sin ((Real.pi : ℂ) * (t : ℂ)) = 0 := by rw [hsin2, h0, mul_zero, zero_mul]
      have hre := congrArg Complex.re hc0
      rw [← Complex.ofReal_mul, Complex.sin_ofReal_re] at hre
      exact hre
    have hcos_th : Complex.cos ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      apply hsin_nz
      have hc0 : Complex.sin ((Real.pi : ℂ) * (t : ℂ)) = 0 := by rw [hsin2, h0, mul_zero]
      have hre := congrArg Complex.re hc0
      rw [← Complex.ofReal_mul, Complex.sin_ofReal_re] at hre
      exact hre
    have htrig : Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) -
        Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ)) =
        2 / Complex.sin ((Real.pi : ℂ) * (t : ℂ)) := by
      rw [hth, Complex.cot, Complex.cot, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two, hsin2]
      have hid := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))
      field_simp [hsin_th, hcos_th]
      linear_combination hid
    calc
      (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))) -
        (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ)))
          = (1 / 2 : ℂ) * (Real.pi : ℂ) *
              (Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) -
                Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ))) := by ring
      _ = (1 / 2 : ℂ) * (Real.pi : ℂ) * (2 / Complex.sin ((Real.pi : ℂ) * (t : ℂ))) := by rw [htrig]
      _ = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (t : ℂ)) := by ring
      _ = L := by dsimp [L]; rw [Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_sin]
  let T : ℕ → ℂ := fun N =>
    (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k : ℤ) : ℂ))) -
      (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k + 1 : ℤ) : ℂ)))
  have hT_tendsto : Filter.Tendsto T Filter.atTop (𝓝 L) := by
    have hev0 := (hcot_even.const_add (1 / ((t / 2 : ℝ) : ℂ))).const_mul (1 / 2 : ℂ)
    have hodd0 := (hcot_odd.const_add (1 / (((t + 1) / 2 : ℝ) : ℂ))).const_mul (1 / 2 : ℂ)
    have hlim_hev : (1 / 2 : ℂ) * (1 / ((t / 2 : ℝ) : ℂ) +
        ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ)) - 1 / ((t / 2 : ℝ) : ℂ))) =
        (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))) := by ring
    have hlim_hodd : (1 / 2 : ℂ) * (1 / (((t + 1) / 2 : ℝ) : ℂ) +
        ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ)) -
          1 / (((t + 1) / 2 : ℝ) : ℂ))) =
        (1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ))) := by ring
    rw [hlim_hev] at hev0
    rw [hlim_hodd] at hodd0
    have hev : Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k : ℤ) : ℂ)))
        Filter.atTop (𝓝 ((1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t / 2 : ℝ) : ℂ))))) :=
      hev0.congr (fun (N : ℕ) => hsum_even N)
    have hodd : Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k + 1 : ℤ) : ℂ)))
        Filter.atTop (𝓝 ((1 / 2 : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (((t + 1) / 2 : ℝ) : ℂ))))) :=
      hodd0.congr (fun (N : ℕ) => hsum_odd N)
    have hdiff_t := hev.sub hodd
    rw [hlim_eq] at hdiff_t
    exact hdiff_t
  let S : ℕ → ℂ := fun M =>
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (-1 : ℂ) ^ m / ((t : ℂ) + (m : ℂ))
  have hS_even : ∀ N : ℕ, S (2 * N) = T N + (1 : ℂ) / ((t : ℂ) + ((2 * N + 1 : ℤ) : ℂ)) := by
    intro N
    dsimp [S, T]
    have hT_split :
        (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k : ℤ) : ℂ))) -
          (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℂ) / ((t : ℂ) + ((2 * k + 1 : ℤ) : ℂ))) +
          (1 : ℂ) / ((t : ℂ) + ((2 * N + 1 : ℤ) : ℂ)) =
          (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (-1 : ℂ) ^ (2 * k) / ((t : ℂ) + ((2 * k : ℤ) : ℂ))) +
          (∑ k ∈ Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1), (-1 : ℂ) ^ (2 * k + 1) / ((t : ℂ) + ((2 * k + 1 : ℤ) : ℂ))) := by
      have hpe : ∀ k : ℤ, (-1 : ℂ) ^ (2 * k) = 1 := fun k => by
        rw [zpow_mul]; norm_num
      have hpo : ∀ k : ℤ, (-1 : ℂ) ^ (2 * k + 1) = -1 := fun k => by
        rw [zpow_add₀ (by norm_num), zpow_mul, zpow_one]; norm_num
      simp_rw [hpe, hpo, neg_div, Finset.sum_neg_distrib]
      have hIcc_top : Finset.Icc (-(N : ℤ)) (N : ℤ) =
          insert (N : ℤ) (Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      conv_lhs =>
        arg 1; arg 2
        rw [hIcc_top, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      push_cast
      ring
    rw [hT_split]
    have hsplit_par : Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) =
        ((Finset.Icc (-(N : ℤ)) (N : ℤ)).image (2 * ·)) ∪
          ((Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)).image (fun k => 2 * k + 1)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
      constructor
      · intro ⟨hlo, hhi⟩
        rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · left; exact ⟨k, by omega, by ring⟩
        · right; exact ⟨k, by omega, rfl⟩
      · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) <;> omega
    have hdisj : Disjoint ((Finset.Icc (-(N : ℤ)) (N : ℤ)).image (2 * ·))
        ((Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)).image (fun k => 2 * k + 1)) := by
      rw [Finset.disjoint_left]
      rintro m hm1 hm2
      rw [Finset.mem_image] at hm1 hm2
      rcases hm1 with ⟨k1, _, rfl⟩
      rcases hm2 with ⟨k2, _, h⟩
      omega
    push_cast
    rw [hsplit_par, Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => by omega),
      Finset.sum_image (fun x _ y _ h => by omega)]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_one]
  have hdiff_bound : Filter.Tendsto (fun M : ℕ => S M - T (M / 2)) Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M0, hM0⟩ := exists_nat_gt (|t| + 3 / ε + 4)
    refine ⟨M0, fun M hM => ?_⟩
    rw [dist_zero_right]
    have hMgt : |t| + 3 / ε + 4 < (M : ℝ) := hM0.trans_le (by exact_mod_cast hM)
    have hsub_eq : S M - T (M / 2) =
        if Even M then (1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ))
        else (1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ)) +
          (-1 : ℂ) ^ (-(M : ℤ)) / ((t : ℂ) + (-(M : ℤ) : ℂ)) +
          (-1 : ℂ) ^ (M : ℤ) / ((t : ℂ) + ((M : ℤ) : ℂ)) := by
      rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hev : Even (k + k) := ⟨k, rfl⟩
        have hdiv : (k + k) / 2 = k := by omega
        simp only [hev, ↓reduceIte, hdiv]
        rw [show k + k = 2 * k by omega, hS_even k]
        ring
      · have hodd : ¬ Even (2 * k + 1) := by
          rintro ⟨j, hj⟩; omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simp only [hodd, ↓reduceIte, hdiv]
        have hIcc : Finset.Icc (-(2 * (k : ℤ) + 1)) (2 * (k : ℤ) + 1) =
            insert (-(2 * (k : ℤ) + 1))
              (insert (2 * (k : ℤ) + 1) (Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)))) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hS1 : S (2 * k + 1) = S (2 * k) +
            (-1 : ℂ) ^ (-(2 * (k : ℤ) + 1)) / ((t : ℂ) + (-(2 * (k : ℤ) + 1) : ℂ)) +
            (-1 : ℂ) ^ (2 * (k : ℤ) + 1) / ((t : ℂ) + ((2 * (k : ℤ) + 1 : ℤ) : ℂ)) := by
          dsimp [S]
          push_cast
          rw [hIcc, Finset.sum_insert, Finset.sum_insert]
          · push_cast; ring
          · simp only [Finset.mem_Icc]; omega
          · simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        rw [hS1, hS_even k]
        push_cast
        ring
    have hM_sub_pos : 0 < (M : ℝ) - |t| := by linarith [div_pos (by norm_num : (0 : ℝ) < 3) hε]
    have hinv_le : ∀ z : ℤ, (M : ℝ) ≤ |(z : ℝ)| →
        ‖(1 : ℂ) / ((t : ℂ) + (z : ℂ))‖ ≤ ((M : ℝ) - |t|)⁻¹ := by
      intro z hz
      rw [one_div, norm_inv, ← Complex.ofReal_intCast, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs]
      have hge : (M : ℝ) - |t| ≤ |t + (z : ℝ)| := by
        have htri : |(z : ℝ)| ≤ |t + (z : ℝ)| + |t| := by
          calc
            |(z : ℝ)| = |(t + (z : ℝ)) + (-t)| := by ring_nf
            _ ≤ |t + (z : ℝ)| + |-t| := abs_add_le _ _
            _ = |t + (z : ℝ)| + |t| := by rw [abs_neg]
        linarith
      exact inv_anti₀ hM_sub_pos hge
    have hterm_le : ∀ (sgn z : ℤ), (M : ℝ) ≤ |(z : ℝ)| →
        ‖(-1 : ℂ) ^ sgn / ((t : ℂ) + (z : ℂ))‖ ≤ ((M : ℝ) - |t|)⁻¹ := by
      intro sgn z hz
      have h1 : ‖(-1 : ℂ) ^ sgn‖ = 1 := by
        rcases Int.even_or_odd sgn with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rw [← two_mul, zpow_mul]; norm_num
        · rw [zpow_add₀ (by norm_num), zpow_mul, zpow_one]; norm_num
      rw [norm_div, h1, ← one_div]
      simpa using hinv_le z hz
    have hz1 : (M : ℝ) ≤ |((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ)| := by
      have hle : (M : ℤ) ≤ 2 * ((M / 2 : ℕ) : ℤ) + 1 := by omega
      have : (M : ℝ) ≤ ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ) := by exact_mod_cast hle
      exact this.trans (le_abs_self _)
    have hz2 : (M : ℝ) ≤ |(-(M : ℤ) : ℝ)| := by
      push_cast; rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg M)]
    have hz3 : (M : ℝ) ≤ |((M : ℤ) : ℝ)| := by
      push_cast; exact le_abs_self _
    have hnorm3 : ‖S M - T (M / 2)‖ ≤ 3 * ((M : ℝ) - |t|)⁻¹ := by
      rw [hsub_eq]
      split_ifs
      · calc
          ‖(1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ))‖ ≤ ((M : ℝ) - |t|)⁻¹ :=
            hinv_le _ hz1
          _ ≤ 3 * ((M : ℝ) - |t|)⁻¹ := by
            have := inv_nonneg.mpr hM_sub_pos.le
            linarith
      · have hb1 := hinv_le _ hz1
        have hb2 := hterm_le (-(M : ℤ)) (-(M : ℤ)) hz2
        have hb3 := hterm_le (M : ℤ) (M : ℤ) hz3
        calc
          ‖(1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ)) +
              (-1 : ℂ) ^ (-(M : ℤ)) / ((t : ℂ) + (-(M : ℤ) : ℂ)) +
              (-1 : ℂ) ^ (M : ℤ) / ((t : ℂ) + ((M : ℤ) : ℂ))‖
              ≤ ‖(1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ)) +
                  (-1 : ℂ) ^ (-(M : ℤ)) / ((t : ℂ) + (-(M : ℤ) : ℂ))‖ +
                ‖(-1 : ℂ) ^ (M : ℤ) / ((t : ℂ) + ((M : ℤ) : ℂ))‖ := norm_add_le _ _
          _ ≤ (‖(1 : ℂ) / ((t : ℂ) + ((2 * ((M / 2 : ℕ) : ℤ) + 1 : ℤ) : ℂ))‖ +
                  ‖(-1 : ℂ) ^ (-(M : ℤ)) / ((t : ℂ) + (-(M : ℤ) : ℂ))‖) +
                ‖(-1 : ℂ) ^ (M : ℤ) / ((t : ℂ) + ((M : ℤ) : ℂ))‖ :=
                add_le_add (norm_add_le _ _) (le_refl _)
          _ ≤ ((M : ℝ) - |t|)⁻¹ + ((M : ℝ) - |t|)⁻¹ + ((M : ℝ) - |t|)⁻¹ :=
                add_le_add (add_le_add hb1 hb2) hb3
          _ = 3 * ((M : ℝ) - |t|)⁻¹ := by ring
    have hlt3 : 3 * ((M : ℝ) - |t|)⁻¹ < ε := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hM_sub_pos]
      have : 3 / ε < (M : ℝ) - |t| := by linarith
      rw [mul_comm]
      exact (div_lt_iff₀ hε).mp this
    exact hnorm3.trans_lt hlt3
  have hhalf_tendsto : Filter.Tendsto (fun M : ℕ => M / 2) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨2 * b, fun M hM => Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)⟩
  have hmain := (hT_tendsto.comp hhalf_tendsto).add hdiff_bound
  simp only [add_zero] at hmain
  refine hmain.congr fun M => ?_
  dsimp [S]
  ring

private theorem sin_add_int_mul_pi_eq (x : ℝ) (m : ℤ) :
    Real.sin (x + (m : ℝ) * Real.pi) = ((-1 : ℝ) ^ m) * Real.sin x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    have hrew : x + ((k : ℝ) + 1) * Real.pi = (x + (k : ℝ) * Real.pi) + Real.pi := by ring
    rw [hrew, Real.sin_add_pi, ih, zpow_add₀ (by norm_num), zpow_one]
    ring
  | pred k ih =>
    push_cast at ih ⊢
    have hrew : x + (-(k : ℝ) - 1) * Real.pi = (x + (-(k : ℝ)) * Real.pi) - Real.pi := by ring
    rw [hrew, Real.sin_sub_pi, ih, zpow_sub₀ (by norm_num), zpow_one]
    ring

private theorem tendsto_finset_sum_complex {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ} {L : ι → ℂ}
    (hf : ∀ i ∈ s, Filter.Tendsto (f i) Filter.atTop (𝓝 (L i))) :
    Filter.Tendsto (fun n => ∑ i ∈ s, f i n) Filter.atTop (𝓝 (∑ i ∈ s, L i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem sin_shift_ratio (a b_star : ℂ) (m n : ℤ) (s : ℝ) (hs : s ≠ 0) :
    ((-1 : ℂ) ^ m * a) * ((-1 : ℂ) ^ n * b_star) / (s : ℂ) =
      a * b_star / ((-1 : ℂ) ^ (m - n) * (s : ℂ)) := by
  have hsgn : (-1 : ℂ) ^ m * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (m - n) := by
    rw [zpow_sub₀ (by norm_num), div_eq_mul_inv, ← zpow_neg, zpow_neg_one_pow_neg]
  have hsq : ((-1 : ℂ) ^ (m - n)) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((-1 : ℂ) ^ ((2 : ℕ) : ℤ)) = 1 by norm_num, one_zpow]
  have hnz : (-1 : ℂ) ^ (m - n) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp [hnz, hsC]
  calc
    (-1 : ℂ) ^ m * a * (-1 : ℂ) ^ n * b_star * (-1 : ℂ) ^ (m - n)
        = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ n) * (-1 : ℂ) ^ (m - n) * (a * b_star) := by ring
    _ = ((-1 : ℂ) ^ (m - n)) ^ 2 * (a * b_star) := by rw [hsgn]; ring
    _ = a * b_star := by rw [hsq, one_mul]

/-- **Hilbert's Inequality Modulo 1 (`sin (π x)` kernel)**:
for any finite `δ`-well-spaced family `α : κ → ℝ` mod `1` (`0 < δ ≤ 1`) and `u : κ → ℂ`,
`‖∑ r ∈ J, ∑ s ∈ J, (if r = s then 0 else u r * star (u s) / sin (π * (α r - α s)))‖ ≤ δ⁻¹ * ∑ r ∈ J, ‖u r‖ ^ 2`. -/
theorem hilbert_inequality_sin_pi {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (u : κ → ℂ) :
    ‖∑ r ∈ J, ∑ s ∈ J,
        (if r = s then (0 : ℂ) else u r * star (u s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ))‖ ≤
      δ⁻¹ * ∑ r ∈ J, ‖u r‖ ^ 2 := by
  have hδ0 : 0 < δ := hws.1
  by_cases hJ_empty : J.card = 0
  · rw [Finset.card_eq_zero.mp hJ_empty]
    simp
  have hR_pos : 0 < J.card := Nat.pos_of_ne_zero hJ_empty
  let R : ℕ := J.card
  have hfract_inj : Set.InjOn (fun r => Int.fract (α r)) (J : Set κ) := by
    intro r hr s hs heq
    by_contra hrs
    have hsp := hws.2.2 r hr s hs hrs
    have hsub : α r - α s = ((⌊α r⌋ - ⌊α s⌋ : ℤ) : ℝ) := by
      have hr' := Int.floor_add_fract (α r)
      have hs' := Int.floor_add_fract (α s)
      push_cast
      linarith
    have hzero : distToInt (α r - α s) = 0 := by
      rw [hsub, ← zero_add (((⌊α r⌋ - ⌊α s⌋ : ℤ) : ℝ)), distToInt_add_intCast]
      simp [distToInt]
    linarith
  let Sfrac : Finset ℝ := J.image (fun r => Int.fract (α r))
  have hSfrac_card : Sfrac.card = R := Finset.card_image_of_injOn hfract_inj
  let y : Fin R → ℝ := fun i => Sfrac.orderEmbOfFin hSfrac_card i
  have hy_mem : ∀ i : Fin R, y i ∈ Sfrac := fun i => Sfrac.orderEmbOfFin_mem hSfrac_card i
  have hy_strict : StrictMono y := fun _ _ hij => (Sfrac.orderEmbOfFin hSfrac_card).strictMono hij
  have hchoose : ∀ i : Fin R, ∃ r ∈ J, Int.fract (α r) = y i := by
    intro i
    exact Finset.mem_image.mp (hy_mem i)
  let σfun : Fin R → κ := fun i => (hchoose i).choose
  have hσ_mem : ∀ i : Fin R, σfun i ∈ J := fun i => (hchoose i).choose_spec.1
  have hσ_eq : ∀ i : Fin R, Int.fract (α (σfun i)) = y i := fun i => (hchoose i).choose_spec.2
  have hσ_inj : Function.Injective σfun := by
    intro i j hij
    apply (Sfrac.orderEmbOfFin hSfrac_card).injective
    change y i = y j
    rw [← hσ_eq i, ← hσ_eq j, hij]
  have hσ_bij : ∀ r ∈ J, ∃ i : Fin R, σfun i = r := by
    have himg : (Finset.univ.image σfun) = J := by
      apply Finset.eq_of_subset_of_card_le
      · intro r hr
        rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
        exact hσ_mem i
      · rw [Finset.card_image_of_injective _ hσ_inj, Finset.card_univ, Fintype.card_fin]
    intro r hr
    rw [← himg, Finset.mem_image] at hr
    rcases hr with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have hy_nonneg : ∀ i : Fin R, 0 ≤ y i := fun i => by rw [← hσ_eq i]; exact Int.fract_nonneg _
  have hy_lt_one : ∀ i : Fin R, y i < 1 := fun i => by rw [← hσ_eq i]; exact Int.fract_lt_one _
  have hy_diff_bounds : ∀ i j : Fin R, i < j →
      δ ≤ y j - y i ∧ δ ≤ 1 - (y j - y i) := by
    intro i j hij
    have hne : σfun i ≠ σfun j := fun h => hij.ne (hσ_inj h)
    have hsp := hws.2.2 (σfun j) (hσ_mem j) (σfun i) (hσ_mem i) hne.symm
    have hdist_eq : distToInt (y j - y i) = distToInt (α (σfun j) - α (σfun i)) := by
      have hrew : α (σfun j) - α (σfun i) =
          (y j - y i) + ((⌊α (σfun j)⌋ - ⌊α (σfun i)⌋ : ℤ) : ℝ) := by
        have h1 := Int.floor_add_fract (α (σfun j))
        have h2 := Int.floor_add_fract (α (σfun i))
        rw [hσ_eq j] at h1
        rw [hσ_eq i] at h2
        push_cast
        linarith
      rw [hrew, distToInt_add_intCast]
    have hlo : 0 < y j - y i := sub_pos.mpr (hy_strict hij)
    have hhi : y j - y i < 1 := by linarith [hy_nonneg i, hy_lt_one j]
    have hmin1 : distToInt (y j - y i) ≤ y j - y i := by
      have := distToInt_le_abs_sub (y j - y i) 0
      simpa [abs_of_pos hlo] using this
    have hmin2 : distToInt (y j - y i) ≤ 1 - (y j - y i) := by
      have := distToInt_le_abs_sub (y j - y i) (1 : ℤ)
      have habs : |(y j - y i) - ((1 : ℤ) : ℝ)| = 1 - (y j - y i) := by
        push_cast
        rw [abs_of_nonpos (by linarith)]
        ring
      rwa [habs] at this
    rw [← hdist_eq] at hsp
    exact ⟨hsp.trans hmin1, hsp.trans hmin2⟩
  let u' : Fin R → ℂ := fun i => ((-1 : ℂ) ^ (⌊α (σfun i)⌋)) * u (σfun i)
  have hu'_norm : ∀ i : Fin R, ‖u' i‖ = ‖u (σfun i)‖ := fun i => by
    dsimp [u']
    have h1 : ‖(-1 : ℂ) ^ (⌊α (σfun i)⌋)‖ = 1 := by
      rcases Int.even_or_odd (⌊α (σfun i)⌋) with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk, ← two_mul, zpow_mul]; norm_num
      · rw [hk, zpow_add₀ (by norm_num), zpow_mul, zpow_one]; norm_num
    rw [norm_mul, h1, one_mul]
  have hsum_norm_u : ∑ i : Fin R, ‖u' i‖ ^ 2 = ∑ r ∈ J, ‖u r‖ ^ 2 := by
    have heq : ∑ i : Fin R, ‖u (σfun i)‖ ^ 2 = ∑ r ∈ J, ‖u r‖ ^ 2 := by
      refine Finset.sum_bij (fun i _ => σfun i) (fun i _ => hσ_mem i)
        (fun i₁ _ i₂ _ h => hσ_inj h) (fun r hr => ?_) (fun i _ => rfl)
      obtain ⟨i, hi⟩ := hσ_bij r hr
      exact ⟨i, Finset.mem_univ i, hi⟩
    simpa [hu'_norm] using heq
  have hsum_rewrite :
      ∑ i : Fin R, ∑ j : Fin R,
        (if i = j then (0 : ℂ) else u' i * star (u' j) / ((Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ)) =
      ∑ r ∈ J, ∑ s ∈ J,
        (if r = s then (0 : ℂ) else u r * star (u s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) := by
    refine Finset.sum_bij (fun i _ => σfun i) (fun i _ => hσ_mem i)
      (fun i₁ _ i₂ _ h => hσ_inj h) (fun r hr => ?_) (fun i _ => ?_)
    · obtain ⟨i, hi⟩ := hσ_bij r hr
      exact ⟨i, Finset.mem_univ i, hi⟩
    · refine Finset.sum_bij (fun j _ => σfun j) (fun j _ => hσ_mem j)
        (fun j₁ _ j₂ _ h => hσ_inj h) (fun s hs => ?_) (fun j _ => ?_)
      · obtain ⟨j, hj⟩ := hσ_bij s hs
        exact ⟨j, Finset.mem_univ j, hj⟩
      · by_cases hij : i = j
        · subst hij
          simp
        · have hne : σfun i ≠ σfun j := fun h => hij (hσ_inj h)
          simp only [hij, hne, ↓reduceIte]
          have hsin_eq : Real.sin (Real.pi * (α (σfun i) - α (σfun j))) =
              ((-1 : ℝ) ^ (⌊α (σfun i)⌋ - ⌊α (σfun j)⌋)) * Real.sin (Real.pi * (y i - y j)) := by
            have h1 := Int.floor_add_fract (α (σfun i))
            have h2 := Int.floor_add_fract (α (σfun j))
            rw [hσ_eq i] at h1
            rw [hσ_eq j] at h2
            have hsub_α : α (σfun i) - α (σfun j) =
                (y i - y j) + ((⌊α (σfun i)⌋ - ⌊α (σfun j)⌋ : ℤ) : ℝ) := by
              conv_lhs => rw [← h1, ← h2]
              push_cast; ring
            rw [hsub_α, mul_add, mul_comm Real.pi ((⌊α (σfun i)⌋ - ⌊α (σfun j)⌋ : ℤ) : ℝ),
              sin_add_int_mul_pi_eq]
          have hsin_nz : Real.sin (Real.pi * (y i - y j)) ≠ 0 := by
            intro h0
            rw [Real.sin_eq_zero_iff] at h0
            obtain ⟨k, hk⟩ := h0
            have hyk : y i - y j = (k : ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by linarith)
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · have hy0 : 0 < y j - y i := sub_pos.mpr (hy_strict hlt)
              have hy1 : y j - y i < 1 := by linarith [hy_nonneg i, hy_lt_one j]
              have hk1 : y j - y i = ((-k : ℤ) : ℝ) := by push_cast; linarith
              have hk_pos : (0 : ℝ) < ((-k : ℤ) : ℝ) := by linarith
              have hk_lt1 : ((-k : ℤ) : ℝ) < 1 := by linarith
              have hkZ_pos : (0 : ℤ) < -k := by exact_mod_cast hk_pos
              have hkZ_lt1 : -k < 1 := by exact_mod_cast hk_lt1
              omega
            · have hy0 : 0 < y i - y j := sub_pos.mpr (hy_strict hgt)
              have hy1 : y i - y j < 1 := by linarith [hy_nonneg j, hy_lt_one i]
              have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
              have hk_lt1 : (k : ℝ) < 1 := by linarith
              have hkZ_pos : (0 : ℤ) < k := by exact_mod_cast hk_pos
              have hkZ_lt1 : k < 1 := by exact_mod_cast hk_lt1
              omega
          have hu'_i : u' i = (-1 : ℂ) ^ (⌊α (σfun i)⌋) * u (σfun i) := rfl
          have hstar_mul : star (u' j) = (-1 : ℂ) ^ (⌊α (σfun j)⌋) * star (u (σfun j)) := by
            dsimp [u']
            simp only [map_mul, map_zpow₀, map_neg, map_one]
          have hsinC : ((Real.sin (Real.pi * (α (σfun i) - α (σfun j))) : ℝ) : ℂ) =
              (-1 : ℂ) ^ (⌊α (σfun i)⌋ - ⌊α (σfun j)⌋) *
                ((Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ) := by
            rw [hsin_eq, Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one]
          rw [hsinC, hstar_mul, hu'_i]
          exact sin_shift_ratio (u (σfun i)) (star (u (σfun j))) ⌊α (σfun i)⌋ ⌊α (σfun j)⌋
            (Real.sin (Real.pi * (y i - y j))) hsin_nz
  have hy_nonint : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, (y i - y j) ≠ (k : ℝ) := by
    intro i j hij k hk
    have hsp := hws.2.2 (σfun i) (hσ_mem i) (σfun j) (hσ_mem j) (fun h => hij (hσ_inj h))
    have hdist0 : distToInt (α (σfun i) - α (σfun j)) = 0 := by
      have hrew : α (σfun i) - α (σfun j) =
          ((k + ⌊α (σfun i)⌋ - ⌊α (σfun j)⌋ : ℤ) : ℝ) := by
        have h1 := Int.floor_add_fract (α (σfun i))
        have h2 := Int.floor_add_fract (α (σfun j))
        rw [hσ_eq i] at h1
        rw [hσ_eq j] at h2
        push_cast
        linarith
      rw [hrew]
      simp [distToInt]
    linarith
  let F : ℕ → ℂ := fun K =>
    ∑ i : Fin R, ∑ j : Fin R,
      if i = j then (0 : ℂ) else
        u' i * star (u' j) *
          ((((2 * K + 1 : ℕ) : ℂ))⁻¹ *
            ∑ k1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              ∑ k2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
                (-1 : ℂ) ^ (k1 - k2) / (((y i - y j : ℝ) : ℂ) + ((k1 - k2 : ℤ) : ℂ)))
  have hF_bd : ∀ K : ℕ, ‖F K‖ ≤ Real.pi * δ⁻¹ * ∑ r ∈ J, ‖u r‖ ^ 2 := by
    intro K
    let M : ℕ := 2 * K + 1
    have hM_pos : 0 < M := by dsimp [M]; omega
    let xK : Fin (M * R) → ℝ := fun p =>
      let q := finProdFinEquiv.symm p
      y q.2 + (((q.1 : ℤ) - (K : ℤ)) : ℝ)
    let vK : Fin (M * R) → ℂ := fun p =>
      let q := finProdFinEquiv.symm p
      ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * (-1 : ℂ) ^ ((q.1 : ℤ) - (K : ℤ)) * u' q.2
    have hxK_spaced : ∀ p1 p2 : Fin (M * R), p1 < p2 → δ ≤ xK p2 - xK p1 := by
      intro p1 p2 hp
      let q1 := finProdFinEquiv.symm p1
      let q2 := finProdFinEquiv.symm p2
      have hidx1 : (p1 : ℕ) = (q1.1 : ℕ) * R + (q1.2 : ℕ) := by
        rw [← finProdFinEquiv.apply_symm_apply p1]
        change (q1.2 : ℕ) + R * (q1.1 : ℕ) = (q1.1 : ℕ) * R + (q1.2 : ℕ)
        ring
      have hidx2 : (p2 : ℕ) = (q2.1 : ℕ) * R + (q2.2 : ℕ) := by
        rw [← finProdFinEquiv.apply_symm_apply p2]
        change (q2.2 : ℕ) + R * (q2.1 : ℕ) = (q2.1 : ℕ) * R + (q2.2 : ℕ)
        ring
      have hlt_nat : (q1.1 : ℕ) * R + (q1.2 : ℕ) < (q2.1 : ℕ) * R + (q2.2 : ℕ) := by
        rw [← hidx1, ← hidx2]
        exact hp
      have hq1_le : (q1.1 : ℕ) ≤ q2.1 := by
        by_contra hgt
        have : (q2.1 : ℕ) + 1 ≤ q1.1 := by omega
        have h1 : (q2.1 : ℕ) * R + (q2.2 : ℕ) < ((q2.1 : ℕ) + 1) * R := by
          have := q2.2.isLt; nlinarith
        have h2 : ((q2.1 : ℕ) + 1) * R ≤ (q1.1 : ℕ) * R + (q1.2 : ℕ) := by nlinarith
        omega
      rcases eq_or_lt_of_le hq1_le with hq1_eq | hq1_lt
      · have hq2_lt : q1.2 < q2.2 := by
          have hlt2 : (q1.2 : ℕ) < (q2.2 : ℕ) := by
            rw [hq1_eq] at hlt_nat
            exact Nat.lt_of_add_lt_add_left hlt_nat
          exact hlt2
        have hsub : xK p2 - xK p1 = y q2.2 - y q1.2 := by
          dsimp [xK, q1, q2]
          rw [hq1_eq]
          ring
        rw [hsub]
        exact (hy_diff_bounds q1.2 q2.2 hq2_lt).1
      · have hdiff_k : (1 : ℝ) ≤ (((q2.1 : ℤ) - (K : ℤ) : ℝ) - ((q1.1 : ℤ) - (K : ℤ) : ℝ)) := by
          have hk : (1 : ℤ) ≤ (q2.1 : ℤ) - (q1.1 : ℤ) := by omega
          have : (1 : ℝ) ≤ ((q2.1 : ℤ) - (q1.1 : ℤ) : ℝ) := by exact_mod_cast hk
          push_cast at this ⊢
          linarith
        have hgap : δ ≤ 1 - (y q1.2 - y q2.2) := by
          by_cases h0 : q2.2 < q1.2
          · exact (hy_diff_bounds q2.2 q1.2 h0).2
          · have hge : y q1.2 ≤ y q2.2 := hy_strict.monotone (le_of_not_gt h0)
            have hδ1 : δ ≤ 1 := hws.2.1
            linarith
        have hsub : xK p2 - xK p1 =
            (y q2.2 - y q1.2) + (((q2.1 : ℤ) - (K : ℤ) : ℝ) - ((q1.1 : ℤ) - (K : ℤ) : ℝ)) := by
          dsimp [xK, q1, q2]
          ring
        linarith
    have hvK_norm_sq : ∑ p : Fin (M * R), ‖vK p‖ ^ 2 = ∑ r ∈ J, ‖u r‖ ^ 2 := by
      have heq1 : ∑ p : Fin (M * R), ‖vK p‖ ^ 2 =
          ∑ q : Fin M × Fin R, ‖vK (finProdFinEquiv q)‖ ^ 2 := by
        rw [← Equiv.sum_comp finProdFinEquiv]
      rw [heq1, Fintype.sum_prod_type]
      have hterm : ∀ k : Fin M, ∀ i : Fin R,
          ‖vK (finProdFinEquiv (k, i))‖ ^ 2 = (M : ℝ)⁻¹ * ‖u' i‖ ^ 2 := by
        intro k i
        dsimp [vK]
        rw [Equiv.symm_apply_apply]
        have hs1 : ‖(-1 : ℂ) ^ ((k : ℤ) - (K : ℤ))‖ = 1 := by
          rcases Int.even_or_odd ((k : ℤ) - (K : ℤ)) with ⟨m, hm⟩ | ⟨m, hm⟩
          · rw [hm, ← two_mul, zpow_mul]; norm_num
          · rw [hm, zpow_add₀ (by norm_num), zpow_mul, zpow_one]; norm_num
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          hs1, mul_one, mul_pow, inv_pow, Real.sq_sqrt (by exact_mod_cast hM_pos.le)]
      simp_rw [hterm, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hM_nz : (M : ℝ) ≠ 0 := by exact_mod_cast hM_pos.ne'
      rw [← mul_assoc, inv_mul_cancel₀ hM_nz, one_mul, hsum_norm_u]
    have hF_eq :
        ∑ p1 : Fin (M * R), ∑ p2 : Fin (M * R),
          (if p1 = p2 then (0 : ℂ) else vK p1 * star (vK p2) / ((xK p1 - xK p2 : ℝ) : ℂ)) =
        F K := by
      have hrew1 :
          ∑ p1 : Fin (M * R), ∑ p2 : Fin (M * R),
            (if p1 = p2 then (0 : ℂ) else vK p1 * star (vK p2) / ((xK p1 - xK p2 : ℝ) : ℂ)) =
          ∑ q1 : Fin M × Fin R, ∑ q2 : Fin M × Fin R,
            (if q1 = q2 then (0 : ℂ) else
              vK (finProdFinEquiv q1) * star (vK (finProdFinEquiv q2)) /
                ((xK (finProdFinEquiv q1) - xK (finProdFinEquiv q2) : ℝ) : ℂ)) := by
        rw [← Equiv.sum_comp finProdFinEquiv]
        refine Finset.sum_congr rfl fun q1 _ => ?_
        rw [← Equiv.sum_comp finProdFinEquiv]
        refine Finset.sum_congr rfl fun q2 _ => ?_
        simp
      rw [hrew1, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      have hswap :
          (∑ i : Fin R, ∑ k1 : Fin M, ∑ k2 : Fin M, ∑ j : Fin R,
            (if (k1, i) = (k2, j) then (0 : ℂ) else
              vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
                ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ))) =
          ∑ i : Fin R, ∑ j : Fin R, ∑ k1 : Fin M, ∑ k2 : Fin M,
            (if (k1, i) = (k2, j) then (0 : ℂ) else
              vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
                ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        trans ∑ k1 : Fin M, ∑ j : Fin R, ∑ k2 : Fin M,
          (if (k1, i) = (k2, j) then (0 : ℂ) else
            vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
              ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ))
        · refine Finset.sum_congr rfl fun k1 _ => Finset.sum_comm
        · exact Finset.sum_comm
      rw [hswap]
      dsimp [F]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hterm_val : ∀ k1 k2 : Fin M, (k1, i) ≠ (k2, j) →
          vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
              ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ) =
            (((M : ℝ) : ℂ))⁻¹ * (u' i * star (u' j)) *
              ((-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ))) := by
        intro k1 k2 _
        have hsqrt' : ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) =
            (((M : ℝ) : ℂ))⁻¹ := by
          rw [← Complex.ofReal_mul, ← sq, inv_pow,
            Real.sq_sqrt (by exact_mod_cast hM_pos.le), Complex.ofReal_inv]
        have hs_inv : starRingEnd ℂ ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) = ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) := by
          simp
        have hs2 : starRingEnd ℂ ((-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ))) = (-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ)) := by
          simp
        have hpow : (-1 : ℂ) ^ ((k1 : ℤ) - (K : ℤ)) * (-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ)) =
            (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) := by
          rw [← zpow_neg_one_pow_neg ((k2 : ℤ) - (K : ℤ)), ← zpow_add₀ (by norm_num),
            ← sub_eq_add_neg]
        have hv1 : vK (finProdFinEquiv (k1, i)) =
            ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * (-1 : ℂ) ^ ((k1 : ℤ) - (K : ℤ)) * u' i := by
          dsimp [vK]
          rw [Equiv.symm_apply_apply]
        have hv2 : star (vK (finProdFinEquiv (k2, j))) =
            ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * (-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ)) * star (u' j) := by
          dsimp [vK]
          rw [Equiv.symm_apply_apply]
          simp only [map_mul, hs_inv, hs2]
        have hx12 : ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ) =
            (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)) := by
          dsimp [xK]
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          dsimp only
          rw [show (y i + ((k1 : ℤ) - (K : ℤ) : ℝ) - (y j + ((k2 : ℤ) - (K : ℤ) : ℝ))) =
              (y i - y j) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℝ) by
            push_cast; ring, Complex.ofReal_add, Complex.ofReal_intCast]
        rw [hv1, hv2, hx12]
        have hstep1 :
            ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * (-1 : ℂ) ^ ((k1 : ℤ) - (K : ℤ)) * u' i *
                (((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * (-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ)) * star (u' j)) =
              (((((Real.sqrt M)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt M)⁻¹ : ℝ)) : ℂ)) *
                ((-1 : ℂ) ^ ((k1 : ℤ) - (K : ℤ)) * (-1 : ℂ) ^ ((k2 : ℤ) - (K : ℤ))) *
                (u' i * star (u' j)) := by ring
        rw [hstep1, hsqrt', hpow]
        ring
      by_cases hij : i = j
      · subst hij
        simp only [ite_true]
        have hdiag_zero :
            (∑ k1 : Fin M, ∑ k2 : Fin M,
              (if (k1, i) = (k2, i) then (0 : ℂ) else
                vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, i))) /
                  ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, i)) : ℝ) : ℂ))) = 0 := by
          have hrew : ∀ k1 k2 : Fin M,
              (if (k1, i) = (k2, i) then (0 : ℂ) else
                vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, i))) /
                  ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, i)) : ℝ) : ℂ)) =
              (((M : ℝ) : ℂ))⁻¹ * (u' i * star (u' i)) *
                (if k1 = k2 then (0 : ℂ) else
                  (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                    ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)) := by
            intro k1 k2
            by_cases hk : k1 = k2
            · simp [hk]
            · have hne : (k1, i) ≠ (k2, i) := by simp [hk]
              simp only [hk, hne, ↓reduceIte]
              rw [hterm_val k1 k2 hne, sub_self, Complex.ofReal_zero, zero_add]
          have hantisym :
              (∑ k1 : Fin M, ∑ k2 : Fin M,
                if k1 = k2 then (0 : ℂ) else
                  (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                    ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)) = 0 := by
            have hneg_sum : ∀ S : ℂ, S = -S → S = 0 := fun S hS => by
              have h2 : (2 : ℂ) * S = 0 := by linear_combination hS
              exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
            apply hneg_sum
            calc
              (∑ k1 : Fin M, ∑ k2 : Fin M,
                if k1 = k2 then (0 : ℂ) else
                  (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                    ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ))
                  = ∑ k2 : Fin M, ∑ k1 : Fin M,
                      if k1 = k2 then (0 : ℂ) else
                        (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                          ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ) := Finset.sum_comm
              _ = -∑ k2 : Fin M, ∑ k1 : Fin M,
                      if k2 = k1 then (0 : ℂ) else
                        (-1 : ℂ) ^ (((k2 : ℤ) - (K : ℤ)) - ((k1 : ℤ) - (K : ℤ))) /
                          ((((k2 : ℤ) - (K : ℤ)) - ((k1 : ℤ) - (K : ℤ)) : ℤ) : ℂ) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun k2 _ => ?_
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun k1 _ => ?_
                    by_cases hk : k1 = k2
                    · simp [hk]
                    · simp only [hk, Ne.symm hk, ↓reduceIte]
                      have hp : (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) =
                          (-1 : ℂ) ^ (((k2 : ℤ) - (K : ℤ)) - ((k1 : ℤ) - (K : ℤ))) := by
                        rw [show ((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) =
                            -(((k2 : ℤ) - (K : ℤ)) - ((k1 : ℤ) - (K : ℤ))) by ring,
                          zpow_neg_one_pow_neg]
                      have hd : ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ) =
                          -((((k2 : ℤ) - (K : ℤ)) - ((k1 : ℤ) - (K : ℤ)) : ℤ) : ℂ) := by
                        push_cast; ring
                      rw [hp, hd, div_neg]
          calc
            ∑ k1 : Fin M, ∑ k2 : Fin M,
                (if (k1, i) = (k2, i) then (0 : ℂ) else
                  vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, i))) /
                    ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, i)) : ℝ) : ℂ))
                = ∑ k1 : Fin M, ∑ k2 : Fin M,
                    (((M : ℝ) : ℂ))⁻¹ * (u' i * star (u' i)) *
                      (if k1 = k2 then (0 : ℂ) else
                        (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                          ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)) :=
                    Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => hrew k1 k2
            _ = (((M : ℝ) : ℂ))⁻¹ * (u' i * star (u' i)) *
                  ∑ k1 : Fin M, ∑ k2 : Fin M,
                    (if k1 = k2 then (0 : ℂ) else
                      (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                        ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun k1 _ => by rw [Finset.mul_sum]
            _ = 0 := by rw [hantisym, mul_zero]
        exact hdiag_zero
      · simp only [hij, ↓reduceIte]
        have hrew : ∀ k1 k2 : Fin M,
            (if (k1, i) = (k2, j) then (0 : ℂ) else
              vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
                ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ)) =
            u' i * star (u' j) * ((((M : ℝ) : ℂ))⁻¹ *
              ((-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)))) := by
          intro k1 k2
          have hne : (k1, i) ≠ (k2, j) := fun h => hij (congrArg Prod.snd h)
          simp only [hne, ↓reduceIte]
          rw [hterm_val k1 k2 hne]
          ring
        have hLHS_pull :
            (∑ k1 : Fin M, ∑ k2 : Fin M,
              (if (k1, i) = (k2, j) then (0 : ℂ) else
                vK (finProdFinEquiv (k1, i)) * star (vK (finProdFinEquiv (k2, j))) /
                  ((xK (finProdFinEquiv (k1, i)) - xK (finProdFinEquiv (k2, j)) : ℝ) : ℂ))) =
              u' i * star (u' j) * ((((M : ℝ) : ℂ))⁻¹ *
                ∑ k1 : Fin M, ∑ k2 : Fin M,
                  (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                    (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ))) := by
          trans ∑ k1 : Fin M, ∑ k2 : Fin M,
              (u' i * star (u' j) * ((((M : ℝ) : ℂ))⁻¹ *
                ((-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                  (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ)))))
          · exact Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => hrew k1 k2
          · rw [← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k1 _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k2 _ => ?_
            exact (mul_assoc (u' i * star (u' j)) _ _).symm
        have hsum_k1 :
            (∑ k1 : Fin (2 * K + 1), ∑ k2 : Fin (2 * K + 1),
              (-1 : ℂ) ^ (((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ))) /
                (((y i - y j : ℝ) : ℂ) + ((((k1 : ℤ) - (K : ℤ)) - ((k2 : ℤ) - (K : ℤ)) : ℤ) : ℂ))) =
            ∑ z1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              ∑ z2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
                (-1 : ℂ) ^ (z1 - z2) / (((y i - y j : ℝ) : ℂ) + ((z1 - z2 : ℤ) : ℂ)) := by
          refine Finset.sum_bij (fun k1 _ => (k1 : ℤ) - (K : ℤ)) ?_ ?_ ?_ ?_
          · intro k1 _; rw [Finset.mem_Icc]; omega
          · intro a1 _ a2 _ h; ext; omega
          · intro z1 hz1
            rw [Finset.mem_Icc] at hz1
            refine ⟨⟨(z1 + K).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
            dsimp
            rw [Int.toNat_of_nonneg (by omega)]
            ring
          · intro k1 _
            refine Finset.sum_bij (fun k2 _ => (k2 : ℤ) - (K : ℤ)) ?_ ?_ ?_ ?_
            · intro k2 _; rw [Finset.mem_Icc]; omega
            · intro a1 _ a2 _ h; ext; omega
            · intro z2 hz2
              rw [Finset.mem_Icc] at hz2
              refine ⟨⟨(z2 + K).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
              dsimp
              rw [Int.toNat_of_nonneg (by omega)]
              ring
            · intro k2 _; rfl
        refine hLHS_pull.trans ?_
        dsimp [M]
        rw [hsum_k1]
    have hhilb := hilbert_inequality_real hδ0 hxK_spaced vK
    rw [hF_eq, hvK_norm_sq] at hhilb
    exact hhilb
  have hF_tendsto : Filter.Tendsto F Filter.atTop
      (𝓝 ((Real.pi : ℂ) * ∑ i : Fin R, ∑ j : Fin R,
        (if i = j then (0 : ℂ) else
          u' i * star (u' j) / ((Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ)))) := by
    have hrew_target :
        ((Real.pi : ℂ) * ∑ i : Fin R, ∑ j : Fin R,
          (if i = j then (0 : ℂ) else
            u' i * star (u' j) / ((Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ))) =
        ∑ i : Fin R, ∑ j : Fin R,
          (if i = j then (0 : ℂ) else
            u' i * star (u' j) * ((Real.pi / Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ↓reduceIte, Complex.ofReal_div]
        ring
    rw [hrew_target]
    refine tendsto_finset_sum_complex Finset.univ fun i _ =>
      tendsto_finset_sum_complex Finset.univ fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      exact tendsto_const_nhds
    · simp only [hij, ↓reduceIte]
      have hsub := tendsto_sum_neg_one_pow_div (hy_nonint i j hij)
      have hces := cesaro_tendsto_complex hsub
      have hces' : Filter.Tendsto
          (fun K : ℕ => (((2 * K + 1 : ℕ) : ℂ))⁻¹ *
            ∑ k1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              ∑ k2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
                (-1 : ℂ) ^ (k1 - k2) / (((y i - y j : ℝ) : ℂ) + ((k1 - k2 : ℤ) : ℂ)))
          Filter.atTop (𝓝 ((Real.pi / Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ)) := by
        refine hces.congr fun K => ?_
        congr 1
        exact (sum_Icc_sub_eq_cesaro
          (fun m => (-1 : ℂ) ^ m / (((y i - y j : ℝ) : ℂ) + (m : ℂ))) K).symm
      exact hces'.const_mul (u' i * star (u' j))
  have hnorm_lim : ‖(Real.pi : ℂ) * ∑ i : Fin R, ∑ j : Fin R,
      (if i = j then (0 : ℂ) else
        u' i * star (u' j) / ((Real.sin (Real.pi * (y i - y j)) : ℝ) : ℂ))‖ ≤
      Real.pi * δ⁻¹ * ∑ r ∈ J, ‖u r‖ ^ 2 := by
    refine le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hF_tendsto) ?_
    exact Filter.Eventually.of_forall hF_bd
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hsum_rewrite] at hnorm_lim
  rw [mul_assoc Real.pi δ⁻¹] at hnorm_lim
  exact le_of_mul_le_mul_left hnorm_lim Real.pi_pos

private theorem e_half_sub_neg_half (θ : ℝ) :
    e (θ / 2) - e (-(θ / 2)) = 2 * Complex.I * ((Real.sin (Real.pi * θ) : ℝ) : ℂ) := by
  dsimp [e]
  have h1 : 2 * (Real.pi : ℂ) * ((θ / 2 : ℝ) : ℂ) * Complex.I =
      ((Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * ((-(θ / 2) : ℝ) : ℂ) * Complex.I =
      -((Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, h2]
  have hsin : Complex.sin ((Real.pi * θ : ℝ) : ℂ) =
      (Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I)) * Complex.I / 2 := by
    rw [Complex.sin]
  have hsinR : Complex.sin ((Real.pi * θ : ℝ) : ℂ) = ((Real.sin (Real.pi * θ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]
  rw [hsinR] at hsin
  calc
    Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I)
        = -(Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I)) := by ring
    _ = 2 * Complex.I *
          ((Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I)) * Complex.I / 2) := by
        calc
          -(Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I))
              = (Complex.I * Complex.I) * (Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
                  Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I)) := by
                rw [Complex.I_mul_I]; ring
          _ = 2 * Complex.I *
                ((Complex.exp (-((Real.pi * θ : ℝ) : ℂ) * Complex.I) -
                    Complex.exp (((Real.pi * θ : ℝ) : ℂ) * Complex.I)) * Complex.I / 2) := by ring
    _ = 2 * Complex.I * ((Real.sin (Real.pi * θ) : ℝ) : ℂ) := by rw [← hsin]

private theorem sum_e_Ioc_formula (θ : ℝ) (M N : ℕ) (hsin : Real.sin (Real.pi * θ) ≠ 0) :
    ∑ n ∈ Finset.Ioc M (M + N), e (θ * (n : ℝ)) =
      (e (θ * ((M : ℝ) + (N : ℝ) + 1 / 2)) - e (θ * ((M : ℝ) + 1 / 2))) /
        (2 * Complex.I * ((Real.sin (Real.pi * θ) : ℝ) : ℂ)) := by
  have hden := e_half_sub_neg_half θ
  have hden_nz : e (θ / 2) - e (-(θ / 2)) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hsin)
  have hmul_tele :
      (e (θ / 2) - e (-(θ / 2))) * ∑ n ∈ Finset.Ioc M (M + N), e (θ * (n : ℝ)) =
        e (θ * ((M : ℝ) + (N : ℝ) + 1 / 2)) - e (θ * ((M : ℝ) + 1 / 2)) := by
    rw [Finset.mul_sum]
    have hstep : ∀ n : ℕ,
        (e (θ / 2) - e (-(θ / 2))) * e (θ * (n : ℝ)) =
          e (θ * ((n : ℝ) + 1 / 2)) - e (θ * ((n : ℝ) - 1 / 2)) := by
      intro n
      rw [sub_mul, ← e_add, ← e_add,
        show θ / 2 + θ * (n : ℝ) = θ * ((n : ℝ) + 1 / 2) by ring,
        show -(θ / 2) + θ * (n : ℝ) = θ * ((n : ℝ) - 1 / 2) by ring]
    simp_rw [hstep]
    induction N with
    | zero => simp
    | succ K ih =>
      have hIoc : Finset.Ioc M (M + (K + 1)) = insert (M + K + 1) (Finset.Ioc M (M + K)) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      rw [hIoc, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega), ih]
      push_cast; ring_nf
  rw [← hden, eq_div_iff hden_nz, mul_comm, hmul_tele]

/-- **Analytic Large Sieve Inequality (additive `N + δ⁻¹` form, valid for all `M, N : ℕ`)**:
for any finite `δ`-well-spaced family `α : κ → ℝ` mod `1` (`0 < δ ≤ 1`),
`∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤ (N + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2`. -/
theorem analytic_large_sieve_add_inv {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (a : ℕ → ℂ) (M N : ℕ) :
    ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      ((N : ℝ) + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let S := Finset.Ioc M (M + N)
  let c : κ → ℕ → ℂ := fun r n => e (α r * (n : ℝ))
  have hdual : ∀ b : κ → ℂ,
      ∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 ≤ ((N : ℝ) + δ⁻¹) * ∑ r ∈ J, ‖b r‖ ^ 2 := by
    intro b
    have hnorm_sq : ∀ n : ℕ, ((‖∑ r ∈ J, b r * c r n‖ ^ 2 : ℝ) : ℂ) =
        ∑ r ∈ J, ∑ s ∈ J, b r * star (b s) * e ((α r - α s) * (n : ℝ)) := by
      intro n
      let w := ∑ r ∈ J, b r * c r n
      have hw : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [hw]
      dsimp [w]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      dsimp [c]
      simp only [map_mul, ← Complex.star_def, ← e_neg]
      rw [mul_mul_mul_comm, ← e_add]
      have harg : α r * (n : ℝ) + -(α s * (n : ℝ)) = (α r - α s) * (n : ℝ) := by ring
      rw [harg]
    have hsum_eq :
        ((∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 : ℝ) : ℂ) =
          ((N : ℝ) : ℂ) * ((∑ r ∈ J, ‖b r‖ ^ 2 : ℝ) : ℂ) +
            ∑ r ∈ J, ∑ s ∈ J,
              (if r = s then (0 : ℂ) else
                b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ))) := by
      rw [Complex.ofReal_sum]
      simp_rw [hnorm_sq]
      rw [Finset.sum_comm]
      have hswap :
          (∑ r ∈ J, ∑ n ∈ S, ∑ s ∈ J, b r * star (b s) * e ((α r - α s) * (n : ℝ))) =
          ∑ r ∈ J, ∑ s ∈ J, b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.mul_sum]
      rw [hswap]
      have hsplit : ∀ r s : κ,
          b r * star (b s) * (∑ n ∈ S, e ((α r - α s) * (n : ℝ))) =
            (if r = s then ((N : ℂ) * ((‖b r‖ ^ 2 : ℝ) : ℂ)) else 0) +
              (if r = s then 0 else b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ))) := by
        intro r s
        by_cases hrs : r = s
        · subst hrs
          simp only [↓reduceIte, sub_self, zero_mul, e_zero, Finset.sum_const, S, Nat.card_Ioc,
            add_tsub_cancel_left, nsmul_eq_mul, add_zero]
          have hbb : b r * star (b r) = ((‖b r‖ ^ 2 : ℝ) : ℂ) := by
            rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
          rw [hbb]
          ring
        · simp [hrs]
      rw [Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => hsplit r s]
      rw [Finset.sum_congr rfl fun r _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      have hdiag : (∑ r ∈ J, ∑ s ∈ J, if r = s then (N : ℂ) * ((‖b r‖ ^ 2 : ℝ) : ℂ) else 0) =
          ((N : ℝ) : ℂ) * ((∑ r ∈ J, ‖b r‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum, Complex.ofReal_natCast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_eq_single r]
        · simp
        · intro s _ hsr; simp [Ne.symm hsr]
        · intro hn; exact absurd hr hn
      exact hdiag
    have hdiag_real :
        ((∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 : ℝ) : ℂ) -
            ((N : ℝ) : ℂ) * ((∑ r ∈ J, ‖b r‖ ^ 2 : ℝ) : ℂ) =
          ∑ r ∈ J, ∑ s ∈ J,
            (if r = s then (0 : ℂ) else b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ))) := by
      rw [hsum_eq]; ring
    let u1 : κ → ℂ := fun r => b r * e (α r * ((M : ℝ) + 1 / 2))
    let u2 : κ → ℂ := fun r => b r * e (α r * ((M : ℝ) + (N : ℝ) + 1 / 2))
    have hu1_norm : ∀ r, ‖u1 r‖ = ‖b r‖ := fun r => by
      dsimp [u1]; rw [norm_mul, norm_e, mul_one]
    have hu2_norm : ∀ r, ‖u2 r‖ = ‖b r‖ := fun r => by
      dsimp [u2]; rw [norm_mul, norm_e, mul_one]
    have hsin_tele : ∀ r s : κ, r ∈ J → s ∈ J → r ≠ s →
        b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ)) =
          (1 / (2 * Complex.I)) *
            (u2 r * star (u2 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ) -
             u1 r * star (u1 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) := by
      intro r s hr hs hrs
      have hsp := hws.2.2 r hr s hs hrs
      have hsin_nz : Real.sin (Real.pi * (α r - α s)) ≠ 0 := by
        intro h0
        rw [Real.sin_eq_zero_iff] at h0
        obtain ⟨k, hk⟩ := h0
        have heq : α r - α s = (k : ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by linarith)
        have hzero : distToInt (α r - α s) = 0 := by
          rw [heq, ← zero_add (k : ℝ), distToInt_add_intCast]; simp [distToInt]
        linarith [hws.1, hsp]
      have hsum_formula : ∑ n ∈ S, e ((α r - α s) * (n : ℝ)) =
          (e ((α r - α s) * ((M : ℝ) + (N : ℝ) + 1 / 2)) - e ((α r - α s) * ((M : ℝ) + 1 / 2))) /
            (2 * Complex.I * ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) :=
        sum_e_Ioc_formula (α r - α s) M N hsin_nz
      have hu1_prod : u1 r * star (u1 s) = b r * star (b s) * e ((α r - α s) * ((M : ℝ) + 1 / 2)) := by
        dsimp [u1]
        simp only [map_mul, ← Complex.star_def, ← e_neg]
        rw [mul_mul_mul_comm, ← e_add,
          show α r * ((M : ℝ) + 1 / 2) + -(α s * ((M : ℝ) + 1 / 2)) =
            (α r - α s) * ((M : ℝ) + 1 / 2) by ring]
      have hu2_prod : u2 r * star (u2 s) = b r * star (b s) * e ((α r - α s) * ((M : ℝ) + (N : ℝ) + 1 / 2)) := by
        dsimp [u2]
        simp only [map_mul, ← Complex.star_def, ← e_neg]
        rw [mul_mul_mul_comm, ← e_add,
          show α r * ((M : ℝ) + (N : ℝ) + 1 / 2) + -(α s * ((M : ℝ) + (N : ℝ) + 1 / 2)) =
            (α r - α s) * ((M : ℝ) + (N : ℝ) + 1 / 2) by ring]
      rw [hsum_formula, hu1_prod, hu2_prod]
      have hsinC : ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hsin_nz
      field_simp [Complex.I_ne_zero, hsinC]
    have hsplit_u :
        ∑ r ∈ J, ∑ s ∈ J,
          (if r = s then (0 : ℂ) else b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ))) =
        (1 / (2 * Complex.I)) *
          ((∑ r ∈ J, ∑ s ∈ J,
              if r = s then (0 : ℂ) else
                u2 r * star (u2 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) -
           (∑ r ∈ J, ∑ s ∈ J,
              if r = s then (0 : ℂ) else
                u1 r * star (u1 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ))) := by
      have h1 :
          ∑ r ∈ J, ∑ s ∈ J,
            (if r = s then (0 : ℂ) else b r * star (b s) * ∑ n ∈ S, e ((α r - α s) * (n : ℝ))) =
          ∑ r ∈ J, ∑ s ∈ J,
            ((1 / (2 * Complex.I)) *
              ((if r = s then (0 : ℂ) else
                  u2 r * star (u2 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) -
               (if r = s then (0 : ℂ) else
                  u1 r * star (u1 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)))) := by
        refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
        by_cases hrs : r = s
        · simp [hrs]
        · simp only [hrs, ↓reduceIte]
          exact hsin_tele r s hr hs hrs
      rw [h1]
      trans (1 / (2 * Complex.I)) * ∑ r ∈ J, ∑ s ∈ J,
        ((if r = s then (0 : ℂ) else
            u2 r * star (u2 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) -
         (if r = s then (0 : ℂ) else
            u1 r * star (u1 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)))
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
      · congr 1
        simp_rw [Finset.sum_sub_distrib]
    have hdiff_norm :
        |∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 - (N : ℝ) * ∑ r ∈ J, ‖b r‖ ^ 2| ≤
          δ⁻¹ * ∑ r ∈ J, ‖b r‖ ^ 2 := by
      have hsub_eq := hdiag_real.trans hsplit_u
      have hnorm_lhs :
          |∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 - (N : ℝ) * ∑ r ∈ J, ‖b r‖ ^ 2| =
            ‖((∑ n ∈ S, ‖∑ r ∈ J, b r * c r n‖ ^ 2 : ℝ) : ℂ) -
              ((N : ℝ) : ℂ) * ((∑ r ∈ J, ‖b r‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm_lhs, hsub_eq, norm_mul]
      have hcoef : ‖(1 : ℂ) / (2 * Complex.I)‖ = 1 / 2 := by
        rw [one_div, norm_inv, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one,
          one_div]
      have hb1 := hilbert_inequality_sin_pi J α hws u1
      have hb2 := hilbert_inequality_sin_pi J α hws u2
      simp_rw [hu1_norm] at hb1
      simp_rw [hu2_norm] at hb2
      rw [hcoef]
      have htri := norm_sub_le
        (∑ r ∈ J, ∑ s ∈ J,
          if r = s then (0 : ℂ) else u2 r * star (u2 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ))
        (∑ r ∈ J, ∑ s ∈ J,
          if r = s then (0 : ℂ) else u1 r * star (u1 s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ))
      nlinarith
    linarith [(abs_le.mp hdiff_norm).2]
  exact (duality_iff S J c (add_nonneg (Nat.cast_nonneg N) (inv_nonneg.mpr hws.1.le))).mpr hdual a

/-- **Sharp Analytic Large Sieve Inequality** (Montgomery–Vaughan):
for `1 ≤ N` and any finite `δ`-well-spaced family `α : κ → ℝ` mod `1` (`0 < δ ≤ 1`),
`∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤ (N - 1 + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2`. -/
theorem analytic_large_sieve {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (a : ℕ → ℂ) (M : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      ((N : ℝ) - 1 + δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let L : ℝ := ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2
  let E : ℝ := ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2
  have hE_nn : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK_bd : ∀ K : ℕ, 1 ≤ K →
      L ≤ ((N : ℝ) - 1 + δ⁻¹ + (K : ℝ)⁻¹) * E := by
    intro K hK
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    let JK := J ×ˢ Finset.range K
    let β : κ × ℕ → ℝ := fun rk => (α rk.1 + (rk.2 : ℝ)) / (K : ℝ)
    have hws_K : WellSpacedModOne JK β (δ / K) := by
      refine ⟨div_pos hws.1 hK_pos, ?_, ?_⟩
      · have : (K : ℝ) ≥ 1 := by exact_mod_cast hK
        rw [div_le_one hK_pos]
        exact hws.2.1.trans this
      · rintro ⟨r1, k1⟩ h1 ⟨r2, k2⟩ h2 hne
        rw [Finset.mem_product, Finset.mem_range] at h1 h2
        let m : ℤ := round (β (r1, k1) - β (r2, k2))
        let t : ℝ := (β (r1, k1) - β (r2, k2)) - (m : ℝ)
        have ht_eq : distToInt (β (r1, k1) - β (r2, k2)) = |t| := rfl
        have hscale : (K : ℝ) * t =
            (α r1 - α r2) + ((k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ) : ℤ) := by
          dsimp [t, β]
          push_cast
          field_simp [hK_pos.ne']
          ring
        have hKt_ge : δ ≤ (K : ℝ) * |t| := by
          by_cases hr : r1 = r2
          · subst hr
            have hk_ne : k1 ≠ k2 := fun h => hne (by ext <;> simp [h])
            have hsub : (K : ℝ) * t = (((k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ) : ℤ) : ℝ) := by
              rw [hscale, sub_self, zero_add]
            have hz_ne : (k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ) ≠ 0 := by
              intro hz
              have hdvd : (K : ℤ) ∣ (k1 : ℤ) - (k2 : ℤ) := ⟨m, by linarith⟩
              have hlt1 : (k1 : ℤ) - (k2 : ℤ) < (K : ℤ) := by omega
              have hlt2 : -(K : ℤ) < (k1 : ℤ) - (k2 : ℤ) := by omega
              have h0 : (k1 : ℤ) - (k2 : ℤ) = 0 := by
                rcases hdvd with ⟨q, hq⟩
                have hq0 : q = 0 := by nlinarith
                rw [hq0, mul_zero] at hq
                exact hq
              omega
            have hz_ge1 : (1 : ℝ) ≤ |(((k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ) : ℤ) : ℝ)| := by
              have hz_abs : (1 : ℤ) ≤ |(k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ)| := by
                rcases lt_or_gt_of_ne hz_ne with hlt | hgt
                · rw [abs_of_neg hlt]; omega
                · rw [abs_of_pos hgt]; omega
              exact_mod_cast hz_abs
            rw [← abs_of_pos hK_pos, ← abs_mul, hsub]
            exact hws.2.1.trans hz_ge1
          · have hsp := hws.2.2 r1 h1.1 r2 h2.1 hr
            have hle := distToInt_le_abs_sub (α r1 - α r2) (-((k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ)))
            have heq : (α r1 - α r2) - ((-((k1 : ℤ) - (k2 : ℤ) - m * (K : ℤ)) : ℤ) : ℝ) =
                (K : ℝ) * t := by
              rw [hscale]
              push_cast
              ring
            rw [heq, abs_mul, abs_of_pos hK_pos] at hle
            exact hsp.trans hle
        rw [ht_eq]
        exact (div_le_iff₀' hK_pos).mpr hKt_ge
    let M' : ℕ := M * K + K - 1
    let N' : ℕ := (N - 1) * K + 1
    let b : ℕ → ℂ := fun m => if m % K = 0 then a (m / K) else 0
    have hK_nat_pos : 0 < K := by omega
    have hMN' : M' + N' = M * K + N * K := by
      dsimp [M', N']
      have hMK : 1 ≤ M * K + K := Nat.le_trans hK (Nat.le_add_left K (M * K))
      zify [hMK, hN]
      ring
    have htrig_K : ∀ rk : κ × ℕ, trigPoly b M' N' (β rk) = trigPoly a M N (α rk.1) := by
      intro ⟨r, k⟩
      dsimp [trigPoly, β]
      rw [hMN']
      have hsum_zero : ∑ m ∈ (Finset.Ioc M' (M * K + N * K)).filter (fun m => m % K ≠ 0),
          b m * e ((α r + k) / K * m) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hne := (Finset.mem_filter.mp hm).2
        simp [b, hne]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc M' (M * K + N * K)) (fun m => m % K = 0),
        hsum_zero, add_zero]
      refine Finset.sum_bij (fun m _ => m / K) ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm
        obtain ⟨⟨hm1, hm2⟩, hmod⟩ := hm
        have hdvd : K ∣ m := Nat.dvd_of_mod_eq_zero hmod
        obtain ⟨q, rfl⟩ := hdvd
        rw [Nat.mul_div_right q hK_nat_pos]
        rw [Finset.mem_Ioc]
        dsimp [M'] at hm1
        constructor
        · by_contra hle
          have hqM : q ≤ M := by omega
          have : K * q ≤ M * K + K - 1 := by
            have : K * q ≤ M * K := by nlinarith
            omega
          omega
        · nlinarith
      · intro m1 hm1 m2 hm2 heq
        have h1 : K ∣ m1 := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm1).2
        have h2 : K ∣ m2 := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm2).2
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        refine ⟨n * K, ?_, Nat.mul_div_left n hK_nat_pos⟩
        rw [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, Nat.mul_mod_left n K⟩
        · dsimp [M']
          have hn1 : M + 1 ≤ n := hn.1
          have : (M + 1) * K ≤ n * K := Nat.mul_le_mul_right K hn1
          have : M * K + K ≤ n * K := by linarith
          omega
        · nlinarith [hn.2]
      · intro m hm
        have hmod : m % K = 0 := (Finset.mem_filter.mp hm).2
        have hdvd : K ∣ m := Nat.dvd_of_mod_eq_zero hmod
        dsimp [b]
        simp only [hmod, ↓reduceIte]
        congr 1
        let q := m / K
        have hq : m = q * K := (Nat.div_mul_cancel hdvd).symm
        have hmdiv : (m : ℝ) / (K : ℝ) = (q : ℝ) := by
          conv_lhs => rw [hq]
          rw [Nat.cast_mul]
          field_simp [hK_pos.ne']
        have harg : (α r + (k : ℝ)) / (K : ℝ) * (m : ℝ) =
            α r * (q : ℝ) + (((k * q : ℕ) : ℤ) : ℝ) := by
          calc
            (α r + (k : ℝ)) / (K : ℝ) * (m : ℝ)
                = (α r + (k : ℝ)) * ((m : ℝ) / (K : ℝ)) := by ring
            _ = (α r + (k : ℝ)) * (q : ℝ) := by rw [hmdiv]
            _ = α r * (q : ℝ) + (((k * q : ℕ) : ℤ) : ℝ) := by
                rw [Int.cast_natCast, Nat.cast_mul]; ring
        rw [harg, e_add_int]
    have hE_K : ∑ m ∈ Finset.Ioc M' (M' + N'), ‖b m‖ ^ 2 = E := by
      rw [hMN']
      have hsum_zero : ∑ m ∈ (Finset.Ioc M' (M * K + N * K)).filter (fun m => m % K ≠ 0),
          ‖b m‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hne := (Finset.mem_filter.mp hm).2
        simp [b, hne]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc M' (M * K + N * K)) (fun m => m % K = 0),
        hsum_zero, add_zero]
      refine Finset.sum_bij (fun m _ => m / K) ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm
        obtain ⟨⟨hm1, hm2⟩, hmod⟩ := hm
        have hdvd : K ∣ m := Nat.dvd_of_mod_eq_zero hmod
        obtain ⟨q, rfl⟩ := hdvd
        rw [Nat.mul_div_right q hK_nat_pos, Finset.mem_Ioc]
        dsimp [M'] at hm1
        constructor
        · by_contra hle; have hqM : q ≤ M := by omega
          have : K * q ≤ M * K := by nlinarith
          omega
        · nlinarith
      · intro m1 hm1 m2 hm2 heq
        have h1 : K ∣ m1 := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm1).2
        have h2 : K ∣ m2 := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm2).2
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        refine ⟨n * K, ?_, Nat.mul_div_left n hK_nat_pos⟩
        rw [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, Nat.mul_mod_left n K⟩
        · dsimp [M']
          have : (M + 1) * K ≤ n * K := Nat.mul_le_mul_right K hn.1
          have : M * K + K ≤ n * K := by linarith
          omega
        · nlinarith [hn.2]
      · intro m hm
        simp [b, (Finset.mem_filter.mp hm).2]
    have hls := analytic_large_sieve_add_inv JK β hws_K b M' N'
    simp_rw [htrig_K] at hls
    rw [hE_K] at hls
    have hLHS : ∑ rk ∈ JK, ‖trigPoly a M N (α rk.1)‖ ^ 2 = (K : ℝ) * L := by
      dsimp [JK, L]
      rw [Finset.sum_product]
      have hconst : ∀ r ∈ J, ∑ _k ∈ Finset.range K, ‖trigPoly a M N (α r)‖ ^ 2 =
          (K : ℝ) * ‖trigPoly a M N (α r)‖ ^ 2 := fun r _ => by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
    have hRHS : ((N' : ℝ) + (δ / (K : ℝ))⁻¹) = (K : ℝ) * ((N : ℝ) - 1 + δ⁻¹ + (K : ℝ)⁻¹) := by
      dsimp [N']
      have h1 : 1 ≤ N := hN
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
      field_simp [hK_pos.ne']
      ring
    rw [hLHS, hRHS, mul_assoc] at hls
    exact le_of_mul_le_mul_left hls hK_pos
  have hlim : Filter.Tendsto (fun K : ℕ => ((N : ℝ) - 1 + δ⁻¹ + (K : ℝ)⁻¹) * E)
      Filter.atTop (𝓝 (((N : ℝ) - 1 + δ⁻¹) * E)) := by
    have hinv : Filter.Tendsto (fun K : ℕ => (K : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using ((tendsto_const_nhds.add hinv).mul_const E)
  exact ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, hK_bd⟩)

/-- Analytic Large Sieve in `(N + π δ⁻¹)` form, valid for all `M, N : ℕ`. -/
theorem analytic_large_sieve_le_add_pi_inv {κ : Type*} (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hws : WellSpacedModOne J α δ) (a : ℕ → ℂ) (M N : ℕ) :
    ∑ r ∈ J, ‖trigPoly a M N (α r)‖ ^ 2 ≤
      ((N : ℝ) + Real.pi * δ⁻¹) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have h1 := analytic_large_sieve_add_inv J α hws a M N
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have hden : 0 ≤ δ⁻¹ := (inv_pos.mpr hws.1).le
  have hE : 0 ≤ ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : (N : ℝ) + δ⁻¹ ≤ (N : ℝ) + Real.pi * δ⁻¹ := by nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_right hle hE)

/-! ### Farey-Point Spacing and Rényi's Prime-Modulus Variance -/

/-- Set of reduced Farey pairs `(q, a)` with `1 ≤ q ≤ Q`, `0 ≤ a < q`, and `Nat.Coprime a q`. -/
def fareyPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => (q, a))

/-- Rational point `(a / q : ℝ)` associated with a Farey pair `(q, a)`. -/
def fareyFraction (p : ℕ × ℕ) : ℝ := (p.2 : ℝ) / (p.1 : ℝ)

/-- Reduced Farey fractions up to denominator `Q ≥ 1` are `(Q ^ 2)⁻¹`-well-spaced modulo `1`. -/
theorem wellSpacedModOne_fareyPairs {Q : ℕ} (hQ : 1 ≤ Q) :
    WellSpacedModOne (fareyPairs Q) fareyFraction ((Q : ℝ) ^ 2)⁻¹ := by
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  refine ⟨inv_pos.mpr (sq_pos_of_pos hQ_pos), ?_, ?_⟩
  · have hQ1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    exact inv_le_one_of_one_le₀ hQ1
  · intro p1 hp1 p2 hp2 hne
    rw [fareyPairs, Finset.mem_biUnion] at hp1 hp2
    rcases hp1 with ⟨q1, hq1_mem, hp1'⟩
    rcases hp2 with ⟨q2, hq2_mem, hp2'⟩
    rw [Finset.mem_image] at hp1' hp2'
    rcases hp1' with ⟨a1, ha1_mem, rfl⟩
    rcases hp2' with ⟨a2, ha2_mem, rfl⟩
    rw [Finset.mem_Icc] at hq1_mem hq2_mem
    rw [Finset.mem_filter, Finset.mem_range] at ha1_mem ha2_mem
    let m : ℤ := round (fareyFraction (q1, a1) - fareyFraction (q2, a2))
    let num : ℤ := (a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - m * (q1 : ℤ) * (q2 : ℤ)
    have hnum_ne : num ≠ 0 := by
      intro h0
      have hq1_dvd : (q1 : ℤ) ∣ (a1 : ℤ) * (q2 : ℤ) :=
        ⟨(a2 : ℤ) + m * (q2 : ℤ), by dsimp [num] at h0; linarith⟩
      have hq2_dvd : (q2 : ℤ) ∣ (a2 : ℤ) * (q1 : ℤ) :=
        ⟨(a1 : ℤ) - m * (q1 : ℤ), by dsimp [num] at h0; linarith⟩
      have hc1 : IsCoprime (q1 : ℤ) (a1 : ℤ) :=
        Int.isCoprime_iff_nat_coprime.mpr ha1_mem.2.symm
      have hc2 : IsCoprime (q2 : ℤ) (a2 : ℤ) :=
        Int.isCoprime_iff_nat_coprime.mpr ha2_mem.2.symm
      have hd1Z : (q1 : ℤ) ∣ (q2 : ℤ) := hc1.dvd_of_dvd_mul_left hq1_dvd
      have hd2Z : (q2 : ℤ) ∣ (q1 : ℤ) := hc2.dvd_of_dvd_mul_left hq2_dvd
      have hd1 : q1 ∣ q2 := Int.natCast_dvd_natCast.mp hd1Z
      have hd2 : q2 ∣ q1 := Int.natCast_dvd_natCast.mp hd2Z
      have hq_eq : q1 = q2 := Nat.dvd_antisymm hd1 hd2
      subst hq_eq
      have hm_eq : (a1 : ℤ) - (a2 : ℤ) = m * (q1 : ℤ) := by
        have hq1_ne : (q1 : ℤ) ≠ 0 := by omega
        have hmul : ((a1 : ℤ) - (a2 : ℤ) - m * (q1 : ℤ)) * (q1 : ℤ) = 0 := by
          dsimp [num] at h0; linarith
        rcases mul_eq_zero.mp hmul with h | h
        · linarith
        · exact absurd h hq1_ne
      have hm0 : m = 0 := by
        have hq1_Z : (0 : ℤ) < q1 := by exact_mod_cast hq1_mem.1
        have ha1 : (a1 : ℤ) < (q1 : ℤ) := by exact_mod_cast ha1_mem.1
        have ha2 : (a2 : ℤ) < (q1 : ℤ) := by exact_mod_cast ha2_mem.1
        by_contra hm_ne
        rcases lt_or_gt_of_ne hm_ne with hm_neg | hm_pos
        · have : m ≤ -1 := by omega
          have : m * (q1 : ℤ) ≤ -(q1 : ℤ) := by nlinarith
          omega
        · have : 1 ≤ m := by omega
          have : (q1 : ℤ) ≤ m * (q1 : ℤ) := by nlinarith
          omega
      rw [hm0, zero_mul] at hm_eq
      have ha_eq : a1 = a2 := by omega
      exact hne (by simp [ha_eq])
    have hnum_ge1 : (1 : ℝ) ≤ |(num : ℝ)| := by
      have hnat : 1 ≤ num.natAbs := by omega
      have hreal : (1 : ℝ) ≤ (num.natAbs : ℝ) := by exact_mod_cast hnat
      simpa [Int.cast_abs] using hreal
    have hq1_pos : (0 : ℝ) < q1 := by exact_mod_cast hq1_mem.1
    have hq2_pos : (0 : ℝ) < q2 := by exact_mod_cast hq2_mem.1
    have hden_pos : (0 : ℝ) < (q1 : ℝ) * (q2 : ℝ) := mul_pos hq1_pos hq2_pos
    have hden_le : (q1 : ℝ) * (q2 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have hq1Q : (q1 : ℝ) ≤ Q := by exact_mod_cast hq1_mem.2
      have hq2Q : (q2 : ℝ) ≤ Q := by exact_mod_cast hq2_mem.2
      nlinarith
    have hdiff_eq : fareyFraction (q1, a1) - fareyFraction (q2, a2) - (m : ℝ) =
        (num : ℝ) / ((q1 : ℝ) * (q2 : ℝ)) := by
      dsimp [fareyFraction, num]
      push_cast
      field_simp [hq1_pos.ne', hq2_pos.ne']
    show ((Q : ℝ) ^ 2)⁻¹ ≤ distToInt (fareyFraction (q1, a1) - fareyFraction (q2, a2))
    change ((Q : ℝ) ^ 2)⁻¹ ≤ |fareyFraction (q1, a1) - fareyFraction (q2, a2) - (m : ℝ)|
    rw [hdiff_eq, abs_div, abs_of_pos hden_pos]
    calc
      ((Q : ℝ) ^ 2)⁻¹ ≤ ((q1 : ℝ) * (q2 : ℝ))⁻¹ := inv_anti₀ hden_pos hden_le
      _ = 1 / ((q1 : ℝ) * (q2 : ℝ)) := by rw [one_div]
      _ ≤ |(num : ℝ)| / ((q1 : ℝ) * (q2 : ℝ)) := by gcongr

/-- **Farey Large Sieve Inequality**:
for `1 ≤ Q` and `1 ≤ N`, summing `‖trigPoly a M N (a / q)‖ ^ 2` over reduced Farey pairs `(q, a)`
is bounded by `(N - 1 + Q ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2`. -/
theorem farey_large_sieve (a : ℕ → ℂ) (M : ℕ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hls := analytic_large_sieve (fareyPairs Q) fareyFraction (wellSpacedModOne_fareyPairs hQ) a M hN
  rw [inv_inv] at hls
  refine hls.trans_eq' ?_
  dsimp [fareyPairs, fareyFraction]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_image]
    · intro r1 _ r2 _ h; exact (Prod.mk.inj h).2
  · intro q1 _ q2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨q, r⟩ h1 h2
    rw [Finset.mem_image] at h1 h2
    rcases h1 with ⟨_, _, h1'⟩
    rcases h2 with ⟨_, _, h2'⟩
    exact hne (by exact (Prod.mk.inj (h1'.trans h2'.symm)).1)

/-- Farey Large Sieve for all `M, N : ℕ` (including `N = 0` or `Q = 0`). -/
theorem farey_large_sieve_add_sq (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp [trigPoly]
    exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hls := analytic_large_sieve_add_inv (fareyPairs Q) fareyFraction
    (wellSpacedModOne_fareyPairs hQ) a M N
  rw [inv_inv] at hls
  refine hls.trans_eq' ?_
  dsimp [fareyPairs, fareyFraction]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_image]
    · intro r1 _ r2 _ h; exact (Prod.mk.inj h).2
  · intro q1 _ q2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨q, r⟩ h1 h2
    rw [Finset.mem_image] at h1 h2
    rcases h1 with ⟨_, _, h1'⟩
    rcases h2 with ⟨_, _, h2'⟩
    exact hne (by exact (Prod.mk.inj (h1'.trans h2'.symm)).1)

/-- Residue-class sum `∑_{n ∈ Ioc M (M + N), n ≡ h [MOD q]} a n`. -/
def residueSum (a : ℕ → ℂ) (M N q h : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n => n ≡ h [MOD q]), a n

private theorem parseval_mod_prime (p : ℕ) (hp_pos : 0 < p) (b : ℕ → ℂ) :
    ((p : ℝ) * ∑ h ∈ Finset.range p, ‖b h‖ ^ 2 : ℝ) =
      ∑ r ∈ Finset.range p, ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 := by
  have hc :
      ((p : ℂ) * ∑ h ∈ Finset.range p, ((‖b h‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r ∈ Finset.range p,
          ((‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ r : ℕ,
        ((‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 : ℝ) : ℂ) =
          ∑ h1 ∈ Finset.range p, ∑ h2 ∈ Finset.range p,
            b h1 * star (b h2) * e ((r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ)) := by
      intro r
      let w := ∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))
      have hw : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [hw]
      dsimp [w]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun h1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h2 _ => ?_
      simp only [map_mul, ← Complex.star_def, ← e_neg]
      rw [mul_mul_mul_comm, ← e_add]
      have harg : (r : ℝ) * (h1 : ℝ) / (p : ℝ) + -((r : ℝ) * (h2 : ℝ) / (p : ℝ)) =
          (r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ) := by push_cast; ring
      rw [harg]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hswap :
        (∑ h1 ∈ Finset.range p, ∑ r ∈ Finset.range p, ∑ h2 ∈ Finset.range p,
          b h1 * star (b h2) * e ((r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ))) =
        ∑ h1 ∈ Finset.range p, ∑ h2 ∈ Finset.range p,
          b h1 * star (b h2) * ∑ r ∈ Finset.range p, e ((r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ)) := by
      refine Finset.sum_congr rfl fun h1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h2 _ => by rw [← Finset.mul_sum]
    rw [hswap]
    have hgeo : ∀ h1 h2 : ℕ, h1 ∈ Finset.range p → h2 ∈ Finset.range p →
        ∑ r ∈ Finset.range p, e ((r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ)) =
          if h1 = h2 then (p : ℂ) else 0 := by
      intro h1 h2 hh1 hh2
      rw [Finset.mem_range] at hh1 hh2
      by_cases heq : h1 = h2
      · subst heq
        simp [e_zero]
      · simp only [heq, ↓reduceIte]
        let z := e (((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ))
        have hz_pow : ∀ r : ℕ, e ((r : ℝ) * ((h1 : ℤ) - (h2 : ℤ)) / (p : ℝ)) = z ^ r := by
          intro r
          dsimp [z, e]
          rw [← Complex.exp_nat_mul]
          congr 1
          push_cast
          ring
        have hzp : z ^ p = 1 := by
          rw [← hz_pow p]
          have harg : (p : ℝ) * (((h1 : ℤ) : ℝ) - ((h2 : ℤ) : ℝ)) / (p : ℝ) =
              0 + (((h1 : ℤ) - (h2 : ℤ) : ℤ) : ℝ) := by
            have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
            push_cast
            field_simp [hpR]
            ring
          rw [harg, e_add_int, e_zero]
        have hz_ne : z ≠ 1 := by
          intro h1z
          dsimp [z, e] at h1z
          rw [Complex.exp_eq_one_iff] at h1z
          obtain ⟨k, hk⟩ := h1z
          have hden : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
            mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
          have hdiv : ((((h1 : ℤ) - (h2 : ℤ) : ℤ) : ℝ) / (p : ℝ) : ℂ) = (k : ℂ) := by
            have hmul : (((((h1 : ℤ) - (h2 : ℤ) : ℤ) : ℝ) / (p : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) =
                (k : ℂ) * (2 * Real.pi * Complex.I) := by
              push_cast at hk ⊢; linear_combination hk
            exact mul_right_cancel₀ hden hmul
          have hre' := congrArg Complex.re hdiv
          simp only [← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re] at hre'
          have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
          have hZ : (h1 : ℤ) - (h2 : ℤ) = k * (p : ℤ) := by
            have hmulR : (((h1 : ℤ) - (h2 : ℤ) : ℤ) : ℝ) = ((k * (p : ℤ) : ℤ) : ℝ) := by
              field_simp [hpR] at hre'
              push_cast at hre' ⊢
              linarith [hre']
            exact_mod_cast hmulR
          have h1Z : (h1 : ℤ) < (p : ℤ) := by exact_mod_cast hh1
          have h2Z : (h2 : ℤ) < (p : ℤ) := by exact_mod_cast hh2
          have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp_pos
          rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
          · have : k ≤ -1 := by omega
            have : k * (p : ℤ) ≤ -(p : ℤ) := by nlinarith
            omega
          · simp at hZ; omega
          · have : 1 ≤ k := by omega
            have : (p : ℤ) ≤ k * (p : ℤ) := by nlinarith
            omega
        simp_rw [hz_pow]
        have hsum_gp := geom_sum_mul z p
        rw [hzp, sub_self, mul_eq_zero] at hsum_gp
        exact hsum_gp.resolve_right (sub_ne_zero.mpr hz_ne)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h1 hh1 => ?_
    rw [Finset.sum_eq_single h1]
    · rw [hgeo h1 h1 hh1 hh1]
      simp only [ite_true]
      have hbb : b h1 * star (b h1) = ((‖b h1‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [hbb]
      ring
    · intro h2 hh2 hne
      rw [hgeo h1 h2 hh1 hh2]
      simp [hne.symm]
    · intro hnot
      exact absurd hh1 hnot
  exact_mod_cast hc

private theorem sum_e_div_prime_eq_zero {p r : ℕ} (hp_pos : 0 < p) (hr_pos : 0 < r) (hr_lt : r < p) :
    ∑ h ∈ Finset.range p, e ((r : ℝ) * (h : ℝ) / (p : ℝ)) = 0 := by
  let z := e ((r : ℝ) / (p : ℝ))
  have hz_pow : ∀ h : ℕ, e ((r : ℝ) * (h : ℝ) / (p : ℝ)) = z ^ h := fun h => by
    dsimp [z, e]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hzp : z ^ p = 1 := by
    rw [← hz_pow p]
    have harg : (r : ℝ) * (p : ℝ) / (p : ℝ) = 0 + ((r : ℤ) : ℝ) := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
      push_cast; field_simp [hpR]; ring
    rw [harg, e_add_int, e_zero]
  have hz_ne : z ≠ 1 := by
    intro h1z
    dsimp [z, e] at h1z
    rw [Complex.exp_eq_one_iff] at h1z
    obtain ⟨k, hk⟩ := h1z
    have hden : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hdiv : ((r : ℝ) / (p : ℝ) : ℂ) = (k : ℂ) := by
      have hmul : (((r : ℝ) / (p : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) =
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast at hk ⊢; linear_combination hk
      exact mul_right_cancel₀ hden hmul
    have hre := congrArg Complex.re hdiv
    simp only [← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re] at hre
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
    have hrZ : (r : ℤ) = k * (p : ℤ) := by
      have hmulR : ((r : ℤ) : ℝ) = ((k * (p : ℤ) : ℤ) : ℝ) := by
        push_cast; field_simp [hpR] at hre; linarith [hre]
      exact_mod_cast hmulR
    have hr_posZ : (0 : ℤ) < r := by exact_mod_cast hr_pos
    have hr_ltZ : (r : ℤ) < p := by exact_mod_cast hr_lt
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp_pos
    rcases le_or_gt k 0 with hk0 | hk1
    · have : k * (p : ℤ) ≤ 0 := by nlinarith
      omega
    · have : (p : ℤ) ≤ k * (p : ℤ) := by nlinarith
      omega
  simp_rw [hz_pow]
  have hsum_gp := geom_sum_mul z p
  rw [hzp, sub_self, mul_eq_zero] at hsum_gp
  exact hsum_gp.resolve_right (sub_ne_zero.mpr hz_ne)

/-- **Rényi's Prime-Modulus Variance Bound** via the Large Sieve:
for `1 ≤ N` and `1 ≤ Q`, setting `Z = ∑_{n ∈ Ioc M (M + N)} a n`,
`∑_{p ≤ Q prime} p * ∑_{h < p} ‖residueSum a M N p h - Z / p‖ ^ 2 ≤ (N - 1 + Q ^ 2) * ∑_{n} ‖a n‖ ^ 2`. -/
theorem renyi_prime_variance_large_sieve (a : ℕ → ℂ) (M : ℕ) {N Q : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ p ∈ (Finset.Icc 1 Q).filter Nat.Prime,
        (p : ℝ) * ∑ h ∈ Finset.range p,
          ‖residueSum a M N p h - (∑ n ∈ Finset.Ioc M (M + N), a n) / (p : ℂ)‖ ^ 2 ≤
      ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let Z : ℂ := ∑ n ∈ Finset.Ioc M (M + N), a n
  have hp_identity : ∀ p : ℕ, p.Prime →
      ((p : ℝ) * ∑ h ∈ Finset.range p, ‖residueSum a M N p h - Z / (p : ℂ)‖ ^ 2) =
        ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
          ‖trigPoly a M N ((r : ℝ) / (p : ℝ))‖ ^ 2 := by
    intro p hp
    have hp_pos : 0 < p := hp.pos
    let b : ℕ → ℂ := fun h => residueSum a M N p h - Z / (p : ℂ)
    have hsum_b : ∑ h ∈ Finset.range p, b h = 0 := by
      have hZ : ∑ h ∈ Finset.range p, residueSum a M N p h = Z := by
        dsimp [residueSum, Z]
        rw [← Finset.sum_biUnion]
        · congr 1
          ext n
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
          constructor
          · rintro ⟨h, _, hn, _⟩; exact hn
          · intro hn
            exact ⟨n % p, Nat.mod_lt n hp_pos, hn, (Nat.mod_modEq n p).symm⟩
        · intro h1 hh1 h2 hh2 hne
          rw [Function.onFun, Finset.disjoint_left]
          intro n hn1 hn2
          rw [Finset.mem_filter] at hn1 hn2
          have hm1 : n % p = h1 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh1)) ▸ hn1.2
          have hm2 : n % p = h2 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh2)) ▸ hn2.2
          exact hne (hm1.symm.trans hm2)
      simp_rw [b, Finset.sum_sub_distrib, hZ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
      field_simp [hpC]
      ring
    rw [parseval_mod_prime p hp_pos b]
    have hsplit_r : Finset.range p =
        insert 0 ((Finset.range p).filter (fun r => Nat.Coprime r p)) := by
      ext r
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hr
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · left; rfl
        · right
          refine ⟨hr, ?_⟩
          exact ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hr0 hr)).symm
      · rintro (rfl | ⟨hr, _⟩)
        · exact hp_pos
        · exact hr
    have hsum_split :
        ∑ r ∈ Finset.range p, ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 =
          ‖∑ h ∈ Finset.range p, b h * e ((0 : ℕ) * (h : ℝ) / (p : ℝ))‖ ^ 2 +
            ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
              ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 := by
      calc
        ∑ r ∈ Finset.range p, ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2
            = ∑ r ∈ insert 0 ((Finset.range p).filter (fun r => Nat.Coprime r p)),
                ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 :=
              Finset.sum_congr hsplit_r fun _ _ => rfl
        _ = ‖∑ h ∈ Finset.range p, b h * e ((0 : ℕ) * (h : ℝ) / (p : ℝ))‖ ^ 2 +
              ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
                ‖∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 :=
              Finset.sum_insert (by simp [hp.ne_one])
    rw [hsum_split]
    have hzero : ∑ h ∈ Finset.range p, b h * e ((0 : ℕ) * (h : ℝ) / (p : ℝ)) = 0 := by
      simpa [e_zero] using hsum_b
    rw [hzero, norm_zero, sq, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hcop : Nat.Coprime r p := (Finset.mem_filter.mp hr).2
    have hnot0 : r ≠ 0 := by
      intro hr0; subst hr0; rw [Nat.coprime_zero_left] at hcop; exact hp.ne_one hcop
    have hr_lt : r < p := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have horth : ∑ h ∈ Finset.range p, e ((r : ℝ) * (h : ℝ) / (p : ℝ)) = 0 :=
      sum_e_div_prime_eq_zero hp_pos (Nat.pos_of_ne_zero hnot0) hr_lt
    have htrig : ∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ)) =
        trigPoly a M N ((r : ℝ) / (p : ℝ)) := by
      have hsub_z : ∑ h ∈ Finset.range p, (Z / (p : ℂ)) * e ((r : ℝ) * (h : ℝ) / (p : ℝ)) = 0 := by
        rw [← Finset.mul_sum, horth, mul_zero]
      have hsub_split :
          ∑ h ∈ Finset.range p, b h * e ((r : ℝ) * (h : ℝ) / (p : ℝ)) =
            (∑ h ∈ Finset.range p, residueSum a M N p h * e ((r : ℝ) * (h : ℝ) / (p : ℝ))) -
              ∑ h ∈ Finset.range p, (Z / (p : ℂ)) * e ((r : ℝ) * (h : ℝ) / (p : ℝ)) := by
        simp only [b, sub_mul, Finset.sum_sub_distrib]
      rw [hsub_split, hsub_z, sub_zero]
      dsimp [residueSum, trigPoly]
      have hin : ∀ h ∈ Finset.range p,
          (∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n => n ≡ h [MOD p]), a n) *
            e ((r : ℝ) * (h : ℝ) / (p : ℝ)) =
          ∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n => n ≡ h [MOD p]),
            a n * e ((r : ℝ) / (p : ℝ) * (n : ℝ)) := by
        intro h hh
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hmod := (Finset.mem_filter.mp hn).2
        have hnp : n % p = h := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh)) ▸ hmod
        let q := n / p
        have hn_eq : n = p * q + h := by
          change n = p * (n / p) + h
          rw [← hnp, Nat.div_add_mod]
        have harg : (r : ℝ) / (p : ℝ) * (n : ℝ) =
            (r : ℝ) * (h : ℝ) / (p : ℝ) + (((r * q : ℕ) : ℤ) : ℝ) := by
          conv_lhs => rw [hn_eq]
          rw [Nat.cast_add, Nat.cast_mul, Int.cast_natCast, Nat.cast_mul]
          have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
          field_simp [hpR]
          ring
        rw [harg, e_add_int]
      rw [Finset.sum_congr rfl hin, ← Finset.sum_biUnion]
      · congr 1
        ext n
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨h, _, hn, _⟩; exact hn
        · intro hn
          exact ⟨n % p, Nat.mod_lt n hp_pos, hn, (Nat.mod_modEq n p).symm⟩
      · intro h1 hh1 h2 hh2 hne
        rw [Function.onFun, Finset.disjoint_left]
        intro n hn1 hn2
        rw [Finset.mem_filter] at hn1 hn2
        have hm1 : n % p = h1 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh1)) ▸ hn1.2
        have hm2 : n % p = h2 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh2)) ▸ hn2.2
        exact hne (hm1.symm.trans hm2)
    rw [htrig]
  calc
    ∑ p ∈ (Finset.Icc 1 Q).filter Nat.Prime,
        (p : ℝ) * ∑ h ∈ Finset.range p, ‖residueSum a M N p h - Z / (p : ℂ)‖ ^ 2
        = ∑ p ∈ (Finset.Icc 1 Q).filter Nat.Prime,
            ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
              ‖trigPoly a M N ((r : ℝ) / (p : ℝ))‖ ^ 2 :=
          Finset.sum_congr rfl fun p hp => hp_identity p (Finset.mem_filter.mp hp).2
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro q _ _
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    _ ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
        farey_large_sieve a M hN hQ

end HilbertAndAnalyticLargeSieve

section ArithmeticLargeSieve

private theorem complex_mul_star_eq_norm_sq (z : ℂ) :
    z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

private theorem character_sum_le_trigPoly_sum (a : ℕ → ℂ) (M N q : ℕ) (hq : 1 ≤ q) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
  have hq_pos : 0 < q := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr hq_pos
  have hφR : (q.totient : ℝ) ≠ 0 := by exact_mod_cast hφ_pos.ne'
  have : NeZero q := ⟨hq_pos.ne'⟩
  let T : ZMod q → ℂ := fun c => trigPoly a M N ((c.val : ℝ) / (q : ℝ))
  let U : Finset (ZMod q) := Finset.univ.filter (fun c : ZMod q => IsUnit c)
  have hchar_id : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (q : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 =
        ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 := by
    intro χ hχ
    have hsum_eq :
        (∑ n ∈ Finset.Ioc M (M + N), a n * χ n) * DirichletLFunctions.gaussSum (star χ) 1 =
          ∑ c ∈ U, star (χ c) * T c := by
      have hterm : ∀ n ∈ Finset.Ioc M (M + N),
          a n * χ (n : ZMod q) * DirichletLFunctions.gaussSum (star χ) 1 =
            ∑ c ∈ Finset.univ, star (χ c) * (a n * e ((c.val : ℝ) / (q : ℝ) * (n : ℝ))) := by
        intro n _
        have hgs := sum_star_char_mul_cexp_of_isPrimitive hχ (n : ZMod q)
        rw [mul_assoc, ← hgs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        let k : ℕ := (n * c.val) / q
        have hdiv : n * c.val = q * k + (n * c.val) % q := (Nat.div_add_mod _ _).symm
        have hval : ((n : ZMod q) * c).val = (n * c.val) % q := by
          rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
        have h1 : Complex.exp (2 * Real.pi * Complex.I * ((((n : ZMod q) * c).val : ℕ) : ℂ) / (q : ℂ)) =
            e ((((((n : ZMod q) * c).val : ℕ) : ℝ) / (q : ℝ))) := by
          dsimp [e]
          congr 1
          push_cast
          ring
        have h2 : ((((((n : ZMod q) * c).val : ℕ) : ℝ) / (q : ℝ)) + (k : ℤ)) =
            (c.val : ℝ) / (q : ℝ) * (n : ℝ) := by
          rw [hval]
          conv_rhs => rw [div_mul_eq_mul_div, mul_comm (c.val : ℝ) (n : ℝ), ← Nat.cast_mul, hdiv]
          push_cast
          field_simp [hqR]
          ring
        rw [h1, ← e_add_int _ (k : ℤ), h2]
        ring
      calc
        (∑ n ∈ Finset.Ioc M (M + N), a n * χ n) * DirichletLFunctions.gaussSum (star χ) 1
            = ∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod q) * DirichletLFunctions.gaussSum (star χ) 1 := by
                rw [Finset.sum_mul]
        _ = ∑ n ∈ Finset.Ioc M (M + N),
              ∑ c ∈ Finset.univ, star (χ c) * (a n * e ((c.val : ℝ) / (q : ℝ) * (n : ℝ))) :=
              Finset.sum_congr rfl hterm
        _ = ∑ c : ZMod q, ∑ n ∈ Finset.Ioc M (M + N),
              star (χ c) * (a n * e ((c.val : ℝ) / (q : ℝ) * (n : ℝ))) := Finset.sum_comm
        _ = ∑ c : ZMod q, star (χ c) * T c := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [← Finset.mul_sum]
              rfl
        _ = ∑ c ∈ U, star (χ c) * T c := by
              rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : ZMod q => IsUnit c)]
              have hzero :
                  ∑ c ∈ Finset.univ.filter (fun c : ZMod q => ¬ IsUnit c), star (χ c) * T c = 0 := by
                refine Finset.sum_eq_zero fun c hc => ?_
                have hnu : ¬ IsUnit c := (Finset.mem_filter.mp hc).2
                rw [MulChar.map_nonunit χ hnu, star_zero, zero_mul]
              rw [hzero, add_zero]
    have hgn : ‖DirichletLFunctions.gaussSum (star χ) 1‖ = Real.sqrt q := by
      rw [norm_gaussSum_star, norm_gaussSum_one_of_isPrimitive hχ]
    have hsq : ‖(∑ n ∈ Finset.Ioc M (M + N), a n * χ n) * DirichletLFunctions.gaussSum (star χ) 1‖ ^ 2 =
        (q : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 := by
      rw [norm_mul, hgn, mul_pow, Real.sq_sqrt (by positivity), mul_comm]
    rw [← hsq, hsum_eq]
  have hle_all :
      (q : ℝ) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
        ∑ χ : DirichletCharacter ℂ q, ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          (q : ℝ) * ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
              ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 := by
            refine Finset.sum_congr rfl fun χ hχ => ?_
            exact hchar_id χ (Finset.mem_filter.mp hχ).2
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro _ _ _; exact sq_nonneg _
  have horth :
      ∑ χ : DirichletCharacter ℂ q, ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 =
        (q.totient : ℝ) * ∑ c ∈ U, ‖T c‖ ^ 2 := by
    have hc :
        ((∑ χ : DirichletCharacter ℂ q, ‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 : ℝ) : ℂ) =
          (((q.totient : ℝ) * ∑ c ∈ U, ‖T c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      have hterm_sq : ∀ χ : DirichletCharacter ℂ q,
          ((‖∑ c ∈ U, star (χ c) * T c‖ ^ 2 : ℝ) : ℂ) =
            ∑ c1 ∈ U, ∑ c2 ∈ U, (T c1 * star (T c2)) * (χ c2 * star (χ c1)) := by
        intro χ
        rw [← complex_mul_star_eq_norm_sq, star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c1 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c2 _ => ?_
        rw [star_mul, star_star]
        ring
      rw [Finset.sum_congr rfl fun χ _ => hterm_sq χ]
      calc
        ∑ χ : DirichletCharacter ℂ q,
            ∑ c1 ∈ U, ∑ c2 ∈ U, (T c1 * star (T c2)) * (χ c2 * star (χ c1))
            = ∑ c1 ∈ U, ∑ χ : DirichletCharacter ℂ q,
                ∑ c2 ∈ U, (T c1 * star (T c2)) * (χ c2 * star (χ c1)) := Finset.sum_comm
        _ = ∑ c1 ∈ U, ∑ c2 ∈ U, ∑ χ : DirichletCharacter ℂ q,
              (T c1 * star (T c2)) * (χ c2 * star (χ c1)) := by
              refine Finset.sum_congr rfl fun c1 _ => Finset.sum_comm
        _ = ∑ c1 ∈ U, ∑ c2 ∈ U,
              (T c1 * star (T c2)) * ∑ χ : DirichletCharacter ℂ q, χ c2 * star (χ c1) := by
              refine Finset.sum_congr rfl fun c1 _ => Finset.sum_congr rfl fun c2 _ => ?_
              rw [← Finset.mul_sum]
        _ = ∑ c1 ∈ U, ∑ c2 ∈ U,
              (T c1 * star (T c2)) * (if c2 = c1 then (q.totient : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun c1 hc1 => Finset.sum_congr rfl fun c2 _ => ?_
              rw [sum_chars_mul_conj_eq c2 (Finset.mem_filter.mp hc1).2]
        _ = ∑ c1 ∈ U, (T c1 * star (T c1)) * (q.totient : ℂ) := by
              refine Finset.sum_congr rfl fun c1 hc1 => ?_
              rw [Finset.sum_eq_single c1]
              · simp
              · intro c2 _ hne; simp [hne]
              · intro hnot; exact absurd hc1 hnot
        _ = (((q.totient : ℝ) * ∑ c ∈ U, ‖T c‖ ^ 2 : ℝ) : ℂ) := by
              simp_rw [complex_mul_star_eq_norm_sq]
              push_cast
              rw [← Finset.sum_mul, mul_comm]
    exact Complex.ofReal_injective hc
  have hU_eq :
      ∑ c ∈ U, ‖T c‖ ^ 2 =
        ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
    refine Finset.sum_bij (fun c _ => c.val) ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt c, ?_⟩
      have hu : IsUnit (c.val : ZMod q) := by simpa [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hc).2
      exact (ZMod.isUnit_iff_coprime c.val q).mp hu
    · intro c1 _ c2 _ h
      exact ZMod.val_injective q h
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      refine ⟨(r : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime r q).mpr hr.2⟩, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr.1]
    · intro c _; rfl
  have hmain :
      (q : ℝ) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
        (q.totient : ℝ) *
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [horth, hU_eq] at hle_all
    exact hle_all
  have hdiv :
      ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
        ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ q.totient))
    calc
      ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          = (q.totient : ℝ)⁻¹ * ((q : ℝ) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2) := by
            rw [div_eq_mul_inv]; ring
      _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) *
            ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
              ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2) := hmul
      _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
            rw [← mul_assoc, inv_mul_cancel₀ hφR, one_mul]
  exact hdiv

/-- **Multiplicative (Character) Large Sieve Inequality**:
for any modulus bound `Q ≥ 1`, interval `(M, M + N]` (`N ≥ 1`), and sequence `a : ℕ → ℂ`,
`∑ q ∈ Finset.Icc 1 Q, (q / φ(q)) * ∑*_{χ mod q} ‖∑_{n ∈ (M, M+N]} a n * χ n‖² ≤ (N - 1 + Q²) * ∑_{n ∈ (M, M+N]} ‖a n‖²`,
where `∑*` runs over primitive Dirichlet characters modulo `q`. -/
theorem character_large_sieve (a : ℕ → ℂ) (M : ℕ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  calc
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
              ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 :=
          Finset.sum_le_sum fun q hq =>
            character_sum_le_trigPoly_sum a M N q (Finset.mem_Icc.mp hq).1
    _ ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
        farey_large_sieve a M hN hQ

/-- **Multiplicative (Character) Large Sieve Inequality** (`N + Q²` form). -/
theorem character_large_sieve_add_sq (a : ℕ → ℂ) (M : ℕ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have h1 := character_large_sieve a M hN hQ
  have hnorm : 0 ≤ ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hnorm)

private theorem sum_residueSum_range (a : ℕ → ℂ) (M N q : ℕ) (hq_pos : 0 < q) :
    ∑ h ∈ Finset.range q, residueSum a M N q h = ∑ n ∈ Finset.Ioc M (M + N), a n := by
  simp_rw [residueSum]
  rw [← Finset.sum_biUnion]
  · congr 1
    ext n
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨_, _, hn, _⟩; exact hn
    · intro hn
      exact ⟨n % q, Nat.mod_lt n hq_pos, hn, (Nat.mod_modEq n q).symm⟩
  · intro h1 hh1 h2 hh2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    have hm1 : n % q = h1 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh1)) ▸ hn1.2
    have hm2 : n % q = h2 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh2)) ▸ hn2.2
    exact hne (hm1.symm.trans hm2)

private theorem trigPoly_prime_sum_eq_parseval (a : ℕ → ℂ) (M N p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ∑ h ∈ Finset.range p,
        ‖residueSum a M N p h - (∑ n ∈ Finset.Ioc M (M + N), a n) / (p : ℂ)‖ ^ 2 =
      ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
        ‖trigPoly a M N ((r : ℝ) / (p : ℝ))‖ ^ 2 := by
  have hp_pos : 0 < p := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  let Z : ℂ := ∑ n ∈ Finset.Ioc M (M + N), a n
  have hparseval := parseval_mod_prime p hp_pos (fun h => residueSum a M N p h - Z / (p : ℂ))
  have hsum_Z : ∑ h ∈ Finset.range p, residueSum a M N p h = Z :=
    sum_residueSum_range a M N p hp_pos
  have hsplit : Finset.range p = insert 0 ((Finset.range p).filter (fun r => Nat.Coprime r p)) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hr
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · left; rfl
      · right
        refine ⟨hr, (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hrpos hr)).symm⟩
    · rintro (rfl | ⟨hr, _⟩)
      · exact hp_pos
      · exact hr
  have hzero_not : (0 : ℕ) ∉ (Finset.range p).filter (fun r => Nat.Coprime r p) := by
    simp only [Finset.mem_filter, Finset.mem_range, Nat.coprime_zero_left]
    intro h
    exact hp.ne_one h.2
  have h0 :
      ∑ h ∈ Finset.range p, (residueSum a M N p h - Z / (p : ℂ)) *
          e (((0 : ℕ) : ℝ) * (h : ℝ) / (p : ℝ)) = 0 := by
    have he0 : ∀ h : ℕ, e (((0 : ℕ) : ℝ) * (h : ℝ) / (p : ℝ)) = 1 := fun h => by
      simp [e_zero]
    simp_rw [he0, mul_one, Finset.sum_sub_distrib, hsum_Z, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_div_cancel₀ _ hpC, sub_self]
  have hr_id : ∀ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
      ∑ h ∈ Finset.range p, (residueSum a M N p h - Z / (p : ℂ)) *
          e ((r : ℝ) * (h : ℝ) / (p : ℝ)) =
        trigPoly a M N ((r : ℝ) / (p : ℝ)) := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hr_lt : r < p := Finset.mem_range.mp hr'.1
    have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 => by
      subst hr0
      exact hp.ne_one (by simpa using hr'.2 : p = 1)
    have hshift :
        ∑ h ∈ Finset.range p, (Z / (p : ℂ)) * e ((r : ℝ) * (h : ℝ) / (p : ℝ)) = 0 := by
      rw [← Finset.mul_sum, sum_e_div_prime_eq_zero hp_pos hr_pos hr_lt, mul_zero]
    simp_rw [sub_mul, Finset.sum_sub_distrib, hshift, sub_zero]
    dsimp [trigPoly, residueSum]
    have hin : ∀ h ∈ Finset.range p,
        (∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n => n ≡ h [MOD p]), a n) *
          e ((r : ℝ) * (h : ℝ) / (p : ℝ)) =
        ∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n => n ≡ h [MOD p]),
          a n * e ((r : ℝ) / (p : ℝ) * (n : ℝ)) := by
      intro h hh
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hmod := (Finset.mem_filter.mp hn).2
      have hnp : n % p = h := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh)) ▸ hmod
      let k := n / p
      have hn_eq : n = p * k + h := by
        change n = p * (n / p) + h
        rw [← hnp, Nat.div_add_mod]
      have harg : (r : ℝ) / (p : ℝ) * (n : ℝ) =
          (r : ℝ) * (h : ℝ) / (p : ℝ) + (((r * k : ℕ) : ℤ) : ℝ) := by
        conv_lhs => rw [hn_eq]
        rw [Nat.cast_add, Nat.cast_mul, Int.cast_natCast, Nat.cast_mul]
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pos.ne'
        field_simp [hpR]
        ring
      rw [harg, e_add_int]
    rw [Finset.sum_congr rfl hin, ← Finset.sum_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨_, _, hn, _⟩; exact hn
      · intro hn
        exact ⟨n % p, Nat.mod_lt n hp_pos, hn, (Nat.mod_modEq n p).symm⟩
    · intro h1 hh1 h2 hh2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro n hn1 hn2
      rw [Finset.mem_filter] at hn1 hn2
      have hm1 : n % p = h1 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh1)) ▸ hn1.2
      have hm2 : n % p = h2 := (Nat.mod_eq_of_lt (Finset.mem_range.mp hh2)) ▸ hn2.2
      exact hne (hm1.symm.trans hm2)
  have hlhs :
      ∑ r ∈ Finset.range p,
          ‖∑ h ∈ Finset.range p,
            (residueSum a M N p h - Z / (p : ℂ)) * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 =
        ∑ r ∈ insert 0 ((Finset.range p).filter (fun r => Nat.Coprime r p)),
          ‖∑ h ∈ Finset.range p,
            (residueSum a M N p h - Z / (p : ℂ)) * e ((r : ℝ) * (h : ℝ) / (p : ℝ))‖ ^ 2 :=
    Finset.sum_congr hsplit fun _ _ => rfl
  rw [hparseval, hlhs, Finset.sum_insert hzero_not, h0, norm_zero, sq, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hr_id r hr]

private theorem prime_step_sieve_inequality (a : ℕ → ℂ) (M N p : ℕ) (hp : p.Prime)
    (Ωp : Finset ℕ) (hΩ : Ωp ⊆ Finset.range p) (hω : Ωp.card < p)
    (ha : ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ωp → a n = 0) :
    ((Ωp.card : ℝ) / ((p : ℝ) - (Ωp.card : ℝ))) *
        ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2 ≤
      ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
        ‖trigPoly a M N ((r : ℝ) / (p : ℝ))‖ ^ 2 := by
  by_cases hω0 : Ωp.card = 0
  · rw [hω0]
    simp only [Nat.cast_zero, zero_div, zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp_pos : 0 < p := hp.pos
  have hpR_pos : (0 : ℝ) < p := by exact_mod_cast hp_pos
  have hpR_ne : (p : ℝ) ≠ 0 := hpR_pos.ne'
  have hpC_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  let Z : ℂ := ∑ n ∈ Finset.Ioc M (M + N), a n
  let U : Finset ℕ := (Finset.range p) \ Ωp
  have hpart_disj : Disjoint U Ωp := disjoint_sdiff_self_left
  have hpart_union : U ∪ Ωp = Finset.range p := Finset.sdiff_union_of_subset hΩ
  have hU_card : U.card + Ωp.card = p := by
    rw [← Finset.card_union_of_disjoint hpart_disj, hpart_union, Finset.card_range]
  have hU_pos : 0 < U.card := by omega
  have hU_R : (U.card : ℝ) = (p : ℝ) - (Ωp.card : ℝ) := by
    have : (U.card : ℝ) + (Ωp.card : ℝ) = p := by exact_mod_cast hU_card
    linarith
  have hU_posR : (0 : ℝ) < (p : ℝ) - (Ωp.card : ℝ) := by rw [← hU_R]; exact_mod_cast hU_pos
  have hΩ_res_zero : ∀ h ∈ Ωp, residueSum a M N p h = 0 := by
    intro h hh
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn' := Finset.mem_filter.mp hn
    have hlt : h < p := Finset.mem_range.mp (hΩ hh)
    have hmod : n % p = h := (Nat.mod_eq_of_lt hlt) ▸ hn'.2
    rw [← hmod] at hh
    exact ha n hn'.1 hh
  have hsum_U : ∑ h ∈ U, residueSum a M N p h = Z := by
    have htot := sum_residueSum_range a M N p hp_pos
    rw [← hpart_union, Finset.sum_union hpart_disj] at htot
    have hzero : ∑ h ∈ Ωp, residueSum a M N p h = 0 := Finset.sum_eq_zero hΩ_res_zero
    rw [hzero, add_zero] at htot
    exact htot
  let b : ℕ → ℂ := fun h => residueSum a M N p h - Z / (p : ℂ)
  have hsum_Ω_val : ∑ h ∈ Ωp, ‖b h‖ ^ 2 = (Ωp.card : ℝ) * (‖Z‖ ^ 2 / (p : ℝ) ^ 2) := by
    have hterm : ∀ h ∈ Ωp, ‖b h‖ ^ 2 = ‖Z‖ ^ 2 / (p : ℝ) ^ 2 := by
      intro h hh
      dsimp [b]
      rw [hΩ_res_zero h hh, zero_sub, norm_neg, norm_div, Complex.norm_natCast, div_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hsum_U_val : ∑ h ∈ U, b h = ((Ωp.card : ℂ) / (p : ℂ)) * Z := by
    dsimp [b]
    rw [Finset.sum_sub_distrib, hsum_U, Finset.sum_const, nsmul_eq_mul]
    have hUC : (U.card : ℂ) = (p : ℂ) - (Ωp.card : ℂ) := by
      have : (U.card : ℂ) + (Ωp.card : ℂ) = p := by exact_mod_cast hU_card
      linear_combination this
    rw [hUC]
    field_simp [hpC_ne]
    ring
  have hCS : ((Ωp.card : ℝ) / (p : ℝ)) ^ 2 * ‖Z‖ ^ 2 ≤ (U.card : ℝ) * ∑ h ∈ U, ‖b h‖ ^ 2 := by
    have hnorm_sum_sq : ‖∑ h ∈ U, b h‖ ^ 2 = ((Ωp.card : ℝ) / (p : ℝ)) ^ 2 * ‖Z‖ ^ 2 := by
      rw [hsum_U_val, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast, mul_pow]
    have htri : ‖∑ h ∈ U, b h‖ ≤ ∑ h ∈ U, ‖b h‖ := norm_sum_le _ _
    have htri_sq : ‖∑ h ∈ U, b h‖ ^ 2 ≤ (∑ h ∈ U, ‖b h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq := sq_sum_le_card_mul_sum_sq (s := U) (f := fun h => ‖b h‖)
    rw [← hnorm_sum_sq]
    exact htri_sq.trans hsq
  have hsum_U_ge :
      (((Ωp.card : ℝ) / (p : ℝ)) ^ 2 * ‖Z‖ ^ 2) / ((p : ℝ) - (Ωp.card : ℝ)) ≤ ∑ h ∈ U, ‖b h‖ ^ 2 := by
    rw [div_le_iff₀ hU_posR, ← hU_R, mul_comm _ (U.card : ℝ)]
    exact hCS
  have hsum_split : ∑ h ∈ Finset.range p, ‖b h‖ ^ 2 = (∑ h ∈ U, ‖b h‖ ^ 2) + (∑ h ∈ Ωp, ‖b h‖ ^ 2) := by
    rw [← hpart_union, Finset.sum_union hpart_disj]
  have halg :
      (p : ℝ) * ((((Ωp.card : ℝ) / (p : ℝ)) ^ 2 * ‖Z‖ ^ 2) / ((p : ℝ) - (Ωp.card : ℝ)) +
          (Ωp.card : ℝ) * (‖Z‖ ^ 2 / (p : ℝ) ^ 2)) =
        ((Ωp.card : ℝ) / ((p : ℝ) - (Ωp.card : ℝ))) * ‖Z‖ ^ 2 := by
    have hsub_ne : ((p : ℝ) - (Ωp.card : ℝ)) ≠ 0 := hU_posR.ne'
    field_simp [hpR_ne, hsub_ne]
    ring
  calc
    ((Ωp.card : ℝ) / ((p : ℝ) - (Ωp.card : ℝ))) * ‖Z‖ ^ 2
        = (p : ℝ) * ((((Ωp.card : ℝ) / (p : ℝ)) ^ 2 * ‖Z‖ ^ 2) / ((p : ℝ) - (Ωp.card : ℝ)) +
            (Ωp.card : ℝ) * (‖Z‖ ^ 2 / (p : ℝ) ^ 2)) := halg.symm
    _ ≤ (p : ℝ) * ((∑ h ∈ U, ‖b h‖ ^ 2) + (∑ h ∈ Ωp, ‖b h‖ ^ 2)) := by
          gcongr
          rw [← hsum_Ω_val]
    _ = (p : ℝ) * ∑ h ∈ Finset.range p, ‖b h‖ ^ 2 := by rw [← hsum_split]
    _ = ∑ r ∈ (Finset.range p).filter (fun r => Nat.Coprime r p),
          ‖trigPoly a M N ((r : ℝ) / (p : ℝ))‖ ^ 2 := trigPoly_prime_sum_eq_parseval a M N p hp

private theorem mod_coprime_of_coprime {k q : ℕ} (_hq : 0 < q) (hk : Nat.Coprime k q) :
    Nat.Coprime (k % q) q := by
  rw [Nat.coprime_iff_gcd_eq_one] at hk ⊢
  refine Nat.eq_one_of_dvd_one ?_
  rw [← hk]
  refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right (k % q) q)
  have h1 : (k % q).gcd q ∣ q * (k / q) :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right (k % q) q) (k / q)
  have h2 : (k % q).gcd q ∣ k % q := Nat.gcd_dvd_left (k % q) q
  have h3 : (k % q).gcd q ∣ q * (k / q) + k % q := Nat.dvd_add h1 h2
  rwa [Nat.div_add_mod k q] at h3

private theorem coprime_crt_mem_and_inj {m p : ℕ} (hm_pos : 0 < m) (hp_pos : 0 < p)
    (hm_cop : Nat.Coprime m p) :
    (∀ r ∈ (Finset.range m).filter (fun r => Nat.Coprime r m),
      ∀ c ∈ (Finset.range p).filter (fun c => Nat.Coprime c p),
        ((r * p + c * m) % (m * p)) ∈
          (Finset.range (m * p)).filter (fun x => Nat.Coprime x (m * p))) ∧
    Set.InjOn (fun x : ℕ × ℕ => (x.1 * p + x.2 * m) % (m * p))
      (((Finset.range m).filter (fun r => Nat.Coprime r m)) ×ˢ
        ((Finset.range p).filter (fun c => Nat.Coprime c p)) : Set (ℕ × ℕ)) := by
  have hmp_pos : 0 < m * p := Nat.mul_pos hm_pos hp_pos
  constructor
  · intro r hr c hc
    have hr' := Finset.mem_filter.mp hr
    have hc' := Finset.mem_filter.mp hc
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hmp_pos, mod_coprime_of_coprime hmp_pos ?_⟩
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm]
      have h1 : Nat.Coprime m (r * p) := Nat.Coprime.mul_right hr'.2.symm hm_cop
      exact (Nat.coprime_add_mul_right_right m (r * p) c).mpr h1
    · rw [Nat.coprime_comm]
      have h1 : Nat.Coprime p (c * m) := Nat.Coprime.mul_right hc'.2.symm hm_cop.symm
      have h2 : Nat.Coprime p (c * m + r * p) :=
        (Nat.coprime_add_mul_right_right p (c * m) r).mpr h1
      simpa [add_comm] using h2
  · rintro ⟨r1, c1⟩ h1 ⟨r2, c2⟩ h2 heq
    simp only [Set.mem_prod, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at h1 h2
    have hmod : (r1 * p + c1 * m) ≡ (r2 * p + c2 * m) [MOD m * p] := heq
    have hmod_m : (r1 * p + c1 * m) ≡ (r2 * p + c2 * m) [MOD m] :=
      hmod.of_dvd (dvd_mul_right m p)
    have hmod_m' : r1 * p ≡ r2 * p [MOD m] := by
      have hcm1 : r1 * p + c1 * m ≡ r1 * p + 0 [MOD m] :=
        Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left m c1))
      have hcm2 : r2 * p + c2 * m ≡ r2 * p + 0 [MOD m] :=
        Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left m c2))
      exact hcm1.symm.trans (hmod_m.trans hcm2)
    have hr_mod : r1 ≡ r2 [MOD m] :=
      Nat.ModEq.cancel_right_of_coprime hm_cop hmod_m'
    have hr_eq : r1 = r2 := by
      change r1 % m = r2 % m at hr_mod
      rwa [Nat.mod_eq_of_lt h1.1.1, Nat.mod_eq_of_lt h2.1.1] at hr_mod
    have hmod_p : (r1 * p + c1 * m) ≡ (r2 * p + c2 * m) [MOD p] :=
      hmod.of_dvd (dvd_mul_left p m)
    have hmod_p' : c1 * m ≡ c2 * m [MOD p] := by
      have hrp1 : r1 * p + c1 * m ≡ 0 + c1 * m [MOD p] :=
        Nat.ModEq.add_right _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p r1))
      have hrp2 : r2 * p + c2 * m ≡ 0 + c2 * m [MOD p] :=
        Nat.ModEq.add_right _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p r2))
      simpa only [zero_add] using hrp1.symm.trans (hmod_p.trans hrp2)
    have hc_mod : c1 ≡ c2 [MOD p] :=
      Nat.ModEq.cancel_right_of_coprime hm_cop.symm hmod_p'
    have hc_eq : c1 = c2 := by
      change c1 % p = c2 % p at hc_mod
      rwa [Nat.mod_eq_of_lt h1.2.1, Nat.mod_eq_of_lt h2.2.1] at hc_mod
    exact Prod.ext hr_eq hc_eq

private theorem crt_shift_real {m p r c n k rem : ℝ} (hm : m ≠ 0) (hp : p ≠ 0)
    (h : r * p + c * m = m * p * k + rem) :
    c / p * n + r / m * n = rem / (m * p) * n + k * n := by
  have hmp : m * p ≠ 0 := mul_ne_zero hm hp
  apply mul_right_cancel₀ hmp
  calc
    (c / p * n + r / m * n) * (m * p)
        = (c / p * p) * n * m + (r / m * m) * n * p := by ring
    _ = (r * p + c * m) * n := by rw [div_mul_cancel₀ _ hp, div_mul_cancel₀ _ hm]; ring
    _ = (m * p * k + rem) * n := by rw [h]
    _ = (rem / (m * p) * (m * p)) * n + k * n * (m * p) := by
          rw [div_mul_cancel₀ _ hmp]; ring
    _ = (rem / (m * p) * n + k * n) * (m * p) := by ring

private theorem e_crt_shift (m p r c n : ℕ) (hm_pos : 0 < m) (hp_pos : 0 < p) :
    e ((c : ℝ) / (p : ℝ) * (n : ℝ)) * e ((r : ℝ) / (m : ℝ) * (n : ℝ)) =
      e ((((r * p + c * m) % (m * p) : ℕ) : ℝ) / ((m * p : ℕ) : ℝ) * (n : ℝ)) := by
  rw [← e_add]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have hdiv : r * p + c * m = (m * p) * ((r * p + c * m) / (m * p)) + (r * p + c * m) % (m * p) :=
    (Nat.div_add_mod _ _).symm
  have hdivR : (r : ℝ) * (p : ℝ) + (c : ℝ) * (m : ℝ) =
      (m : ℝ) * (p : ℝ) * (((r * p + c * m) / (m * p) : ℕ) : ℝ) +
        (((r * p + c * m) % (m * p) : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdiv
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  have harg : (c : ℝ) / (p : ℝ) * (n : ℝ) + (r : ℝ) / (m : ℝ) * (n : ℝ) =
      (((r * p + c * m) % (m * p) : ℕ) : ℝ) / ((m * p : ℕ) : ℝ) * (n : ℝ) +
        ((((r * p + c * m) / (m * p) * n : ℕ) : ℤ) : ℝ) := by
    rw [Nat.cast_mul, Int.cast_natCast, Nat.cast_mul]
    exact crt_shift_real hmR hpR hdivR
  rw [harg, e_add_int]

private theorem trigPoly_crt_shift (a : ℕ → ℂ) (M N m p r c : ℕ)
    (hm_pos : 0 < m) (hp_pos : 0 < p) :
    trigPoly (fun n => a n * e ((c : ℝ) / (p : ℝ) * (n : ℝ))) M N ((r : ℝ) / (m : ℝ)) =
      trigPoly a M N ((((r * p + c * m) % (m * p) : ℕ) : ℝ) / ((m * p : ℕ) : ℝ)) := by
  dsimp [trigPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, e_crt_shift m p r c n hm_pos hp_pos]

/-- Local multiplicative density weight `g(q) = ∏_{p ∣ q} ω(p) / (p - ω(p))` for a sieve
with `ω(p) = (Ω p).card` removed residue classes modulo `p`. -/
noncomputable def sieveWeight (Ω : ℕ → Finset ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((Ω p).card : ℝ) / ((p : ℝ) - ((Ω p).card : ℝ))

/-- At `q = 1`, `sieveWeight Ω 1 = 1`. -/
theorem sieveWeight_one (Ω : ℕ → Finset ℕ) : sieveWeight Ω 1 = 1 := by
  simp [sieveWeight]

/-- `sieveWeight Ω q` is nonnegative whenever `(Ω p).card ≤ p` for all prime factors `p` of `q`. -/
theorem sieveWeight_nonneg {Ω : ℕ → Finset ℕ} {q : ℕ}
    (hω : ∀ p ∈ q.primeFactors, (Ω p).card ≤ p) : 0 ≤ sieveWeight Ω q := by
  refine Finset.prod_nonneg fun p hp => div_nonneg (Nat.cast_nonneg _) ?_
  have hle : ((Ω p).card : ℝ) ≤ (p : ℝ) := by exact_mod_cast hω p hp
  linarith

/-- Multiplicativity of `sieveWeight` under multiplying by a prime `p` not dividing `m > 0`. -/
theorem sieveWeight_mul_prime {Ω : ℕ → Finset ℕ} {m p : ℕ} (hm_pos : 0 < m)
    (hp : p.Prime) (hndvd : ¬ p ∣ m) :
    sieveWeight Ω (m * p) =
      sieveWeight Ω m * (((Ω p).card : ℝ) / ((p : ℝ) - ((Ω p).card : ℝ))) := by
  have hpf : (m * p).primeFactors = insert p m.primeFactors := by
    ext r
    simp only [Nat.mem_primeFactors, Finset.mem_insert, ne_eq, Nat.mul_eq_zero, not_or]
    constructor
    · rintro ⟨hr, hr_dvd, hm0, _⟩
      rcases hr.dvd_mul.mp hr_dvd with hdm | hdp
      · right; exact ⟨hr, hdm, hm0⟩
      · left; exact ((Nat.dvd_prime hp).mp hdp).resolve_left hr.ne_one
    · rintro (hrp | ⟨hr, hr_dvd, hm0⟩)
      · rw [hrp]; exact ⟨hp, dvd_mul_left p m, hm_pos.ne', hp.ne_zero⟩
      · exact ⟨hr, dvd_mul_of_dvd_left hr_dvd p, hm0, hp.ne_zero⟩
  have hp_not_mem : p ∉ m.primeFactors := by
    rw [Nat.mem_primeFactors]
    rintro ⟨_, hdvd, _⟩
    exact hndvd hdvd
  rw [sieveWeight, hpf, Finset.prod_insert hp_not_mem, mul_comm]
  rfl

private theorem arithmetic_large_sieve_squarefree_ind (Ω : ℕ → Finset ℕ) (M N : ℕ) :
    ∀ q : ℕ, 1 ≤ q → Squarefree q →
      (∀ p ∈ q.primeFactors, Ω p ⊆ Finset.range p ∧ (Ω p).card < p) →
      ∀ a : ℕ → ℂ,
      (∀ p ∈ q.primeFactors, ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ω p → a n = 0) →
      sieveWeight Ω q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2 ≤
        ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro hq1 hsq hΩ a ha
    by_cases hq_one : q = 1
    · subst hq_one
      rw [sieveWeight_one, one_mul]
      have hf1 : (Finset.range 1).filter (fun r => Nat.Coprime r 1) = {0} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro h; omega
        · rintro rfl; exact ⟨by omega, Nat.coprime_one_right 0⟩
      rw [hf1, Finset.sum_singleton]
      have htp : trigPoly a M N (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) =
          ∑ n ∈ Finset.Ioc M (M + N), a n := by
        dsimp [trigPoly]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp [zero_mul, e_zero]
      rw [htp]
    · have hq_gt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hq_one)
      let p : ℕ := q.minFac
      have hp : p.Prime := Nat.minFac_prime hq_gt.ne'
      have hp_dvd : p ∣ q := Nat.minFac_dvd q
      let m : ℕ := q / p
      have hqm : q = m * p := (Nat.div_mul_cancel hp_dvd).symm
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp.pos
      have hm_lt : m < q := Nat.div_lt_self (by omega) hp.one_lt
      have hsq_m : Squarefree m := hsq.squarefree_of_dvd (hqm ▸ dvd_mul_right m p)
      have hndvd : ¬ p ∣ m := by
        intro hpm
        have hpp : p * p ∣ q := by
          rw [hqm]
          exact mul_dvd_mul_right hpm p
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hpp))
      have hm_cop : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
      have hm_pf_sub : m.primeFactors ⊆ q.primeFactors := by
        intro r hr
        rw [Nat.mem_primeFactors] at hr ⊢
        exact ⟨hr.1, hr.2.1.trans (hqm ▸ dvd_mul_right m p), (by omega)⟩
      have hp_pf : p ∈ q.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hp_dvd, by omega⟩
      have hΩp := hΩ p hp_pf
      have ha_p : ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ω p → a n = 0 := ha p hp_pf
      have hstep_p := prime_step_sieve_inequality a M N p hp (Ω p) hΩp.1 hΩp.2 ha_p
      have hsw : sieveWeight Ω q =
          sieveWeight Ω m * (((Ω p).card : ℝ) / ((p : ℝ) - ((Ω p).card : ℝ))) := by
        rw [hqm]
        exact sieveWeight_mul_prime hm_pos hp hndvd
      have hsw_m_nonneg : 0 ≤ sieveWeight Ω m :=
        sieveWeight_nonneg fun r hr => (hΩ r (hm_pf_sub hr)).2.le
      have hstep_c : ∀ c ∈ (Finset.range p).filter (fun c => Nat.Coprime c p),
          sieveWeight Ω m *
              ‖trigPoly a M N ((c : ℝ) / (p : ℝ))‖ ^ 2 ≤
            ∑ r ∈ (Finset.range m).filter (fun r => Nat.Coprime r m),
              ‖trigPoly (fun n => a n * e ((c : ℝ) / (p : ℝ) * (n : ℝ))) M N
                ((r : ℝ) / (m : ℝ))‖ ^ 2 := by
        intro c _
        have hbc := ih m hm_lt hm_pos hsq_m
          (fun r hr => hΩ r (hm_pf_sub hr))
          (fun n => a n * e ((c : ℝ) / (p : ℝ) * (n : ℝ)))
          (fun r hr n hn hmod => by rw [ha r (hm_pf_sub hr) n hn hmod, zero_mul])
        exact hbc
      have hsum_c :
          sieveWeight Ω m *
              ∑ c ∈ (Finset.range p).filter (fun c => Nat.Coprime c p),
                ‖trigPoly a M N ((c : ℝ) / (p : ℝ))‖ ^ 2 ≤
            ∑ c ∈ (Finset.range p).filter (fun c => Nat.Coprime c p),
              ∑ r ∈ (Finset.range m).filter (fun r => Nat.Coprime r m),
                ‖trigPoly a M N
                  ((((r * p + c * m) % (m * p) : ℕ) : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c hc => ?_
        calc
          sieveWeight Ω m * ‖trigPoly a M N ((c : ℝ) / (p : ℝ))‖ ^ 2
              ≤ ∑ r ∈ (Finset.range m).filter (fun r => Nat.Coprime r m),
                  ‖trigPoly (fun n => a n * e ((c : ℝ) / (p : ℝ) * (n : ℝ))) M N
                    ((r : ℝ) / (m : ℝ))‖ ^ 2 := hstep_c c hc
          _ = ∑ r ∈ (Finset.range m).filter (fun r => Nat.Coprime r m),
                ‖trigPoly a M N
                  ((((r * p + c * m) % (m * p) : ℕ) : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 := by
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [trigPoly_crt_shift a M N m p r c hm_pos hp.pos]
      have hcrt := coprime_crt_mem_and_inj hm_pos hp.pos hm_cop
      let Sm := (Finset.range m).filter (fun r => Nat.Coprime r m)
      let Sp := (Finset.range p).filter (fun c => Nat.Coprime c p)
      let Smp := (Finset.range (m * p)).filter (fun x => Nat.Coprime x (m * p))
      let φ : ℕ × ℕ → ℕ := fun x => (x.1 * p + x.2 * m) % (m * p)
      have hprod_le :
          ∑ c ∈ Sp, ∑ r ∈ Sm, ‖trigPoly a M N ((φ (r, c) : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 ≤
            ∑ x ∈ Smp, ‖trigPoly a M N ((x : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 := by
        rw [Finset.sum_comm, ← Finset.sum_product']
        have himg :
            ∑ x ∈ Sm ×ˢ Sp, ‖trigPoly a M N ((φ x : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 =
              ∑ y ∈ (Sm ×ˢ Sp).image φ, ‖trigPoly a M N ((y : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 := by
          rw [Finset.sum_image]
          intro x1 hx1 x2 hx2 hxy
          rw [Finset.coe_product] at hx1 hx2
          dsimp [Sm, Sp] at hx1 hx2
          exact hcrt.2 hx1 hx2 hxy
        rw [himg]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨⟨r, c⟩, hrc, rfl⟩
        rcases Finset.mem_product.mp hrc with ⟨hr, hc⟩
        exact hcrt.1 r hr c hc
      calc
        sieveWeight Ω q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2
            = sieveWeight Ω m * ((((Ω p).card : ℝ) / ((p : ℝ) - ((Ω p).card : ℝ))) *
                ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2) := by rw [hsw]; ring
        _ ≤ sieveWeight Ω m * ∑ c ∈ Sp, ‖trigPoly a M N ((c : ℝ) / (p : ℝ))‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hstep_p hsw_m_nonneg
        _ ≤ ∑ c ∈ Sp, ∑ r ∈ Sm, ‖trigPoly a M N ((φ (r, c) : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 :=
              hsum_c
        _ ≤ ∑ x ∈ Smp, ‖trigPoly a M N ((x : ℝ) / ((m * p : ℕ) : ℝ))‖ ^ 2 := hprod_le
        _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
              ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by dsimp [Smp]; rw [← hqm]

/-- **Squarefree CRT Inequality for the Arithmetic Large Sieve**:
for any squarefree modulus `q ≥ 1` and sequence `a : ℕ → ℂ` supported outside `Ω p` mod `p` for
every prime factor `p ∣ q`,
`sieveWeight Ω q * ‖∑_{n ∈ (M, M+N]} a n‖² ≤ ∑_{r mod q, (r, q) = 1} ‖trigPoly a M N (r / q)‖²`. -/
theorem arithmetic_large_sieve_squarefree (Ω : ℕ → Finset ℕ) (a : ℕ → ℂ) (M N q : ℕ)
    (hq : 1 ≤ q) (hsq : Squarefree q)
    (hΩ : ∀ p ∈ q.primeFactors, Ω p ⊆ Finset.range p ∧ (Ω p).card < p)
    (ha : ∀ p ∈ q.primeFactors, ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ω p → a n = 0) :
    sieveWeight Ω q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2 ≤
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 :=
  arithmetic_large_sieve_squarefree_ind Ω M N q hq hsq hΩ a ha

/-- Total arithmetic large-sieve weight `L(Q) = ∑_{1 ≤ q ≤ Q, q squarefree} g(q)` associated
with the removed residue classes `Ω`. -/
noncomputable def sieveWeightSum (Ω : ℕ → Finset ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, sieveWeight Ω q

/-- For `Q ≥ 1`, `sieveWeightSum Ω Q ≥ 1` whenever `(Ω p).card ≤ p` for primes `p ≤ Q`. -/
theorem one_le_sieveWeightSum {Ω : ℕ → Finset ℕ} {Q : ℕ} (hQ : 1 ≤ Q)
    (hω : ∀ p, p.Prime → p ≤ Q → (Ω p).card ≤ p) : 1 ≤ sieveWeightSum Ω Q := by
  have h1 : (1 : ℕ) ∈ (Finset.Icc 1 Q).filter Squarefree := by
    simp [Finset.mem_filter, Finset.mem_Icc, hQ]
  have hle : sieveWeight Ω 1 ≤ sieveWeightSum Ω Q := by
    refine Finset.single_le_sum (f := sieveWeight Ω) ?_ h1
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hq_le : q ≤ Q := (Finset.mem_Icc.mp hq'.1).2
    refine sieveWeight_nonneg fun p hp => ?_
    rw [Nat.mem_primeFactors] at hp
    exact hω p hp.1 ((Nat.le_of_dvd (by omega) hp.2.1).trans hq_le)
  simpa [sieveWeight_one] using hle

/-- **Arithmetic Large Sieve Inequality (Weighted Form)**:
if `a : ℕ → ℂ` vanishes whenever `n % p ∈ Ω p` for primes `p ≤ Q`, then
`sieveWeightSum Ω Q * ‖∑_{n ∈ (M, M+N]} a n‖² ≤ (N - 1 + Q²) * ∑_{n ∈ (M, M+N]} ‖a n‖²`. -/
theorem arithmetic_large_sieve_sifted (Ω : ℕ → Finset ℕ) (a : ℕ → ℂ) (M : ℕ)
    {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hΩ : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ Finset.range p ∧ (Ω p).card < p)
    (ha : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ω p → a n = 0) :
    sieveWeightSum Ω Q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2 ≤
      ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hsum :
      sieveWeightSum Ω Q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2 ≤
        ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [sieveWeightSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq' := Finset.mem_filter.mp hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq'.1).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq'.1).2
    refine arithmetic_large_sieve_squarefree Ω a M N q hq1 hq'.2 ?_ ?_
    · intro p hp
      rw [Nat.mem_primeFactors] at hp
      exact hΩ p hp.1 ((Nat.le_of_dvd (by omega) hp.2.1).trans hqQ)
    · intro p hp n hn hmod
      rw [Nat.mem_primeFactors] at hp
      exact ha p hp.1 ((Nat.le_of_dvd (by omega) hp.2.1).trans hqQ) n hn hmod
  calc
    sieveWeightSum Ω Q * ‖∑ n ∈ Finset.Ioc M (M + N), a n‖ ^ 2
        ≤ ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
            ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
              ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := hsum
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            ‖trigPoly a M N ((r : ℝ) / (q : ℝ))‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro _ _ _; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    _ ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
        farey_large_sieve a M hN hQ

/-- **Arithmetic Large Sieve Inequality (Sifted Set Cardinality)**:
for any finite set `A ⊆ Finset.Ioc M (M + N)` (`N ≥ 1`, `Q ≥ 1`) avoiding `Ω p` mod `p` for
every prime `p ≤ Q`,
`(A.card : ℝ) ≤ ((N - 1 + Q²) / sieveWeightSum Ω Q)`. -/
theorem arithmetic_large_sieve_sifted_card (Ω : ℕ → Finset ℕ) (A : Finset ℕ) (M : ℕ)
    {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hA : A ⊆ Finset.Ioc M (M + N))
    (hΩ : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ Finset.range p ∧ (Ω p).card < p)
    (hA_sift : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, n % p ∉ Ω p) :
    (A.card : ℝ) ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) / sieveWeightSum Ω Q := by
  have hL_pos : 0 < sieveWeightSum Ω Q :=
    lt_of_lt_of_le zero_lt_one (one_le_sieveWeightSum hQ fun p hp hpQ => (hΩ p hp hpQ).2.le)
  rw [le_div_iff₀ hL_pos, mul_comm]
  by_cases hA0 : A.card = 0
  · rw [hA0, Nat.cast_zero, mul_zero]
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  let a : ℕ → ℂ := fun n => if n ∈ A then 1 else 0
  have ha_sift : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ Finset.Ioc M (M + N), n % p ∈ Ω p → a n = 0 := by
    intro p hp hpQ n _ hmod
    dsimp [a]
    split_ifs with hn
    · exact absurd hmod (hA_sift p hp hpQ n hn)
    · rfl
  have hls := arithmetic_large_sieve_sifted Ω a M hN hQ hΩ ha_sift
  have hsum_Z : ∑ n ∈ Finset.Ioc M (M + N), a n = (A.card : ℂ) := by
    dsimp [a]
    rw [← Finset.sum_filter]
    have hf : (Finset.Ioc M (M + N)).filter (fun n => n ∈ A) = A := by
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
    rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_sq : ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 = (A.card : ℝ) := by
    dsimp [a]
    have hterm : ∀ n, ‖if n ∈ A then (1 : ℂ) else 0‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      intro n
      split_ifs <;> simp
    simp_rw [hterm, ← Finset.sum_filter]
    have hf : (Finset.Ioc M (M + N)).filter (fun n => n ∈ A) = A := by
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
    rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum_Z, hsum_sq, Complex.norm_natCast] at hls
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hA0
  have hmul_cancel :
      (sieveWeightSum Ω Q * (A.card : ℝ)) * (A.card : ℝ) ≤
        ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * (A.card : ℝ) := by
    linarith [hls, show sieveWeightSum Ω Q * (A.card : ℝ) ^ 2 =
      (sieveWeightSum Ω Q * (A.card : ℝ)) * (A.card : ℝ) by ring]
  exact le_of_mul_le_mul_right hmul_cancel hA_pos

end ArithmeticLargeSieve

section BrunTitchmarshAndSelberg

private theorem sum_image_le_sum_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (φ : α → β) (f : β → ℝ) (hf : ∀ x ∈ s, 0 ≤ f (φ x)) :
    ∑ y ∈ s.image φ, f y ≤ ∑ x ∈ s, f (φ x) := by
  have hfib : ∑ x ∈ s, f (φ x) =
      ∑ y ∈ s.image φ, ∑ x ∈ s with φ x = y, f (φ x) :=
    (Finset.sum_fiberwise_of_maps_to (fun _ hx => Finset.mem_image_of_mem φ hx)
      (fun x => f (φ x))).symm
  rw [hfib]
  refine Finset.sum_le_sum fun y hy => ?_
  rcases Finset.mem_image.mp hy with ⟨x0, hx0, rfl⟩
  have hmem : x0 ∈ s.filter (fun x => φ x = φ x0) := Finset.mem_filter.mpr ⟨hx0, rfl⟩
  exact Finset.single_le_sum (fun x hx => hf x (Finset.mem_filter.mp hx).1) hmem

private theorem one_sub_mul_geom_sum (r : ℝ) (n : ℕ) :
    (1 - r) * ∑ e ∈ Finset.range n, r ^ e = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private theorem squarefree_prod_primes_set {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp_not ih =>
    rw [Finset.prod_insert hp_not]
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : Squarefree (∏ q ∈ S, q) := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : q.Prime := hS q (Finset.mem_insert_of_mem hq)
      exact (hp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp_not ((((Nat.dvd_prime hqp).mp hdvd).resolve_left hp.ne_one) ▸ hq))
    exact Nat.squarefree_mul hcop |>.mpr ⟨hp.squarefree, hS'⟩

private theorem totient_squarefree_eq_prod {s : ℕ} (hs_pos : 0 < s) (hsq : Squarefree s) :
    s.totient = ∏ p ∈ s.primeFactors, (p - 1) := by
  have hprod := Nat.totient_mul_prod_primeFactors s
  have hsf : ∏ p ∈ s.primeFactors, p = s := Nat.prod_primeFactors_of_squarefree hsq
  rw [hsf, mul_comm s _] at hprod
  exact Nat.eq_of_mul_eq_mul_right hs_pos hprod

private theorem sum_inv_primeFactors_subset_le (M : ℕ) :
    ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) →
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ T), (k : ℝ)⁻¹ ≤
        ∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    have hf : (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ ∅) =
        if 1 ≤ M then {1} else ∅ := by
      ext k
      split_ifs with hM
      · simp only [Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hk, hpf⟩
          have hk0 : k ≠ 0 := by omega
          rcases Nat.primeFactors_eq_empty.mp hpf with rfl | rfl <;> omega
        · rintro rfl
          exact ⟨⟨le_rfl, hM⟩, Nat.primeFactors_one⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
        rintro ⟨hk, _⟩
        omega
    rw [hf, Finset.prod_empty]
    split_ifs <;> simp
  | @insert p T hp_not ih =>
    intro hT
    have hp : p.Prime := hT p (Finset.mem_insert_self p T)
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have ih' := ih fun q hq => hT q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp_not]
    let S_ins := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ insert p T)
    let S_T := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ T)
    let E := Finset.range (M + 1)
    let φ : ℕ × ℕ → ℕ := fun x => p ^ x.1 * x.2
    have hmem_im : ∀ k ∈ S_ins,
        ∃ x ∈ E ×ˢ S_T, φ x = k := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk'.1).1
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk'.1).2
      have hk0 : k ≠ 0 := by omega
      let e := k.factorization p
      let k' := k / p ^ e
      have hdvd : p ^ e ∣ k := Nat.ordProj_dvd k p
      have hk_eq : p ^ e * k' = k := Nat.mul_div_cancel' hdvd
      have he_le : e ≤ M := by
        have h2e : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        have he2 : e ≤ 2 ^ e := (Nat.lt_pow_self (by decide)).le
        have hpe_le : p ^ e ≤ k := Nat.le_of_dvd (by omega) hdvd
        exact le_trans (le_trans (le_trans he2 h2e) hpe_le) hkM
      have hk'_pos : 1 ≤ k' := Nat.div_pos (Nat.le_of_dvd hk1 hdvd) (pow_pos hp.pos e)
      have hk'_le : k' ≤ M := (Nat.div_le_self k (p ^ e)).trans hkM
      have hndvd_p : ¬ p ∣ k' := Nat.not_dvd_ordCompl hp hk0
      have hk'_pf : k'.primeFactors ⊆ T := by
        intro q hq
        rw [Nat.mem_primeFactors] at hq
        have hq_k : q ∈ k.primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨hq.1, hq.2.1.trans (hk_eq ▸ dvd_mul_left k' (p ^ e)), hk0⟩
        have hq_ins := hk'.2 hq_k
        rcases Finset.mem_insert.mp hq_ins with rfl | hqT
        · exact absurd hq.2.1 hndvd_p
        · exact hqT
      refine ⟨(e, k'), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk'_pos, hk'_le⟩, hk'_pf⟩⟩, hk_eq⟩
    have hsum_le_prod :
        ∑ k ∈ S_ins, (k : ℝ)⁻¹ ≤
          (∑ e ∈ E, ((p : ℝ) ^ e)⁻¹) * ∑ k' ∈ S_T, (k' : ℝ)⁻¹ := by
      have h1 : ∑ k ∈ S_ins, (k : ℝ)⁻¹ ≤
          ∑ x ∈ E ×ˢ S_T, (φ x : ℝ)⁻¹ := by
        have himg : S_ins ⊆ (E ×ˢ S_T).image φ := by
          intro k hk
          rcases hmem_im k hk with ⟨x, hx, rfl⟩
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        calc
          ∑ k ∈ S_ins, (k : ℝ)⁻¹
              ≤ ∑ k ∈ (E ×ˢ S_T).image φ, (k : ℝ)⁻¹ :=
                Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          _ ≤ ∑ x ∈ E ×ˢ S_T, (φ x : ℝ)⁻¹ :=
                sum_image_le_sum_of_nonneg (E ×ˢ S_T) φ (fun k : ℕ => (k : ℝ)⁻¹)
                  (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      have h2 : ∑ x ∈ E ×ˢ S_T, (φ x : ℝ)⁻¹ =
          (∑ e ∈ E, ((p : ℝ) ^ e)⁻¹) * ∑ k' ∈ S_T, (k' : ℝ)⁻¹ := by
        rw [Finset.sum_product]
        have hterm : ∀ e : ℕ, ∀ k' : ℕ, (φ (e, k') : ℝ)⁻¹ = ((p : ℝ) ^ e)⁻¹ * (k' : ℝ)⁻¹ := by
          intro e k'
          dsimp [φ]
          rw [Nat.cast_mul, Nat.cast_pow, mul_inv]
        simp_rw [hterm]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => (Finset.mul_sum _ _ _).symm
      exact h1.trans_eq h2
    have hgeom : ∑ e ∈ E, ((p : ℝ) ^ e)⁻¹ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      have hr : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      have h1_r : 0 < 1 - (p : ℝ)⁻¹ := by linarith
      have hsum_eq : (1 - (p : ℝ)⁻¹) * ∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e =
          1 - ((p : ℝ)⁻¹) ^ (M + 1) :=
        one_sub_mul_geom_sum (p : ℝ)⁻¹ (M + 1)
      have hgeom_id : (∑ e ∈ E, ((p : ℝ) ^ e)⁻¹) =
          ∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e := by
        refine Finset.sum_congr rfl fun e _ => by rw [inv_pow]
      rw [hgeom_id, ← mul_le_mul_iff_of_pos_left h1_r]
      have hle1 : (1 - (p : ℝ)⁻¹) * ∑ e ∈ Finset.range (M + 1), ((p : ℝ)⁻¹) ^ e ≤ 1 := by
        rw [hsum_eq]
        have hpow_nn : 0 ≤ ((p : ℝ)⁻¹) ^ (M + 1) := pow_nonneg (inv_nonneg.mpr hp_pos.le) _
        linarith
      have hEq : (1 - (p : ℝ)⁻¹) * ((p : ℝ) / ((p : ℝ) - 1)) = 1 := by
        field_simp [hp_pos.ne', hp_sub_pos.ne']
      linarith
    calc
      ∑ k ∈ S_ins, (k : ℝ)⁻¹
          ≤ (∑ e ∈ E, ((p : ℝ) ^ e)⁻¹) * ∑ k' ∈ S_T, (k' : ℝ)⁻¹ := hsum_le_prod
      _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ T, (q : ℝ) / ((q : ℝ) - 1) := by
            gcongr

/-- Telescoping logarithmic lower bound for the partial harmonic sum:
`Real.log ((n : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹` for every `n : ℕ`. -/
theorem sum_inv_ge_log_succ (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
    have hlog_step : Real.log (((k : ℕ) + 1 : ℝ) + 1) - Real.log ((k : ℝ) + 1) ≤
        ((k + 1 : ℕ) : ℝ)⁻¹ := by
      have hdiv : ((k : ℝ) + 1 + 1) / ((k : ℝ) + 1) > 0 := div_pos hk2 hk1
      rw [Nat.cast_add, Nat.cast_one, ← Real.log_div hk2.ne' hk1.ne']
      calc
        Real.log (((k : ℝ) + 1 + 1) / ((k : ℝ) + 1))
            ≤ ((k : ℝ) + 1 + 1) / ((k : ℝ) + 1) - 1 := Real.log_le_sub_one_of_pos hdiv
        _ = ((k : ℝ) + 1)⁻¹ := by field_simp [hk1.ne']; ring
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hsplit, Finset.sum_insert hnot]
    push_cast at hlog_step ⊢
    linarith

/-- Lower bound for the sum of `1 / φ(s)` over squarefree `s ≤ M` by the harmonic sum `∑_{1 ≤ m ≤ M} 1 / m`. -/
theorem sum_squarefree_inv_totient_ge_sum_inv (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ ≤
      ∑ s ∈ (Finset.Icc 1 M).filter Squarefree, (s.totient : ℝ)⁻¹ := by
  let rad : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors, p
  let SF := (Finset.Icc 1 M).filter Squarefree
  have hrad_mem : ∀ m ∈ Finset.Icc 1 M, rad m ∈ SF := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hsq : Squarefree (rad m) := squarefree_prod_primes_set fun p hp => (Nat.mem_primeFactors.mp hp).1
    have hdvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
    have hpos : 1 ≤ rad m := Nat.pos_of_ne_zero hsq.ne_zero
    have hle : rad m ≤ M := (Nat.le_of_dvd (by omega) hdvd).trans hm'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩, hsq⟩
  have hfiber : ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ =
      ∑ s ∈ SF, ∑ m ∈ (Finset.Icc 1 M).filter (fun m => rad m = s), (m : ℝ)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hrad_mem]
  rw [hfiber]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs' := Finset.mem_filter.mp hs
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs'.1).1
  have hs_sq : Squarefree s := hs'.2
  have hs_pos : 0 < s := by omega
  let T := s.primeFactors
  have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hsub_fib :
      ∑ m ∈ (Finset.Icc 1 M).filter (fun m => rad m = s), (m : ℝ)⁻¹ ≤
        (s : ℝ)⁻¹ * ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ T), (k : ℝ)⁻¹ := by
    let F_k := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ T)
    let F_m := (Finset.Icc 1 M).filter (fun m => rad m = s)
    have hinj : ∀ m ∈ F_m, ∃ k ∈ F_k, s * k = m := by
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hm_icc := Finset.mem_Icc.mp hm'.1
      have hrad_eq : rad m = s := hm'.2
      have hs_dvd : s ∣ m := hrad_eq ▸ Nat.prod_primeFactors_dvd m
      let k := m / s
      have hk_eq : s * k = m := Nat.mul_div_cancel' hs_dvd
      have hm1 : 1 ≤ m := hm_icc.1
      have hk_pos : 1 ≤ k := Nat.div_pos (Nat.le_of_dvd hm1 hs_dvd) hs_pos
      have hk_le : k ≤ M := (Nat.div_le_self m s).trans hm_icc.2
      have hk_pf : k.primeFactors ⊆ T := by
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        have hp_m : p ∈ m.primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨hp.1, hp.2.1.trans (hk_eq ▸ dvd_mul_left k s), (by omega)⟩
        have hp_rad : p ∣ rad m := Finset.dvd_prod_of_mem _ hp_m
        rw [hrad_eq] at hp_rad
        exact Nat.mem_primeFactors.mpr ⟨hp.1, hp_rad, hs_pos.ne'⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, hk_pf⟩, hk_eq⟩
    have himg : F_m ⊆ F_k.image (fun k => s * k) := by
      intro m hm
      rcases hinj m hm with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    calc
      ∑ m ∈ F_m, (m : ℝ)⁻¹
          ≤ ∑ m ∈ F_k.image (fun k => s * k), (m : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ ∑ k ∈ F_k, ((s * k : ℕ) : ℝ)⁻¹ :=
            sum_image_le_sum_of_nonneg F_k (fun k => s * k) (fun m : ℕ => (m : ℝ)⁻¹)
              (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = (s : ℝ)⁻¹ * ∑ k ∈ F_k, (k : ℝ)⁻¹ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by rw [Nat.cast_mul, mul_inv]
  have hprod_id :
      (s : ℝ)⁻¹ * ∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1) = (s.totient : ℝ)⁻¹ := by
    have hs_prod : (s : ℝ) = ∏ p ∈ T, (p : ℝ) := by
      have := Nat.prod_primeFactors_of_squarefree hs_sq
      rw [← this]
      simp [T]
    have hφ_prod : (s.totient : ℝ) = ∏ p ∈ T, ((p : ℝ) - 1) := by
      rw [totient_squarefree_eq_prod hs_pos hs_sq, Nat.cast_prod]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (hT_prime p hp).one_lt.le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    have hprod_inv : (s : ℝ)⁻¹ = ∏ p ∈ T, (p : ℝ)⁻¹ := by
      rw [hs_prod, Finset.prod_inv_distrib]
    rw [hprod_inv, ← Finset.prod_mul_distrib, hφ_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hT_prime p hp).pos
    have hp_sub : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hT_prime p hp).two_le
      linarith
    field_simp [hp_pos.ne', hp_sub]
  calc
    ∑ m ∈ (Finset.Icc 1 M).filter (fun m => rad m = s), (m : ℝ)⁻¹
        ≤ (s : ℝ)⁻¹ * ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ T), (k : ℝ)⁻¹ :=
          hsub_fib
    _ ≤ (s : ℝ)⁻¹ * ∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1) := by
          gcongr
          exact sum_inv_primeFactors_subset_le M T hT_prime
    _ = (s.totient : ℝ)⁻¹ := hprod_id

/-- Logarithmic lower bound for the squarefree totient reciprocal sum (`1 ≤ z`):
`Real.log ((⌊z⌋₊ : ℝ) + 1) ≤ ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter Squarefree, (s.totient : ℝ)⁻¹`. -/
theorem sum_squarefree_inv_totient_ge_log_succ (z : ℝ) :
    Real.log ((⌊z⌋₊ : ℝ) + 1) ≤
      ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter Squarefree, (s.totient : ℝ)⁻¹ :=
  (sum_inv_ge_log_succ ⌊z⌋₊).trans (sum_squarefree_inv_totient_ge_sum_inv ⌊z⌋₊)

/-- Logarithmic lower bound for the squarefree totient reciprocal sum (`1 ≤ z`):
`Real.log z ≤ ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter Squarefree, (s.totient : ℝ)⁻¹`. -/
theorem sum_squarefree_inv_totient_ge_log {z : ℝ} (hz : 1 ≤ z) :
    Real.log z ≤
      ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter Squarefree, (s.totient : ℝ)⁻¹ := by
  have hz_lt : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hlog : Real.log z ≤ Real.log ((⌊z⌋₊ : ℝ) + 1) :=
    Real.log_le_log (by linarith) hz_lt.le
  exact hlog.trans (sum_squarefree_inv_totient_ge_log_succ z)

private theorem prod_div_totient_eq_sum_divisors_of_squarefree {d : ℕ} (hd : Squarefree d) :
    ((d : ℝ) / (d.totient : ℝ)) = ∑ r ∈ d.divisors, (r.totient : ℝ)⁻¹ := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp
    · have hd_gt : 1 < d := lt_of_le_of_ne hd_pos (Ne.symm hd1)
      let p := d.minFac
      have hp : p.Prime := Nat.minFac_prime hd_gt.ne'
      have hp_dvd : p ∣ d := Nat.minFac_dvd d
      let m := d / p
      have hdm : d = m * p := (Nat.div_mul_cancel hp_dvd).symm
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hd_pos hp_dvd) hp.pos
      have hm_lt : m < d := Nat.div_lt_self hd_pos hp.one_lt
      have hsq_m : Squarefree m := hd.squarefree_of_dvd (hdm ▸ dvd_mul_right m p)
      have hndvd : ¬ p ∣ m := by
        intro hpm
        exact hp.ne_one (Nat.isUnit_iff.mp (hd p (hdm ▸ mul_dvd_mul_right hpm p)))
      have hm_cop : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
      have ih_m := ih m hm_lt hsq_m hm_pos
      have hφ_d : d.totient = m.totient * (p - 1) := by
        rw [hdm, Nat.totient_mul hm_cop, Nat.totient_prime hp]
      have hmφ_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm_pos
      have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        linarith
      have hLHS : (d : ℝ) / (d.totient : ℝ) =
          ((m : ℝ) / (m.totient : ℝ)) * (1 + ((p : ℝ) - 1)⁻¹) := by
        rw [hφ_d, hdm, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
        field_simp [hmφ_pos.ne', hp_sub_pos.ne', hp_pos.ne']
        ring
      have hdiv_part :
          ∑ r ∈ d.divisors, (r.totient : ℝ)⁻¹ =
            (∑ r ∈ m.divisors, (r.totient : ℝ)⁻¹) +
              (∑ r ∈ m.divisors, ((r * p).totient : ℝ)⁻¹) := by
        have hdisj : Disjoint m.divisors (m.divisors.image (· * p)) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          rcases Finset.mem_image.mp hr2 with ⟨u, _, rfl⟩
          exact hndvd ((dvd_mul_left p u).trans (Nat.dvd_of_mem_divisors hr1))
        have hunion : d.divisors = m.divisors ∪ m.divisors.image (· * p) := by
          ext r
          simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image, ne_eq]
          constructor
          · rintro ⟨hrd, hd0⟩
            rw [hdm] at hrd
            by_cases hpr : p ∣ r
            · right
              rcases hpr with ⟨u, rfl⟩
              refine ⟨u, ⟨?_, hm_pos.ne'⟩, mul_comm u p⟩
              have hu : p * u ∣ p * m := mul_comm m p ▸ hrd
              exact Nat.dvd_of_mul_dvd_mul_left hp.pos hu
            · left
              have hr_cop_p : Nat.Coprime r p := (hp.coprime_iff_not_dvd.mpr hpr).symm
              exact ⟨hr_cop_p.dvd_of_dvd_mul_right hrd, hm_pos.ne'⟩
          · rintro (⟨hrm, _⟩ | ⟨u, ⟨hum, _⟩, rfl⟩)
            · exact ⟨hrm.trans (hdm ▸ dvd_mul_right m p), hd_pos.ne'⟩
            · exact ⟨hdm ▸ mul_dvd_mul_right hum p, hd_pos.ne'⟩
        rw [hunion, Finset.sum_union hdisj, Finset.sum_image]
        intro u1 _ u2 _ hu
        exact Nat.eq_of_mul_eq_mul_right hp.pos hu
      have hmul_sum :
          ∑ r ∈ m.divisors, ((r * p).totient : ℝ)⁻¹ =
            ((p : ℝ) - 1)⁻¹ * ∑ r ∈ m.divisors, (r.totient : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr_dvd : r ∣ m := Nat.dvd_of_mem_divisors hr
        have hr_cop : Nat.Coprime r p := hm_cop.coprime_dvd_left hr_dvd
        rw [Nat.totient_mul hr_cop, Nat.totient_prime hp, Nat.cast_mul,
          Nat.cast_sub hp.one_lt.le, Nat.cast_one, mul_inv, mul_comm]
      rw [hLHS, ih_m, hdiv_part, hmul_sum]
      ring

private theorem sum_squarefree_dvd_inv_totient_eq_div_totient {q : ℕ} (hq : 1 ≤ q) :
    ∑ d ∈ q.divisors.filter Squarefree, (d.totient : ℝ)⁻¹ = (q : ℝ) / (q.totient : ℝ) := by
  let P : ℕ := ∏ p ∈ q.primeFactors, p
  have hP_sq : Squarefree P :=
    squarefree_prod_primes_set fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hP_pos : 0 < P := Nat.pos_of_ne_zero hP_sq.ne_zero
  have hP_div : P.divisors = q.divisors.filter Squarefree := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, ne_eq]
    constructor
    · rintro ⟨hdP, _⟩
      have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hdP
      exact ⟨⟨hdP.trans (Nat.prod_primeFactors_dvd q), (by omega)⟩, hd_sq⟩
    · rintro ⟨⟨hdq, _⟩, hd_sq⟩
      refine ⟨?_, hP_pos.ne'⟩
      have hsf_d := Nat.prod_primeFactors_of_squarefree hd_sq
      rw [← hsf_d]
      refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
      exact Nat.primeFactors_mono hdq (by omega)
  have hP_ratio : (P : ℝ) / (P.totient : ℝ) = (q : ℝ) / (q.totient : ℝ) := by
    have hq_id := Nat.totient_mul_prod_primeFactors q
    have hP_id := Nat.totient_mul_prod_primeFactors P
    have hP_pf : P.primeFactors = q.primeFactors := by
      ext p
      simp only [Nat.mem_primeFactors, ne_eq]
      constructor
      · rintro ⟨hp, hpP, _⟩
        exact ⟨hp, hpP.trans (Nat.prod_primeFactors_dvd q), by omega⟩
      · rintro ⟨hp, hpq, _⟩
        exact ⟨hp, Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩), hP_pos.ne'⟩
    have hq_nz : q.totient ≠ 0 := (Nat.totient_pos.mpr hq).ne'
    have hP_nz : P.totient ≠ 0 := (Nat.totient_pos.mpr hP_pos).ne'
    have hprod_nz : (∏ p ∈ q.primeFactors, p) ≠ 0 := hP_pos.ne'
    have hsub_nz : (∏ p ∈ q.primeFactors, (p - 1)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have : 2 ≤ p := (Nat.mem_primeFactors.mp hp).1.two_le
      omega
    have hcomb : P * q.totient = q * P.totient := by
      have h1 := hq_id
      have h2 := hP_id
      rw [hP_pf] at h2
      have hprod_eq : P = ∏ p ∈ q.primeFactors, p := rfl
      rw [← hprod_eq] at h1 h2
      nlinarith [h1, h2]
    have hcombR : (P : ℝ) * (q.totient : ℝ) = (q : ℝ) * (P.totient : ℝ) := by
      exact_mod_cast hcomb
    have hqφ_ne : (q.totient : ℝ) ≠ 0 := by exact_mod_cast hq_nz
    have hPφ_ne : (P.totient : ℝ) ≠ 0 := by exact_mod_cast hP_nz
    field_simp [hqφ_ne, hPφ_ne]
    simpa [mul_comm (q : ℝ)] using hcombR
  rw [← hP_div, ← prod_div_totient_eq_sum_divisors_of_squarefree hP_sq, hP_ratio]

/-- Comparison between the full squarefree totient reciprocal sum and the coprime-to-`q`
squarefree totient reciprocal sum (`1 ≤ q`). -/
theorem sum_squarefree_coprime_inv_totient_ge (q M : ℕ) (hq : 1 ≤ q) :
    (∑ s ∈ (Finset.Icc 1 M).filter Squarefree, (s.totient : ℝ)⁻¹) ≤
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ s.Coprime q), (s.totient : ℝ)⁻¹ := by
  let SF := (Finset.Icc 1 M).filter Squarefree
  let SFq := (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ s.Coprime q)
  let Dq := q.divisors.filter Squarefree
  have hmem : ∀ s ∈ SF, ∃ x ∈ Dq ×ˢ SFq, x.1 * x.2 = s := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hs_icc := Finset.mem_Icc.mp hs'.1
    have hs1 : 1 ≤ s := hs_icc.1
    have hs_sq := hs'.2
    let d := s.gcd q
    let t := s / d
    have hd_dvd_s : d ∣ s := Nat.gcd_dvd_left s q
    have hd_dvd_q : d ∣ q := Nat.gcd_dvd_right s q
    have hst : d * t = s := Nat.mul_div_cancel' hd_dvd_s
    have hd_sq : Squarefree d := hs_sq.squarefree_of_dvd hd_dvd_s
    have ht_sq : Squarefree t := hs_sq.squarefree_of_dvd (hst ▸ dvd_mul_left t d)
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_s hs1
    have ht_pos : 1 ≤ t := Nat.div_pos (Nat.le_of_dvd hs1 hd_dvd_s) hd_pos
    have ht_le : t ≤ M := (Nat.div_le_self s d).trans hs_icc.2
    have hd_cop_t : Nat.Coprime d t := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      let p := (d.gcd t).minFac
      have hp : p.Prime := Nat.minFac_prime hne
      have hp_dvd := Nat.minFac_dvd (d.gcd t)
      have hpd : p ∣ d := hp_dvd.trans (Nat.gcd_dvd_left d t)
      have hpt : p ∣ t := hp_dvd.trans (Nat.gcd_dvd_right d t)
      have hpp : p * p ∣ s := by
        rw [← hst]
        exact mul_dvd_mul hpd hpt
      exact hp.ne_one (Nat.isUnit_iff.mp (hs_sq p hpp))
    have ht_cop_q : Nat.Coprime t q := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      let p := (t.gcd q).minFac
      have hp : p.Prime := Nat.minFac_prime hne
      have hpt : p ∣ t := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left t q)
      have hpq : p ∣ q := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right t q)
      have hps : p ∣ s := hpt.trans (hst ▸ dvd_mul_left t d)
      have hpd : p ∣ d := Nat.dvd_gcd hps hpq
      have hp1 : p ∣ 1 := hd_cop_t ▸ Nat.dvd_gcd hpd hpt
      exact hp.ne_one (Nat.dvd_one.mp hp1)
    refine ⟨(d, t), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd_dvd_q, by omega⟩, hd_sq⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht_pos, ht_le⟩, ht_sq, ht_cop_q⟩⟩, hst⟩
  have hsum_le :
      ∑ s ∈ SF, (s.totient : ℝ)⁻¹ ≤
        ∑ x ∈ Dq ×ˢ SFq, ((x.1 * x.2).totient : ℝ)⁻¹ := by
    have himg : SF ⊆ (Dq ×ˢ SFq).image (fun x => x.1 * x.2) := by
      intro s hs
      rcases hmem s hs with ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    calc
      ∑ s ∈ SF, (s.totient : ℝ)⁻¹
          ≤ ∑ s ∈ (Dq ×ˢ SFq).image (fun x => x.1 * x.2), (s.totient : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ ∑ x ∈ Dq ×ˢ SFq, ((x.1 * x.2).totient : ℝ)⁻¹ :=
            sum_image_le_sum_of_nonneg (Dq ×ˢ SFq) (fun x => x.1 * x.2)
              (fun m : ℕ => (m.totient : ℝ)⁻¹)
              (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hprod_eq :
      ∑ x ∈ Dq ×ˢ SFq, ((x.1 * x.2).totient : ℝ)⁻¹ =
        (∑ d ∈ Dq, (d.totient : ℝ)⁻¹) * ∑ t ∈ SFq, (t.totient : ℝ)⁻¹ := by
    rw [Finset.sum_product]
    have hterm : ∀ d ∈ Dq, ∀ t ∈ SFq,
        ((d * t).totient : ℝ)⁻¹ = (d.totient : ℝ)⁻¹ * (t.totient : ℝ)⁻¹ := by
      intro d hd t ht
      have hd_dvd : d ∣ q := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      have ht_cop : t.Coprime q := (Finset.mem_filter.mp ht).2.2
      have hcop : d.Coprime t := (ht_cop.coprime_dvd_right hd_dvd).symm
      rw [Nat.totient_mul hcop, Nat.cast_mul, mul_inv]
    calc
      ∑ d ∈ Dq, ∑ t ∈ SFq, ((d * t).totient : ℝ)⁻¹
          = ∑ d ∈ Dq, ∑ t ∈ SFq, (d.totient : ℝ)⁻¹ * (t.totient : ℝ)⁻¹ :=
            Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun t ht => hterm d hd t ht
      _ = (∑ d ∈ Dq, (d.totient : ℝ)⁻¹) * ∑ t ∈ SFq, (t.totient : ℝ)⁻¹ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
  rw [hprod_eq, sum_squarefree_dvd_inv_totient_eq_div_totient hq] at hsum_le
  exact hsum_le

private theorem card_Ioc_filter_modEq_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    y / (M : ℝ) - 1 <
        (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun n => n ≡ r [MOD M])).card : ℝ) ∧
      (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun n => n ≡ r [MOD M])).card : ℝ) <
        y / (M : ℝ) + 1 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  let r0 : ℕ := r % M
  have hr0_lt : r0 < M := Nat.mod_lt r (by omega)
  let Mlo : ℤ := ⌊(x - (r0 : ℝ)) / (M : ℝ)⌋
  let Mhi : ℤ := ⌊(x + y - (r0 : ℝ)) / (M : ℝ)⌋
  have hMlo_ge : -1 ≤ Mlo := by
    rw [← Int.lt_add_one_iff]
    change (-1 : ℤ) < ⌊(x - (r0 : ℝ)) / (M : ℝ)⌋ + 1
    have h1 : (-1 : ℝ) < (x - (r0 : ℝ)) / (M : ℝ) := by
      rw [lt_div_iff₀ hM_pos]
      have hr0_R : (r0 : ℝ) < (M : ℝ) := by exact_mod_cast hr0_lt
      linarith
    have h2 : (-1 : ℝ) < (⌊(x - (r0 : ℝ)) / (M : ℝ)⌋ : ℝ) + 1 :=
      h1.trans (Int.lt_floor_add_one _)
    exact_mod_cast h2
  have hbij :
      ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun n => n ≡ r [MOD M])).card =
        (Finset.Ioc Mlo Mhi).card := by
    refine Finset.card_bij (fun n _ => ((n / M : ℕ) : ℤ)) ?_ ?_ ?_
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hn_icc := Finset.mem_Ioc.mp hn'.1
      have hmod : n % M = r0 := hn'.2
      have hdiv : n = M * (n / M) + r0 := by rw [← hmod, Nat.div_add_mod]
      have hn_gt : x < (n : ℝ) := by
        by_contra hle
        push Not at hle
        have hfl : n ≤ ⌊x⌋₊ := Nat.le_floor hle
        omega
      have hn_le : (n : ℝ) ≤ x + y := by
        exact (Nat.le_floor_iff (by linarith)).mp hn_icc.2
      have hloR : (x - (r0 : ℝ)) / (M : ℝ) < ((n / M : ℕ) : ℝ) := by
        rw [div_lt_iff₀ hM_pos]
        have hn_eqR : (n : ℝ) = ((n / M : ℕ) : ℝ) * (M : ℝ) + (r0 : ℝ) := by
          exact_mod_cast (show n = (n / M) * M + r0 by rw [mul_comm]; exact hdiv)
        linarith
      have hhiR : ((n / M : ℕ) : ℝ) ≤ (x + y - (r0 : ℝ)) / (M : ℝ) := by
        rw [le_div_iff₀ hM_pos]
        have hn_eqR : (n : ℝ) = ((n / M : ℕ) : ℝ) * (M : ℝ) + (r0 : ℝ) := by
          exact_mod_cast (show n = (n / M) * M + r0 by rw [mul_comm]; exact hdiv)
        linarith
      rw [Finset.mem_Ioc]
      refine ⟨Int.floor_lt.mpr (by exact_mod_cast hloR), Int.le_floor.mpr (by exact_mod_cast hhiR)⟩
    · intro n1 hn1 n2 hn2 heq
      have h1 := (Finset.mem_filter.mp hn1).2
      have h2 := (Finset.mem_filter.mp hn2).2
      have hm1 : n1 % M = r0 := h1
      have hm2 : n2 % M = r0 := h2
      have hq : n1 / M = n2 / M := by exact_mod_cast heq
      rw [← Nat.div_add_mod n1 M, ← Nat.div_add_mod n2 M, hq, hm1, hm2]
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      have hk_nn : 0 ≤ k := by omega
      let kn : ℕ := k.toNat
      let n : ℕ := M * kn + r0
      have hkn : (kn : ℤ) = k := Int.toNat_of_nonneg hk_nn
      have hdiv : n / M = kn := by
        dsimp [n]
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr0_lt, add_zero]
      have hmod : n % M = r0 := by
        dsimp [n]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr0_lt]
      have hk_loR : (x - (r0 : ℝ)) / (M : ℝ) < (k : ℝ) :=
        Int.floor_lt.mp hk.1
      have hk_hiR : (k : ℝ) ≤ (x + y - (r0 : ℝ)) / (M : ℝ) := by
        exact Int.le_floor.mp hk.2
      have hn_eqR : (n : ℝ) = (k : ℝ) * (M : ℝ) + (r0 : ℝ) := by
        have hknR : (kn : ℝ) = (k : ℝ) := by exact_mod_cast hkn
        dsimp [n]
        push_cast
        rw [hknR]
        ring
      have hn_gt_x : x < (n : ℝ) := by
        have := (div_lt_iff₀ hM_pos).mp hk_loR
        linarith
      have hn_le_xy : (n : ℝ) ≤ x + y := by
        have := (le_div_iff₀ hM_pos).mp hk_hiR
        linarith
      have hn_lo : ⌊x⌋₊ < n := Nat.floor_lt hx |>.mpr hn_gt_x
      have hn_hi : n ≤ ⌊x + y⌋₊ := Nat.le_floor hn_le_xy
      refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn_lo, hn_hi⟩, ?_⟩, ?_⟩
      · change n % M = r % M
        exact hmod
      · rw [hdiv, hkn]
  rw [hbij]
  have hdiff_lo : y / (M : ℝ) - 1 < ((Mhi - Mlo : ℤ) : ℝ) := by
    have h1 : (x + y - (r0 : ℝ)) / (M : ℝ) - 1 < (Mhi : ℝ) := Int.sub_one_lt_floor _
    have h2 : (Mlo : ℝ) ≤ (x - (r0 : ℝ)) / (M : ℝ) := Int.floor_le _
    push_cast
    have hsub : (x + y - (r0 : ℝ)) / (M : ℝ) - (x - (r0 : ℝ)) / (M : ℝ) = y / (M : ℝ) := by
      field_simp [hM_pos.ne']; ring
    linarith
  have hdiff_hi : ((Mhi - Mlo : ℤ) : ℝ) < y / (M : ℝ) + 1 := by
    have h1 : (Mhi : ℝ) ≤ (x + y - (r0 : ℝ)) / (M : ℝ) := Int.floor_le _
    have h2 : (x - (r0 : ℝ)) / (M : ℝ) - 1 < (Mlo : ℝ) := Int.sub_one_lt_floor _
    push_cast
    have hsub : (x + y - (r0 : ℝ)) / (M : ℝ) - (x - (r0 : ℝ)) / (M : ℝ) = y / (M : ℝ) := by
      field_simp [hM_pos.ne']; ring
    linarith
  by_cases hle : Mlo ≤ Mhi
  · have hcard : ((Finset.Ioc Mlo Mhi).card : ℝ) = ((Mhi - Mlo : ℤ) : ℝ) := by
      rw [Int.card_Ioc]
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    rw [hcard]
    exact ⟨hdiff_lo, hdiff_hi⟩
  · have hlt : Mhi < Mlo := lt_of_not_ge hle
    have hcard0 : (Finset.Ioc Mlo Mhi).card = 0 := by
      rw [Finset.card_eq_zero, Finset.Ioc_eq_empty]
      omega
    rw [hcard0, Nat.cast_zero]
    have hneg : ((Mhi - Mlo : ℤ) : ℝ) ≤ -1 := by
      have : Mhi - Mlo ≤ -1 := by omega
      exact_mod_cast this
    constructor
    · linarith
    · positivity

/-- **Brun–Titchmarsh Inequality (Large-Sieve Form)**:
for `0 ≤ x`, `1 ≤ q`, `q < y`, and `(a, q) = 1`,
`piAP (x + y) q a - piAP x q a ≤ √(y / q) + 4 * y / (φ(q) * log (y / q))`. -/
theorem brun_titchmarsh_large_sieve {x y : ℝ} {q a : ℕ} (hx : 0 ≤ x) (hq : 1 ≤ q)
    (hqy : (q : ℝ) < y) (_ha : Nat.Coprime a q) :
    piAP (x + y) q a - piAP x q a ≤
      Real.sqrt (y / (q : ℝ)) + 4 * y / ((q.totient : ℝ) * Real.log (y / (q : ℝ))) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hy_pos : 0 < y := by linarith
  have hyq_gt1 : 1 < y / (q : ℝ) := (one_lt_div hq_pos).mpr hqy
  have hsqrt_gt1 : 1 < Real.sqrt (y / (q : ℝ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hyq_gt1
  let Q : ℕ := ⌊Real.sqrt (y / (q : ℝ))⌋₊
  have hQ : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hsqrt_gt1.le)
  have hQ_le_sqrt : (Q : ℝ) ≤ Real.sqrt (y / (q : ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
  have hQ_sq : (Q : ℝ) ^ 2 ≤ y / (q : ℝ) := by
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt (y / (q : ℝ))) ^ 2 := by gcongr
      _ = y / (q : ℝ) := Real.sq_sqrt (by positivity)
  have hpi_diff :
      piAP (x + y) q a - piAP x q a =
        (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) := by
    rw [piAP, piAP, primeCountingAP, primeCountingAP]
    have hsub : (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        (Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp_icc := Finset.mem_Icc.mp hp'.1
      have hfl : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_icc.1, hp_icc.2.trans hfl⟩, hp'.2⟩
    have hsdiff :
        ((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) \
          ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) =
          (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨_, hp2⟩, hpP⟩, hnot⟩
        refine ⟨⟨?_, hp2⟩, hpP⟩
        by_contra hle
        exact hnot ⟨⟨hpP.1.one_lt.le, by omega⟩, hpP⟩
      · rintro ⟨⟨hp1, hp2⟩, hpP⟩
        exact ⟨⟨⟨hpP.1.one_lt.le, hp2⟩, hpP⟩, fun h => by omega⟩
    have hcard_eq :
        ((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card =
          ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card +
            ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card := by
      rw [← hsdiff, ← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hsub]
    have hR : (((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) =
        (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) +
          (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) := by
      exact_mod_cast hcard_eq
    linarith
  let P_all := (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  let P_sm := P_all.filter (fun p => p ≤ Q)
  let P_lg := P_all.filter (fun p => Q < p)
  have hP_split : (P_all.card : ℝ) = (P_sm.card : ℝ) + (P_lg.card : ℝ) := by
    have hcard := P_all.card_filter_add_card_filter_not (fun p => p ≤ Q)
    have hnot_eq : P_all.filter (fun p => ¬ p ≤ Q) = P_lg := by
      ext p; simp [P_lg]
    rw [hnot_eq] at hcard
    exact_mod_cast hcard.symm
  have hP_sm_le : (P_sm.card : ℝ) ≤ Real.sqrt (y / (q : ℝ)) := by
    have hsub : P_sm ⊆ Finset.Icc 1 Q := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp'' := Finset.mem_filter.mp hp'.1
      exact Finset.mem_Icc.mpr ⟨hp''.2.1.one_lt.le, hp'.2⟩
    have hle : P_sm.card ≤ Q := by
      calc
        P_sm.card ≤ (Finset.Icc 1 Q).card := Finset.card_le_card hsub
        _ = Q := by simp
    exact (by exact_mod_cast hle : (P_sm.card : ℝ) ≤ (Q : ℝ)).trans hQ_le_sqrt
  have hP_lg_le : (P_lg.card : ℝ) ≤ 4 * y / ((q.totient : ℝ) * Real.log (y / (q : ℝ))) := by
    have hlog_pos : 0 < Real.log (y / (q : ℝ)) := Real.log_pos hyq_gt1
    have hφ_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    by_cases hPlg0 : P_lg.card = 0
    · rw [hPlg0, Nat.cast_zero]
      positivity
    let a0 : ℕ := a % q
    have ha0_lt : a0 < q := Nat.mod_lt a hq
    let Mlo : ℤ := ⌊(x - (a0 : ℝ)) / (q : ℝ)⌋
    let Mhi : ℤ := ⌊(x + y - (a0 : ℝ)) / (q : ℝ)⌋
    have hMlo_ge : -1 ≤ Mlo := by
      rw [← Int.lt_add_one_iff]
      have h1 : (-1 : ℝ) < (x - (a0 : ℝ)) / (q : ℝ) := by
        rw [lt_div_iff₀ hq_pos]
        have : (a0 : ℝ) < (q : ℝ) := by exact_mod_cast ha0_lt
        linarith
      exact_mod_cast h1.trans (Int.lt_floor_add_one _)
    let M0 : ℕ := (Mlo + 1).toNat
    have hM0_eq : (M0 : ℤ) = Mlo + 1 := Int.toNat_of_nonneg (by omega)
    let A : Finset ℕ := P_lg.image (fun p => p / q + 1)
    have hA_card : A.card = P_lg.card := by
      refine Finset.card_image_of_injOn ?_
      intro p1 hp1 p2 hp2 heq
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).2.2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).2.2
      have hm1 : p1 % q = a0 := h1
      have hm2 : p2 % q = a0 := h2
      have hq_div : p1 / q = p2 / q := Nat.succ_inj.mp heq
      rw [← Nat.div_add_mod p1 q, ← Nat.div_add_mod p2 q, hq_div, hm1, hm2]
    have hA_mem : ∀ m' ∈ A, Mlo < ((m' : ℤ) - 1) ∧ ((m' : ℤ) - 1) ≤ Mhi := by
      intro m' hm'
      rcases Finset.mem_image.mp hm' with ⟨p, hp, rfl⟩
      have hp' := Finset.mem_filter.mp hp
      have hp_all := Finset.mem_filter.mp hp'.1
      have hp_ioc := Finset.mem_Ioc.mp hp_all.1
      have hp_mod : p % q = a0 := hp_all.2.2
      have hp_eq : p = q * (p / q) + a0 := by rw [← hp_mod, Nat.div_add_mod]
      have hp_gt : x < (p : ℝ) := (Nat.floor_lt hx).mp hp_ioc.1
      have hp_le : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by linarith)).mp hp_ioc.2
      have hp_eqR : (p : ℝ) = ((p / q : ℕ) : ℝ) * (q : ℝ) + (a0 : ℝ) := by
        exact_mod_cast (show p = (p / q) * q + a0 by rw [mul_comm]; exact hp_eq)
      have hloR : (x - (a0 : ℝ)) / (q : ℝ) < ((p / q : ℕ) : ℝ) := by
        rw [div_lt_iff₀ hq_pos]; linarith
      have hhiR : ((p / q : ℕ) : ℝ) ≤ (x + y - (a0 : ℝ)) / (q : ℝ) := by
        rw [le_div_iff₀ hq_pos]; linarith
      have h1 : Mlo < ((p / q : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hloR)
      have h2 : ((p / q : ℕ) : ℤ) ≤ Mhi := Int.le_floor.mpr (by exact_mod_cast hhiR)
      omega
    have hM_lt : Mlo < Mhi := by
      have hAne : A.Nonempty := Finset.card_pos.mp (hA_card.symm ▸ Nat.pos_of_ne_zero hPlg0)
      rcases hAne with ⟨m', hm'⟩
      have hm'' := hA_mem m' hm'
      omega
    let N : ℕ := (Mhi - Mlo).toNat
    have hN1 : 1 ≤ N := by dsimp [N]; omega
    have hN_eq : (N : ℤ) = Mhi - Mlo := Int.toNat_of_nonneg (by omega)
    have hA_sub : A ⊆ Finset.Ioc M0 (M0 + N) := by
      intro m' hm'
      have hm'' := hA_mem m' hm'
      rw [Finset.mem_Ioc]
      omega
    have hN_sub_le : (N : ℝ) - 1 ≤ y / (q : ℝ) := by
      have h1 : (Mhi : ℝ) ≤ (x + y - (a0 : ℝ)) / (q : ℝ) := Int.floor_le _
      have h2 : (x - (a0 : ℝ)) / (q : ℝ) - 1 < (Mlo : ℝ) := Int.sub_one_lt_floor _
      have hNR : (N : ℝ) = (Mhi : ℝ) - (Mlo : ℝ) := by exact_mod_cast hN_eq
      have hsub : (x + y - (a0 : ℝ)) / (q : ℝ) - (x - (a0 : ℝ)) / (q : ℝ) = y / (q : ℝ) := by
        field_simp [hq_pos.ne']; ring
      linarith
    let Ω : ℕ → Finset ℕ := fun p' =>
      if h : p'.Prime ∧ ¬ p' ∣ q then
        let u := ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd h.1).mpr h.2).symm
        let x0 : ZMod p' := -((a0 : ZMod p') * (u⁻¹ : (ZMod p')ˣ))
        {(x0 + 1).val}
      else ∅
    have hΩ_spec : ∀ p', p'.Prime → p' ≤ Q → Ω p' ⊆ Finset.range p' ∧ (Ω p').card < p' := by
      intro p' hp' _
      dsimp [Ω]
      split_ifs with h
      · have : NeZero p' := ⟨hp'.ne_zero⟩
        constructor
        · intro r hr
          rw [Finset.mem_singleton] at hr
          rw [hr, Finset.mem_range]
          exact ZMod.val_lt _
        · simpa using hp'.one_lt
      · exact ⟨Finset.empty_subset _, hp'.pos⟩
    have hA_sift : ∀ p', p'.Prime → p' ≤ Q → ∀ m' ∈ A, m' % p' ∉ Ω p' := by
      intro p' hp' hp'Q m' hm' hmem
      dsimp [Ω] at hmem
      split_ifs at hmem with h
      swap
      · simp at hmem
      rcases Finset.mem_image.mp hm' with ⟨p, hp_mem, rfl⟩
      have hp_lg := Finset.mem_filter.mp hp_mem
      have hp_all := Finset.mem_filter.mp hp_lg.1
      have hp_prime : p.Prime := hp_all.2.1
      have hp_gt : p' < p := lt_of_le_of_lt hp'Q hp_lg.2
      have hp_mod : p % q = a0 := hp_all.2.2
      have hp_eq : p = q * (p / q) + a0 := by rw [← hp_mod, Nat.div_add_mod]
      rw [Finset.mem_singleton] at hmem
      have : NeZero p' := ⟨hp'.ne_zero⟩
      let u := ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd h.1).mpr h.2).symm
      have hm'_zmod : ((p / q + 1 : ℕ) : ZMod p') = -((a0 : ZMod p') * (u⁻¹ : (ZMod p')ˣ)) + 1 := by
        have hv : (((p / q + 1) % p' : ℕ) : ZMod p') = ((p / q + 1 : ℕ) : ZMod p') := by
          rw [← ZMod.val_natCast p' (p / q + 1), ZMod.natCast_zmod_val]
        rw [← hv, hmem, ZMod.natCast_zmod_val]
      have hm_zmod : ((p / q : ℕ) : ZMod p') = -((a0 : ZMod p') * (u⁻¹ : (ZMod p')ˣ)) := by
        rw [Nat.cast_add, Nat.cast_one] at hm'_zmod
        exact add_right_cancel hm'_zmod
      have hp_zmod : (p : ZMod p') = 0 := by
        conv_lhs => rw [hp_eq, Nat.cast_add, Nat.cast_mul, hm_zmod]
        have hu_eq : (q : ZMod p') = (u : ZMod p') := (ZMod.coe_unitOfCoprime q _).symm
        rw [hu_eq, mul_neg, mul_left_comm, Units.mul_inv, mul_one, neg_add_cancel]
      have hdvd : p' ∣ p := (ZMod.natCast_eq_zero_iff p p').mp hp_zmod
      rcases (Nat.dvd_prime hp_prime).mp hdvd with h1 | heq
      · exact hp'.ne_one h1
      · exact hp_gt.ne heq
    have hsieve := arithmetic_large_sieve_sifted_card Ω A M0 hN1 hQ hA_sub hΩ_spec hA_sift
    have hsieve_weight_eq :
        sieveWeightSum Ω Q =
          ∑ s ∈ (Finset.Icc 1 Q).filter (fun s => Squarefree s ∧ s.Coprime q),
            (s.totient : ℝ)⁻¹ := by
      rw [sieveWeightSum]
      have hsplit_sum :
          (∑ s ∈ (Finset.Icc 1 Q).filter Squarefree with s.Coprime q, sieveWeight Ω s) +
            (∑ s ∈ (Finset.Icc 1 Q).filter Squarefree with ¬ s.Coprime q, sieveWeight Ω s) =
          ∑ s ∈ (Finset.Icc 1 Q).filter Squarefree, sieveWeight Ω s :=
        Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 Q).filter Squarefree)
          (fun s => s.Coprime q) (sieveWeight Ω)
      rw [← hsplit_sum]
      have hzero :
          ∑ s ∈ ((Finset.Icc 1 Q).filter Squarefree).filter (fun s => ¬ s.Coprime q),
            sieveWeight Ω s = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have hs1 := Finset.mem_filter.mp hs
        have hs2 := Finset.mem_filter.mp hs1.1
        have hncop : ¬ s.Coprime q := hs1.2
        have hbad : ∃ p ∈ s.primeFactors, p ∣ q := by
          by_contra hnone
          push Not at hnone
          apply hncop
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hg
          let p := (s.gcd q).minFac
          have hp : p.Prime := Nat.minFac_prime hg
          have hps : p ∣ s := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left s q)
          have hpq : p ∣ q := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right s q)
          have hs_pos : s ≠ 0 := (hs2.2).ne_zero
          exact hnone p (Nat.mem_primeFactors.mpr ⟨hp, hps, hs_pos⟩) hpq
        rcases hbad with ⟨p, hp_pf, hpq⟩
        have hΩ_empty : Ω p = ∅ := by
          dsimp [Ω]
          split_ifs with h
          · exact absurd hpq h.2
          · rfl
        refine Finset.prod_eq_zero hp_pf ?_
        rw [hΩ_empty]
        simp
      have hmatch :
          ∑ s ∈ ((Finset.Icc 1 Q).filter Squarefree).filter (fun s => s.Coprime q),
            sieveWeight Ω s =
          ∑ s ∈ (Finset.Icc 1 Q).filter (fun s => Squarefree s ∧ s.Coprime q),
            (s.totient : ℝ)⁻¹ := by
        rw [Finset.filter_filter]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := Finset.mem_filter.mp hs
        have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs'.1).1
        have hsq : Squarefree s := hs'.2.1
        have hcop : s.Coprime q := hs'.2.2
        rw [sieveWeight, totient_squarefree_eq_prod hs1 hsq, Nat.cast_prod, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp' := Nat.mem_primeFactors.mp hp
        have hndvd : ¬ p ∣ q := fun hpq =>
          hp'.1.ne_one (Nat.isUnit_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hp'.2.1 hpq) |> Nat.isUnit_iff.mpr))
        have hcard1 : (Ω p).card = 1 := by
          dsimp [Ω]
          split_ifs with h
          · simp
          · exfalso; exact h ⟨hp'.1, hndvd⟩
        rw [hcard1, Nat.cast_one, Nat.cast_sub hp'.1.one_lt.le, Nat.cast_one, one_div]
      rw [hzero, add_zero, hmatch]
    have hL_ge :
        ((q.totient : ℝ) / (q : ℝ)) * ((1 / 2 : ℝ) * Real.log (y / (q : ℝ))) ≤
          sieveWeightSum Ω Q := by
      have hlog_Q : (1 / 2 : ℝ) * Real.log (y / (q : ℝ)) ≤ Real.log ((Q : ℝ) + 1) := by
        have hsqrt_lt : Real.sqrt (y / (q : ℝ)) < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
        have hlog1 : Real.log (Real.sqrt (y / (q : ℝ))) ≤ Real.log ((Q : ℝ) + 1) :=
          Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) hsqrt_lt.le
        have hlog_sq : Real.log (Real.sqrt (y / (q : ℝ))) = (1 / 2 : ℝ) * Real.log (y / (q : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
        linarith
      have hfull := hlog_Q.trans (sum_squarefree_inv_totient_ge_log_succ (Real.sqrt (y / (q : ℝ))))
      have hcomp := sum_squarefree_coprime_inv_totient_ge q Q hq
      have hprod := mul_le_mul_of_nonneg_left (hfull.trans hcomp) (by positivity : (0 : ℝ) ≤ (q.totient : ℝ) / (q : ℝ))
      have hcancel : ((q.totient : ℝ) / (q : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) = 1 := by
        field_simp [hq_pos.ne', hφ_pos.ne']
      calc
        ((q.totient : ℝ) / (q : ℝ)) * ((1 / 2 : ℝ) * Real.log (y / (q : ℝ)))
            ≤ ((q.totient : ℝ) / (q : ℝ)) *
                (((q : ℝ) / (q.totient : ℝ)) *
                  ∑ s ∈ (Finset.Icc 1 Q).filter (fun s => Squarefree s ∧ s.Coprime q), (s.totient : ℝ)⁻¹) := hprod
        _ = sieveWeightSum Ω Q := by
              rw [← mul_assoc, hcancel, one_mul, hsieve_weight_eq]
    have hL_lb_pos : 0 < ((q.totient : ℝ) / (q : ℝ)) * ((1 / 2 : ℝ) * Real.log (y / (q : ℝ))) := by
      positivity
    have hnum_le : (N : ℝ) - 1 + (Q : ℝ) ^ 2 ≤ 2 * (y / (q : ℝ)) := by linarith
    calc
      (P_lg.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hA_card.symm
      _ ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) / sieveWeightSum Ω Q := hsieve
      _ ≤ (2 * (y / (q : ℝ))) / (((q.totient : ℝ) / (q : ℝ)) * ((1 / 2 : ℝ) * Real.log (y / (q : ℝ)))) :=
            div_le_div₀ (by positivity) hnum_le hL_lb_pos hL_ge
      _ = 4 * y / ((q.totient : ℝ) * Real.log (y / (q : ℝ))) := by
            field_simp [hq_pos.ne', hφ_pos.ne', hlog_pos.ne']
            ring
  linarith

private theorem sum_totient_real_gcd_eq (S : Finset ℕ)
    (hS : ∀ d ∈ S, 1 ≤ d ∧ Squarefree d)
    (hS_dvd : ∀ d ∈ S, ∀ δ, δ ∣ d → δ ∈ S)
    {d1 d2 : ℕ} (hd1 : d1 ∈ S) (_hd2 : d2 ∈ S) :
    (Nat.gcd d1 d2 : ℝ) =
      ∑ δ ∈ S, if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) else 0 := by
  have hgcd_dvd1 : Nat.gcd d1 d2 ∣ d1 := Nat.gcd_dvd_left d1 d2
  have hdiv_eq : (Nat.gcd d1 d2).divisors = S.filter (fun δ => δ ∣ d1 ∧ δ ∣ d2) := by
    have hgcd_pos : 0 < Nat.gcd d1 d2 := Nat.gcd_pos_of_pos_left d2 (hS d1 hd1).1
    ext δ
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq]
    constructor
    · rintro ⟨⟨hδ1, hδ2⟩, _⟩
      exact ⟨hS_dvd d1 hd1 δ hδ1, hδ1, hδ2⟩
    · rintro ⟨_, hδ1, hδ2⟩
      exact ⟨⟨hδ1, hδ2⟩, hgcd_pos.ne'⟩
  have htot := Nat.sum_totient (Nat.gcd d1 d2)
  have htotR : (Nat.gcd d1 d2 : ℝ) = ∑ δ ∈ (Nat.gcd d1 d2).divisors, (δ.totient : ℝ) := by
    exact_mod_cast htot.symm
  rw [htotR, hdiv_eq, Finset.sum_filter]

private theorem sum_divisors_moebius_squarefree {m δ : ℕ} (hm_sq : Squarefree m) (hδm : δ ∣ m) :
    ∑ d ∈ m.divisors with δ ∣ d, (μ d : ℤ) = if m = δ then μ δ else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sq.ne_zero
  have hδ_pos : 0 < δ := Nat.pos_of_dvd_of_pos hδm hm_pos
  let k := m / δ
  have hmk : δ * k = m := Nat.mul_div_cancel' hδm
  have hk_pos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, mul_zero] at hmk
    omega
  have hk_cop : Nat.Coprime δ k := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    let p := (δ.gcd k).minFac
    have hp : p.Prime := Nat.minFac_prime hne
    have hpp : p * p ∣ m := by
      rw [← hmk]
      exact mul_dvd_mul ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left δ k))
        ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right δ k))
    exact hp.ne_one (Nat.isUnit_iff.mp (hm_sq p hpp))
  have hsum_bij :
      ∑ d ∈ m.divisors with δ ∣ d, (μ d : ℤ) =
        ∑ u ∈ k.divisors, (μ (δ * u) : ℤ) := by
    refine Finset.sum_bij (fun d hd => d / δ) ?_ ?_ ?_ ?_
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hdm := Nat.dvd_of_mem_divisors hd'.1
      rw [← hmk] at hdm
      rcases hd'.2 with ⟨u, rfl⟩
      have hu_dvd : u ∣ k := Nat.dvd_of_mul_dvd_mul_left hδ_pos hdm
      rw [Nat.mul_div_cancel_left u hδ_pos]
      exact Nat.mem_divisors.mpr ⟨hu_dvd, hk_pos.ne'⟩
    · intro d1 hd1 d2 hd2 heq
      rcases (Finset.mem_filter.mp hd1).2 with ⟨u1, rfl⟩
      rcases (Finset.mem_filter.mp hd2).2 with ⟨u2, rfl⟩
      rw [Nat.mul_div_cancel_left _ hδ_pos, Nat.mul_div_cancel_left _ hδ_pos] at heq
      rw [heq]
    · intro u hu
      have huk := Nat.dvd_of_mem_divisors hu
      refine ⟨δ * u, Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hmk ▸ mul_dvd_mul_left δ huk, hm_pos.ne'⟩, dvd_mul_right δ u⟩, ?_⟩
      exact Nat.mul_div_cancel_left u hδ_pos
    · intro d hd
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2]
  have hmul : ∑ u ∈ k.divisors, (μ (δ * u) : ℤ) = μ δ * ∑ u ∈ k.divisors, (μ u : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have huk := Nat.dvd_of_mem_divisors hu
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hk_cop.coprime_dvd_right huk)
  have hzeta : ∑ u ∈ k.divisors, (μ u : ℤ) = if k = 1 then 1 else 0 := by
    have hz := ArithmeticFunction.moebius_mul_coe_zeta
    have hzk := congrArg (fun f : ArithmeticFunction ℤ => f k) hz
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hzk
    have hsum_k : ∑ x ∈ k.divisorsAntidiagonal,
          μ x.1 * (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
        ∑ u ∈ k.divisors, μ u := by
      refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
      · intro x hx
        exact Nat.fst_mem_divisors_of_mem_antidiagonal hx
      · intro x1 hx1 x2 hx2 heq
        have h1 := Nat.mem_divisorsAntidiagonal.mp hx1
        have h2 := Nat.mem_divisorsAntidiagonal.mp hx2
        have hfst : x1.1 = x2.1 := heq
        have hx1_nz : x1.1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact hk_pos.ne' h1.1.symm
        have hsnd : x1.2 = x2.2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1_nz)
          (h1.1.trans (hfst ▸ h2.1.symm))
        exact Prod.ext hfst hsnd
      · intro u hu
        have huk := Nat.dvd_of_mem_divisors hu
        refine ⟨(u, k / u), Nat.mem_divisorsAntidiagonal.mpr
          ⟨Nat.mul_div_cancel' huk, hk_pos.ne'⟩, rfl⟩
      · intro x hx
        have hx2_nz : x.2 ≠ 0 := by
          intro h0
          have h1 := (Nat.mem_divisorsAntidiagonal.mp hx).1
          rw [h0, mul_zero] at h1
          exact hk_pos.ne' h1.symm
        have hζ : (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 = 1 := by
          simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hx2_nz]
        rw [hζ, mul_one]
    rw [← hsum_k, hzk]
  rw [hsum_bij, hmul, hzeta]
  by_cases hmδ : m = δ
  · have hk1 : k = 1 := by
      dsimp [k]
      rw [hmδ, Nat.div_self hδ_pos]
    simp [hmδ, hk1]
  · have hk1 : k ≠ 1 := by
      intro h
      rw [h, mul_one] at hmk
      exact hmδ hmk.symm
    simp [hmδ, hk1]

/-- The numerator of the first absolute moment of Selberg's optimal weights. -/
def selbergWeightMass (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, (∑ d ∈ n.divisors, (d:ℝ)) / n.totient

private theorem selbergWeightMass_identity (S : Finset ℕ) (hS : ∀ n∈S, Squarefree n)
    (hdiv : ∀ n∈S, ∀ d, d∣n → d∈S) (G : ℝ) (hG : 0<G) :
    (∑ d∈S, |(d:ℝ)*(((μ d:ℤ):ℝ)*(∑ n∈S with d∣n,(n.totient:ℝ)⁻¹)/G)|) = selbergWeightMass S/G := by
  have hab (d : ℕ) (hd : d∈S) :
      |(d:ℝ)*(((μ d:ℤ):ℝ)*(∑ n∈S with d∣n,(n.totient:ℝ)⁻¹)/G)| =
      ((∑ n∈S with d∣n,(d:ℝ)*(n.totient:ℝ)⁻¹)/G) := by
    have hm : |((μ d:ℤ):ℝ)|=1 := by exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree (hS d hd)
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_div,abs_mul,hm,one_mul,
      abs_of_nonneg (by positivity : 0≤∑ n∈S with d∣n,(n.totient:ℝ)⁻¹),abs_of_pos hG,← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hab,← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hf : S.filter (fun d => d∣n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2,(hS n hn).ne_zero⟩,fun h => ⟨hdiv n hn d h.1,h.1⟩⟩
  rw [← Finset.sum_filter,hf,← Finset.sum_mul,div_eq_mul_inv]

/-- Selberg bound retaining the first absolute moment of the optimal weights in the remainder. -/
theorem selberg_sieve_ap_upper_bound_refined {x y z : ℝ} {q a : ℕ} (hx : 0 ≤ x) (hy : 0 < y)
    (hq : 1 ≤ q) (_ha : Nat.Coprime a q) (hz : 1 ≤ z) :
    piAP (x + y) q a - piAP x q a ≤
      z + (y / (q : ℝ)) /
        (∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
          (s.totient : ℝ)⁻¹) +
      min (z^2) ((selbergWeightMass ((Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q)) /
        (∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q), (s.totient:ℝ)⁻¹))^2) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  let S : Finset ℕ := (Finset.Icc 1 ⌊z⌋₊).filter (fun d => Squarefree d ∧ d.Coprime q)
  have hS_spec : ∀ d ∈ S, 1 ≤ d ∧ Squarefree d ∧ d.Coprime q := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact ⟨(Finset.mem_Icc.mp hd'.1).1, hd'.2.1, hd'.2.2⟩
  have hS_dvd : ∀ d ∈ S, ∀ δ, δ ∣ d → δ ∈ S := by
    intro d hd δ hδd
    have hd' := hS_spec d hd
    have hδ_pos : 1 ≤ δ := Nat.pos_of_dvd_of_pos hδd hd'.1
    have hδ_le : δ ≤ ⌊z⌋₊ :=
      (Nat.le_of_dvd hd'.1 hδd).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hδ_pos, hδ_le⟩, hd'.2.1.squarefree_of_dvd hδd,
        hd'.2.2.coprime_dvd_left hδd⟩
  have h1S : (1 : ℕ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hz)⟩, squarefree_one, Nat.coprime_one_left _⟩
  let G : ℝ := ∑ m ∈ S, (m.totient : ℝ)⁻¹
  have hG_ge1 : 1 ≤ G := by
    have hle := Finset.single_le_sum (f := fun m : ℕ => (m.totient : ℝ)⁻¹)
      (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg _)) h1S
    simpa using hle
  have hG_pos : 0 < G := by linarith
  let w : ℕ → ℝ := fun d =>
    ((μ d : ℤ) : ℝ) * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G
  let lam : ℕ → ℝ := fun d => (d : ℝ) * w d
  have hlam1 : lam 1 = 1 := by
    dsimp [lam, w]
    have hflt : S.filter (1 ∣ ·) = S := by
      ext m; simp
    rw [hflt]
    simp only [Nat.cast_one, one_mul, ArithmeticFunction.moebius_apply_one, Int.cast_one]
    exact div_self hG_pos.ne'
  have hw_inv : ∀ δ ∈ S,
      ∑ d ∈ S with δ ∣ d, w d = ((μ δ : ℤ) : ℝ) / ((δ.totient : ℝ) * G) := by
    intro δ hδ
    have hδ_spec := hS_spec δ hδ
    have hδφ_pos : (0 : ℝ) < (δ.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hδ_spec.1
    calc
      ∑ d ∈ S with δ ∣ d, ((μ d : ℤ) : ℝ) * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G
          = G⁻¹ * ∑ d ∈ S with δ ∣ d,
              ∑ m ∈ S, if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun d _ => ?_
                have hinner_d :
                    ((μ d : ℤ) : ℝ) * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G =
                      G⁻¹ * ∑ m ∈ S, if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0 := by
                  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
                  refine Finset.sum_congr rfl fun m _ => ?_
                  split_ifs <;> ring
                exact hinner_d
      _ = G⁻¹ * ∑ m ∈ S, ∑ d ∈ S with δ ∣ d,
            if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0 := by
              rw [Finset.sum_comm]
      _ = G⁻¹ * ∑ m ∈ S, (m.totient : ℝ)⁻¹ *
            ∑ d ∈ m.divisors with δ ∣ d, ((μ d : ℤ) : ℝ) := by
              congr 1
              refine Finset.sum_congr rfl fun m hm => ?_
              have hm_pos : 0 < m := (hS_spec m hm).1
              have hfilter_eq : (S.filter (δ ∣ ·)).filter (· ∣ m) = m.divisors.filter (δ ∣ ·) := by
                ext d
                simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq]
                constructor
                · rintro ⟨⟨_, hδd⟩, hdm⟩
                  exact ⟨⟨hdm, hm_pos.ne'⟩, hδd⟩
                · rintro ⟨⟨hdm, _⟩, hδd⟩
                  exact ⟨⟨hS_dvd m hm d hdm, hδd⟩, hdm⟩
              have hrew1 : (∑ d ∈ S with δ ∣ d,
                  if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0) =
                  ∑ d ∈ (S.filter (δ ∣ ·)).filter (· ∣ m),
                    (m.totient : ℝ)⁻¹ * ((μ d : ℤ) : ℝ) := by
                rw [← Finset.sum_filter_add_sum_filter_not (S.filter (δ ∣ ·)) (· ∣ m)]
                have h1 : ∑ d ∈ (S.filter (δ ∣ ·)).filter (· ∣ m),
                    (if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0) =
                    ∑ d ∈ (S.filter (δ ∣ ·)).filter (· ∣ m),
                      (m.totient : ℝ)⁻¹ * ((μ d : ℤ) : ℝ) := by
                  refine Finset.sum_congr rfl fun d hd => ?_
                  simp only [(Finset.mem_filter.mp hd).2, ↓reduceIte, mul_comm]
                have h2 : ∑ d ∈ (S.filter (δ ∣ ·)).filter (fun d => ¬ d ∣ m),
                    (if d ∣ m then ((μ d : ℤ) : ℝ) * (m.totient : ℝ)⁻¹ else 0) = 0 := by
                  refine Finset.sum_eq_zero fun d hd => ?_
                  simp [(Finset.mem_filter.mp hd).2]
                rw [h1, h2, add_zero]
              rw [hrew1, hfilter_eq, ← Finset.mul_sum]
      _ = G⁻¹ * ∑ m ∈ S, (m.totient : ℝ)⁻¹ * (if m = δ then ((μ δ : ℤ) : ℝ) else 0) := by
              congr 1
              refine Finset.sum_congr rfl fun m hm => ?_
              by_cases hδm : δ ∣ m
              · have hm_sum := sum_divisors_moebius_squarefree (hS_spec m hm).2.1 hδm
                have hm_sumR : ∑ d ∈ m.divisors with δ ∣ d, ((μ d : ℤ) : ℝ) =
                    if m = δ then ((μ δ : ℤ) : ℝ) else 0 := by
                  have h := congrArg (Int.cast (R := ℝ)) hm_sum
                  rw [Int.cast_sum] at h
                  simpa [apply_ite] using h
                rw [hm_sumR]
              · have hemp : m.divisors.filter (δ ∣ ·) = ∅ := by
                  rw [Finset.eq_empty_iff_forall_notMem]
                  intro d hd
                  have hd' := Finset.mem_filter.mp hd
                  exact hδm (hd'.2.trans (Nat.dvd_of_mem_divisors hd'.1))
                have hne : m ≠ δ := fun h => hδm (h ▸ dvd_rfl)
                simp [hemp, hne]
      _ = G⁻¹ * ((δ.totient : ℝ)⁻¹ * ((μ δ : ℤ) : ℝ)) := by
              congr 1
              rw [Finset.sum_eq_single δ]
              · simp
              · intro m _ hne; simp [hne]
              · intro hnot; exact absurd hδ hnot
      _ = ((μ δ : ℤ) : ℝ) / ((δ.totient : ℝ) * G) := by
              field_simp [hG_pos.ne', hδφ_pos.ne']
  have hdiag_val :
      ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 / ((Nat.lcm d1 d2 : ℕ) : ℝ) = G⁻¹ := by
    have hterm_eq : ∀ d1 ∈ S, ∀ d2 ∈ S,
        lam d1 * lam d2 / ((Nat.lcm d1 d2 : ℕ) : ℝ) =
          w d1 * w d2 * (Nat.gcd d1 d2 : ℝ) := by
      intro d1 hd1 d2 hd2
      have hlcm : (d1 * d2 : ℕ) = Nat.gcd d1 d2 * Nat.lcm d1 d2 := (Nat.gcd_mul_lcm d1 d2).symm
      have hlcm_pos : (0 : ℝ) < ((Nat.lcm d1 d2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lcm_pos (hS_spec d1 hd1).1 (hS_spec d2 hd2).1
      have hlcmR : (d1 : ℝ) * (d2 : ℝ) = (Nat.gcd d1 d2 : ℝ) * ((Nat.lcm d1 d2 : ℕ) : ℝ) := by
        exact_mod_cast hlcm
      dsimp [lam]
      field_simp [hlcm_pos.ne']
      calc
        (d1 : ℝ) * w d1 * (d2 : ℝ) * w d2
            = w d1 * w d2 * ((d1 : ℝ) * (d2 : ℝ)) := by ring
        _ = w d1 * w d2 * ((Nat.gcd d1 d2 : ℝ) * ((Nat.lcm d1 d2 : ℕ) : ℝ)) := by rw [hlcmR]
        _ = w d1 * w d2 * ((Nat.lcm d1 d2 : ℕ) : ℝ) * (Nat.gcd d1 d2 : ℝ) := by ring
    calc
      ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 / ((Nat.lcm d1 d2 : ℕ) : ℝ)
          = ∑ d1 ∈ S, ∑ d2 ∈ S, w d1 * w d2 * (Nat.gcd d1 d2 : ℝ) :=
            Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hterm_eq d1 hd1 d2 hd2
      _ = ∑ d1 ∈ S, ∑ d2 ∈ S, ∑ δ ∈ S,
            (if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0) := by
            refine Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => ?_
            rw [sum_totient_real_gcd_eq S (fun d hd => ⟨(hS_spec d hd).1, (hS_spec d hd).2.1⟩)
              hS_dvd hd1 hd2, Finset.mul_sum]
            refine Finset.sum_congr rfl fun δ _ => by split_ifs <;> ring
      _ = ∑ δ ∈ S, (δ.totient : ℝ) * (∑ d ∈ S with δ ∣ d, w d) ^ 2 := by
            have hswap_outer :
                (∑ d1 ∈ S, ∑ d2 ∈ S, ∑ δ ∈ S,
                  if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0) =
                  ∑ δ ∈ S, ∑ d1 ∈ S, ∑ d2 ∈ S,
                    if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0 := by
              trans ∑ d1 ∈ S, ∑ δ ∈ S, ∑ d2 ∈ S,
                  if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0
              · exact Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
              · exact Finset.sum_comm
            have hswap : ∀ δ : ℕ,
                (∑ d1 ∈ S, ∑ d2 ∈ S,
                  if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0) =
                  (δ.totient : ℝ) * (∑ d ∈ S with δ ∣ d, w d) ^ 2 := by
              intro δ
              rw [sq, Finset.sum_mul, Finset.mul_sum]
              have hinner : ∑ d1 ∈ S, ∑ d2 ∈ S,
                  (if δ ∣ d1 ∧ δ ∣ d2 then (δ.totient : ℝ) * (w d1 * w d2) else 0) =
                  ∑ d1 ∈ S with δ ∣ d1, (δ.totient : ℝ) * (w d1 * ∑ d2 ∈ S with δ ∣ d2, w d2) := by
                conv_rhs => rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun d1 _ => ?_
                by_cases h1 : δ ∣ d1
                · simp only [h1, true_and, ↓reduceIte, Finset.sum_filter, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun d2 _ => by split_ifs <;> ring
                · simp [h1]
              rw [hinner, ← Finset.mul_sum]
            rw [hswap_outer]
            exact Finset.sum_congr rfl fun δ _ => hswap δ
      _ = ∑ δ ∈ S, (δ.totient : ℝ) * (((μ δ : ℤ) : ℝ) / ((δ.totient : ℝ) * G)) ^ 2 := by
            refine Finset.sum_congr rfl fun δ hδ => by rw [hw_inv δ hδ]
      _ = ∑ δ ∈ S, (δ.totient : ℝ)⁻¹ * G⁻¹ ^ 2 := by
            refine Finset.sum_congr rfl fun δ hδ => ?_
            have hδ_spec := hS_spec δ hδ
            have hδφ_pos : (0 : ℝ) < (δ.totient : ℝ) := by
              exact_mod_cast Nat.totient_pos.mpr hδ_spec.1
            have hμsq : ((μ δ : ℤ) : ℝ) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hδ_spec.2.1
            rw [div_pow, mul_pow, hμsq]
            field_simp [hδφ_pos.ne', hG_pos.ne']
      _ = G * G⁻¹ ^ 2 := by rw [← Finset.sum_mul]
      _ = G⁻¹ := by field_simp [hG_pos.ne']
  have hlam_abs_le : ∀ d ∈ S, |lam d| ≤ 1 := by
    intro d hd
    have hd_spec := hS_spec d hd
    have hdφ_pos : (0 : ℝ) < (d.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hd_spec.1
    have hμ_abs : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hsum_nn : 0 ≤ ∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹ :=
      Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    have habs_lam : |lam d| ≤ ((d : ℝ) / (d.totient : ℝ)) *
        ((d.totient : ℝ) * ∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G := by
      dsimp [lam, w]
      rw [← mul_div_assoc, abs_div, abs_mul, abs_mul,
        abs_of_pos (by exact_mod_cast hd_spec.1 : (0 : ℝ) < d),
        abs_of_pos hG_pos, abs_of_nonneg hsum_nn]
      have hmul : |((μ d : ℤ) : ℝ)| * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) ≤
          1 * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hμ_abs hsum_nn
      have h1 : (d : ℝ) * (|((μ d : ℤ) : ℝ)| * ∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G ≤
          (d : ℝ) * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G := by
        gcongr
        linarith
      refine h1.trans_eq ?_
      field_simp [hdφ_pos.ne', hG_pos.ne']
    let K_d := S.filter (fun k => k.Coprime d ∧ d * k ≤ ⌊z⌋₊)
    have hKd_sum :
        (d.totient : ℝ) * (∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) ≤
          ∑ k ∈ K_d, (k.totient : ℝ)⁻¹ := by
      have hmap : ∀ m ∈ S.filter (d ∣ ·),
          m / d ∈ K_d ∧ d * (m / d) = m := by
        intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hm_spec := hS_spec m hm'.1
        have hdm : d ∣ m := hm'.2
        have hm_pos : 0 < m := hm_spec.1
        have hk_eq : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hk_memS : m / d ∈ S := hS_dvd m hm'.1 (m / d) ⟨d, by rw [mul_comm]; exact hk_eq.symm⟩
        have hk_cop : (m / d).Coprime d := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          let p := ((m / d).gcd d).minFac
          have hp : p.Prime := Nat.minFac_prime hne
          have hpp : p * p ∣ m := by
            rw [← hk_eq]
            exact mul_dvd_mul ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _))
              ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _))
          exact hp.ne_one (Nat.isUnit_iff.mp (hm_spec.2.1 p hpp))
        have hm_le : m ≤ ⌊z⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm'.1).1).2
        refine ⟨Finset.mem_filter.mpr ⟨hk_memS, hk_cop, by rw [hk_eq]; exact hm_le⟩, hk_eq⟩
      have hsum_eq : ∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹ =
          ∑ k ∈ (S.filter (d ∣ ·)).image (· / d), ((d * k).totient : ℝ)⁻¹ := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun m hm => ?_
          rw [(hmap m hm).2]
        · intro m1 hm1 m2 hm2 heq
          dsimp only at heq
          rw [← (hmap m1 hm1).2, ← (hmap m2 hm2).2, heq]
      rw [hsum_eq, Finset.mul_sum]
      calc
        ∑ k ∈ (S.filter (d ∣ ·)).image (· / d), (d.totient : ℝ) * ((d * k).totient : ℝ)⁻¹
            ≤ ∑ k ∈ K_d, (d.totient : ℝ) * ((d * k).totient : ℝ)⁻¹ := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
                intro k hk
                rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
                exact (hmap m hm).1
        _ = ∑ k ∈ K_d, (k.totient : ℝ)⁻¹ := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hk' := Finset.mem_filter.mp hk
              have hk_pos : 1 ≤ k := (hS_spec k hk'.1).1
              have hkφ_pos : (0 : ℝ) < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk_pos
              rw [Nat.totient_mul hk'.2.1.symm, Nat.cast_mul, mul_inv]
              field_simp [hdφ_pos.ne', hkφ_pos.ne']
    have hprod_bound :
        ((d : ℝ) / (d.totient : ℝ)) * ∑ k ∈ K_d, (k.totient : ℝ)⁻¹ ≤ G := by
      rw [prod_div_totient_eq_sum_divisors_of_squarefree hd_spec.2.1, Finset.sum_mul]
      have hmul_sum :
          ∑ r ∈ d.divisors, (r.totient : ℝ)⁻¹ * ∑ k ∈ K_d, (k.totient : ℝ)⁻¹ =
            ∑ x ∈ d.divisors ×ˢ K_d, ((x.1 * x.2).totient : ℝ)⁻¹ := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hrd : r ∣ d := Nat.dvd_of_mem_divisors hr
        have hk_cop : k.Coprime d := (Finset.mem_filter.mp hk).2.1
        have hcop_rk : r.Coprime k := (hk_cop.coprime_dvd_right hrd).symm
        rw [Nat.totient_mul hcop_rk, Nat.cast_mul, mul_inv]
      rw [hmul_sum]
      have hinj_mul : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (d.divisors ×ˢ K_d : Set (ℕ × ℕ)) := by
        rintro ⟨r1, k1⟩ h1 ⟨r2, k2⟩ h2 heq
        simp only [Set.mem_prod, Finset.mem_coe] at h1 h2
        dsimp only at heq
        have hr1 : r1 ∣ d := Nat.dvd_of_mem_divisors h1.1
        have hr2 : r2 ∣ d := Nat.dvd_of_mem_divisors h2.1
        have hk1 : k1.Coprime d := (Finset.mem_filter.mp h1.2).2.1
        have hk2 : k2.Coprime d := (Finset.mem_filter.mp h2.2).2.1
        have hg1 : (r1 * k1).gcd d = r1 := by
          rw [Nat.Coprime.gcd_mul_right_cancel r1 hk1, Nat.gcd_eq_left hr1]
        have hg2 : (r2 * k2).gcd d = r2 := by
          rw [Nat.Coprime.gcd_mul_right_cancel r2 hk2, Nat.gcd_eq_left hr2]
        have hr_eq : r1 = r2 := by rw [← hg1, heq, hg2]
        have hr1_pos : 0 < r1 := Nat.pos_of_dvd_of_pos hr1 hd_spec.1
        have hk_eq : k1 = k2 := Nat.eq_of_mul_eq_mul_left hr1_pos (heq.trans (hr_eq ▸ rfl))
        exact Prod.ext hr_eq hk_eq
      have himg_sub : (d.divisors ×ˢ K_d).image (fun x => x.1 * x.2) ⊆ S := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨⟨r, k⟩, hrk, rfl⟩
        rcases Finset.mem_product.mp hrk with ⟨hr, hk⟩
        have hrd : r ∣ d := Nat.dvd_of_mem_divisors hr
        have hk' := Finset.mem_filter.mp hk
        have hk_spec := hS_spec k hk'.1
        have hr_sq : Squarefree r := hd_spec.2.1.squarefree_of_dvd hrd
        have hr_cop_k : r.Coprime k := (hk'.2.1.coprime_dvd_right hrd).symm
        have hr_cop_q : r.Coprime q := hd_spec.2.2.coprime_dvd_left hrd
        have hpos : 1 ≤ r * k := Nat.mul_pos (Nat.pos_of_dvd_of_pos hrd hd_spec.1) hk_spec.1
        have hle : r * k ≤ ⌊z⌋₊ :=
          (Nat.mul_le_mul_right k (Nat.le_of_dvd hd_spec.1 hrd)).trans hk'.2.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩,
          (Nat.squarefree_mul hr_cop_k).mpr ⟨hr_sq, hk_spec.2.1⟩,
          hr_cop_q.mul_left hk_spec.2.2⟩
      have himg_eq :
          ∑ x ∈ d.divisors ×ˢ K_d, ((x.1 * x.2).totient : ℝ)⁻¹ =
            ∑ m ∈ (d.divisors ×ˢ K_d).image (fun x => x.1 * x.2), (m.totient : ℝ)⁻¹ := by
        rw [Finset.sum_image]
        intro x1 hx1 x2 hx2 hxy
        rw [Finset.coe_product] at hx1 hx2
        exact hinj_mul hx1 hx2 hxy
      rw [himg_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub
        (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    calc
      |lam d| ≤ ((d : ℝ) / (d.totient : ℝ)) *
          ((d.totient : ℝ) * ∑ m ∈ S with d ∣ m, (m.totient : ℝ)⁻¹) / G := habs_lam
      _ ≤ ((d : ℝ) / (d.totient : ℝ)) * (∑ k ∈ K_d, (k.totient : ℝ)⁻¹) / G := by gcongr
      _ ≤ G / G := by gcongr
      _ = 1 := div_self hG_pos.ne'
  let P_all : Finset ℕ := (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  let P_sm : Finset ℕ := P_all.filter (fun p => (p : ℝ) ≤ z)
  let P_lg : Finset ℕ := P_all.filter (fun p => z < (p : ℝ))
  let N_ap : Finset ℕ := (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun n => n ≡ a [MOD q])
  have hpi_diff : piAP (x + y) q a - piAP x q a = (P_all.card : ℝ) := by
    rw [piAP, piAP, primeCountingAP, primeCountingAP]
    have hsub : (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        (Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp_icc := Finset.mem_Icc.mp hp'.1
      have hfl : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_icc.1, hp_icc.2.trans hfl⟩, hp'.2⟩
    have hsdiff :
        ((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) \
          ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) = P_all := by
      ext p
      simp only [P_all, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨_, hp2⟩, hpP⟩, hnot⟩
        refine ⟨⟨?_, hp2⟩, hpP⟩
        by_contra hle
        exact hnot ⟨⟨hpP.1.one_lt.le, by omega⟩, hpP⟩
      · rintro ⟨⟨hp1, hp2⟩, hpP⟩
        exact ⟨⟨⟨hpP.1.one_lt.le, hp2⟩, hpP⟩, fun h => by omega⟩
    have hcard_eq :
        ((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card =
          ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card +
            P_all.card := by
      rw [← hsdiff, ← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hsub]
    have hR : (((Finset.Icc 1 ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) =
        (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) +
          (P_all.card : ℝ) := by
      exact_mod_cast hcard_eq
    linarith
  have hP_sm_le : (P_sm.card : ℝ) ≤ z := by
    have hsub : P_sm ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp'' := Finset.mem_filter.mp hp'.1
      exact Finset.mem_Icc.mpr ⟨hp''.2.1.one_lt.le, Nat.le_floor hp'.2⟩
    have hle : P_sm.card ≤ ⌊z⌋₊ := by
      calc
        P_sm.card ≤ (Finset.Icc 1 ⌊z⌋₊).card := Finset.card_le_card hsub
        _ = ⌊z⌋₊ := by simp
    exact (by exact_mod_cast hle : (P_sm.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
  have hP_lg_le_quad : (P_lg.card : ℝ) ≤
      ∑ n ∈ N_ap, (∑ d ∈ S with d ∣ n, lam d) ^ 2 := by
    have hsub : P_lg ⊆ N_ap := by
      intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.2⟩
    have hplg_one : ∀ p ∈ P_lg, (∑ d ∈ S with d ∣ p, lam d) ^ 2 = 1 := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp'.1).2.1
      have hflt : S.filter (· ∣ p) = {1} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hdS, hdp⟩
          rcases (Nat.dvd_prime hp_prime).mp hdp with rfl | hdp_eq
          · rfl
          · exfalso
            have hle : (p : ℝ) ≤ z := by
              have hd_le : p ≤ ⌊z⌋₊ := hdp_eq ▸ (Finset.mem_Icc.mp (Finset.mem_filter.mp hdS).1).2
              exact (by exact_mod_cast hd_le : (p : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
            linarith [hp'.2]
        · rintro rfl; exact ⟨h1S, one_dvd p⟩
      rw [hflt, Finset.sum_singleton, hlam1, one_pow]
    calc
      (P_lg.card : ℝ) = ∑ p ∈ P_lg, (∑ d ∈ S with d ∣ p, lam d) ^ 2 := by
            rw [Finset.sum_congr rfl hplg_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ n ∈ N_ap, (∑ d ∈ S with d ∣ n, lam d) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hquad_expand :
      ∑ n ∈ N_ap, (∑ d ∈ S with d ∣ n, lam d) ^ 2 =
        ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 *
          ((N_ap.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := by
    have hterm : ∀ n ∈ N_ap, (∑ d ∈ S with d ∣ n, lam d) ^ 2 =
        ∑ d1 ∈ S, ∑ d2 ∈ S, if Nat.lcm d1 d2 ∣ n then lam d1 * lam d2 else 0 := by
      intro n _
      rw [sq, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      by_cases h1 : d1 ∣ n
      · simp only [h1, ↓reduceIte, Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d2 _ => ?_
        by_cases h2 : d2 ∣ n
        · simp [h2, Nat.lcm_dvd h1 h2]
        · have hl : ¬ Nat.lcm d1 d2 ∣ n := fun h => h2 ((Nat.dvd_lcm_right d1 d2).trans h)
          simp [h2, hl]
      · simp only [h1, ↓reduceIte]
        rw [Finset.sum_eq_zero]
        intro d2 _
        have hl : ¬ Nat.lcm d1 d2 ∣ n := fun h => h1 ((Nat.dvd_lcm_left d1 d2).trans h)
        simp [hl]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcount_bd : ∀ d1 ∈ S, ∀ d2 ∈ S,
      |((N_ap.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) -
          y / (((Nat.lcm d1 d2 : ℕ) : ℝ) * (q : ℝ))| ≤ 1 := by
    intro d1 hd1 d2 hd2
    let D := Nat.lcm d1 d2
    have hD_pos : 1 ≤ D := Nat.lcm_pos (hS_spec d1 hd1).1 (hS_spec d2 hd2).1
    have hD_cop : D.Coprime q :=
      ((hS_spec d1 hd1).2.2.mul_left (hS_spec d2 hd2).2.2).coprime_dvd_left
        (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
    have hr_ex : ∃ r : ℕ, ∀ n : ℕ, (n ≡ a [MOD q] ∧ D ∣ n) ↔ n ≡ r [MOD D * q] := by
      let u := ZMod.unitOfCoprime D hD_cop
      have : NeZero D := ⟨by omega⟩
      have : NeZero q := ⟨by omega⟩
      have hDq_pos : 0 < D * q := Nat.mul_pos hD_pos hq
      have : NeZero (D * q) := ⟨hDq_pos.ne'⟩
      let r : ℕ := D * ((a : ZMod q) * (u⁻¹ : (ZMod q)ˣ)).val
      refine ⟨r, fun n => ?_⟩
      constructor
      · rintro ⟨hna, ⟨k, rfl⟩⟩
        have hk_zmod : (k : ZMod q) = (a : ZMod q) * (u⁻¹ : (ZMod q)ˣ) := by
          have hna_z : ((D * k : ℕ) : ZMod q) = (a : ZMod q) :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mpr hna
          rw [Nat.cast_mul, (ZMod.coe_unitOfCoprime D hD_cop).symm] at hna_z
          calc
            (k : ZMod q) = (u⁻¹ : (ZMod q)ˣ) * (u * (k : ZMod q)) := by
              rw [← mul_assoc, Units.inv_mul, one_mul]
            _ = (u⁻¹ : (ZMod q)ˣ) * (a : ZMod q) := by rw [hna_z]
            _ = (a : ZMod q) * (u⁻¹ : (ZMod q)ˣ) := mul_comm _ _
        have hkm : k ≡ ((a : ZMod q) * (u⁻¹ : (ZMod q)ˣ)).val [MOD q] := by
          rw [← ZMod.natCast_eq_natCast_iff, hk_zmod, ZMod.natCast_zmod_val]
        change (D * k) % (D * q) = (D * ((a : ZMod q) * (u⁻¹ : (ZMod q)ˣ)).val) % (D * q)
        rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
        exact congrArg (D * ·) hkm
      · intro hnr
        refine ⟨?_, ?_⟩
        · have hmod_q : n ≡ r [MOD q] := hnr.of_dvd (dvd_mul_left q D)
          have hr_q : (r : ZMod q) = (a : ZMod q) := by
            dsimp [r]
            rw [Nat.cast_mul, ZMod.natCast_zmod_val, (ZMod.coe_unitOfCoprime D hD_cop).symm,
              ← mul_assoc, mul_comm (u : ZMod q) (a : ZMod q), mul_assoc, Units.mul_inv, mul_one]
          have hram : r ≡ a [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hr_q
          exact hmod_q.trans hram
        · have hmod_D : n % D = r % D := hnr.of_dvd (dvd_mul_right D q)
          have hr_D : D ∣ r := dvd_mul_right D _
          exact Nat.dvd_of_mod_eq_zero (hmod_D.trans (Nat.mod_eq_zero_of_dvd hr_D))
    rcases hr_ex with ⟨r, hr⟩
    have hflt_eq : N_ap.filter (fun n => D ∣ n) =
        (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (fun n => n ≡ r [MOD D * q]) := by
      ext n
      simp only [N_ap, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn1, hna⟩, hDn⟩
        exact ⟨hn1, (hr n).mp ⟨hna, hDn⟩⟩
      · rintro ⟨hn1, hnr⟩
        have h2 := (hr n).mpr hnr
        exact ⟨⟨hn1, h2.1⟩, h2.2⟩
    have hDq1 : 1 ≤ D * q := Nat.mul_pos hD_pos hq
    have hbd := card_Ioc_filter_modEq_bounds hx hy hDq1 r
    rw [← hflt_eq, Nat.cast_mul] at hbd
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let R : ℕ → ℕ → ℝ := fun d1 d2 =>
    ((N_ap.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) -
      y / (((Nat.lcm d1 d2 : ℕ) : ℝ) * (q : ℝ))
  let mass := ∑ d∈S, |lam d|
  have hmass : mass=selbergWeightMass S/G :=
    selbergWeightMass_identity S (fun n hn => (hS_spec n hn).2.1) hS_dvd G hG_pos
  have herr : ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 * R d1 d2 ≤ mass^2 := by
    dsimp [mass]
    rw [sq,Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => (le_abs_self _).trans ?_
    rw [abs_mul,abs_mul]
    exact mul_le_of_le_one_right (by positivity) (hcount_bd i hi j hj)
  have hsum_R : ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 * R d1 d2 ≤ min (z^2) ((selbergWeightMass S/G)^2) := by
    have hS_card : (S.card : ℝ) ≤ z := by
      calc
        (S.card : ℝ) ≤ ((Finset.Icc 1 ⌊z⌋₊).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = (⌊z⌋₊ : ℝ) := by simp
        _ ≤ z := Nat.floor_le (by linarith)
    rw [← hmass]
    refine le_min (herr.trans ?_) herr
    have htotal : mass≤(S.card:ℝ) := by
      simpa [mass] using Finset.sum_le_sum (s:=S) (fun d hd => hlam_abs_le d hd)
    exact pow_le_pow_left₀ (by dsimp [mass]; positivity) (htotal.trans hS_card) 2
  have hquad_split :
      ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 *
          ((N_ap.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) =
        (y / (q : ℝ)) * (∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) +
          ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 * R d1 d2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    dsimp [R]
    ring
  have hP_all_card : (P_all.card : ℝ) = (P_sm.card : ℝ) + (P_lg.card : ℝ) := by
    have hcard := P_all.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ z)
    have hnot : P_all.filter (fun p : ℕ => ¬ (p : ℝ) ≤ z) = P_lg := by
      ext p; simp [P_lg]
    rw [hnot] at hcard
    exact_mod_cast hcard.symm
  rw [hpi_diff, hP_all_card]
  have hcomb : (P_lg.card : ℝ) ≤ (y / (q : ℝ)) / G + min (z^2) ((selbergWeightMass S/G)^2) := by
    calc
      (P_lg.card : ℝ) ≤ ∑ n ∈ N_ap, (∑ d ∈ S with d ∣ n, lam d) ^ 2 := hP_lg_le_quad
      _ = ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 *
            ((N_ap.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := hquad_expand
      _ = (y / (q : ℝ)) * G⁻¹ + ∑ d1 ∈ S, ∑ d2 ∈ S, lam d1 * lam d2 * R d1 d2 := by
            rw [hquad_split, hdiag_val]
      _ ≤ (y / (q : ℝ)) / G + min (z^2) ((selbergWeightMass S/G)^2) := by
            rw [← div_eq_mul_inv]
            linarith [hsum_R]
  linarith [hP_sm_le, hcomb]

/-- **Selberg's `Λ²` Upper-Bound Sieve for Primes in Arithmetic Progressions**:
for `0 ≤ x`, `0 < y`, `1 ≤ q`, `Nat.Coprime a q`, and any sieve level `z ≥ 1`,
`piAP (x + y) q a - piAP x q a ≤ z + (y / q) / G_q(z) + z ^ 2`, where
`G_q(z) = ∑_{1 ≤ s ≤ z, s squarefree, (s, q) = 1} 1 / φ(s)`. -/
theorem selberg_sieve_ap_upper_bound {x y z : ℝ} {q a : ℕ} (hx : 0 ≤ x) (hy : 0 < y)
    (hq : 1 ≤ q) (_ha : Nat.Coprime a q) (hz : 1 ≤ z) :
    piAP (x + y) q a - piAP x q a ≤
      z + (y / (q : ℝ)) /
        (∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
          (s.totient : ℝ)⁻¹) + z ^ 2 := by
  exact (selberg_sieve_ap_upper_bound_refined hx hy hq _ha hz).trans (add_le_add_right (min_le_left ..) _)

/-- **Explicit Selberg Brun–Titchmarsh Bound**:
for `0 ≤ x`, `0 < y`, `1 ≤ q`, `Nat.Coprime a q`, and `1 < z`,
`piAP (x + y) q a - piAP x q a ≤ z + y / (φ(q) * log z) + z ^ 2`. -/
theorem brun_titchmarsh_selberg_explicit {x y z : ℝ} {q a : ℕ} (hx : 0 ≤ x) (hy : 0 < y)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hz : 1 < z) :
    piAP (x + y) q a - piAP x q a ≤
      z + y / ((q.totient : ℝ) * Real.log z) + z ^ 2 := by
  have hsel := selberg_sieve_ap_upper_bound hx hy hq ha hz.le
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hφ_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog_pos : 0 < Real.log z := Real.log_pos hz
  have hG_ge : ((q.totient : ℝ) / (q : ℝ)) * Real.log z ≤
      ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
        (s.totient : ℝ)⁻¹ := by
    have h1 := sum_squarefree_inv_totient_ge_log hz.le
    have h2 := sum_squarefree_coprime_inv_totient_ge q ⌊z⌋₊ hq
    have hprod := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ (q.totient : ℝ) / (q : ℝ))
    have hcancel : ((q.totient : ℝ) / (q : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) = 1 := by
      field_simp [hq_pos.ne', hφ_pos.ne']
    calc
      ((q.totient : ℝ) / (q : ℝ)) * Real.log z
          ≤ ((q.totient : ℝ) / (q : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) *
              ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q), (s.totient : ℝ)⁻¹) := hprod
      _ = ∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
            (s.totient : ℝ)⁻¹ := by rw [← mul_assoc, hcancel, one_mul]
  have hdiv_le :
      (y / (q : ℝ)) /
          (∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
            (s.totient : ℝ)⁻¹) ≤
        y / ((q.totient : ℝ) * Real.log z) := by
    have hden_pos : 0 < ((q.totient : ℝ) / (q : ℝ)) * Real.log z := by positivity
    calc
      (y / (q : ℝ)) /
          (∑ s ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime q),
            (s.totient : ℝ)⁻¹)
          ≤ (y / (q : ℝ)) / (((q.totient : ℝ) / (q : ℝ)) * Real.log z) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hG_ge
      _ = y / ((q.totient : ℝ) * Real.log z) := by
            field_simp [hq_pos.ne', hφ_pos.ne', hlog_pos.ne']
  linarith

/-- **Asymptotic Brun–Titchmarsh Inequality (Sharp Constant `2` via Selberg's Sieve)**:
for every `ε > 0`, there exists `C > 1` such that whenever `0 ≤ x`, `1 ≤ q`, `0 < y`,
`y / q ≥ C`, and `(a, q) = 1`,
`piAP (x + y) q a - piAP x q a ≤ (2 + ε) * y / (φ(q) * log (y / q))`. -/
theorem brun_titchmarsh_selberg_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 1, ∀ {x y : ℝ} {q a : ℕ}, 0 ≤ x → 1 ≤ q → 0 < y → C ≤ y / (q : ℝ) →
      Nat.Coprime a q →
      piAP (x + y) q a - piAP x q a ≤
        (2 + ε) * y / ((q.totient : ℝ) * Real.log (y / (q : ℝ))) := by
  let δ : ℝ := min (1 / 8 : ℝ) (ε / (4 * (4 + ε)))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le : δ ≤ 1 / 8 := min_le_left _ _
  have hδ_le2 : δ ≤ ε / (4 * (4 + ε)) := min_le_right _ _
  let α : ℝ := 1 / 2 - δ
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hinv_α : α⁻¹ ≤ 2 + ε / 2 := by
    have h1 : 4 * (4 + ε) * δ ≤ ε := by
      calc
        4 * (4 + ε) * δ ≤ 4 * (4 + ε) * (ε / (4 * (4 + ε))) := by gcongr
        _ = ε := by field_simp [(by linarith : 4 + ε ≠ 0)]
    have h2 : (1 : ℝ) ≤ (2 + ε / 2) * (1 / 2 - δ) := by nlinarith
    calc
      α⁻¹ = 1 / (1 / 2 - δ) := by rw [one_div]
      _ ≤ 2 + ε / 2 := (div_le_iff₀ hα_pos).mpr h2
  let M_r : ℝ := 4 / (ε * δ)
  let C1 : ℝ := max 2 (M_r ^ (δ⁻¹))
  let C : ℝ := max C1 (4 ^ (α⁻¹))
  have hC1_ge2 : 2 ≤ C1 := le_max_left _ _
  have hC_ge2 : 2 ≤ C := hC1_ge2.trans (le_max_left _ _)
  refine ⟨C, by linarith, ?_⟩
  intro x y q a hx hq hy hCu ha
  let u : ℝ := y / (q : ℝ)
  have hu_ge2 : 2 ≤ u := hC_ge2.trans hCu
  have hu_pos : 0 < u := by linarith
  have hlog_u_pos : 0 < Real.log u := Real.log_pos (by linarith)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hφ_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ_le_q : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  let z : ℝ := u ^ α
  have hz_gt1 : 1 < z := Real.one_lt_rpow (by linarith) hα_pos
  have hz_ge4 : 4 ≤ z := by
    have h4 : (4 ^ (α⁻¹)) ≤ u := (le_max_right C1 (4 ^ (α⁻¹))).trans hCu
    calc
      (4 : ℝ) = (4 ^ (α⁻¹)) ^ α := by
          rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ hα_pos.ne', Real.rpow_one]
      _ ≤ u ^ α := Real.rpow_le_rpow (by positivity) h4 hα_pos.le
  have hz_le_sq : z ≤ z ^ 2 := by nlinarith
  have hlog_z : Real.log z = α * Real.log u := Real.log_rpow hu_pos α
  have hmain_term :
      y / ((q.totient : ℝ) * Real.log z) ≤
        (2 + ε / 2) * y / ((q.totient : ℝ) * Real.log u) := by
    rw [hlog_z]
    have h1 : y / ((q.totient : ℝ) * (α * Real.log u)) =
        α⁻¹ * (y / ((q.totient : ℝ) * Real.log u)) := by
      field_simp [hφ_pos.ne', hα_pos.ne', hlog_u_pos.ne']
    rw [h1]
    calc
      α⁻¹ * (y / ((q.totient : ℝ) * Real.log u))
          ≤ (2 + ε / 2) * (y / ((q.totient : ℝ) * Real.log u)) := by gcongr
      _ = (2 + ε / 2) * y / ((q.totient : ℝ) * Real.log u) := by ring
  have hlog_u_bd : Real.log u ≤ (ε / 4) * u ^ (2 * δ) := by
    have hlog_rpow : Real.log (u ^ δ) = δ * Real.log u := Real.log_rpow hu_pos δ
    have huδ_pos : 0 < u ^ δ := Real.rpow_pos_of_pos hu_pos δ
    have hlog_le : Real.log (u ^ δ) ≤ u ^ δ := by
      linarith [Real.log_le_sub_one_of_pos huδ_pos]
    have hlog_div : Real.log u ≤ u ^ δ / δ := by
      rw [le_div_iff₀ hδ_pos]
      linarith [hlog_rpow, hlog_le]
    have hu_ge_Mr : M_r ≤ u ^ δ := by
      have hMr_nn : 0 ≤ M_r := by positivity
      have hC_mr : M_r ^ (δ⁻¹) ≤ u := ((le_max_right 2 (M_r ^ (δ⁻¹))).trans (le_max_left _ _)).trans hCu
      calc
        M_r = (M_r ^ (δ⁻¹)) ^ δ := by
            rw [← Real.rpow_mul hMr_nn, inv_mul_cancel₀ hδ_pos.ne', Real.rpow_one]
        _ ≤ u ^ δ := Real.rpow_le_rpow (by positivity) hC_mr hδ_pos.le
    have h1 : Real.log u * 1 ≤ (u ^ δ / δ) * ((ε * δ / 4) * u ^ δ) := by
      have hstep : 1 ≤ (ε * δ / 4) * u ^ δ := by
        have : 4 / (ε * δ) ≤ u ^ δ := hu_ge_Mr
        have hpos : 0 < ε * δ := by positivity
        calc
          (1 : ℝ) = (ε * δ / 4) * (4 / (ε * δ)) := by field_simp [hε.ne', hδ_pos.ne']
          _ ≤ (ε * δ / 4) * u ^ δ := by gcongr
      exact mul_le_mul hlog_div hstep zero_le_one (by positivity)
    have h2 : u ^ δ * u ^ δ = u ^ (2 * δ) := by
      rw [← Real.rpow_add hu_pos, two_mul]
    calc
      Real.log u = Real.log u * 1 := (mul_one _).symm
      _ ≤ (u ^ δ / δ) * ((ε * δ / 4) * u ^ δ) := h1
      _ = (ε / 4) * (u ^ δ * u ^ δ) := by field_simp [hδ_pos.ne']
      _ = (ε / 4) * u ^ (2 * δ) := by rw [h2]
  have herr_term : z + z ^ 2 ≤ (ε / 2) * y / ((q.totient : ℝ) * Real.log u) := by
    have hz_sq_eq : z ^ 2 = u ^ (2 * α) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]
      congr 1
      ring
    have hu_split : u = u ^ (2 * α) * u ^ (2 * δ) := by
      rw [← Real.rpow_add hu_pos]
      have hexp : 2 * α + 2 * δ = 1 := by dsimp [α]; ring
      rw [hexp, Real.rpow_one]
    have h2z_le : z + z ^ 2 ≤ (ε / 2) * u / Real.log u := by
      have hsum_le : z + z ^ 2 ≤ 2 * u ^ (2 * α) := by linarith [hz_le_sq, hz_sq_eq]
      have hmul_log : 2 * u ^ (2 * α) * Real.log u ≤ (ε / 2) * u := by
        calc
          2 * u ^ (2 * α) * Real.log u
              ≤ 2 * u ^ (2 * α) * ((ε / 4) * u ^ (2 * δ)) := by gcongr
          _ = (ε / 2) * (u ^ (2 * α) * u ^ (2 * δ)) := by ring
          _ = (ε / 2) * u := by rw [← hu_split]
      exact hsum_le.trans ((le_div_iff₀ hlog_u_pos).mpr hmul_log)
    have hu_le_yφ : u ≤ y / (q.totient : ℝ) := by
      dsimp [u]
      exact div_le_div_of_nonneg_left hy.le hφ_pos hφ_le_q
    calc
      z + z ^ 2 ≤ (ε / 2) * u / Real.log u := h2z_le
      _ ≤ (ε / 2) * (y / (q.totient : ℝ)) / Real.log u := by gcongr
      _ = (ε / 2) * y / ((q.totient : ℝ) * Real.log u) := by ring
  have hexpl := brun_titchmarsh_selberg_explicit hx hy hq ha hz_gt1
  calc
    piAP (x + y) q a - piAP x q a
        ≤ z + y / ((q.totient : ℝ) * Real.log z) + z ^ 2 := hexpl
    _ = y / ((q.totient : ℝ) * Real.log z) + (z + z ^ 2) := by ring
    _ ≤ (2 + ε / 2) * y / ((q.totient : ℝ) * Real.log u) +
          (ε / 2) * y / ((q.totient : ℝ) * Real.log u) := by linarith [hmain_term, herr_term]
    _ = (2 + ε) * y / ((q.totient : ℝ) * Real.log (y / (q : ℝ))) := by dsimp [u]; ring

end BrunTitchmarshAndSelberg

end AnalyticNumberTheory.SieveMethods
