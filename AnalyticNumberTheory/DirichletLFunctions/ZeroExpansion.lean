import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import AnalyticNumberTheory.AnalyticTools.EntireFunctions.Order
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import AnalyticNumberTheory.DirichletLFunctions.GaussSums
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-!
# Zero Expansion and Zero-Density Estimates for Dirichlet L-Functions

This file develops the global zero theory of Dirichlet L-functions `L(s, χ)` and their
completed counterparts `Λ(s, χ)`:

1. Critical-strip zero characterization, conjugation symmetries, and functional-equation
   symmetries with preservation of analytic multiplicities.
2. Entireness and order-1 growth (`EntireOrderLe (completedLFunction χ) 1`) for primitive
   characters of modulus `q ≥ 2`.
3. Genus-1 Hadamard factorization and logarithmic derivative partial fraction expansions for
   primitive and imprimitive characters.
4. Local unit-interval zero-density estimates via Jensen's formula.
5. Zero-counting functions `zeroCountL` and `zeroCountHalfL`, unconditional Stirling gamma
   and `Re s = 2` boundary estimates, and the Riemann–von Mangoldt asymptotic deduction.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter MeasureTheory Metric Set

namespace AnalyticNumberTheory.DirichletLFunctions

open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.EntireFunctions
open AnalyticNumberTheory.AnalyticTools.Gamma

section CriticalStripAndSymmetry

/-- The set of critical-strip zeros of the Dirichlet L-function associated with `χ`,
consisting of all `ρ : ℂ` with `0 < Re ρ < 1` and `LFunction χ ρ = 0`. -/
def CriticalStripZerosL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

private lemma star_ne_one_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : star χ ≠ 1 := by
  intro h
  apply hχ
  simpa using congrArg star h

private lemma cpow_natCast_conj (n : ℕ) (s : ℂ) :
    (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
  have hn_cast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [hn_cast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

private lemma star_char_apply_nat {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (star χ) n = conj (χ n) := by
  rw [star_char_eq_inv]
  exact (star_char_apply χ n).symm

/-- A primitive character of modulus `q ≥ 2` is non-principal. -/
lemma isPrimitive_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) : χ ≠ 1 := by
  intro h1
  have hcond : χ.conductor = 1 := by
    rw [h1]
    exact DirichletCharacter.conductor_one
  have hprim : χ.conductor = q := hχ
  omega

/-- The conjugate character `star χ` of a primitive character `χ` is also primitive. -/
lemma isPrimitive_star {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : (star χ).IsPrimitive := by
  rw [star_char_eq_inv]
  exact hχ.inv

/-- On the half-plane `0 < Re s`, the Gamma factor of `χ` does not vanish. -/
lemma gammaFactor_ne_zero_of_re_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rw [gammaFactor_eq_pi_mul_Gamma]
  refine mul_ne_zero ?_ ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    have hre : 0 < (s + (parityExp χ : ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      positivity
    linarith [show ((s + (parityExp χ : ℂ)) / 2).re = (s + (parityExp χ : ℂ)).re / 2 by simp]

/-- Vanishing characterization of the Gamma factor of `χ`: `gammaFactor χ s = 0` iff
`s = -(2 * m + parityExp χ)` for some `m : ℕ`. -/
lemma gammaFactor_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s = 0 ↔
      ∃ m : ℕ, s = -((2 * (m : ℂ) + parityExp χ)) := by
  rw [gammaFactor_eq_pi_mul_Gamma, mul_eq_zero]
  have hpi : (Real.pi : ℂ) ^ (-(s + (parityExp χ : ℂ)) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  simp only [hpi, false_or]
  constructor
  · intro hG
    by_contra hnone
    exact absurd hG (Complex.Gamma_ne_zero fun m hm ↦ hnone ⟨m, by linear_combination 2 * hm⟩)
  · rintro ⟨m, rfl⟩
    have hz : (-((2 * (m : ℂ) + parityExp χ)) + parityExp χ) / 2 = -(m : ℂ) := by ring
    rw [hz]
    exact Complex.Gamma_neg_nat_eq_zero m

/-- Conjugation symmetry of the Gamma factor:
`gammaFactor (star χ) (conj s) = conj (gammaFactor χ s)`. -/
lemma gammaFactor_star_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor (star χ) (conj s) =
      conj (DirichletCharacter.gammaFactor χ s) := by
  rw [gammaFactor_eq_Gammaℝ, gammaFactor_eq_Gammaℝ, parityExp_star]
  have hconj : conj s + (parityExp χ : ℂ) = conj (s + (parityExp χ : ℂ)) := by
    simp
  rw [hconj, Complex.Gammaℝ_conj]

private lemma LFunction_star_conj_of_one_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction (star χ) (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  have hs' : 1 < (conj s).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries (star χ) hs',
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum : LSeriesSummable (fun n ↦ χ n) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hhas : HasSum (fun n ↦ conj (LSeries.term (fun n ↦ χ n) s n))
      (conj (∑' n : ℕ, LSeries.term (fun n ↦ χ n) s n)) :=
    hsum.hasSum.map Complex.conjCLE.toContinuousLinearMap Complex.continuous_conj
  have hhas' : HasSum (LSeries.term (fun n ↦ (star χ) n) (conj s))
      (conj (∑' n : ℕ, LSeries.term (fun n ↦ χ n) s n)) := by
    refine hhas.congr_fun fun n ↦ ?_
    cases n with
    | zero => simp [LSeries.term]
    | succ k =>
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k),
        LSeries.term_of_ne_zero (Nat.succ_ne_zero k), map_div₀,
        cpow_natCast_conj (k + 1) s, star_char_apply_nat]
  exact hhas'.tsum_eq

/-- Conjugation symmetry of Dirichlet L-functions for non-principal characters on all of `ℂ`. -/
theorem LFunction_star_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction (star χ) (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  have hf : Differentiable ℂ (fun z ↦ conj (DirichletCharacter.LFunction (star χ) (conj z))) :=
    fun z ↦ differentiableAt_conj_conj_iff.mpr
      ((differentiable_LFunction_of_ne_one (star_ne_one_of_ne_one hχ)) (conj z))
  have hg : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    differentiable_LFunction_of_ne_one hχ
  have heqOn : Set.EqOn
      (fun z ↦ conj (DirichletCharacter.LFunction (star χ) (conj z)))
      (DirichletCharacter.LFunction χ) Set.univ := by
    refine (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (z₀ := (2 : ℂ))
      (Set.mem_univ _) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [LFunction_star_conj_of_one_lt_re χ hz, Complex.conj_conj]
  simpa using congrArg conj (heqOn (Set.mem_univ s))

private lemma conj_prod_eulerFactors (q : ℕ) (s : ℂ) :
    (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-conj s))) =
      conj (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) := by
  have h1 : conj (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) =
      ∏ p ∈ q.primeFactors, conj (1 - (p : ℂ) ^ (-s)) := map_prod conj _ _
  rw [h1]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [map_sub, map_one, show -conj s = conj (-s) from (map_neg conj s).symm, cpow_natCast_conj p (-s)]

/-- Conjugation symmetry of Dirichlet L-functions away from the possible pole at `s = 1`. -/
theorem LFunction_star_conj_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction (star χ) (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  rcases hχs with hχ | hs
  · exact LFunction_star_conj hχ s
  · by_cases hχ : χ = 1
    · have hstar1 : star χ = 1 := by simp [hχ]
      have hconj_ne : conj s ≠ 1 := fun h ↦ hs (by simpa using congrArg conj h)
      have hL1 : DirichletCharacter.LFunction χ = DirichletCharacter.LFunctionTrivChar q := by
        rw [hχ]
      have hLs : DirichletCharacter.LFunction (star χ) =
          DirichletCharacter.LFunctionTrivChar q := by
        rw [hstar1]
      rw [hLs, hL1,
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hconj_ne,
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs,
        map_mul, riemannZeta_conj, conj_prod_eulerFactors]
    · exact LFunction_star_conj hχ s

/-- Conjugation symmetry of completed Dirichlet L-functions in the half-plane `0 < Re s`
away from `s = 1` when `χ = 1`. -/
lemma completedLFunction_star_conj_of_zero_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs_re : 0 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.completedLFunction (star χ) (conj s) =
      conj (DirichletCharacter.completedLFunction χ s) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs_re
  have hconj_re : 0 < (conj s).re := by simpa using hs_re
  have hconj0 : conj s ≠ 0 := fun h ↦ by simp [h] at hconj_re
  rw [completedLFunction_eq_mul_gammaFactor (star χ) (Or.inl hconj0)
        (gammaFactor_ne_zero_of_re_pos (star χ) hconj_re),
    completedLFunction_eq_mul_gammaFactor χ (Or.inl hs0)
        (gammaFactor_ne_zero_of_re_pos χ hs_re),
    map_mul, LFunction_star_conj_of_ne_one χ hχs, gammaFactor_star_conj]

/-- Conjugation symmetry of completed Dirichlet L-functions for non-principal characters on all
of `ℂ`. -/
theorem completedLFunction_star_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction (star χ) (conj s) =
      conj (DirichletCharacter.completedLFunction χ s) := by
  have hf : Differentiable ℂ
      (fun z ↦ conj (DirichletCharacter.completedLFunction (star χ) (conj z))) :=
    fun z ↦ differentiableAt_conj_conj_iff.mpr
      ((differentiable_completedLFunction_of_ne_one (star_ne_one_of_ne_one hχ)) (conj z))
  have hg : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction_of_ne_one hχ
  have heqOn : Set.EqOn
      (fun z ↦ conj (DirichletCharacter.completedLFunction (star χ) (conj z)))
      (DirichletCharacter.completedLFunction χ) Set.univ := by
    refine (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (z₀ := (2 : ℂ))
      (Set.mem_univ _) ?_
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [completedLFunction_star_conj_of_zero_lt_re χ hz (Or.inl hχ), Complex.conj_conj]
  simpa using congrArg conj (heqOn (Set.mem_univ s))

/-- In the right half-plane `0 < Re s`, `LFunction χ s = 0` iff `completedLFunction χ s = 0`. -/
lemma LFunction_eq_zero_iff_completedLFunction_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔ DirichletCharacter.completedLFunction χ s = 0 := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  exact div_eq_zero_iff.trans (or_iff_left (gammaFactor_ne_zero_of_re_pos χ hs))

/-- For a primitive character `χ` of modulus `q ≥ 2`, `completedLFunction χ` does not vanish
in the closed left half-plane `Re s ≤ 0`. -/
lemma completedLFunction_ne_zero_of_re_nonpos_of_isPrimitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hfeq := completedLFunction_one_sub_primitive hχ (1 - s)
  have h1s : 1 - (1 - s) = s := by ring
  rw [h1s] at hfeq
  rw [hfeq]
  have hre : 1 ≤ (1 - s).re := by simp; linarith
  have hstar_ne : star χ ≠ 1 := star_ne_one_of_ne_one (isPrimitive_ne_one hχ hq)
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  · exact DirichletCharacter.rootNumber_ne_zero hχ
  · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re (star χ)
      (Or.inl hstar_ne) hre

/-- Characterization of zeros of `completedLFunction χ` for primitive `χ` of modulus `q ≥ 2`:
every zero lies strictly inside the critical strip `0 < Re ρ < 1` and coincides with the zeros
of `LFunction χ` there. -/
theorem completedLFunction_eq_zero_iff_criticalStrip {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (ρ : ℂ) :
    DirichletCharacter.completedLFunction χ ρ = 0 ↔ ρ ∈ CriticalStripZerosL χ := by
  constructor
  · intro h0
    have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
    have hre_pos : 0 < ρ.re := by
      by_contra hle
      exact completedLFunction_ne_zero_of_re_nonpos_of_isPrimitive hχ hq (not_lt.mp hle) h0
    have hre_lt : ρ.re < 1 := by
      by_contra hge
      exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ
        (Or.inl hχ_ne) (not_lt.mp hge) h0
    exact ⟨hre_pos, hre_lt, (LFunction_eq_zero_iff_completedLFunction_eq_zero χ hre_pos).mpr h0⟩
  · rintro ⟨hpos, _, hL⟩
    exact (LFunction_eq_zero_iff_completedLFunction_eq_zero χ hpos).mp hL

/-- Helper: `analyticOrderNatAt` is invariant under the Schwarz reflection `w ↦ conj (f (conj w))`
whenever `f` is analytic at `conj z₀`. -/
lemma analyticOrderNatAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f (conj z₀)) :
    analyticOrderNatAt (fun w ↦ conj (f (conj w))) z₀ = analyticOrderNatAt f (conj z₀) := by
  have hF_analytic : AnalyticAt ℂ (fun w ↦ conj (f (conj w))) z₀ := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hf_ev := analyticAt_iff_eventually_differentiableAt.mp hf
    have hten : Tendsto (conj : ℂ → ℂ) (𝓝 z₀) (𝓝 (conj z₀)) :=
      Complex.continuous_conj.continuousAt.tendsto
    filter_upwards [hten hf_ev] with w hw
    exact differentiableAt_conj_conj_iff.mpr hw
  by_cases htop : analyticOrderAt f (conj z₀) = ⊤
  · have hzero : f =ᶠ[𝓝 (conj z₀)] 0 := analyticOrderAt_eq_top.mp htop
    have hF_zero : (fun w ↦ conj (f (conj w))) =ᶠ[𝓝 z₀] 0 := by
      have hten : Tendsto (conj : ℂ → ℂ) (𝓝 z₀) (𝓝 (conj z₀)) :=
        Complex.continuous_conj.continuousAt.tendsto
      filter_upwards [hten hzero] with w hw
      have hw0 : f (conj w) = 0 := hw
      simp [hw0]
    have hF_top : analyticOrderAt (fun w ↦ conj (f (conj w))) z₀ = ⊤ :=
      analyticOrderAt_eq_top.mpr hF_zero
    simp [analyticOrderNatAt, htop, hF_top]
  · obtain ⟨g, hg_ana, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
    let h : ℂ → ℂ := fun w ↦ conj (g (conj w))
    have hh_ana : AnalyticAt ℂ h z₀ := by
      rw [analyticAt_iff_eventually_differentiableAt]
      have hg_ev := analyticAt_iff_eventually_differentiableAt.mp hg_ana
      have hten : Tendsto (conj : ℂ → ℂ) (𝓝 z₀) (𝓝 (conj z₀)) :=
        Complex.continuous_conj.continuousAt.tendsto
      filter_upwards [hten hg_ev] with w hw
      exact differentiableAt_conj_conj_iff.mpr hw
    have hh0 : h z₀ ≠ 0 := by simp [h, hg0]
    have hF_eq : (fun w ↦ conj (f (conj w))) =ᶠ[𝓝 z₀]
        fun w ↦ (w - z₀) ^ analyticOrderNatAt f (conj z₀) • h w := by
      have hten : Tendsto (conj : ℂ → ℂ) (𝓝 z₀) (𝓝 (conj z₀)) :=
        Complex.continuous_conj.continuousAt.tendsto
      filter_upwards [hten hfg] with w hw
      have hconj := congrArg conj hw
      simpa [h, smul_eq_mul, map_mul, map_pow, map_sub] using hconj
    have hF_top : analyticOrderAt (fun w ↦ conj (f (conj w))) z₀ ≠ ⊤ := by
      intro hF_top'
      have hF_zero : (fun w ↦ conj (f (conj w))) =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp hF_top'
      have hten : Tendsto (conj : ℂ → ℂ) (𝓝 (conj z₀)) (𝓝 z₀) := by
        simpa using (Complex.continuous_conj.continuousAt (x := conj z₀)).tendsto
      have hf_zero : f =ᶠ[𝓝 (conj z₀)] 0 := by
        filter_upwards [hten hF_zero] with z hz
        have hz0 : conj (f (conj (conj z))) = 0 := hz
        simpa using congrArg conj hz0
      exact htop (analyticOrderAt_eq_top.mpr hf_zero)
    exact (hF_analytic.analyticOrderNatAt_eq_iff hF_top).mpr ⟨h, hh_ana, hh0, hF_eq⟩

/-- Conjugation symmetry preserves analytic zero multiplicity of `LFunction`:
`analyticOrderNatAt (LFunction (star χ)) (conj ρ) = analyticOrderNatAt (LFunction χ) ρ`. -/
theorem analyticOrderNatAt_LFunction_star_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {ρ : ℂ} (hχρ : χ ≠ 1 ∨ ρ ≠ 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction (star χ)) (conj ρ) =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  have hana : AnalyticAt ℂ (DirichletCharacter.LFunction (star χ)) (conj ρ) := by
    have hne : star χ ≠ 1 ∨ conj ρ ≠ 1 := by
      rcases hχρ with h | h
      · exact Or.inl (star_ne_one_of_ne_one h)
      · exact Or.inr fun hc ↦ h (by simpa using congrArg conj hc)
    have hopen : IsOpen {z : ℂ | star χ ≠ 1 ∨ z ≠ 1} := by
      by_cases hs : star χ = 1
      · simp [hs, isOpen_ne]
      · simp [hs]
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction (star χ))
        {z : ℂ | star χ ≠ 1 ∨ z ≠ 1} :=
      fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction (star χ) z hz.symm).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hne)
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ]
      fun w ↦ conj (DirichletCharacter.LFunction (star χ) (conj w)) := by
    have hopen : IsOpen {z : ℂ | χ ≠ 1 ∨ z ≠ 1} := by
      by_cases h : χ = 1
      · simp [h, isOpen_ne]
      · simp [h]
    filter_upwards [hopen.mem_nhds hχρ] with w hw
    rw [LFunction_star_conj_of_ne_one χ hw, Complex.conj_conj]
  rw [show analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (fun w ↦ conj (DirichletCharacter.LFunction (star χ) (conj w))) ρ from
    congrArg ENat.toNat (analyticOrderAt_congr hev)]
  exact (analyticOrderNatAt_conj_conj hana).symm

/-- Conjugation symmetry preserves analytic zero multiplicity of `completedLFunction` for `χ ≠ 1`. -/
theorem analyticOrderNatAt_completedLFunction_star_conj {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction (star χ)) (conj ρ) =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hana : AnalyticAt ℂ (DirichletCharacter.completedLFunction (star χ)) (conj ρ) :=
    (differentiable_completedLFunction_of_ne_one (star_ne_one_of_ne_one hχ)).analyticAt (conj ρ)
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 ρ]
      fun w ↦ conj (DirichletCharacter.completedLFunction (star χ) (conj w)) :=
    Eventually.of_forall fun w ↦ by
      dsimp only
      rw [completedLFunction_star_conj hχ w, Complex.conj_conj]
  rw [show analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ =
      analyticOrderNatAt
        (fun w ↦ conj (DirichletCharacter.completedLFunction (star χ) (conj w))) ρ from
    congrArg ENat.toNat (analyticOrderAt_congr hev)]
  exact (analyticOrderNatAt_conj_conj hana).symm

private lemma analyticOrderAt_completedLFunction_ne_top {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
  intro htop
  have hzero : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 ρ] 0 :=
    analyticOrderAt_eq_top.mp htop
  have hd : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction_of_ne_one hχ
  have heq : Set.EqOn (DirichletCharacter.completedLFunction χ) 0 Set.univ :=
    (hd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_univ (z₀ := ρ) (Set.mem_univ ρ) hzero
  have h2 : DirichletCharacter.completedLFunction χ 2 = 0 := heq (Set.mem_univ 2)
  exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
    (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2

/-- Functional-equation reflection `ρ ↦ 1 - ρ` preserves analytic zero multiplicity between
`completedLFunction χ` and `completedLFunction (star χ)` for primitive `χ` of modulus `q ≥ 2`. -/
theorem analyticOrderNatAt_completedLFunction_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (ρ : ℂ) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (1 - ρ) =
      analyticOrderNatAt (DirichletCharacter.completedLFunction (star χ)) ρ := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hstar_ne : star χ ≠ 1 := star_ne_one_of_ne_one hχ_ne
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) ρ :=
    (differentiable_const (1 : ℂ) |>.sub differentiable_id).analyticAt ρ
  have hg' : deriv (fun s : ℂ ↦ 1 - s) ρ ≠ 0 := by
    have hd : HasDerivAt (fun s : ℂ ↦ 1 - s) (-1) ρ := (hasDerivAt_id ρ).const_sub (1 : ℂ)
    rw [hd.deriv]
    norm_num
  have hcomp := congrArg ENat.toNat
    (analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.completedLFunction χ) hg hg')
  change analyticOrderNatAt (fun s ↦ DirichletCharacter.completedLFunction χ (1 - s)) ρ =
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (1 - ρ) at hcomp
  rw [← hcomp]
  have hfeq : (fun s : ℂ ↦ DirichletCharacter.completedLFunction χ (1 - s)) =
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction (star χ) := by
    ext s
    simpa [one_div] using completedLFunction_one_sub_primitive hχ s
  rw [hfeq]
  have hpref_diff : Differentiable ℂ
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) := by
    intro s
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    exact ((differentiableAt_id.sub (differentiableAt_const _)).const_cpow
      (Or.inl hq0)).mul (differentiableAt_const _)
  have hpref_ne : (q : ℂ) ^ (ρ - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
      (DirichletCharacter.rootNumber_ne_zero hχ)
  have hpref_ana : AnalyticAt ℂ
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) ρ :=
    hpref_diff.analyticAt ρ
  have hpref_ord0 : analyticOrderAt
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hpref_ne)
  have hpref_top : analyticOrderAt
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) ρ ≠ ⊤ := by
    rw [hpref_ord0]
    exact WithTop.zero_ne_top
  have hstar_ana : AnalyticAt ℂ (DirichletCharacter.completedLFunction (star χ)) ρ :=
    (differentiable_completedLFunction_of_ne_one hstar_ne).analyticAt ρ
  have hstar_top : analyticOrderAt (DirichletCharacter.completedLFunction (star χ)) ρ ≠ ⊤ :=
    analyticOrderAt_completedLFunction_ne_top hstar_ne ρ
  rw [analyticOrderNatAt_mul hpref_ana hstar_ana hpref_top hstar_top]
  have hord0 : analyticOrderNatAt
      (fun s : ℂ ↦ (q : ℂ) ^ (s - (2 : ℂ)⁻¹) * DirichletCharacter.rootNumber χ) ρ = 0 := by
    simp [analyticOrderNatAt, hpref_ord0]
  rw [hord0, zero_add]

/-- Critical-strip symmetry `ρ ↦ 1 - conj ρ` preserves the analytic multiplicity of
`completedLFunction χ` for a primitive character `χ` of modulus `q ≥ 2`. -/
theorem analyticOrderNatAt_completedLFunction_one_sub_conj {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (ρ : ℂ) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (1 - conj ρ) =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  rw [analyticOrderNatAt_completedLFunction_one_sub hχ hq (conj ρ)]
  exact analyticOrderNatAt_completedLFunction_star_conj hχ_ne ρ

/-- In the right half-plane `0 < Re ρ`, `LFunction χ` and `completedLFunction χ` have the exact
same analytic zero multiplicity (when `χ ≠ 1 ∨ ρ ≠ 1`). -/
lemma analyticOrderNatAt_LFunction_eq_completedLFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hre : 0 < ρ.re) (hχρ : χ ≠ 1 ∨ ρ ≠ 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hopen_re : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen_ne : IsOpen {z : ℂ | χ ≠ 1 ∨ z ≠ 1} := by
    by_cases h : χ = 1 <;> simp [h, isOpen_ne]
  have hL_ana : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {z : ℂ | χ ≠ 1 ∨ z ≠ 1} :=
      fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z hz.symm).differentiableWithinAt
    exact hd.analyticAt (hopen_ne.mem_nhds hχρ)
  have hG_ana : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) ρ := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.gammaFactor χ) {z : ℂ | 0 < z.re} := by
      intro z hz
      have hre2 : 0 < ((z + (parityExp χ : ℂ)) / 2).re := by
        have : ((z + (parityExp χ : ℂ)) / 2).re = (z.re + (parityExp χ : ℝ)) / 2 := by
          simp [Complex.add_re, Complex.natCast_re]
        rw [this]
        have hzre : 0 < z.re := hz
        positivity
      have hdiff1 : DifferentiableAt ℂ
          (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2)) z := by
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact (((differentiableAt_id.add (differentiableAt_const _)).neg.div_const 2).const_cpow
          (Or.inl hpi))
      have hdiff2 : DifferentiableAt ℂ
          (fun w : ℂ ↦ Complex.Gamma ((w + (parityExp χ : ℂ)) / 2)) z :=
        (Complex.differentiableAt_Gamma _ (fun m hm ↦ by
          have := hre2
          rw [hm] at this
          simp at this
          linarith)).comp z ((differentiableAt_id.add (differentiableAt_const _)).div_const 2)
      have heq : DirichletCharacter.gammaFactor χ =
          fun w ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2) *
            Complex.Gamma ((w + (parityExp χ : ℂ)) / 2) := by
        ext w; exact gammaFactor_eq_pi_mul_Gamma χ w
      rw [heq]
      exact (hdiff1.mul hdiff2).differentiableWithinAt
    exact hd.analyticAt (hopen_re.mem_nhds hre)
  have hL_top : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hzero : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp htop
    rcases hχρ with hχ | hρ1
    · have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
        differentiable_LFunction_of_ne_one hχ
      have heq : Set.EqOn (DirichletCharacter.LFunction χ) 0 Set.univ :=
        (hd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
          analyticOnNhd_const isPreconnected_univ (z₀ := ρ) (Set.mem_univ ρ) hzero
      have h2 : DirichletCharacter.LFunction χ 2 = 0 := heq (Set.mem_univ 2)
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
        (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2
    · by_cases hχ : χ = 1
      · have hzero1 : DirichletCharacter.LFunctionTrivChar₁ q =ᶠ[𝓝 ρ] 0 := by
          filter_upwards [isOpen_ne.mem_nhds hρ1, hzero] with z hz1 hz0
          have hz0' : DirichletCharacter.LFunction χ z = 0 := hz0
          have htriv : DirichletCharacter.LFunctionTrivChar q z = 0 := by
            simpa [DirichletCharacter.LFunctionTrivChar, hχ] using hz0'
          rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1, htriv, mul_zero]
          rfl
        have hd1 := DirichletCharacter.differentiable_LFunctionTrivChar₁ q
        have heq1 : Set.EqOn (DirichletCharacter.LFunctionTrivChar₁ q) 0 Set.univ :=
          (hd1.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
            analyticOnNhd_const isPreconnected_univ (z₀ := ρ) (Set.mem_univ ρ) hzero1
        have h1 : DirichletCharacter.LFunctionTrivChar₁ q 1 = 0 := heq1 (Set.mem_univ 1)
        exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q h1
      · have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
          differentiable_LFunction_of_ne_one hχ
        have heq : Set.EqOn (DirichletCharacter.LFunction χ) 0 Set.univ :=
          (hd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
            analyticOnNhd_const isPreconnected_univ (z₀ := ρ) (Set.mem_univ ρ) hzero
        have h2 : DirichletCharacter.LFunction χ 2 = 0 := heq (Set.mem_univ 2)
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
          (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2
  have hG_ord0 : analyticOrderAt (DirichletCharacter.gammaFactor χ) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (gammaFactor_ne_zero_of_re_pos χ hre))
  have hG_top : analyticOrderAt (DirichletCharacter.gammaFactor χ) ρ ≠ ⊤ := by
    rw [hG_ord0]
    exact WithTop.zero_ne_top
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 ρ]
      DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ := by
    filter_upwards [hopen_re.mem_nhds hre] with z hz
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
    exact completedLFunction_eq_mul_gammaFactor χ (Or.inl hz0)
      (gammaFactor_ne_zero_of_re_pos χ hz)
  have heq_nat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ) ρ :=
    congrArg ENat.toNat (analyticOrderAt_congr hev)
  rw [heq_nat, analyticOrderNatAt_mul hL_ana hG_ana hL_top hG_top]
  have hG_nat0 : analyticOrderNatAt (DirichletCharacter.gammaFactor χ) ρ = 0 := by
    simp [analyticOrderNatAt, hG_ord0]
  rw [hG_nat0, add_zero]

/-- On the critical strip `0 < Re ρ < 1`, the symmetry `ρ ↦ 1 - conj ρ` preserves
`CriticalStripZerosL χ` membership for primitive `χ` (`q ≥ 2`). -/
theorem criticalStripZerosL_one_sub_conj_iff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (ρ : ℂ) :
    1 - conj ρ ∈ CriticalStripZerosL χ ↔ ρ ∈ CriticalStripZerosL χ := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  simp only [← completedLFunction_eq_zero_iff_criticalStrip hχ hq]
  constructor
  · intro h
    have hfeq := completedLFunction_one_sub_primitive hχ (conj ρ)
    rw [h, completedLFunction_star_conj hχ_ne ρ] at hfeq
    have hq0 : (q : ℂ) ^ (conj ρ - 1 / 2) * DirichletCharacter.rootNumber χ ≠ 0 :=
      mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
        (DirichletCharacter.rootNumber_ne_zero hχ)
    have hc0 : conj (DirichletCharacter.completedLFunction χ ρ) = 0 :=
      (mul_eq_zero.mp hfeq.symm).resolve_left hq0
    exact (map_eq_zero (starRingEnd ℂ)).mp hc0
  · intro h
    rw [completedLFunction_one_sub_primitive hχ (conj ρ), completedLFunction_star_conj hχ_ne ρ,
      h, map_zero, mul_zero]

/-- Multiplicity symmetry `analyticOrderNatAt (LFunction χ) (1 - conj ρ) = analyticOrderNatAt (LFunction χ) ρ`
for `0 < Re ρ < 1` and primitive `χ` (`q ≥ 2`). -/
theorem analyticOrderNatAt_LFunction_one_sub_conj {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) (1 - conj ρ) =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hre0' : 0 < (1 - conj ρ).re := by simp; linarith
  rw [analyticOrderNatAt_LFunction_eq_completedLFunction χ hre0' (Or.inl hχ_ne),
    analyticOrderNatAt_LFunction_eq_completedLFunction χ hre0 (Or.inl hχ_ne)]
  exact analyticOrderNatAt_completedLFunction_one_sub_conj hχ hq ρ

/-- Critical-strip functional-equation symmetry `ρ ↦ 1 - ρ` between `χ` and `star χ`. -/
theorem criticalStripZerosL_one_sub_iff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (ρ : ℂ) :
    1 - ρ ∈ CriticalStripZerosL χ ↔ ρ ∈ CriticalStripZerosL (star χ) := by
  have hstar : (star χ).IsPrimitive := isPrimitive_star hχ
  rw [← completedLFunction_eq_zero_iff_criticalStrip hχ hq,
    ← completedLFunction_eq_zero_iff_criticalStrip hstar hq,
    completedLFunction_one_sub_primitive hχ ρ]
  have hpref : (q : ℂ) ^ (ρ - 1 / 2) * DirichletCharacter.rootNumber χ ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
      (DirichletCharacter.rootNumber_ne_zero hχ)
  exact mul_eq_zero.trans (or_iff_right hpref)

/-- Multiplicity symmetry `ρ ↦ 1 - ρ` on `LFunction` inside `0 < Re ρ < 1` for primitive `χ` (`q ≥ 2`). -/
theorem analyticOrderNatAt_LFunction_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) (1 - ρ) =
      analyticOrderNatAt (DirichletCharacter.LFunction (star χ)) ρ := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hstar_ne : star χ ≠ 1 := star_ne_one_of_ne_one hχ_ne
  have hre0' : 0 < (1 - ρ).re := by simp; linarith
  rw [analyticOrderNatAt_LFunction_eq_completedLFunction χ hre0' (Or.inl hχ_ne),
    analyticOrderNatAt_LFunction_eq_completedLFunction (star χ) hre0 (Or.inl hstar_ne)]
  exact analyticOrderNatAt_completedLFunction_one_sub hχ hq ρ

/-- Critical-strip conjugation symmetry `ρ ↦ conj ρ` between `χ` and `star χ`. -/
theorem criticalStripZerosL_star_conj_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    conj ρ ∈ CriticalStripZerosL (star χ) ↔ ρ ∈ CriticalStripZerosL χ := by
  simp only [CriticalStripZerosL, Set.mem_ofPred_eq, Complex.conj_re]
  refine and_congr_right fun _ ↦ and_congr_right fun hre1 ↦ ?_
  have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hre1
  rw [LFunction_star_conj_of_ne_one χ (Or.inr hne1), (map_eq_zero (starRingEnd ℂ))]

end CriticalStripAndSymmetry

section EntirenessAndOrder

/-- Uniform upper bound `‖LFunction χ w‖ ≤ Real.pi ^ 2 / 6` in the half-plane `2 ≤ Re w`. -/
lemma norm_LFunction_le_pi_sq_div_six {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {w : ℂ} (hw : 2 ≤ w.re) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ Real.pi ^ 2 / 6 := by
  have hw1 : 1 < w.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hw1]
  have hle : ∀ n : ℕ, ‖LSeries.term (fun n ↦ χ n) w n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    cases n with
    | zero => simp [LSeries.term]
    | succ k =>
      have hk_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
      have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos k
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), Nat.succ_eq_add_one]
      have hχ_norm : ‖χ ((k + 1 : ℕ) : ZMod q)‖ ≤ 1 := norm_char_le_one χ _
      have hrpow : (k + 1 : ℝ) ^ (2 : ℝ) ≤ (k + 1 : ℝ) ^ w.re :=
        Real.rpow_le_rpow_of_exponent_le hk1 hw
      calc ‖χ ((k + 1 : ℕ) : ZMod q)‖ / ((k + 1 : ℕ) : ℝ) ^ w.re
          ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ w.re := div_le_div_of_nonneg_right hχ_norm (by positivity)
        _ ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
            refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
            simpa using hrpow
        _ = (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by norm_cast
  have hsum_norm : Summable (fun n : ℕ ↦ ‖LSeries.term (fun n ↦ χ n) w n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hasSum_zeta_two.summable
  calc ‖∑' n : ℕ, LSeries.term (fun n ↦ χ n) w n‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n ↦ χ n) w n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
        hsum_norm.tsum_le_tsum hle hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

/-- Uniform upper bound `‖LFunction χ w‖ ≤ 2` in the half-plane `2 ≤ Re w`. -/
lemma norm_LFunction_le_two_of_two_le_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {w : ℂ} (hw : 2 ≤ w.re) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  exact (norm_LFunction_le_pi_sq_div_six χ hw).trans (by nlinarith)

private lemma complex_gamma_add_nat (u : ℂ) (hu : 0 < u.re) :
    ∀ k : ℕ, Complex.Gamma (u + k) = (∏ j ∈ Finset.range k, (u + j)) * Complex.Gamma u
  | 0 => by simp
  | k + 1 => by
    have hne : u + (k : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne,
      complex_gamma_add_nat u hu k, Finset.prod_range_succ]
    ring

private lemma exists_gamma_right_half_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, 1 / 4 ≤ z.re → ‖Complex.Gamma z‖ ≤ M * Real.exp (11 * ‖z‖ * Real.log (‖z‖ + 2)) := by
  let K : Set ℂ := {u : ℂ | u.re ∈ Icc (1 / 4 : ℝ) (5 / 4) ∧ u.im ∈ Icc (-1 : ℝ) 1}
  have hK_closed : IsClosed K := by
    have h1 : IsClosed {u : ℂ | u.re ∈ Icc (1 / 4 : ℝ) (5 / 4)} :=
      isClosed_Icc.preimage Complex.continuous_re
    have h2 : IsClosed {u : ℂ | u.im ∈ Icc (-1 : ℝ) 1} :=
      isClosed_Icc.preimage Complex.continuous_im
    exact h1.inter h2
  have hK_sub : K ⊆ Metric.closedBall (0 : ℂ) 3 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |u.re| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
    have him : |u.im| ≤ 1 := abs_le.mpr hu.2
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ 2 + 1 := add_le_add hre him
      _ = 3 := by norm_num
  have hK_cpt : IsCompact K := (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset hK_closed hK_sub
  have hK_cont : ContinuousOn Complex.Gamma K := by
    intro u hu
    refine (Complex.differentiableAt_Gamma u fun m hm ↦ ?_).continuousAt.continuousWithinAt
    have hre := congrArg Complex.re hm
    simp at hre
    linarith [hu.1.1]
  obtain ⟨M₀, hM₀⟩ := hK_cpt.exists_bound_of_continuousOn hK_cont
  obtain ⟨c_s, C_s, hc0, hcC, hstrip⟩ := norm_complex_gamma_strip_bounds (1 / 4) (5 / 4)
  let M : ℝ := max (max M₀ C_s) 1
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_right _ _)
  have hM_strip : ∀ u : ℂ, u.re ∈ Icc (1 / 4 : ℝ) (5 / 4) → ‖Complex.Gamma u‖ ≤ M * (‖u‖ + 1) := by
    intro u hu
    by_cases him : 1 ≤ |u.im|
    · have hbd := (hstrip (σ := u.re) (t := u.im) hu him).2
      have hre_im : (u.re : ℂ) + (u.im : ℂ) * I = u := Complex.re_add_im u
      rw [hre_im] at hbd
      have hexp : Real.exp (-(Real.pi / 2) * |u.im|) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (abs_nonneg _))
      have hrpow : |u.im| ^ (u.re - 1 / 2) ≤ ‖u‖ + 1 := by
        have h1 : |u.im| ^ (u.re - 1 / 2) ≤ |u.im| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le him (by linarith [hu.2])
        rw [Real.rpow_one] at h1
        exact h1.trans ((Complex.abs_im_le_norm u).trans (by linarith))
      have hC_pos : 0 ≤ C_s := hc0.le.trans hcC
      have hCM : C_s ≤ M := le_trans (le_max_right M₀ C_s) (le_max_left _ 1)
      calc ‖Complex.Gamma u‖
          ≤ C_s * Real.exp (-(Real.pi / 2) * |u.im|) * |u.im| ^ (u.re - 1 / 2) := hbd
        _ ≤ C_s * 1 * (‖u‖ + 1) := by gcongr
        _ = C_s * (‖u‖ + 1) := by ring
        _ ≤ M * (‖u‖ + 1) := mul_le_mul_of_nonneg_right hCM (by positivity)
    · have him' : u.im ∈ Icc (-1 : ℝ) 1 := abs_le.mp (not_le.mp him).le
      have hMM : M₀ ≤ M := le_trans (le_max_left M₀ C_s) (le_max_left _ 1)
      have h1 : 1 ≤ ‖u‖ + 1 := by linarith [norm_nonneg u]
      calc ‖Complex.Gamma u‖ ≤ M₀ := hM₀ u ⟨hu, him'⟩
        _ ≤ M := hMM
        _ = M * 1 := (mul_one M).symm
        _ ≤ M * (‖u‖ + 1) := mul_le_mul_of_nonneg_left h1 hM0
  refine ⟨M, hM0, fun z hz ↦ ?_⟩
  let k : ℕ := Nat.floor (z.re - 1 / 4)
  let u : ℂ := z - (k : ℂ)
  have hu_re : u.re ∈ Icc (1 / 4 : ℝ) (5 / 4) := by
    have hk_le : (k : ℝ) ≤ z.re - 1 / 4 := Nat.floor_le (by linarith)
    have hlt_k : z.re - 1 / 4 < (k : ℝ) + 1 := Nat.lt_floor_add_one (z.re - 1 / 4)
    have hre_eq : u.re = z.re - (k : ℝ) := by simp [u]
    exact ⟨by linarith, by linarith⟩
  have hu_pos : 0 < u.re := by linarith [hu_re.1]
  have hzk : z = u + (k : ℂ) := by simp [u]
  have hnorm_le : ∀ j : ℕ, j ≤ k → ‖u + (j : ℂ)‖ ≤ ‖z‖ := by
    intro j hj
    have hj_re : 0 ≤ (u + (j : ℂ)).re := by
      have : (u + (j : ℂ)).re = u.re + j := by simp
      linarith [hu_pos]
    have hj_le_re : (u + (j : ℂ)).re ≤ z.re := by
      have h1 : (u + (j : ℂ)).re = z.re - (k : ℝ) + (j : ℝ) := by simp [u]
      have hjr : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
      linarith
    have hj_im : (u + (j : ℂ)).im = z.im := by simp [u]
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq, hj_im]
    exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq' (by linarith) hj_le_re) le_rfl)
  have hu_norm : ‖u‖ ≤ ‖z‖ := by
    simpa using hnorm_le 0 (Nat.zero_le k)
  have hgamma := complex_gamma_add_nat u hu_pos k
  rw [← hzk] at hgamma
  have hprod_norm : ‖∏ j ∈ Finset.range k, (u + (j : ℂ))‖ ≤ ‖z‖ ^ k := by
    rw [norm_prod]
    calc ∏ j ∈ Finset.range k, ‖u + (j : ℂ)‖
        ≤ ∏ _j ∈ Finset.range k, ‖z‖ := by
          gcongr with j hj
          exact hnorm_le j (Finset.mem_range.mp hj).le
      _ = ‖z‖ ^ k := by simp
  have hz_norm_ge : 1 / 4 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hlog2 : 1 / 2 ≤ Real.log (‖z‖ + 2) := by
    have h2 : (2 : ℝ) ≤ ‖z‖ + 2 := by linarith [norm_nonneg z]
    have hlt : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact hlt.le.trans (Real.log_le_log (by norm_num) h2)
  have hk_le_norm : (k : ℝ) ≤ ‖z‖ := by
    have hk1 : (k : ℝ) ≤ z.re - 1 / 4 := Nat.floor_le (by linarith)
    exact hk1.trans (by linarith [Complex.re_le_norm z])
  have hpow_le : ‖z‖ ^ k ≤ Real.exp (‖z‖ * Real.log (‖z‖ + 2)) := by
    have hz_add : ‖z‖ ≤ ‖z‖ + 2 := by linarith
    have hz_add1 : 1 ≤ ‖z‖ + 2 := by linarith [norm_nonneg z]
    calc ‖z‖ ^ k ≤ (‖z‖ + 2) ^ k := pow_le_pow_left₀ (norm_nonneg z) hz_add k
      _ = (‖z‖ + 2) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
      _ ≤ (‖z‖ + 2) ^ ‖z‖ := Real.rpow_le_rpow_of_exponent_le hz_add1 hk_le_norm
      _ = Real.exp (Real.log (‖z‖ + 2) * ‖z‖) := Real.rpow_def_of_pos (by linarith [norm_nonneg z]) _
      _ = Real.exp (‖z‖ * Real.log (‖z‖ + 2)) := by ring_nf
  have hlin_le : ‖z‖ + 1 ≤ Real.exp (10 * ‖z‖ * Real.log (‖z‖ + 2)) := by
    have h1 : ‖z‖ + 1 ≤ 5 * ‖z‖ := by linarith
    have h2 : 5 * ‖z‖ ≤ 10 * ‖z‖ * Real.log (‖z‖ + 2) := by
      calc 5 * ‖z‖ = 10 * ‖z‖ * (1 / 2) := by ring
        _ ≤ 10 * ‖z‖ * Real.log (‖z‖ + 2) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have h3 : 10 * ‖z‖ * Real.log (‖z‖ + 2) ≤ Real.exp (10 * ‖z‖ * Real.log (‖z‖ + 2)) := by
      linarith [Real.add_one_le_exp (10 * ‖z‖ * Real.log (‖z‖ + 2))]
    linarith
  calc ‖Complex.Gamma z‖
      = ‖∏ j ∈ Finset.range k, (u + (j : ℂ))‖ * ‖Complex.Gamma u‖ := by
        rw [hgamma, norm_mul]
    _ ≤ ‖z‖ ^ k * (M * (‖u‖ + 1)) := by
        gcongr
        exact hM_strip u hu_re
    _ ≤ ‖z‖ ^ k * (M * (‖z‖ + 1)) := by gcongr
    _ = M * (‖z‖ ^ k * (‖z‖ + 1)) := by ring
    _ ≤ M * (Real.exp (‖z‖ * Real.log (‖z‖ + 2)) *
          Real.exp (10 * ‖z‖ * Real.log (‖z‖ + 2))) := by
        gcongr
    _ = M * Real.exp (11 * ‖z‖ * Real.log (‖z‖ + 2)) := by
        rw [← Real.exp_add]
        congr 2
        ring

private lemma norm_completedLFunction_half_re_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ_ne : χ ≠ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → 2 ≤ ‖w‖ →
      ‖DirichletCharacter.completedLFunction χ w‖ ≤
        C * Real.exp (D * ‖w‖ * Real.log (‖w‖ + 2)) := by
  obtain ⟨M, hM0, hgamma⟩ := exists_gamma_right_half_bound
  let κ : ℝ := parityExp χ
  have hκ0 : 0 ≤ κ := Nat.cast_nonneg _
  let C : ℝ := 4 * (q + 48 * (q : ℝ) ^ 2 + 2) * M
  let D : ℝ := 2 + 11 * (1 + κ / 2) * (Real.log (κ + 2) + 1)
  have hC0 : 0 ≤ C := by positivity
  have hD0 : 0 ≤ D := by
    have : 0 ≤ Real.log (κ + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨C, D, hC0, hD0, fun w hw hw2 ↦ ?_⟩
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw2; norm_num at hw2
  have hw_re_pos : 0 < w.re := by linarith
  have hcomp : DirichletCharacter.completedLFunction χ w =
      DirichletCharacter.LFunction χ w *
        ((Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2) *
          Complex.Gamma ((w + (parityExp χ : ℂ)) / 2)) := by
    rw [completedLFunction_eq_mul_gammaFactor χ (Or.inl hw0)
      (gammaFactor_ne_zero_of_re_pos χ hw_re_pos), gammaFactor_eq_pi_mul_Gamma]
  rw [hcomp, norm_mul, norm_mul]
  have hlog4 : 1 ≤ Real.log (‖w‖ + 2) := by
    have h4 : (4 : ℝ) ≤ ‖w‖ + 2 := by linarith
    have h2 : 1 < 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hl4 : 1 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      simpa using h2
    exact hl4.le.trans (Real.log_le_log (by norm_num) h4)
  have hL_bd : ‖DirichletCharacter.LFunction χ w‖ ≤
      4 * (q + 48 * (q : ℝ) ^ 2 + 2) * Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2)) := by
    have hpoly : ‖DirichletCharacter.LFunction χ w‖ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (‖w‖ + 2) ^ 2 := by
      by_cases hw2_re : w.re ≤ 2
      · have hstrip := norm_LFunction_strip_poly_le hχ_ne (by linarith : -(1 / 2 : ℝ) ≤ w.re) hw2_re
        have him : |w.im| + 2 ≤ ‖w‖ + 2 := by linarith [Complex.abs_im_le_norm w]
        have hsq : (|w.im| + 2) ^ 2 ≤ (‖w‖ + 2) ^ 2 := pow_le_pow_left₀ (by positivity) him 2
        calc ‖DirichletCharacter.LFunction χ w‖
            ≤ (q + 48 * (q : ℝ) ^ 2) * (|w.im| + 2) ^ 2 := hstrip
          _ ≤ (q + 48 * (q : ℝ) ^ 2) * (‖w‖ + 2) ^ 2 := by gcongr
          _ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (‖w‖ + 2) ^ 2 := by
              refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · have h2le : 2 ≤ w.re := (not_le.mp hw2_re).le
        have hL2 := norm_LFunction_le_two_of_two_le_re χ h2le
        have hsq : (1 : ℝ) ≤ (‖w‖ + 2) ^ 2 := by nlinarith [norm_nonneg w]
        calc ‖DirichletCharacter.LFunction χ w‖ ≤ 2 := hL2
          _ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * 1 := by nlinarith
          _ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (‖w‖ + 2) ^ 2 := by gcongr
    have hsq_exp : (‖w‖ + 2) ^ 2 ≤ 4 * Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2)) := by
      have hw_add : ‖w‖ + 2 ≤ 2 * ‖w‖ := by linarith
      have hsq1 : (‖w‖ + 2) ^ 2 ≤ 4 * ‖w‖ ^ 2 := by
        calc (‖w‖ + 2) ^ 2 ≤ (2 * ‖w‖) ^ 2 := pow_le_pow_left₀ (by positivity) hw_add 2
          _ = 4 * ‖w‖ ^ 2 := by ring
      have hexp1 : ‖w‖ ≤ Real.exp ‖w‖ := by linarith [Real.add_one_le_exp ‖w‖]
      have hexp2 : ‖w‖ ^ 2 ≤ Real.exp (2 * ‖w‖) := by
        calc ‖w‖ ^ 2 ≤ (Real.exp ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hexp1 2
          _ = Real.exp (2 * ‖w‖) := by rw [← Real.exp_nat_mul]; norm_num
      have hexp3 : Real.exp (2 * ‖w‖) ≤ Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2)) := by
        refine Real.exp_le_exp.mpr ?_
        calc 2 * ‖w‖ = 2 * ‖w‖ * 1 := by ring
          _ ≤ 2 * ‖w‖ * Real.log (‖w‖ + 2) := mul_le_mul_of_nonneg_left hlog4 (by positivity)
      linarith
    calc ‖DirichletCharacter.LFunction χ w‖
        ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (‖w‖ + 2) ^ 2 := hpoly
      _ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (4 * Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2))) := by gcongr
      _ = 4 * (q + 48 * (q : ℝ) ^ 2 + 2) * Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2)) := by ring
  have hpi_bd : ‖(Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2)‖ ≤ 1 := by
    have hre : (-(w + (parityExp χ : ℂ)) / 2).re ≤ 0 := by
      have : (-(w + (parityExp χ : ℂ)) / 2).re = -(w.re + κ) / 2 := by
        simp [κ, Complex.add_re, Complex.natCast_re]
      rw [this]
      linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) hre
  let z : ℂ := (w + (parityExp χ : ℂ)) / 2
  have hz_re : 1 / 4 ≤ z.re := by
    have : z.re = (w.re + κ) / 2 := by simp [z, κ, Complex.add_re, Complex.natCast_re]
    rw [this]; linarith
  have hz_norm : ‖z‖ ≤ (1 + κ / 2) * ‖w‖ := by
    have h1 : ‖w + (parityExp χ : ℂ)‖ ≤ ‖w‖ + κ := by
      calc ‖w + (parityExp χ : ℂ)‖ ≤ ‖w‖ + ‖(parityExp χ : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ + κ := by simp [κ]
    have h2 : ‖z‖ = ‖w + (parityExp χ : ℂ)‖ / 2 := by simp [z]
    rw [h2]
    nlinarith
  have hz_log : Real.log (‖z‖ + 2) ≤ (Real.log (κ + 2) + 1) * Real.log (‖w‖ + 2) := by
    have h3 : ‖z‖ + 2 ≤ (κ + 2) * ‖w‖ := by nlinarith
    have h4 : Real.log (‖z‖ + 2) ≤ Real.log ((κ + 2) * ‖w‖) :=
      Real.log_le_log (by positivity) h3
    rw [Real.log_mul (by positivity) (by positivity)] at h4
    have h5 : Real.log ‖w‖ ≤ Real.log (‖w‖ + 2) := Real.log_le_log (by positivity) (by linarith)
    have h6 : Real.log (κ + 2) ≤ Real.log (κ + 2) * Real.log (‖w‖ + 2) := by
      have : 0 ≤ Real.log (κ + 2) := Real.log_nonneg (by linarith)
      nlinarith
    linarith
  have hgamma_bd : ‖Complex.Gamma z‖ ≤
      M * Real.exp ((11 * (1 + κ / 2) * (Real.log (κ + 2) + 1)) * ‖w‖ * Real.log (‖w‖ + 2)) := by
    refine (hgamma z hz_re).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM0
    calc 11 * ‖z‖ * Real.log (‖z‖ + 2)
        ≤ 11 * ((1 + κ / 2) * ‖w‖) * ((Real.log (κ + 2) + 1) * Real.log (‖w‖ + 2)) := by
          gcongr
          exact Real.log_nonneg (by linarith [norm_nonneg z])
      _ = (11 * (1 + κ / 2) * (Real.log (κ + 2) + 1)) * ‖w‖ * Real.log (‖w‖ + 2) := by ring
  calc ‖DirichletCharacter.LFunction χ w‖ *
        (‖(Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2)‖ * ‖Complex.Gamma z‖)
      ≤ (4 * (q + 48 * (q : ℝ) ^ 2 + 2) * Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2))) *
          (1 * (M * Real.exp ((11 * (1 + κ / 2) * (Real.log (κ + 2) + 1)) *
            ‖w‖ * Real.log (‖w‖ + 2)))) := by gcongr
    _ = C * (Real.exp (2 * ‖w‖ * Real.log (‖w‖ + 2)) *
          Real.exp ((11 * (1 + κ / 2) * (Real.log (κ + 2) + 1)) *
            ‖w‖ * Real.log (‖w‖ + 2))) := by
        simp only [C]; ring
    _ = C * Real.exp (D * ‖w‖ * Real.log (‖w‖ + 2)) := by
        rw [← Real.exp_add]
        congr 2
        simp only [D]
        ring

/-- Global `‖w‖ * log (‖w‖ + 2)` exponential growth bound for `completedLFunction χ` when `χ`
is primitive of modulus `q ≥ 2`. -/
theorem norm_completedLFunction_le_exp_norm_mul_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ w : ℂ, 3 ≤ ‖w‖ →
      ‖DirichletCharacter.completedLFunction χ w‖ ≤
        C * Real.exp (D * ‖w‖ * Real.log (‖w‖ + 2)) := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hstar_ne : star χ ≠ 1 := star_ne_one_of_ne_one hχ_ne
  obtain ⟨C₁, D₁, hC₁0, hD₁0, hbd₁⟩ := norm_completedLFunction_half_re_le hχ_ne
  obtain ⟨C₂, D₂, hC₂0, hD₂0, hbd₂⟩ := norm_completedLFunction_half_re_le hstar_ne
  let C : ℝ := max C₁ C₂
  let D : ℝ := max D₁ (4 * D₂ + 2 * Real.log q + 2)
  have hC0 : 0 ≤ C := le_max_of_le_left hC₁0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_of_lt hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hD0 : 0 ≤ D := le_max_of_le_left hD₁0
  refine ⟨C, D, hC0, hD0, fun w hw3 ↦ ?_⟩
  have hw2 : 2 ≤ ‖w‖ := by linarith
  have hlog_ge1 : 1 ≤ Real.log (‖w‖ + 2) := by
    have h4 : (4 : ℝ) ≤ ‖w‖ + 2 := by linarith
    have h2 : 1 < 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hl4 : 1 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      simpa using h2
    exact hl4.le.trans (Real.log_le_log (by norm_num) h4)
  by_cases hre : 1 / 2 ≤ w.re
  · calc ‖DirichletCharacter.completedLFunction χ w‖
        ≤ C₁ * Real.exp (D₁ * ‖w‖ * Real.log (‖w‖ + 2)) := hbd₁ w hre hw2
      _ ≤ C * Real.exp (D * ‖w‖ * Real.log (‖w‖ + 2)) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
  · have hre_lt : w.re < 1 / 2 := not_le.mp hre
    have h1w_re : 1 / 2 ≤ (1 - w).re := by simp; linarith
    have h1w_norm2 : 2 ≤ ‖1 - w‖ := by
      have : ‖w‖ - ‖(1 : ℂ)‖ ≤ ‖w - 1‖ := norm_sub_norm_le w 1
      rw [norm_one, norm_sub_rev] at this
      linarith
    have h1w_norm_le : ‖1 - w‖ ≤ 2 * ‖w‖ := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le 1 w
        _ = 1 + ‖w‖ := by rw [norm_one]
        _ ≤ 2 * ‖w‖ := by linarith
    have hlog_1w : Real.log (‖1 - w‖ + 2) ≤ Real.log (‖w‖ + 2) + Real.log 2 := by
      have hsub : ‖1 - w‖ + 2 ≤ 2 * (‖w‖ + 2) := by linarith
      calc Real.log (‖1 - w‖ + 2) ≤ Real.log (2 * (‖w‖ + 2)) :=
            Real.log_le_log (by positivity) hsub
        _ = Real.log 2 + Real.log (‖w‖ + 2) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log (‖w‖ + 2) + Real.log 2 := by ring
    have hfeq := completedLFunction_one_sub_primitive hχ (1 - w)
    have h11 : 1 - (1 - w) = w := by ring
    rw [h11] at hfeq
    rw [hfeq, norm_mul, norm_mul, norm_rootNumber_primitive hχ, mul_one]
    have hq_bd : ‖(q : ℂ) ^ ((1 - w) - 1 / 2)‖ ≤
        Real.exp ((2 * Real.log q) * ‖w‖ * Real.log (‖w‖ + 2)) := by
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
      have hre_exp : ((1 - w) - 1 / 2).re = 1 / 2 - w.re := by simp; ring
      rw [hre_exp]
      have hexp_le : 1 / 2 - w.re ≤ 2 * ‖w‖ := by
        linarith [neg_le_abs w.re, Complex.abs_re_le_norm w]
      calc (q : ℝ) ^ (1 / 2 - w.re) ≤ (q : ℝ) ^ (2 * ‖w‖) :=
            Real.rpow_le_rpow_of_exponent_le hq1 hexp_le
        _ = Real.exp (Real.log q * (2 * ‖w‖)) := Real.rpow_def_of_pos hq_pos _
        _ ≤ Real.exp ((2 * Real.log q) * ‖w‖ * Real.log (‖w‖ + 2)) := by
            refine Real.exp_le_exp.mpr ?_
            calc Real.log q * (2 * ‖w‖) = (2 * Real.log q) * ‖w‖ * 1 := by ring
              _ ≤ (2 * Real.log q) * ‖w‖ * Real.log (‖w‖ + 2) :=
                  mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
    have hcomp_bd : ‖DirichletCharacter.completedLFunction (star χ) (1 - w)‖ ≤
        C₂ * Real.exp ((4 * D₂ + 2) * ‖w‖ * Real.log (‖w‖ + 2)) := by
      refine (hbd₂ (1 - w) h1w_re h1w_norm2).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₂0
      have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have hD₂_1w : D₂ * ‖1 - w‖ * Real.log (‖1 - w‖ + 2) ≤
          D₂ * (2 * ‖w‖) * (Real.log (‖w‖ + 2) + 1) := by
        gcongr
        · exact Real.log_nonneg (by linarith [norm_nonneg (1 - w)])
        · linarith
      have hw_mul : 2 * D₂ * ‖w‖ ≤ 2 * D₂ * ‖w‖ * Real.log (‖w‖ + 2) := by
        calc 2 * D₂ * ‖w‖ = 2 * D₂ * ‖w‖ * 1 := by ring
          _ ≤ 2 * D₂ * ‖w‖ * Real.log (‖w‖ + 2) := mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
      have hwl_nonneg : 0 ≤ ‖w‖ * Real.log (‖w‖ + 2) := by positivity
      calc D₂ * ‖1 - w‖ * Real.log (‖1 - w‖ + 2)
          ≤ D₂ * (2 * ‖w‖) * (Real.log (‖w‖ + 2) + 1) := hD₂_1w
        _ = 2 * D₂ * ‖w‖ * Real.log (‖w‖ + 2) + 2 * D₂ * ‖w‖ := by ring
        _ ≤ 2 * D₂ * ‖w‖ * Real.log (‖w‖ + 2) + 2 * D₂ * ‖w‖ * Real.log (‖w‖ + 2) := by linarith
        _ = 4 * D₂ * (‖w‖ * Real.log (‖w‖ + 2)) := by ring
        _ ≤ (4 * D₂ + 2) * ‖w‖ * Real.log (‖w‖ + 2) := by nlinarith
    calc ‖(q : ℂ) ^ ((1 - w) - 1 / 2)‖ *
          ‖DirichletCharacter.completedLFunction (star χ) (1 - w)‖
        ≤ Real.exp ((2 * Real.log q) * ‖w‖ * Real.log (‖w‖ + 2)) *
            (C₂ * Real.exp ((4 * D₂ + 2) * ‖w‖ * Real.log (‖w‖ + 2))) := by gcongr
      _ = C₂ * Real.exp ((4 * D₂ + 2 * Real.log q + 2) * ‖w‖ * Real.log (‖w‖ + 2)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
      _ ≤ C * Real.exp (D * ‖w‖ * Real.log (‖w‖ + 2)) := by
          gcongr
          · exact le_max_right _ _
          · exact le_max_right _ _

/-- For any primitive Dirichlet character `χ` of modulus `q ≥ 2`, `completedLFunction χ` is an
entire function of order at most `1`. -/
theorem entireOrderLe_completedLFunction_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    EntireOrderLe (DirichletCharacter.completedLFunction χ) 1 := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction_of_ne_one hχ_ne
  refine entireOrderLe_of_eventually_exp hdiff fun δ hδ ↦ ?_
  obtain ⟨C, D, hC0, hD0, hbd⟩ := norm_completedLFunction_le_exp_norm_mul_log hχ hq
  refine ⟨C, D * (1 + 1 / δ), 3, by norm_num, fun w hw3 ↦ ?_⟩
  refine (hbd w hw3).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
  have hw0 : 0 < ‖w‖ := by linarith
  have hw1 : 1 ≤ ‖w‖ := by linarith
  have hlog2 : Real.log (‖w‖ + 2) ≤ (1 + 1 / δ) * ‖w‖ ^ δ := by
    have h2w : ‖w‖ + 2 ≤ 2 * ‖w‖ := by linarith
    have hlog_mul : Real.log (‖w‖ + 2) ≤ Real.log 2 + Real.log ‖w‖ := by
      calc Real.log (‖w‖ + 2) ≤ Real.log (2 * ‖w‖) := Real.log_le_log (by positivity) h2w
        _ = Real.log 2 + Real.log ‖w‖ := Real.log_mul (by norm_num) hw0.ne'
    have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hpow_ge1 : 1 ≤ ‖w‖ ^ δ := Real.one_le_rpow hw1 hδ.le
    have hlog_pow : Real.log ‖w‖ ≤ (1 / δ) * ‖w‖ ^ δ := by
      have hdelta : Real.log (‖w‖ ^ δ) = δ * Real.log ‖w‖ := Real.log_rpow hw0 δ
      have hlin : Real.log (‖w‖ ^ δ) ≤ ‖w‖ ^ δ := by
        linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hw0 δ)]
      calc Real.log ‖w‖ = (1 / δ) * (δ * Real.log ‖w‖) := by field_simp [hδ.ne']
        _ = (1 / δ) * Real.log (‖w‖ ^ δ) := by rw [hdelta]
        _ ≤ (1 / δ) * ‖w‖ ^ δ := mul_le_mul_of_nonneg_left hlin (by positivity)
    nlinarith
  have hmul : ‖w‖ * ‖w‖ ^ δ = ‖w‖ ^ (1 + δ) := by
    rw [Real.rpow_add hw0, Real.rpow_one]
  calc D * ‖w‖ * Real.log (‖w‖ + 2)
      ≤ D * ‖w‖ * ((1 + 1 / δ) * ‖w‖ ^ δ) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = D * (1 + 1 / δ) * (‖w‖ * ‖w‖ ^ δ) := by ring
    _ = D * (1 + 1 / δ) * ‖w‖ ^ (1 + δ) := by rw [hmul]

/-- For primitive `χ` (`q ≥ 2`), `completedLFunction χ` has finite entire order. -/
theorem hasFiniteOrder_completedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    HasFiniteOrder (DirichletCharacter.completedLFunction χ) :=
  ⟨1, zero_le_one, entireOrderLe_completedLFunction_one hχ hq⟩

end EntirenessAndOrder

section HadamardAndLogDeriv

private lemma completedLFunction_ne_zero_fn {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    DirichletCharacter.completedLFunction χ ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : ℂ)
  exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ
    (Or.inl (isPrimitive_ne_one hχ hq)) (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2

private lemma analyticOrderNatAt_completedLFunction_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) 0 = 0 := by
  have h0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    completedLFunction_ne_zero_of_re_nonpos_of_isPrimitive hχ hq (by norm_num)
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h0)]

/-- Genus-1 Hadamard factorization of `completedLFunction χ` for a primitive Dirichlet character
`χ` of modulus `q ≥ 2`, splitting into the finite-zero-list case and the infinite-zero-sequence
case, with all nontrivial zeros belonging to `CriticalStripZerosL χ`. -/
theorem hadamard_factorization_completedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    (∃ (zs : List ℂ) (A B : ℂ),
        (∀ a ∈ zs, a ∈ CriticalStripZerosL χ) ∧
          (∀ z : ℂ, z ≠ 0 → List.count z zs =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          ∀ z : ℂ, DirichletCharacter.completedLFunction χ z =
            Complex.exp (A + B * z) *
              (zs.map fun a ↦ weierstrassPrimaryFactor 1 (z / a)).prod) ∨
      (∃ (a : ℕ → ℂ) (A B : ℂ),
        (∀ n : ℕ, a n ∈ CriticalStripZerosL χ) ∧
          (∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite) ∧
          (∀ z : ℂ, z ≠ 0 → {n | a n = z}.ncard =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          (Summable fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
          ∀ z : ℂ, DirichletCharacter.completedLFunction χ z =
            Complex.exp (A + B * z) * canonicalProduct a 1 z) := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hdiff := differentiable_completedLFunction_of_ne_one hχ_ne
  have hne := completedLFunction_ne_zero_fn hχ hq
  have hord := entireOrderLe_completedLFunction_one hχ hq
  have h0 := analyticOrderNatAt_completedLFunction_zero hχ hq
  rcases hadamard_factorization_genus_one hdiff hne zero_le_one hord (by norm_num : (1 : ℝ) < 2) with
    ⟨zs, A, B, hzs0, hcount, hprod⟩ | ⟨a, A, B, ha0, hfin, hncard, hsum, hprod⟩
  · refine Or.inl ⟨zs, A, B, fun a ha ↦ ?_, hcount, fun z ↦ ?_⟩
    · have hcnt : List.count a zs ≠ 0 := Nat.ne_of_gt (List.count_pos_iff.mpr ha)
      have ha0' : a ≠ 0 := hzs0 a ha
      rw [hcount a ha0'] at hcnt
      have hzero : DirichletCharacter.completedLFunction χ a = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hcnt
      exact (completedLFunction_eq_zero_iff_criticalStrip hχ hq a).mp hzero
    · simpa [h0] using hprod z
  · refine Or.inr ⟨a, A, B, fun n ↦ ?_, hfin, hncard, hsum, fun z ↦ ?_⟩
    · have hfin_n : {k : ℕ | a k = a n}.Finite :=
        (hfin ‖a n‖).subset fun k hk ↦ show ‖a k‖ ≤ ‖a n‖ by rw [show a k = a n from hk]
      have hne_empty : {k : ℕ | a k = a n}.Nonempty := ⟨n, rfl⟩
      have hpos : 0 < {k : ℕ | a k = a n}.ncard :=
        Set.ncard_pos hfin_n |>.mpr hne_empty
      have hord_ne : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (a n) ≠ 0 := by
        rw [← hncard (a n) (ha0 n)]
        exact hpos.ne'
      have hzero : DirichletCharacter.completedLFunction χ (a n) = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hord_ne
      exact (completedLFunction_eq_zero_iff_criticalStrip hχ hq (a n)).mp hzero
    · simpa [h0] using hprod z

/-- Hadamard partial-fraction expansion for the logarithmic derivative of `completedLFunction χ`
for primitive `χ` (`q ≥ 2`). -/
theorem hadamard_logDeriv_completedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    (∃ (zs : List ℂ) (A B : ℂ),
        (∀ a ∈ zs, a ∈ CriticalStripZerosL χ) ∧
          (∀ z : ℂ, z ≠ 0 → List.count z zs =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          (∀ z : ℂ, DirichletCharacter.completedLFunction χ z =
            Complex.exp (A + B * z) *
              (zs.map fun a ↦ weierstrassPrimaryFactor 1 (z / a)).prod) ∧
          ∀ z : ℂ, z ≠ 0 → DirichletCharacter.completedLFunction χ z ≠ 0 →
            deriv (DirichletCharacter.completedLFunction χ) z /
              DirichletCharacter.completedLFunction χ z =
              B + (zs.map fun a ↦ 1 / (z - a) + 1 / a).sum) ∨
      (∃ (a : ℕ → ℂ) (A B : ℂ),
        (∀ n : ℕ, a n ∈ CriticalStripZerosL χ) ∧
          (∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite) ∧
          (∀ z : ℂ, z ≠ 0 → {n | a n = z}.ncard =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          (Summable fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
          (∀ z : ℂ, DirichletCharacter.completedLFunction χ z =
            Complex.exp (A + B * z) * canonicalProduct a 1 z) ∧
          ∀ z : ℂ, z ≠ 0 → DirichletCharacter.completedLFunction χ z ≠ 0 →
            deriv (DirichletCharacter.completedLFunction χ) z /
              DirichletCharacter.completedLFunction χ z =
              B + ∑' n : ℕ, (1 / (z - a n) + 1 / a n)) := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hdiff := differentiable_completedLFunction_of_ne_one hχ_ne
  have hne := completedLFunction_ne_zero_fn hχ hq
  have hord := entireOrderLe_completedLFunction_one hχ hq
  have h0 := analyticOrderNatAt_completedLFunction_zero hχ hq
  rcases hadamard_logDeriv_genus_one hdiff hne zero_le_one hord (by norm_num : (1 : ℝ) < 2) with
    ⟨zs, A, B, hzs0, hcount, hprod, hlog⟩ | ⟨a, A, B, ha0, hfin, hncard, hsum, hprod, hlog⟩
  · refine Or.inl ⟨zs, A, B, fun a ha ↦ ?_, hcount, fun z ↦ ?_, fun z hz0 hfz ↦ ?_⟩
    · have hcnt : List.count a zs ≠ 0 := Nat.ne_of_gt (List.count_pos_iff.mpr ha)
      rw [hcount a (hzs0 a ha)] at hcnt
      exact (completedLFunction_eq_zero_iff_criticalStrip hχ hq a).mp
        (apply_eq_zero_of_analyticOrderNatAt_ne_zero hcnt)
    · simpa [h0] using hprod z
    · simpa [h0] using hlog z hz0 hfz
  · refine Or.inr ⟨a, A, B, fun n ↦ ?_, hfin, hncard, hsum, fun z ↦ ?_, fun z hz0 hfz ↦ ?_⟩
    · have hfin_n : {k : ℕ | a k = a n}.Finite :=
        (hfin ‖a n‖).subset fun k hk ↦ show ‖a k‖ ≤ ‖a n‖ by rw [show a k = a n from hk]
      have hpos : 0 < {k : ℕ | a k = a n}.ncard :=
        Set.ncard_pos hfin_n |>.mpr ⟨n, rfl⟩
      have hord_ne : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (a n) ≠ 0 := by
        rw [← hncard (a n) (ha0 n)]
        exact hpos.ne'
      exact (completedLFunction_eq_zero_iff_criticalStrip hχ hq (a n)).mp
        (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord_ne)
    · simpa [h0] using hprod z
    · simpa [h0] using hlog z hz0 hfz

/-- Logarithmic derivative of the Gamma factor `gammaFactor χ` in terms of `digamma`. -/
theorem logDeriv_gammaFactor_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : DirichletCharacter.gammaFactor χ s ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2) := by
  have heq : DirichletCharacter.gammaFactor χ =
      (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2)) *
        (fun w : ℂ ↦ Complex.Gamma ((w + (parityExp χ : ℂ)) / 2)) := by
    ext w
    exact gammaFactor_eq_pi_mul_Gamma χ w
  rw [heq]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let f₁ : ℂ → ℂ := fun w ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2)
  let f₂ : ℂ → ℂ := fun w ↦ Complex.Gamma ((w + (parityExp χ : ℂ)) / 2)
  have hf₁_ne : f₁ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne)
  have hf₂_ne : f₂ s ≠ 0 := by
    intro h2
    apply hs
    rw [heq]
    simp [f₂, h2]
  have hnopole : ∀ m : ℕ, (s + (parityExp χ : ℂ)) / 2 ≠ -(m : ℂ) := by
    intro m hm
    apply hs
    rw [gammaFactor_eq_zero_iff]
    exact ⟨m, by linear_combination 2 * hm⟩
  have hf₁_deriv : HasDerivAt f₁
      ((-(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)) * f₁ s) s := by
    have hg : HasDerivAt (fun w : ℂ ↦ -(w + (parityExp χ : ℂ)) / 2) (-(1 / 2 : ℂ)) s := by
      have h0 : HasDerivAt (fun w : ℂ ↦ w + (parityExp χ : ℂ)) 1 s :=
        (hasDerivAt_id s).add_const _
      exact (h0.neg.div_const 2).congr_deriv (by ring)
    have hc := hg.const_cpow (Or.inl hpi_ne)
    convert hc using 1
    simp only [f₁]
    ring
  have hf₂_diff_g : HasDerivAt (fun w : ℂ ↦ (w + (parityExp χ : ℂ)) / 2) (1 / 2 : ℂ) s := by
    have h0 : HasDerivAt (fun w : ℂ ↦ w + (parityExp χ : ℂ)) 1 s :=
      (hasDerivAt_id s).add_const _
    simpa using h0.div_const 2
  have hG_diff : DifferentiableAt ℂ Complex.Gamma ((s + (parityExp χ : ℂ)) / 2) :=
    Complex.differentiableAt_Gamma _ hnopole
  have hf₂_deriv : HasDerivAt f₂
      (deriv Complex.Gamma ((s + (parityExp χ : ℂ)) / 2) * (1 / 2 : ℂ)) s :=
    hG_diff.hasDerivAt.comp s hf₂_diff_g
  rw [logDeriv_mul s hf₁_ne hf₂_ne hf₁_deriv.differentiableAt hf₂_deriv.differentiableAt]
  have hlog₁ : logDeriv f₁ s = -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) := by
    rw [logDeriv_apply, hf₁_deriv.deriv, mul_div_cancel_right₀ _ hf₁_ne,
      Complex.ofReal_log Real.pi_pos.le]
  have hlog₂ : logDeriv f₂ s =
      (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2) := by
    rw [logDeriv_apply, hf₂_deriv.deriv, AnalyticTools.Gamma.digamma_def]
    dsimp only [f₂]
    ring
  rw [hlog₁, hlog₂]

/-- Splitting the logarithmic derivative of `completedLFunction χ` into `LFunction χ` and
`gammaFactor χ` for `q ≥ 2` away from zeros of `LFunction χ` and poles of `gammaFactor χ`. -/
theorem logDeriv_completedLFunction_eq_add_gammaFactor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) {s : ℂ}
    (hs1 : χ ≠ 1 ∨ s ≠ 1) (hLs : DirichletCharacter.LFunction χ s ≠ 0)
    (hGs : DirichletCharacter.gammaFactor χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
          (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2)) := by
  have hq1 : q ≠ 1 := by omega
  have hG_cont : ContinuousAt (DirichletCharacter.gammaFactor χ) s := by
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnopole : ∀ m : ℕ, (s + (parityExp χ : ℂ)) / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hGs
      rw [gammaFactor_eq_zero_iff]
      exact ⟨m, by linear_combination 2 * hm⟩
    have hdiff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
      have heq : DirichletCharacter.gammaFactor χ =
          fun w ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2) *
            Complex.Gamma ((w + (parityExp χ : ℂ)) / 2) := by
        ext w; exact gammaFactor_eq_pi_mul_Gamma χ w
      rw [heq]
      refine DifferentiableAt.mul ?_ ?_
      · exact (((differentiableAt_id.add (differentiableAt_const _)).neg.div_const 2).const_cpow
          (Or.inl hpi_ne))
      · exact (Complex.differentiableAt_Gamma _ hnopole).comp s
          ((differentiableAt_id.add (differentiableAt_const _)).div_const 2)
    exact hdiff.continuousAt
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ := by
    filter_upwards [hG_cont.eventually_ne hGs] with w hw
    exact completedLFunction_eq_mul_gammaFactor χ (Or.inr hq1) hw
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hL_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    DirichletCharacter.differentiableAt_LFunction χ s hs1.symm
  have hG_diff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnopole : ∀ m : ℕ, (s + (parityExp χ : ℂ)) / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hGs
      rw [gammaFactor_eq_zero_iff]
      exact ⟨m, by linear_combination 2 * hm⟩
    have heq : DirichletCharacter.gammaFactor χ =
        fun w ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2) *
          Complex.Gamma ((w + (parityExp χ : ℂ)) / 2) := by
      ext w; exact gammaFactor_eq_pi_mul_Gamma χ w
    rw [heq]
    refine DifferentiableAt.mul ?_ ?_
    · exact (((differentiableAt_id.add (differentiableAt_const _)).neg.div_const 2).const_cpow
        (Or.inl hpi_ne))
    · exact (Complex.differentiableAt_Gamma _ hnopole).comp s
        ((differentiableAt_id.add (differentiableAt_const _)).div_const 2)
  rw [logDeriv_mul s hLs hGs hL_diff hG_diff, logDeriv_gammaFactor_eq χ hGs]

/-- Splitting the logarithmic derivative of `completedLFunction χ` (rewrite form). -/
lemma logDeriv_completedLFunction_eq_add_gammaFactor_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) {s : ℂ}
    (hs1 : χ ≠ 1 ∨ s ≠ 1) (hLs : DirichletCharacter.LFunction χ s ≠ 0)
    (hGs : DirichletCharacter.gammaFactor χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
          (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2)) :=
  logDeriv_completedLFunction_eq_add_gammaFactor χ hq hs1 hLs hGs

/-- Partial fraction expansion of `deriv (LFunction χ) s / LFunction χ s` for a primitive
character `χ` of modulus `q ≥ 2`, combining Hadamard's expansion with the `digamma` term. -/
theorem hadamard_logDeriv_LFunction_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    (∃ (zs : List ℂ) (B : ℂ),
        (∀ a ∈ zs, a ∈ CriticalStripZerosL χ) ∧
          (∀ z : ℂ, z ≠ 0 → List.count z zs =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          ∀ s : ℂ, s ≠ 0 → DirichletCharacter.LFunction χ s ≠ 0 →
            DirichletCharacter.gammaFactor χ s ≠ 0 →
              deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
                B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) -
                  (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2) +
                  (zs.map fun a ↦ 1 / (s - a) + 1 / a).sum) ∨
      (∃ (a : ℕ → ℂ) (B : ℂ),
        (∀ n : ℕ, a n ∈ CriticalStripZerosL χ) ∧
          (∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite) ∧
          (∀ z : ℂ, z ≠ 0 → {n | a n = z}.ncard =
            analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z) ∧
          (Summable fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
          ∀ s : ℂ, s ≠ 0 → DirichletCharacter.LFunction χ s ≠ 0 →
            DirichletCharacter.gammaFactor χ s ≠ 0 →
              deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
                B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) -
                  (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp χ : ℂ)) / 2) +
                  ∑' n : ℕ, (1 / (s - a n) + 1 / a n)) := by
  have hχ_ne : χ ≠ 1 := isPrimitive_ne_one hχ hq
  have hq1 : q ≠ 1 := by omega
  rcases hadamard_logDeriv_completedLFunction hχ hq with
    ⟨zs, A, B, hzs, hcount, _, hlog⟩ | ⟨a, A, B, ha, hfin, hncard, hsum, _, hlog⟩
  · refine Or.inl ⟨zs, B, hzs, hcount, fun s hs0 hLs hGs ↦ ?_⟩
    have hcomp_ne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
      rw [completedLFunction_eq_mul_gammaFactor χ (Or.inr hq1) hGs]
      exact mul_ne_zero hLs hGs
    have hsplit := logDeriv_completedLFunction_eq_add_gammaFactor χ hq (Or.inl hχ_ne) hLs hGs
    rw [logDeriv_apply, logDeriv_apply, hlog s hs0 hcomp_ne] at hsplit
    linear_combination -hsplit
  · refine Or.inr ⟨a, B, ha, hfin, hncard, hsum, fun s hs0 hLs hGs ↦ ?_⟩
    have hcomp_ne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
      rw [completedLFunction_eq_mul_gammaFactor χ (Or.inr hq1) hGs]
      exact mul_ne_zero hLs hGs
    have hsplit := logDeriv_completedLFunction_eq_add_gammaFactor χ hq (Or.inl hχ_ne) hLs hGs
    rw [logDeriv_apply, logDeriv_apply, hlog s hs0 hcomp_ne] at hsplit
    linear_combination -hsplit

private lemma principalChar_mul_eq_self {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) :
    principalChar q * ψ = ψ := by
  ext a
  simp [principalChar]

private lemma differentiableAt_finset_prod_fn {ι : Type*} (S : Finset ι)
    (f : ι → ℂ → ℂ) (s : ℂ) (hf : ∀ i ∈ S, DifferentiableAt ℂ (f i) s) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ∏ i ∈ S, f i w) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [differentiableAt_const]
  | insert a S ha ih =>
    have ha_diff : DifferentiableAt ℂ (f a) s := hf a (Finset.mem_insert_self a S)
    have hS_diff : DifferentiableAt ℂ (fun w : ℂ ↦ ∏ i ∈ S, f i w) s :=
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.prod_insert ha] using ha_diff.fun_mul hS_diff

/-- Any `NeZero q` character has nonzero conductor (`NeZero χ.conductor`). -/
lemma neZero_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor :=
  ⟨(Nat.pos_of_dvd_of_pos (conductor_dvd χ) (NeZero.pos q)).ne'⟩

/-- Reduction of the logarithmic derivative of an imprimitive Dirichlet L-function `LFunction χ`
to that of its inducing primitive character `χ.primitiveCharacter` plus finitely many local
Euler-factor terms over `q.primeFactors`. -/
theorem logDeriv_LFunction_eq_primitive_add_euler {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1)
    (hψs : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0)
    (heul : ∀ p ∈ q.primeFactors, 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s) ≠ 0) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      deriv (DirichletCharacter.LFunction χ.primitiveCharacter) s /
          DirichletCharacter.LFunction χ.primitiveCharacter s +
        ∑ p ∈ q.primeFactors,
          (χ.primitiveCharacter p * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) /
            (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  let ψ := χ.primitiveCharacter
  have hψ_ne_or : ψ ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs
    · refine Or.inl ?_
      intro h1
      apply hχ
      have hch : DirichletCharacter.changeLevel (conductor_dvd χ) ψ = χ := by
        rw [← principalChar_mul_eq_self (DirichletCharacter.changeLevel (conductor_dvd χ) ψ)]
        exact (induced_factorization_eq χ).symm
      rw [← hch, h1]
      exact DirichletCharacter.changeLevel_one _
    · exact Or.inr hs
  have hopen : IsOpen {w : ℂ | ψ ≠ 1 ∨ w ≠ 1} := by
    by_cases h : ψ = 1 <;> simp [h, isOpen_ne]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s]
      DirichletCharacter.LFunction ψ *
        (fun w : ℂ ↦ ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-w))) := by
    filter_upwards [hopen.mem_nhds hψ_ne_or] with w hw
    have hch : DirichletCharacter.changeLevel (conductor_dvd χ) ψ = χ := by
      rw [← principalChar_mul_eq_self (DirichletCharacter.changeLevel (conductor_dvd χ) ψ)]
      exact (induced_factorization_eq χ).symm
    change DirichletCharacter.LFunction χ w =
      DirichletCharacter.LFunction ψ w * ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-w))
    conv_lhs => rw [← hch]
    exact LFunction_changeLevel_eq (conductor_dvd χ) ψ hw
  have hg_diff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun w : ℂ ↦ 1 - ψ p * (p : ℂ) ^ (-w)) s := by
    intro p hp
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'
    exact (differentiableAt_const 1).sub
      ((differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (Or.inl hp_ne)))
  have hprod_ne : (∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr heul
  have hprod_diff : DifferentiableAt ℂ
      (fun w : ℂ ↦ ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-w))) s :=
    differentiableAt_finset_prod_fn q.primeFactors (fun p w ↦ 1 - ψ p * (p : ℂ) ^ (-w)) s hg_diff
  have hψ_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) s :=
    DirichletCharacter.differentiableAt_LFunction ψ s hψ_ne_or.symm
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_mul s hψs hprod_ne hψ_diff hprod_diff]
  have hprod_log := logDeriv_prod (s := q.primeFactors)
    (f := fun p w ↦ 1 - ψ p * (p : ℂ) ^ (-w)) (x := s) heul (fun p hp ↦ hg_diff p hp)
  have heq_prod : (fun w : ℂ ↦ ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-w))) =
      ∏ p ∈ q.primeFactors, fun w : ℂ ↦ 1 - ψ p * (p : ℂ) ^ (-w) := by
    ext w; simp
  rw [heq_prod, hprod_log]
  congr 1
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'
  have hpow : HasDerivAt (fun w : ℂ ↦ (p : ℂ) ^ (-w))
      (-Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) s := by
    have hneg : HasDerivAt (fun w : ℂ ↦ -w) (-1) s := (hasDerivAt_id s).neg
    have hc := hneg.const_cpow (Or.inl hp_ne)
    refine hc.congr_deriv ?_
    ring
  have hg : HasDerivAt (fun w : ℂ ↦ 1 - ψ p * (p : ℂ) ^ (-w))
      (ψ p * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) s := by
    have hc := (hasDerivAt_const s (1 : ℂ)).sub (hpow.const_mul (ψ p))
    convert hc using 1
    ring
  rw [logDeriv_apply, hg.deriv]

/-- Full Hadamard partial fraction expansion of `deriv (LFunction χ) s / LFunction χ s` for any
non-principal character `χ ≠ 1` (primitive or imprimitive), via `χ.primitiveCharacter`. -/
theorem hadamard_logDeriv_LFunction_of_ne_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} [NeZero χ.conductor] (hχ : χ ≠ 1) :
    let ψ := χ.primitiveCharacter
    (∃ (zs : List ℂ) (B : ℂ),
        (∀ a ∈ zs, a ∈ CriticalStripZerosL ψ) ∧
          (∀ z : ℂ, z ≠ 0 → List.count z zs =
            analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) z) ∧
          ∀ s : ℂ, s ≠ 0 → DirichletCharacter.LFunction ψ s ≠ 0 →
            DirichletCharacter.gammaFactor ψ s ≠ 0 →
            (∀ p ∈ q.primeFactors, 1 - ψ p * (p : ℂ) ^ (-s) ≠ 0) →
              deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
                B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) -
                  (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp ψ : ℂ)) / 2) +
                  (zs.map fun a ↦ 1 / (s - a) + 1 / a).sum +
                  ∑ p ∈ q.primeFactors,
                    (ψ p * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) /
                      (1 - ψ p * (p : ℂ) ^ (-s))) ∨
      (∃ (a : ℕ → ℂ) (B : ℂ),
        (∀ n : ℕ, a n ∈ CriticalStripZerosL ψ) ∧
          (∀ R : ℝ, {n | ‖a n‖ ≤ R}.Finite) ∧
          (∀ z : ℂ, z ≠ 0 → {n | a n = z}.ncard =
            analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) z) ∧
          (Summable fun n : ℕ ↦ ‖a n‖ ^ (-2 : ℝ)) ∧
          ∀ s : ℂ, s ≠ 0 → DirichletCharacter.LFunction ψ s ≠ 0 →
            DirichletCharacter.gammaFactor ψ s ≠ 0 →
            (∀ p ∈ q.primeFactors, 1 - ψ p * (p : ℂ) ^ (-s) ≠ 0) →
              deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
                B + (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) -
                  (1 / 2 : ℂ) * AnalyticTools.Gamma.digamma ((s + (parityExp ψ : ℂ)) / 2) +
                  (∑' n : ℕ, (1 / (s - a n) + 1 / a n)) +
                  ∑ p ∈ q.primeFactors,
                    (ψ p * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) /
                      (1 - ψ p * (p : ℂ) ^ (-s))) := by
  have hd_pos : 3 ≤ χ.conductor := three_le_conductor_of_ne_one hχ
  have hψ_prim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hd2 : 2 ≤ χ.conductor := by omega
  rcases hadamard_logDeriv_LFunction_primitive hψ_prim hd2 with
    ⟨zs, B, hzs, hcount, hlog⟩ | ⟨a, B, ha, hfin, hncard, hsum, hlog⟩
  · refine Or.inl ⟨zs, B, hzs, hcount, fun s hs0 hψs hGs heul ↦ ?_⟩
    rw [logDeriv_LFunction_eq_primitive_add_euler χ (Or.inl hχ) hψs heul,
      hlog s hs0 hψs hGs]
  · refine Or.inr ⟨a, B, ha, hfin, hncard, hsum, fun s hs0 hψs hGs heul ↦ ?_⟩
    rw [logDeriv_LFunction_eq_primitive_add_euler χ (Or.inl hχ) hψs heul,
      hlog s hs0 hψs hGs]

end HadamardAndLogDeriv

section LocalJensenBounds

private lemma summable_inv_nat_sq_sub_one :
    Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  exact (summable_nat_add_iff 2).mpr h

/-- Real-part lower bound on the line `Re s = 2`: `(LFunction χ (2 + t * I)).re ≥ 2 - π^2 / 6 > 0`. -/
lemma re_LFunction_two_add_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ (DirichletCharacter.LFunction χ (2 + (t : ℂ) * I)).re := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hs_re : 1 < s.re := by simp [s]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs_re]
  have hsum : LSeriesSummable (fun n ↦ χ n) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs_re
  have h1sum : Summable (fun b : ℕ ↦ LSeries.term (fun n ↦ χ n) s (b + 1)) :=
    hsum.comp_injective (add_left_injective 1)
  have hsplit1 : (∑' n : ℕ, LSeries.term (fun n ↦ χ n) s n) =
      LSeries.term (fun n ↦ χ n) s 0 +
        LSeries.term (fun n ↦ χ n) s 1 +
          ∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2) := by
    rw [hsum.tsum_eq_zero_add, h1sum.tsum_eq_zero_add]
    ring_nf
  have h0 : LSeries.term (fun n ↦ χ n) s 0 = 0 := by simp [LSeries.term]
  have h1 : LSeries.term (fun n ↦ χ n) s 1 = 1 := by simp
  change 2 - Real.pi ^ 2 / 6 ≤ (∑' n : ℕ, LSeries.term (fun n ↦ χ n) s n).re
  rw [hsplit1, h0, h1, zero_add]
  have hre : (1 + ∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2)).re =
      1 + (∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2)).re := by simp
  rw [hre]
  have htail_norm : ‖∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hle : ∀ k : ℕ,
        ‖LSeries.term (fun n ↦ χ n) s (k + 2)‖ ≤ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      intro k
      rw [LSeries.term_of_ne_zero (by omega : k + 2 ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos (by omega : 0 < k + 2)]
      have hre2 : s.re = 2 := by simp [s]
      rw [hre2]
      have hχ1 : ‖χ ((k + 2 : ℕ) : ZMod q)‖ ≤ 1 := norm_char_le_one χ _
      refine (div_le_div_of_nonneg_right hχ1 (by positivity)).trans ?_
      norm_cast
    have hsn : Summable (fun k : ℕ ↦ ‖LSeries.term (fun n ↦ χ n) s (k + 2)‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle summable_inv_nat_sq_sub_one
    have hzeta_split : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
        (1 : ℝ) / (0 : ℝ) ^ 2 + (1 : ℝ) / (1 : ℝ) ^ 2 +
          ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      have hz := hasSum_zeta_two.summable
      have hz1 : Summable (fun b : ℕ ↦ (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2) :=
        hz.comp_injective (add_left_injective 1)
      rw [hz.tsum_eq_zero_add, hz1.tsum_eq_zero_add]
      simp [one_div, add_assoc]
    have hzeta_tail : (∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
      rw [hasSum_zeta_two.tsum_eq] at hzeta_split
      norm_num at hzeta_split
      have hzeta_inv : (∑' k : ℕ, (((k : ℝ) + 2) ^ 2)⁻¹) = Real.pi ^ 2 / 6 - 1 := by linarith
      simpa only [one_div, Nat.cast_add, Nat.cast_ofNat] using hzeta_inv
    calc ‖∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2)‖
        ≤ ∑' k : ℕ, ‖LSeries.term (fun n ↦ χ n) s (k + 2)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 :=
          hsn.tsum_le_tsum hle summable_inv_nat_sq_sub_one
      _ = Real.pi ^ 2 / 6 - 1 := hzeta_tail
  have habs_re := Complex.abs_re_le_norm (∑' k : ℕ, LSeries.term (fun n ↦ χ n) s (k + 2))
  have hneg := (abs_le.mp (habs_re.trans htail_norm)).1
  linarith

/-- Strict positivity of `(LFunction χ (2 + t * I)).re` for every character `χ` and real `t`. -/
lemma re_LFunction_two_add_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    0 < (DirichletCharacter.LFunction χ (2 + (t : ℂ) * I)).re := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < 2 - Real.pi ^ 2 / 6 := by nlinarith
  exact h2.trans_le (re_LFunction_two_add_ge χ t)

/-- Uniform inverse norm bound `‖LFunction χ w‖⁻¹ ≤ Real.pi ^ 2 / 6 ≤ 2` for `2 ≤ Re w`. -/
lemma norm_LFunction_inv_le_of_two_le_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {w : ℂ} (hw : 2 ≤ w.re) :
    ‖DirichletCharacter.LFunction χ w‖⁻¹ ≤ 2 := by
  have hw1 : 1 < w.re := by linarith
  let fχ : ArithmeticFunction ℂ :=
    ⟨fun n ↦ if n = 0 then 0 else χ n, by simp⟩
  let gχ : ArithmeticFunction ℂ :=
    ⟨fun n ↦ (ArithmeticFunction.moebius n : ℂ) * χ n, by simp⟩
  have hmul_one : fχ * gχ = (1 : ArithmeticFunction ℂ) := by
    ext n
    cases n with
    | zero => simp
    | succ k =>
      have hn : k + 1 ≠ 0 := Nat.succ_ne_zero k
      rw [ArithmeticFunction.mul_apply]
      have hconv : (∑ x ∈ (k + 1).divisorsAntidiagonal, fχ x.1 * gχ x.2) =
          (∑ x ∈ (k + 1).divisorsAntidiagonal, (ArithmeticFunction.moebius x.2 : ℂ)) *
            χ ((k + 1 : ℕ) : ZMod q) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hx' := Nat.mem_divisorsAntidiagonal.mp hx
        have hx1 : x.1 ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hx'
          exact hn hx'.1.symm
        have hmul_eq : χ (x.1 : ZMod q) * χ (x.2 : ZMod q) = χ ((k + 1 : ℕ) : ZMod q) := by
          have hnat : x.1 * x.2 = k + 1 := hx'.1
          have hz : (x.1 : ZMod q) * (x.2 : ZMod q) = ((k + 1 : ℕ) : ZMod q) := by
            simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → ZMod q) hnat
          rw [← map_mul, hz]
        simp only [fχ, gχ, ArithmeticFunction.coe_mk]
        split_ifs with h0
        · exact absurd h0 hx1
        · linear_combination (ArithmeticFunction.moebius x.2 : ℂ) * hmul_eq
      rw [hconv]
      have hswap : (∑ x ∈ (k + 1).divisorsAntidiagonal, (ArithmeticFunction.moebius x.2 : ℂ)) =
          ∑ d ∈ (k + 1).divisors, (ArithmeticFunction.moebius d : ℂ) := by
        rw [← Nat.sum_divisorsAntidiagonal' (fun _ y ↦ (ArithmeticFunction.moebius y : ℂ))]
      have hmob : (∑ d ∈ (k + 1).divisors, ArithmeticFunction.moebius d) =
          if k + 1 = 1 then 1 else 0 := by
        have hm := congrArg (fun f : ArithmeticFunction ℤ ↦ f (k + 1))
          ArithmeticFunction.moebius_mul_coe_zeta
        rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hm
        have hsum_eq : (∑ x ∈ (k + 1).divisorsAntidiagonal,
            ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2) =
            ∑ d ∈ (k + 1).divisors, ArithmeticFunction.moebius d := by
          have h1 : ∀ x ∈ (k + 1).divisorsAntidiagonal,
              ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
                ArithmeticFunction.moebius x.1 := by
            intro x hx
            have hx' := Nat.mem_divisorsAntidiagonal.mp hx
            have hx2 : x.2 ≠ 0 := by
              intro h0
              rw [h0, mul_zero] at hx'
              exact hn hx'.1.symm
            simp [ArithmeticFunction.zeta_apply, hx2]
          rw [Finset.sum_congr rfl h1]
          exact Nat.sum_divisorsAntidiagonal (fun d _ ↦ ArithmeticFunction.moebius d)
        rw [hsum_eq] at hm
        exact hm
      have hmobC : (∑ d ∈ (k + 1).divisors, (ArithmeticFunction.moebius d : ℂ)) =
          if k + 1 = 1 then 1 else 0 := by
        have := congrArg (Int.cast : ℤ → ℂ) hmob
        push_cast at this
        simpa using this
      rw [hswap, hmobC]
      by_cases hk1 : k + 1 = 1
      · have hk0 : k = 0 := by omega
        subst hk0
        simp
      · simp only [hk1, ↓reduceIte, zero_mul]
        exact (ArithmeticFunction.one_apply_ne hk1).symm
  have hf_sum : LSeriesSummable (fun n ↦ fχ n) w := by
    have hs := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hw1
    refine hs.congr fun n ↦ ?_
    cases n with
    | zero => simp [LSeries.term]
    | succ k => simp [fχ]
  have hg_norm : ∀ n : ℕ, ‖LSeries.term (fun n ↦ gχ n) w n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    cases n with
    | zero => simp [LSeries.term]
    | succ k =>
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), Nat.succ_eq_add_one]
      have hmob_le : ‖(ArithmeticFunction.moebius (k + 1) : ℂ)‖ ≤ 1 := by
        rw [ArithmeticFunction.moebius]
        dsimp only [ArithmeticFunction.coe_mk]
        split_ifs <;> simp
      have hg_le : ‖gχ (k + 1)‖ ≤ 1 := by
        simp only [gχ, ArithmeticFunction.coe_mk, norm_mul, Nat.cast_add, Nat.cast_one]
        calc ‖(ArithmeticFunction.moebius (k + 1) : ℂ)‖ * ‖χ ((k : ZMod q) + 1)‖
            ≤ 1 * 1 := mul_le_mul hmob_le (norm_char_le_one χ _) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      have hrpow : ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ w.re :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos k) hw
      calc ‖gχ (k + 1)‖ / ((k + 1 : ℕ) : ℝ) ^ w.re
          ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ w.re := div_le_div_of_nonneg_right hg_le (by positivity)
        _ ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hrpow
        _ = (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by norm_cast
  have hg_sum : LSeriesSummable (fun n ↦ gχ n) w := by
    rw [LSeriesSummable]
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hg_norm hasSum_zeta_two.summable |>.of_norm
  have hprod_eq := ArithmeticFunction.LSeries_mul' hf_sum hg_sum
  have h1_series : LSeries (fun n ↦ ((1 : ArithmeticFunction ℂ) n)) w = 1 := by
    rw [LSeries]
    calc ∑' n : ℕ, LSeries.term (fun n ↦ ((1 : ArithmeticFunction ℂ) n)) w n
        = LSeries.term (fun n ↦ ((1 : ArithmeticFunction ℂ) n)) w 1 := by
          refine tsum_eq_single 1 fun n hn ↦ ?_
          cases n with
          | zero => simp [LSeries.term]
          | succ m =>
            rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m),
              ArithmeticFunction.one_apply_ne hn, zero_div]
      _ = 1 := by simp [ArithmeticFunction.one_apply]
  rw [hmul_one, h1_series] at hprod_eq
  have hf_eq : LSeries (fun n ↦ fχ n) w = DirichletCharacter.LFunction χ w := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hw1]
    refine tsum_congr fun n ↦ ?_
    cases n with
    | zero => simp [LSeries.term]
    | succ k => simp [fχ]
  rw [hf_eq] at hprod_eq
  have hinv : (DirichletCharacter.LFunction χ w)⁻¹ = LSeries (fun n ↦ gχ n) w := by
    have hL_ne : DirichletCharacter.LFunction χ w ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hprod_eq
      exact one_ne_zero hprod_eq
    field_simp [hL_ne]
    exact hprod_eq
  rw [← norm_inv, hinv]
  have hsn : Summable (fun n : ℕ ↦ ‖LSeries.term (fun n ↦ gχ n) w n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hg_norm hasSum_zeta_two.summable
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  calc ‖∑' n : ℕ, LSeries.term (fun n ↦ gχ n) w n‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n ↦ gχ n) w n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := hsn.tsum_le_tsum hg_norm hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 2 := by nlinarith

private lemma criticalStrip_unit_mem_closedBall (T : ℝ) {ρ : ℂ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him0 : T ≤ ρ.im) (him1 : ρ.im ≤ T + 1) :
    ρ ∈ Metric.closedBall ((2 : ℂ) + (T + 1 / 2 : ℝ) * I) (9 / 4) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hre : (ρ - ((2 : ℂ) + (T + 1 / 2 : ℝ) * I)).re ^ 2 ≤ 4 := by
    have : (ρ - ((2 : ℂ) + (T + 1 / 2 : ℝ) * I)).re = ρ.re - 2 := by simp
    rw [this]
    nlinarith
  have him : (ρ - ((2 : ℂ) + (T + 1 / 2 : ℝ) * I)).im ^ 2 ≤ 1 / 4 := by
    have : (ρ - ((2 : ℂ) + (T + 1 / 2 : ℝ) * I)).im = ρ.im - (T + 1 / 2) := by simp
    rw [this]
    nlinarith
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  refine Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩

/-- Explicit local Jensen constant `12 / Real.log (10 / 9)` appearing in unit-interval zero-count
estimates for non-principal Dirichlet L-functions. -/
noncomputable def jensenUnitZeroDensityConst : ℝ :=
  12 / Real.log (10 / 9)

/-- Positivity of `jensenUnitZeroDensityConst`. -/
lemma jensenUnitZeroDensityConst_pos : 0 < jensenUnitZeroDensityConst := by
  rw [jensenUnitZeroDensityConst]
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

/-- Local unit-interval Jensen zero-count bound for non-principal `χ ≠ 1`: the Jensen zero count
on `closedBall (2 + (T + 1/2) * I) (9 / 4)` (which contains `(0, 1) × [T, T + 1]`) is bounded
by `(12 / Real.log (10 / 9)) * Real.log (q * (|T| + 2))`. -/
theorem zeroCount_LFunction_unit_interval_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (T : ℝ) :
    (zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (T + 1 / 2 : ℝ) * I) (9 / 4) : ℝ) ≤
      jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
  let z₀ : ℂ := (2 : ℂ) + (T + 1 / 2 : ℝ) * I
  let M : ℝ := 343 * (q : ℝ) ^ 2 * (|T| + 2) ^ 2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM0 : 0 < M := by positivity
  have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (5 / 2)) :=
    ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ _)
  have hz₀_re : 2 ≤ z₀.re := by simp [z₀]
  have hinv_le : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 2 :=
    norm_LFunction_inv_le_of_two_le_re χ hz₀_re
  have hz₀_norm : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hpos : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := by
      by_contra hle
      have h0 : ‖DirichletCharacter.LFunction χ z₀‖ = 0 :=
        le_antisymm (not_lt.mp hle) (norm_nonneg _)
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
        (by linarith) (norm_eq_zero.mp h0)
    exact inv_anti₀ (inv_pos.mpr hpos) hinv_le |> fun h ↦ by simpa using h
  have hz₀_ne : DirichletCharacter.LFunction χ z₀ ≠ 0 := by
    intro h0
    simp only [h0, norm_zero] at hz₀_norm
    linarith
  have hsphere : ∀ z ∈ Metric.sphere z₀ (5 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M := by
    intro z hz
    have hdist : ‖z - z₀‖ = 5 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hre_lo : -(1 / 2 : ℝ) ≤ z.re := by
      have : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
      have hz0r : z₀.re = 2 := by simp [z₀]
      linarith [(abs_le.mp (this.trans_eq hdist)).1]
    have him_bd : |z.im| ≤ |T| + 3 := by
      have h1 : |z.im - z₀.im| ≤ 5 / 2 := by
        simpa [Complex.sub_im] using (Complex.abs_im_le_norm (z - z₀)).trans_eq hdist
      have hz0i : z₀.im = T + 1 / 2 := by simp [z₀]
      rw [hz0i] at h1
      have := abs_le.mp h1
      rw [abs_le]
      exact ⟨by linarith [neg_le_abs T], by linarith [le_abs_self T]⟩
    by_cases hre2 : z.re ≤ 2
    · have hstrip := norm_LFunction_strip_poly_le hχ hre_lo hre2
      have hq_sq : (q : ℝ) + 48 * (q : ℝ) ^ 2 ≤ 49 * (q : ℝ) ^ 2 := by nlinarith
      have him_sq : (|z.im| + 2) ^ 2 ≤ 7 * (|T| + 2) ^ 2 := by
        have hlin : |z.im| + 2 ≤ 5 / 2 * (|T| + 2) := by
          have : 0 ≤ |T| := abs_nonneg T
          linarith
        calc (|z.im| + 2) ^ 2 ≤ (5 / 2 * (|T| + 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hlin 2
          _ = 25 / 4 * (|T| + 2) ^ 2 := by ring
          _ ≤ 7 * (|T| + 2) ^ 2 := by nlinarith
      calc ‖DirichletCharacter.LFunction χ z‖
          ≤ ((q : ℝ) + 48 * (q : ℝ) ^ 2) * (|z.im| + 2) ^ 2 := hstrip
        _ ≤ (49 * (q : ℝ) ^ 2) * (7 * (|T| + 2) ^ 2) := by gcongr
        _ = M := by simp only [M]; ring
    · have h2le : 2 ≤ z.re := (not_le.mp hre2).le
      have hq_sq : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
      have hT_sq : (4 : ℝ) ≤ (|T| + 2) ^ 2 := by nlinarith [abs_nonneg T]
      calc ‖DirichletCharacter.LFunction χ z‖ ≤ 2 := norm_LFunction_le_two_of_two_le_re χ h2le
        _ ≤ M := by
          change 2 ≤ 343 * (q : ℝ) ^ 2 * (|T| + 2) ^ 2
          nlinarith
  have hj := zeroCount_le_sub_log_div_log (f := DirichletCharacter.LFunction χ)
    (by norm_num : (0 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) < 5 / 2) hM0 hana hz₀_ne hsphere
  have hdiv : (5 / 2 : ℝ) / (9 / 4) = 10 / 9 := by norm_num
  rw [hdiv] at hj
  have hlog_pos : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have hlog_inv : -Real.log ‖DirichletCharacter.LFunction χ z₀‖ ≤ Real.log 2 := by
    have : Real.log (1 / 2 : ℝ) ≤ Real.log ‖DirichletCharacter.LFunction χ z₀‖ :=
      Real.log_le_log (by norm_num) hz₀_norm
    rw [one_div, Real.log_inv] at this
    linarith
  have hlog_M : Real.log M ≤ Real.log (343 : ℝ) + 2 * Real.log ((q : ℝ) * (|T| + 2)) := by
    have hM_eq : M = 343 * ((q : ℝ) * (|T| + 2)) ^ 2 := by simp only [M]; ring
    rw [hM_eq, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have harg_ge2 : 2 ≤ (q : ℝ) * (|T| + 2) := by
    have : 2 ≤ |T| + 2 := by linarith [abs_nonneg T]
    nlinarith
  have hlog2_le : Real.log 2 ≤ Real.log ((q : ℝ) * (|T| + 2)) :=
    Real.log_le_log (by norm_num) harg_ge2
  have h686 : Real.log (343 : ℝ) + Real.log 2 ≤ 10 * Real.log ((q : ℝ) * (|T| + 2)) := by
    have : (343 : ℝ) * 2 ≤ (2 : ℝ) ^ 10 := by norm_num
    calc Real.log 343 + Real.log 2 = Real.log (343 * 2) := (Real.log_mul (by norm_num) (by norm_num)).symm
      _ ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) this
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 10 * Real.log ((q : ℝ) * (|T| + 2)) := by linarith
  have hnum : Real.log M - Real.log ‖DirichletCharacter.LFunction χ z₀‖ ≤
      12 * Real.log ((q : ℝ) * (|T| + 2)) := by
    linarith
  calc (zeroCount (DirichletCharacter.LFunction χ) z₀ (9 / 4) : ℝ)
      ≤ (Real.log M - Real.log ‖DirichletCharacter.LFunction χ z₀‖) / Real.log (10 / 9) := hj
    _ ≤ (12 * Real.log ((q : ℝ) * (|T| + 2))) / Real.log (10 / 9) :=
        div_le_div_of_nonneg_right hnum hlog_pos.le
    _ = jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
        rw [jensenUnitZeroDensityConst]; ring

/-- Any `Finset ℂ` of critical-strip zeros of `LFunction χ` (`χ ≠ 1`) in `0 < Re ρ < 1`,
`T ≤ Im ρ ≤ T + 1` has cardinality at most `jensenUnitZeroDensityConst * log (q * (|T| + 2))`. -/
theorem finset_card_zeros_unit_interval_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (T : ℝ) {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1 ∧
      DirichletCharacter.LFunction χ ρ = 0) :
    (S.card : ℝ) ≤ jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
  let z₀ : ℂ := (2 : ℂ) + (T + 1 / 2 : ℝ) * I
  have hle_count : (S.card : ℝ) ≤ (zeroCount (DirichletCharacter.LFunction χ) z₀ (9 / 4) : ℝ) := by
    have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (9 / 4)) :=
      ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono
        (Set.subset_univ _)
    have hz₀_ne : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [z₀])
    have hS' : ∀ ρ ∈ S, ρ ∈ Metric.closedBall z₀ (9 / 4) ∧ DirichletCharacter.LFunction χ ρ = 0 := by
      intro ρ hρ
      rcases hS ρ hρ with ⟨h0, h1, ht0, ht1, hL0⟩
      exact ⟨criticalStrip_unit_mem_closedBall T h0 h1 ht0 ht1, hL0⟩
    exact_mod_cast finset_card_le_zeroCount (f := DirichletCharacter.LFunction χ)
      (by norm_num : (0 : ℝ) ≤ 9 / 4) hana hz₀_ne hS'
  exact hle_count.trans (zeroCount_LFunction_unit_interval_le hχ T)

end LocalJensenBounds

section ZeroCountingAndRiemannVonMangoldt

/-- Critical-strip zeros of `LFunction χ` whose imaginary part lies in `[t₁, t₂]`. -/
def criticalStripZeroSetInRect {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t₁ t₂ : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ t₁ ≤ ρ.im ∧ ρ.im ≤ t₂ ∧ DirichletCharacter.LFunction χ ρ = 0}

/-- Every unit-height critical-strip box `(0, 1) × [T, T + 1]` contains only finitely many
zeros of `LFunction χ` (for both non-principal and principal `χ`). -/
lemma criticalStripZeroSetInUnit_finite {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (criticalStripZeroSetInRect χ T (T + 1)).Finite := by
  let z₀ : ℂ := (2 : ℂ) + (T + 1 / 2 : ℝ) * I
  by_cases hχ : χ = 1
  · subst hχ
    have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
        (Metric.closedBall z₀ (9 / 4)) :=
      ((DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn.analyticOnNhd
        isOpen_univ).mono (Set.subset_univ _)
    have hz₀_ne1 : z₀ ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [z₀] at this
    have hL_ne : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z₀ ≠ 0 := by
      intro h0
      have hinv := norm_LFunction_inv_le_of_two_le_re (1 : DirichletCharacter ℂ q)
        (by simp [z₀] : (2 : ℝ) ≤ z₀.re)
      have hz := norm_LFunction_le_two_of_two_le_re (1 : DirichletCharacter ℂ q)
        (by simp [z₀] : (2 : ℝ) ≤ z₀.re)
      have : 0 < ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z₀‖ := by
        have := re_LFunction_two_add_pos (1 : DirichletCharacter ℂ q) (T + 1 / 2)
        have hz_eq : z₀ = 2 + ((T + 1 / 2 : ℝ) : ℂ) * I := rfl
        rw [← hz_eq] at this
        exact lt_of_lt_of_le this (Complex.re_le_norm _)
      simp [h0] at this
    have hz₀_ne : DirichletCharacter.LFunctionTrivChar₁ q z₀ ≠ 0 := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz₀_ne1]
      exact mul_ne_zero (sub_ne_zero.mpr hz₀_ne1) hL_ne
    have hsub : criticalStripZeroSetInRect (1 : DirichletCharacter ℂ q) T (T + 1) ⊆
        zeroSet (DirichletCharacter.LFunctionTrivChar₁ q) z₀ (9 / 4) := by
      intro ρ ⟨h0, h1, ht0, ht1, hL0⟩
      have hρ1 : ρ ≠ 1 := fun h ↦ by simp [h] at h1
      refine ⟨criticalStrip_unit_mem_closedBall T h0 h1 ht0 ht1, ?_⟩
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ1]
      change (ρ - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0
      rw [hL0, mul_zero]
    exact (zeroSet_finite (by norm_num : (0 : ℝ) ≤ 9 / 4) hana hz₀_ne).subset hsub
  · have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (9 / 4)) :=
      ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono
        (Set.subset_univ _)
    have hz₀_ne : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [z₀])
    have hsub : criticalStripZeroSetInRect χ T (T + 1) ⊆
        zeroSet (DirichletCharacter.LFunction χ) z₀ (9 / 4) := by
      intro ρ ⟨h0, h1, ht0, ht1, hL0⟩
      exact ⟨criticalStrip_unit_mem_closedBall T h0 h1 ht0 ht1, hL0⟩
    exact (zeroSet_finite (by norm_num : (0 : ℝ) ≤ 9 / 4) hana hz₀_ne).subset hsub

/-- Finiteness of critical-strip zeros of `LFunction χ` in any bounded vertical box `t₁ ≤ Im ρ ≤ t₂`. -/
lemma criticalStripZeroSetInRect_finite {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t₁ t₂ : ℝ) :
    (criticalStripZeroSetInRect χ t₁ t₂).Finite := by
  let N : ℕ := Nat.ceil (t₂ - t₁) + 1
  have hcov : criticalStripZeroSetInRect χ t₁ t₂ ⊆
      ⋃ k ∈ Finset.range N, criticalStripZeroSetInRect χ (t₁ + k) (t₁ + k + 1) := by
    intro ρ ⟨h0, h1, ht0, ht1, hL0⟩
    let k : ℕ := Nat.floor (ρ.im - t₁)
    have hk_le : (k : ℝ) ≤ ρ.im - t₁ := Nat.floor_le (by linarith)
    have hlt_k : ρ.im - t₁ < (k : ℝ) + 1 := Nat.lt_floor_add_one (ρ.im - t₁)
    have hk_lt_N : k < N := by
      have hceil : t₂ - t₁ ≤ Nat.ceil (t₂ - t₁) := Nat.le_ceil _
      have hlt_real : (k : ℝ) < (N : ℝ) := by
        simp only [N, Nat.cast_add, Nat.cast_one]
        linarith
      exact Nat.cast_lt.mp hlt_real
    refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk_lt_N, ?_⟩
    exact ⟨h0, h1, by linarith, by linarith, hL0⟩
  exact ((Finset.finite_toSet (Finset.range N)).biUnion
    fun k _ ↦ criticalStripZeroSetInUnit_finite χ (t₁ + k)).subset hcov

/-- Finite set of critical-strip zeros of `LFunction χ` in `t₁ ≤ Im ρ ≤ t₂`. -/
noncomputable def criticalStripZeroFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t₁ t₂ : ℝ) : Finset ℂ :=
  (criticalStripZeroSetInRect_finite χ t₁ t₂).toFinset

/-- Membership characterization for `criticalStripZeroFinset χ t₁ t₂`. -/
@[simp]
lemma mem_criticalStripZeroFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t₁ t₂ : ℝ} {ρ : ℂ} :
    ρ ∈ criticalStripZeroFinset χ t₁ t₂ ↔
      0 < ρ.re ∧ ρ.re < 1 ∧ t₁ ≤ ρ.im ∧ ρ.im ≤ t₂ ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  simp [criticalStripZeroFinset, criticalStripZeroSetInRect]

/-- Symmetric zero-counting function `N(T, χ)` counting zeros of `LFunction χ` in
`0 < Re ρ < 1`, `|Im ρ| ≤ T` with analytic multiplicity. -/
noncomputable def zeroCountL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ∑ ρ ∈ criticalStripZeroFinset χ (-T) T, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- Upper-half zero-counting function `N⁺(T, χ)` counting zeros of `LFunction χ` in
`0 < Re ρ < 1`, `0 ≤ Im ρ ≤ T` with analytic multiplicity. -/
noncomputable def zeroCountHalfL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ∑ ρ ∈ criticalStripZeroFinset χ 0 T, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- Zero-counting function along the real segment `0 < Re ρ < 1`, `Im ρ = 0` with multiplicity. -/
noncomputable def zeroCountRealStripL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℕ :=
  ∑ ρ ∈ criticalStripZeroFinset χ 0 0, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- For negative `T < 0`, `zeroCountL χ T = 0`. -/
lemma zeroCountL_of_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : T < 0) :
    zeroCountL χ T = 0 := by
  have hemp : criticalStripZeroFinset χ (-T) T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    rw [mem_criticalStripZeroFinset] at hρ
    linarith
  simp [zeroCountL, hemp]

/-- For negative `T < 0`, `zeroCountHalfL χ T = 0`. -/
lemma zeroCountHalfL_of_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : T < 0) :
    zeroCountHalfL χ T = 0 := by
  have hemp : criticalStripZeroFinset χ 0 T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    rw [mem_criticalStripZeroFinset] at hρ
    linarith
  simp [zeroCountHalfL, hemp]

/-- Monotonicity of `zeroCountL χ`. -/
lemma zeroCountL_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T₁ T₂ : ℝ}
    (hT : T₁ ≤ T₂) : zeroCountL χ T₁ ≤ zeroCountL χ T₂ := by
  refine Finset.sum_le_sum_of_subset fun ρ hρ ↦ ?_
  rw [mem_criticalStripZeroFinset] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, by linarith, by linarith, hρ.2.2.2.2⟩

/-- Monotonicity of `zeroCountHalfL χ`. -/
lemma zeroCountHalfL_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T₁ T₂ : ℝ}
    (hT : T₁ ≤ T₂) : zeroCountHalfL χ T₁ ≤ zeroCountHalfL χ T₂ := by
  refine Finset.sum_le_sum_of_subset fun ρ hρ ↦ ?_
  rw [mem_criticalStripZeroFinset] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by linarith, hρ.2.2.2.2⟩

/-- Conjugation symmetry of the symmetric zero count: `zeroCountL (star χ) T = zeroCountL χ T`. -/
theorem zeroCountL_star_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zeroCountL (star χ) T = zeroCountL χ T := by
  rw [zeroCountL, zeroCountL]
  refine Finset.sum_bij (fun ρ _ ↦ conj ρ) ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [mem_criticalStripZeroFinset] at hρ ⊢
    refine ⟨by simpa using hρ.1, by simpa using hρ.2.1, ?_, ?_, ?_⟩
    · simp; linarith
    · simp; linarith
    · have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hρ
      have hconj := LFunction_star_conj_of_ne_one (star χ) (Or.inr hne1)
      simp only [star_star] at hconj
      rw [hconj, hρ.2.2.2.2, map_zero]
  · intro ρ₁ _ ρ₂ _ h
    simpa using congrArg conj h
  · intro σ hσ
    rw [mem_criticalStripZeroFinset] at hσ
    refine ⟨conj σ, ?_, by simp⟩
    rw [mem_criticalStripZeroFinset]
    refine ⟨by simpa using hσ.1, by simpa using hσ.2.1, ?_, ?_, ?_⟩
    · simp; linarith
    · simp; linarith
    · have hne1 : σ ≠ 1 := fun h ↦ by simp [h] at hσ
      rw [LFunction_star_conj_of_ne_one χ (Or.inr hne1), hσ.2.2.2.2, map_zero]
  · intro ρ hρ
    rw [mem_criticalStripZeroFinset] at hρ
    have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hρ
    have hord := analyticOrderNatAt_LFunction_star_conj (star χ) (Or.inr hne1)
    simp only [star_star] at hord
    exact hord.symm

/-- Exact decomposition of the symmetric zero count `zeroCountL χ T` into the upper-half counts
for `χ` and `star χ`: `zeroCountL χ T + zeroCountRealStripL χ = zeroCountHalfL χ T + zeroCountHalfL (star χ) T`. -/
theorem zeroCountL_add_real_eq_half_add_half_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 ≤ T) :
    zeroCountL χ T + zeroCountRealStripL χ =
      zeroCountHalfL χ T + zeroCountHalfL (star χ) T := by
  let S := criticalStripZeroFinset χ (-T) T
  let S_hi := criticalStripZeroFinset χ 0 T
  let S_lo := criticalStripZeroFinset χ (-T) 0
  have hunion : S = S_hi ∪ S_lo := by
    ext ρ
    simp only [S, S_hi, S_lo, Finset.mem_union, mem_criticalStripZeroFinset]
    constructor
    · rintro ⟨h0, h1, hlo, hhi, hL⟩
      by_cases h0im : 0 ≤ ρ.im
      · exact Or.inl ⟨h0, h1, h0im, hhi, hL⟩
      · exact Or.inr ⟨h0, h1, hlo, (not_le.mp h0im).le, hL⟩
    · rintro (⟨h0, h1, h0im, hhi, hL⟩ | ⟨h0, h1, hlo, h0im, hL⟩)
      · exact ⟨h0, h1, by linarith, hhi, hL⟩
      · exact ⟨h0, h1, hlo, by linarith, hL⟩
  have hinter : S_hi ∩ S_lo = criticalStripZeroFinset χ 0 0 := by
    ext ρ
    simp only [S_hi, S_lo, Finset.mem_inter, mem_criticalStripZeroFinset]
    constructor
    · rintro ⟨⟨h0, h1, him1, _, hL⟩, ⟨_, _, _, him2, _⟩⟩
      exact ⟨h0, h1, him1, him2, hL⟩
    · rintro ⟨h0, h1, him1, him2, hL⟩
      exact ⟨⟨h0, h1, him1, by linarith, hL⟩, ⟨h0, h1, by linarith, him2, hL⟩⟩
  have hS_lo : ∑ ρ ∈ S_lo, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      zeroCountHalfL (star χ) T := by
    rw [zeroCountHalfL]
    refine Finset.sum_bij (fun ρ _ ↦ conj ρ) ?_ ?_ ?_ ?_
    · intro ρ hρ
      rw [mem_criticalStripZeroFinset] at hρ ⊢
      have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hρ
      refine ⟨by simpa using hρ.1, by simpa using hρ.2.1, ?_, ?_, ?_⟩
      · simp; linarith
      · simp; linarith
      · rw [LFunction_star_conj_of_ne_one χ (Or.inr hne1), hρ.2.2.2.2, map_zero]
    · intro ρ₁ _ ρ₂ _ h
      simpa using congrArg conj h
    · intro σ hσ
      rw [mem_criticalStripZeroFinset] at hσ
      have hne1 : σ ≠ 1 := fun h ↦ by simp [h] at hσ
      refine ⟨conj σ, ?_, by simp⟩
      rw [mem_criticalStripZeroFinset]
      refine ⟨by simpa using hσ.1, by simpa using hσ.2.1, ?_, ?_, ?_⟩
      · simp; linarith
      · simp; linarith
      · have hconj := LFunction_star_conj_of_ne_one (star χ) (Or.inr hne1)
        simp only [star_star] at hconj
        rw [hconj, hσ.2.2.2.2, map_zero]
    · intro ρ hρ
      rw [mem_criticalStripZeroFinset] at hρ
      have hne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hρ
      exact (analyticOrderNatAt_LFunction_star_conj χ (Or.inr hne1)).symm
  have hsum_ui := Finset.sum_union_inter (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (s₁ := S_hi) (s₂ := S_lo)
  rw [← hunion, hinter] at hsum_ui
  change zeroCountL χ T + zeroCountRealStripL χ =
    zeroCountHalfL χ T + ∑ ρ ∈ S_lo, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ at hsum_ui
  rw [hS_lo] at hsum_ui
  exact hsum_ui

private lemma sum_order_in_unit_le_zeroCount {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (T : ℝ) :
    ∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≤
      zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (T + 1 / 2 : ℝ) * I) (9 / 4) := by
  let z₀ : ℂ := (2 : ℂ) + (T + 1 / 2 : ℝ) * I
  have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (9 / 4)) :=
    ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ _)
  have hz₀_ne : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [z₀])
  have hfin : (zeroSet (DirichletCharacter.LFunction χ) z₀ (9 / 4)).Finite :=
    zeroSet_finite (by norm_num : (0 : ℝ) ≤ 9 / 4) hana hz₀_ne
  let Z : Finset ℂ := hfin.toFinset
  have hZ : (Z : Set ℂ) = zeroSet (DirichletCharacter.LFunction χ) z₀ (9 / 4) := by
    simp [Z]
  have hzero := zeroCount_eq_sum_analyticOrderNatAt (by norm_num : (0 : ℝ) ≤ 9 / 4) hana hz₀_ne hZ
  rw [hzero]
  refine Finset.sum_le_sum_of_subset fun ρ hρ ↦ ?_
  rw [mem_criticalStripZeroFinset] at hρ
  rw [← Finset.mem_coe, hZ]
  exact ⟨criticalStrip_unit_mem_closedBall T hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2.1, hρ.2.2.2.2⟩

/-- Unconditional unit-interval zero-density bound on the upper-half zero-counting function
`zeroCountHalfL χ` (`χ ≠ 1`). -/
theorem zeroCountHalfL_add_one_sub_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {T : ℝ} (_hT : 0 ≤ T) :
    (zeroCountHalfL χ (T + 1) : ℝ) - (zeroCountHalfL χ T : ℝ) ≤
      jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
  have hsub : criticalStripZeroFinset χ 0 (T + 1) ⊆
      criticalStripZeroFinset χ 0 T ∪ criticalStripZeroFinset χ T (T + 1) := by
    intro ρ hρ
    rw [Finset.mem_union, mem_criticalStripZeroFinset, mem_criticalStripZeroFinset]
    rw [mem_criticalStripZeroFinset] at hρ
    by_cases hle : ρ.im ≤ T
    · exact Or.inl ⟨hρ.1, hρ.2.1, hρ.2.2.1, hle, hρ.2.2.2.2⟩
    · exact Or.inr ⟨hρ.1, hρ.2.1, (not_le.mp hle).le, hρ.2.2.2.1, hρ.2.2.2.2⟩
  have hsum_nat : zeroCountHalfL χ (T + 1) ≤
      zeroCountHalfL χ T +
        ∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
    have h1 := Finset.sum_le_sum_of_subset
      (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) hsub
    have h2 := Finset.sum_union_inter
      (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
      (s₁ := criticalStripZeroFinset χ 0 T) (s₂ := criticalStripZeroFinset χ T (T + 1))
    change zeroCountHalfL χ (T + 1) ≤ _ at h1
    change _ + _ = zeroCountHalfL χ T + _ at h2
    omega
  have hstep : (zeroCountHalfL χ (T + 1) : ℝ) - (zeroCountHalfL χ T : ℝ) ≤
      (zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (T + 1 / 2 : ℝ) * I) (9 / 4) : ℝ) := by
    have h1 : (zeroCountHalfL χ (T + 1) : ℝ) ≤
        (zeroCountHalfL χ T : ℝ) +
          (∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
            analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      exact_mod_cast hsum_nat
    have h2 : (∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
        (zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (T + 1 / 2 : ℝ) * I) (9 / 4) : ℝ) := by
      exact_mod_cast sum_order_in_unit_le_zeroCount hχ T
    linarith
  exact hstep.trans (zeroCount_LFunction_unit_interval_le hχ T)

/-- Unconditional unit-interval zero-density bound on the symmetric zero-counting function
`zeroCountL χ` (`χ ≠ 1`) for `0 ≤ T`. -/
theorem zeroCountL_add_one_sub_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {T : ℝ} (hT : 0 ≤ T) :
    (zeroCountL χ (T + 1) : ℝ) - (zeroCountL χ T : ℝ) ≤
      3 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
  have hsub : criticalStripZeroFinset χ (-(T + 1)) (T + 1) ⊆
      criticalStripZeroFinset χ (-T) T ∪
        (criticalStripZeroFinset χ T (T + 1) ∪ criticalStripZeroFinset χ (-(T + 1)) (-T)) := by
    intro ρ hρ
    simp only [Finset.mem_union, mem_criticalStripZeroFinset]
    rw [mem_criticalStripZeroFinset] at hρ
    by_cases hhi : ρ.im ≤ T
    · by_cases hlo : -T ≤ ρ.im
      · exact Or.inl ⟨hρ.1, hρ.2.1, hlo, hhi, hρ.2.2.2.2⟩
      · exact Or.inr (Or.inr ⟨hρ.1, hρ.2.1, hρ.2.2.1, (not_le.mp hlo).le, hρ.2.2.2.2⟩)
    · exact Or.inr (Or.inl ⟨hρ.1, hρ.2.1, (not_le.mp hhi).le, hρ.2.2.2.1, hρ.2.2.2.2⟩)
  have hsum_nat : zeroCountL χ (T + 1) ≤
      zeroCountL χ T +
        (∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ +
         ∑ ρ ∈ criticalStripZeroFinset χ (-(T + 1)) (-T),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) := by
    have h1 := Finset.sum_le_sum_of_subset
      (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) hsub
    have h2 := Finset.sum_union_inter
      (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
      (s₁ := criticalStripZeroFinset χ (-T) T)
      (s₂ := criticalStripZeroFinset χ T (T + 1) ∪ criticalStripZeroFinset χ (-(T + 1)) (-T))
    have h3 := Finset.sum_union_inter
      (f := fun ρ ↦ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
      (s₁ := criticalStripZeroFinset χ T (T + 1)) (s₂ := criticalStripZeroFinset χ (-(T + 1)) (-T))
    change zeroCountL χ (T + 1) ≤ _ at h1
    change _ + _ = zeroCountL χ T + _ at h2
    omega
  have htop := (show (∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) from
    (show (_ : ℝ) ≤ _ by exact_mod_cast sum_order_in_unit_le_zeroCount hχ T).trans
      (zeroCount_LFunction_unit_interval_le hχ T))
  have hbot_unit := (show (∑ ρ ∈ criticalStripZeroFinset χ (-(T + 1)) (-(T + 1) + 1),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|-(T + 1)| + 2)) from
    (show (_ : ℝ) ≤ _ by exact_mod_cast sum_order_in_unit_le_zeroCount hχ (-(T + 1))).trans
      (zeroCount_LFunction_unit_interval_le hχ (-(T + 1))))
  have heq_neg : -(T + 1) + 1 = -T := by ring
  rw [heq_neg] at hbot_unit
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog2 : Real.log ((q : ℝ) * (|-(T + 1)| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|T| + 2)) := by
    have harg : (q : ℝ) * (|-(T + 1)| + 2) ≤ 2 * ((q : ℝ) * (|T| + 2)) := by
      have habs : |-(T + 1)| = T + 1 := by rw [abs_neg, abs_of_nonneg (by linarith)]
      have habsT : |T| = T := abs_of_nonneg hT
      rw [habs, habsT]
      nlinarith
    have hge2 : 2 ≤ (q : ℝ) * (|T| + 2) := by
      have : 2 ≤ |T| + 2 := by linarith [abs_nonneg T]
      nlinarith
    have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|T| + 2)) := Real.log_le_log (by norm_num) hge2
    calc Real.log ((q : ℝ) * (|-(T + 1)| + 2))
        ≤ Real.log (2 * ((q : ℝ) * (|T| + 2))) := Real.log_le_log (by positivity) harg
      _ = Real.log 2 + Real.log ((q : ℝ) * (|T| + 2)) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 2 * Real.log ((q : ℝ) * (|T| + 2)) := by linarith
  have hbot : (∑ ρ ∈ criticalStripZeroFinset χ (-(T + 1)) (-T),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      2 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * (|T| + 2)) := by
    refine hbot_unit.trans ?_
    have hc : 0 < jensenUnitZeroDensityConst := jensenUnitZeroDensityConst_pos
    nlinarith
  have hsum_real : (zeroCountL χ (T + 1) : ℝ) ≤ (zeroCountL χ T : ℝ) +
      ((∑ ρ ∈ criticalStripZeroFinset χ T (T + 1),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) +
       (∑ ρ ∈ criticalStripZeroFinset χ (-(T + 1)) (-T),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) := by
    exact_mod_cast hsum_nat
  linarith

private lemma zeroCountL_nat_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∀ n : ℕ, (zeroCountL χ (n : ℝ) : ℝ) ≤
      3 * jensenUnitZeroDensityConst * ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 2))
  | 0 => by
    have hsub : criticalStripZeroFinset χ (-0) 0 ⊆ criticalStripZeroFinset χ 0 1 := by
      intro ρ hρ
      rw [mem_criticalStripZeroFinset] at hρ ⊢
      exact ⟨hρ.1, hρ.2.1, by linarith, by linarith, hρ.2.2.2.2⟩
    have hnat0 : zeroCountL χ 0 ≤
        zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (0 + 1 / 2 : ℝ) * I) (9 / 4) :=
      (Finset.sum_le_sum_of_subset hsub).trans (by simpa using sum_order_in_unit_le_zeroCount hχ 0)
    have h0 : (zeroCountL χ 0 : ℝ) ≤
        jensenUnitZeroDensityConst * Real.log ((q : ℝ) * 2) := by
      have h1 : (zeroCountL χ 0 : ℝ) ≤
          (zeroCount (DirichletCharacter.LFunction χ) ((2 : ℂ) + (0 + 1 / 2 : ℝ) * I) (9 / 4) : ℝ) := by
        exact_mod_cast hnat0
      have h2 := zeroCount_LFunction_unit_interval_le hχ 0
      simpa using h1.trans h2
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * 2) := Real.log_nonneg (by nlinarith)
    have hc : 0 ≤ jensenUnitZeroDensityConst := jensenUnitZeroDensityConst_pos.le
    simpa using h0.trans (by nlinarith)
  | n + 1 => by
    have hstep := zeroCountL_add_one_sub_le hχ (Nat.cast_nonneg n)
    have hih := zeroCountL_nat_le hχ n
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hq_n2 : (1 : ℝ) ≤ (q : ℝ) * ((n : ℝ) + 2) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hq_n3 : (1 : ℝ) ≤ (q : ℝ) * (((n + 1 : ℕ) : ℝ) + 2) := by
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hlog_mono : Real.log ((q : ℝ) * ((n : ℝ) + 2)) ≤
        Real.log ((q : ℝ) * (((n + 1 : ℕ) : ℝ) + 2)) := by
      refine Real.log_le_log (by linarith) ?_
      push_cast
      nlinarith
    have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [habs] at hstep
    have hc : 0 ≤ jensenUnitZeroDensityConst := jensenUnitZeroDensityConst_pos.le
    have hlog_n2 : 0 ≤ Real.log ((q : ℝ) * ((n : ℝ) + 2)) := Real.log_nonneg hq_n2
    have hlog_n3 : 0 ≤ Real.log ((q : ℝ) * (((n + 1 : ℕ) : ℝ) + 2)) := Real.log_nonneg hq_n3
    have hle1 : (zeroCountL χ ((n + 1 : ℕ) : ℝ) : ℝ) ≤
        (zeroCountL χ (n : ℝ) : ℝ) + 3 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by
      push_cast at hstep ⊢
      linarith
    calc (zeroCountL χ ((n + 1 : ℕ) : ℝ) : ℝ)
        ≤ 3 * jensenUnitZeroDensityConst * ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 2)) +
            3 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by linarith
      _ = 3 * jensenUnitZeroDensityConst * (((n + 1 : ℕ) : ℝ) + 1) *
            Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by push_cast; ring
      _ ≤ 3 * jensenUnitZeroDensityConst * (((n + 1 : ℕ) : ℝ) + 1) *
            Real.log ((q : ℝ) * (((n + 1 : ℕ) : ℝ) + 2)) := by
          gcongr

/-- Global coarse upper bound `N(T, χ) ≤ C * (T + 2) * log (q * (T + 3))` for `0 ≤ T` (`χ ≠ 1`). -/
theorem zeroCountL_le_mul_log {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (zeroCountL χ T : ℝ) ≤
      3 * jensenUnitZeroDensityConst * (T + 2) * Real.log ((q : ℝ) * (T + 3)) := by
  let n : ℕ := Nat.ceil T
  have hTn : T ≤ n := Nat.le_ceil T
  have hnT : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
  have hmono : (zeroCountL χ T : ℝ) ≤ (zeroCountL χ n : ℝ) := by
    exact_mod_cast zeroCountL_mono χ hTn
  have hnat := zeroCountL_nat_le hχ n
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq_n2 : (1 : ℝ) ≤ (q : ℝ) * ((n : ℝ) + 2) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hlog_n2 : 0 ≤ Real.log ((q : ℝ) * ((n : ℝ) + 2)) := Real.log_nonneg hq_n2
  have hlog_mono : Real.log ((q : ℝ) * ((n : ℝ) + 2)) ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_le_log (by linarith) ?_
    nlinarith
  have hc : 0 ≤ jensenUnitZeroDensityConst := jensenUnitZeroDensityConst_pos.le
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 3)) :=
    Real.log_nonneg (by nlinarith)
  calc (zeroCountL χ T : ℝ) ≤ (zeroCountL χ n : ℝ) := hmono
    _ ≤ 3 * jensenUnitZeroDensityConst * ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 2)) := hnat
    _ ≤ 3 * jensenUnitZeroDensityConst * (T + 2) * Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hlog_n2
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 3 * jensenUnitZeroDensityConst * (T + 2) * Real.log ((q : ℝ) * (T + 3)) := by
        refine mul_le_mul_of_nonneg_left hlog_mono (by positivity)

/-- Unconditional bound on the vertical `Re s = 2` L-series argument-variation integral:
`|∫ t in a..b, (logDeriv (LFunction χ) (2 + t * I)).re| ≤ π` for all `χ` and `a ≤ b`. -/
theorem integral_re_logDeriv_LFunction_two_add_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {a b : ℝ} (_hab : a ≤ b) :
    |∫ t in a..b, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re| ≤
      Real.pi := by
  let γ : ℝ → ℂ := fun t ↦ (2 : ℂ) + (t : ℂ) * I
  let g : ℝ → ℂ := fun t ↦ DirichletCharacter.LFunction χ (γ t)
  have hg_re_pos : ∀ t : ℝ, 0 < (g t).re := fun t ↦ re_LFunction_two_add_pos χ t
  have hg_slit : ∀ t : ℝ, g t ∈ Complex.slitPlane :=
    fun t ↦ Complex.mem_slitPlane_iff.mpr (Or.inl (hg_re_pos t))
  have hγ_ne1 : ∀ t : ℝ, γ t ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp [γ] at this
  have hL_ana_open : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 1 < z.re} := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd ?_ hopen
    intro z hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz1)).differentiableWithinAt
  have hderiv_cont : Continuous (fun t : ℝ ↦ (logDeriv (DirichletCharacter.LFunction χ) (γ t)).re) := by
    have hγ_cont : Continuous γ := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hγ_mem : ∀ t : ℝ, γ t ∈ {z : ℂ | 1 < z.re} := fun t ↦ by simp [γ]
    have hL_cont : Continuous (fun t : ℝ ↦ DirichletCharacter.LFunction χ (γ t)) :=
      (hL_ana_open.continuousOn.comp_continuous hγ_cont hγ_mem)
    have hLd_cont : Continuous (fun t : ℝ ↦ deriv (DirichletCharacter.LFunction χ) (γ t)) :=
      (hL_ana_open.deriv.continuousOn.comp_continuous hγ_cont hγ_mem)
    have hg_ne0 : ∀ t : ℝ, g t ≠ 0 := fun t h ↦ by have := hg_re_pos t; simp [g, h] at this
    refine Complex.continuous_re.comp (Continuous.div hLd_cont hL_cont hg_ne0)
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (logDeriv (DirichletCharacter.LFunction χ) (γ t)).re) volume a b :=
    hderiv_cont.intervalIntegrable a b
  have hftoc : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ ↦ (Complex.log (g u)).im)
        (logDeriv (DirichletCharacter.LFunction χ) (γ t)).re t := by
    intro t _
    have hγ_deriv : HasDerivAt γ I t := by
      have h1 : HasDerivAt (fun u : ℝ ↦ (u : ℂ) * I) I t := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const I
      simpa [γ] using h1.const_add (2 : ℂ)
    have hL_deriv : HasDerivAt (DirichletCharacter.LFunction χ)
        (deriv (DirichletCharacter.LFunction χ) (γ t)) (γ t) :=
      (DirichletCharacter.differentiableAt_LFunction χ (γ t) (Or.inl (hγ_ne1 t))).hasDerivAt
    have hg_deriv : HasDerivAt g (deriv (DirichletCharacter.LFunction χ) (γ t) * I) t :=
      hL_deriv.comp t hγ_deriv
    have hlog_deriv : HasDerivAt (fun u : ℝ ↦ Complex.log (g u))
        ((g t)⁻¹ * (deriv (DirichletCharacter.LFunction χ) (γ t) * I)) t :=
      (Complex.hasDerivAt_log (hg_slit t)).comp t hg_deriv
    have him_deriv : HasDerivAt (fun u : ℝ ↦ (Complex.log (g u)).im)
        (Complex.imCLM ((g t)⁻¹ * (deriv (DirichletCharacter.LFunction χ) (γ t) * I))) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog_deriv
    refine him_deriv.congr_deriv ?_
    have heq : (g t)⁻¹ * (deriv (DirichletCharacter.LFunction χ) (γ t) * I) =
        logDeriv (DirichletCharacter.LFunction χ) (γ t) * I := by
      rw [logDeriv_apply]
      change (g t)⁻¹ * (deriv (DirichletCharacter.LFunction χ) (γ t) * I) =
        (deriv (DirichletCharacter.LFunction χ) (γ t) / g t) * I
      ring
    simp only [Complex.imCLM_apply]
    rw [heq]
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftoc hint]
  have harg_le : ∀ t : ℝ, |(Complex.log (g t)).im| ≤ Real.pi / 2 := by
    intro t
    rw [Complex.log_im]
    exact (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hg_re_pos t))).le
  calc |(Complex.log (g b)).im - (Complex.log (g a)).im|
      ≤ |(Complex.log (g b)).im| + |(Complex.log (g a)).im| := abs_sub _ _
    _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add (harg_le b) (harg_le a)
    _ = Real.pi := by ring

private lemma stirling_log_half_integral {T : ℝ} (hT : 2 ≤ T) :
    ∫ t in (2 : ℝ)..T, Real.log (t / 2) = T * Real.log (T / (2 * Real.exp 1)) + 2 := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ Real.log (t / 2)) volume 2 T := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    have ht_pos : t ≠ 0 := by
      have : t ∈ Set.Icc (2 : ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
      linarith [this.1]
    exact ((continuousAt_id.div_const 2).log (div_ne_zero ht_pos two_ne_zero)).continuousWithinAt
  have hftoc : ∀ t ∈ Set.uIcc (2 : ℝ) T,
      HasDerivAt (fun x : ℝ ↦ x * Real.log (x / 2) - x) (Real.log (t / 2)) t := by
    intro t ht
    have ht_pos : 0 < t := by
      have : t ∈ Set.Icc (2 : ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
      linarith [this.1]
    have hdiv : HasDerivAt (fun x : ℝ ↦ x / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const (2 : ℝ)
    have hlog : HasDerivAt (fun x : ℝ ↦ Real.log (x / 2)) ((1 / 2) / (t / 2)) t :=
      hdiv.log (by positivity : t / 2 ≠ 0)
    have hmul : HasDerivAt (fun x : ℝ ↦ x * Real.log (x / 2))
        (1 * Real.log (t / 2) + t * ((1 / 2) / (t / 2))) t :=
      (hasDerivAt_id t).mul hlog
    have hsub := hmul.sub (hasDerivAt_id t)
    refine hsub.congr_deriv ?_
    field_simp [ht_pos.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftoc hint]
  have hT_pos : 0 < T := by linarith
  have hlog2 : Real.log (2 / 2 : ℝ) = 0 := by norm_num
  have hlog_eq : Real.log (T / (2 * Real.exp 1)) = Real.log (T / 2) - 1 := by
    rw [show T / (2 * Real.exp 1) = (T / 2) / Real.exp 1 by ring,
      Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  rw [hlog2, hlog_eq]
  ring

private lemma digamma_strip_continuous (a : ℝ) (ha : 1 ≤ a) :
    Continuous (fun t : ℝ ↦ (AnalyticTools.Gamma.digamma ((a : ℂ) + (t / 2 : ℝ) * I)).re) := by
  refine Complex.continuous_re.comp ?_
  rw [continuous_iff_continuousAt]
  intro t
  have hnopole : ∀ m : ℕ, (a : ℂ) + ((t / 2 : ℝ) : ℂ) * I ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hd : DifferentiableAt ℂ AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I) :=
    AnalyticTools.Gamma.differentiableAt_digamma hnopole
  have hc_inner : Continuous (fun u : ℝ ↦ (a : ℂ) + ((u / 2 : ℝ) : ℂ) * I) :=
    continuous_const.add ((Complex.continuous_ofReal.comp (continuous_id.div_const 2)).mul continuous_const)
  exact ContinuousAt.comp (g := AnalyticTools.Gamma.digamma) hd.continuousAt hc_inner.continuousAt

private lemma stirling_digamma_tail_error (a : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 3 / 2)
    (t : ℝ) (ht : 2 ≤ |t|) :
    ‖AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I) -
        Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤
      (1 + 2 * (1 + 8 * ((3 / 2 : ℝ) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) / |t| := by
  have ht2 : 1 ≤ |t / 2| := by
    rw [abs_div, abs_two]
    linarith
  have hstrip := norm_digamma_sub_log_strip_le (σ₁ := 1) (σ₂ := 3 / 2) (σ := a) (t := t / 2)
    ⟨ha1, ha2⟩ ht2
  have hmax : max |(1 : ℝ)| |(3 / 2 : ℝ)| = 3 / 2 := by
    norm_num
  rw [hmax] at hstrip
  refine hstrip.trans_eq ?_
  rw [abs_div, abs_two]
  ring

private lemma log_norm_strip_sub_log_half (a : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 3 / 2)
    (t : ℝ) (ht : 2 ≤ |t|) :
    |(Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re - Real.log (|t| / 2)| ≤ 9 / (2 * |t|) := by
  have ht0 : 0 < |t| := by linarith
  rw [Complex.log_re]
  have hnorm_sq : ‖(a : ℂ) + ((t / 2 : ℝ) : ℂ) * I‖ = Real.sqrt (a ^ 2 + (t / 2) ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp
  rw [hnorm_sq]
  have hpos_sq : 0 < a ^ 2 + (t / 2) ^ 2 := by positivity
  have hhalf : Real.log (Real.sqrt (a ^ 2 + (t / 2) ^ 2)) =
      (1 / 2) * Real.log (a ^ 2 + (t / 2) ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hpos_sq]
  rw [hhalf]
  have ht_ne : t ≠ 0 := by intro h; simp [h] at ht; norm_num at ht
  have ht2_pos : 0 < (t / 2) ^ 2 := sq_pos_of_ne_zero (div_ne_zero ht_ne two_ne_zero)
  have hfactor : a ^ 2 + (t / 2) ^ 2 = (|t| / 2) ^ 2 * (1 + (2 * a / t) ^ 2) := by
    have htsq : |t| ^ 2 = t ^ 2 := sq_abs t
    calc a ^ 2 + (t / 2) ^ 2 = a ^ 2 + t ^ 2 / 4 := by ring
      _ = (t ^ 2 / 4) * (1 + (2 * a / t) ^ 2) := by field_simp; ring
      _ = (|t| / 2) ^ 2 * (1 + (2 * a / t) ^ 2) := by
          rw [show (|t| / 2) ^ 2 = t ^ 2 / 4 by rw [div_pow, htsq]; norm_num]
  rw [hfactor, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  simp only [Nat.cast_ofNat]
  have hdiff : (1 / 2 : ℝ) * (2 * Real.log (|t| / 2) + Real.log (1 + (2 * a / t) ^ 2)) -
      Real.log (|t| / 2) = (1 / 2) * Real.log (1 + (2 * a / t) ^ 2) := by ring
  rw [hdiff]
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + (2 * a / t) ^ 2) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [sq_nonneg (2 * a / t)]))
  rw [abs_of_nonneg hnonneg]
  have hlog1 : Real.log (1 + (2 * a / t) ^ 2) ≤ (2 * a / t) ^ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (2 * a / t) ^ 2)]
  have hsq_bd : (2 * a / t) ^ 2 ≤ 9 / |t| := by
    have h2a : (2 * a) ^ 2 ≤ 9 := by nlinarith
    have htsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have htabs2 : 2 * |t| ≤ |t| ^ 2 := by nlinarith
    calc (2 * a / t) ^ 2 = (2 * a) ^ 2 / t ^ 2 := by ring
      _ ≤ 9 / |t| ^ 2 := by rw [htsq]; exact div_le_div_of_nonneg_right h2a (by positivity)
      _ ≤ 9 / |t| := div_le_div_of_nonneg_left (by norm_num) ht0 (by nlinarith)
  have h9 : (1 / 2 : ℝ) * (9 / |t|) = 9 / (2 * |t|) := by ring
  linarith

/-- Unconditional Stirling asymptotic for the symmetric `digamma` vertical-line integral
on `Re s = a ∈ [1, 3 / 2]` (uniform in `a ∈ [1, 3 / 2]`, hence uniform in `q` and `χ`). -/
theorem integral_re_digamma_half_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), a ∈ Icc (1 : ℝ) (3 / 2) → ∀ T : ℝ, 2 ≤ T →
      |(∫ t in (-T)..T, (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) -
          2 * (T * Real.log (T / (2 * Real.exp 1)))| ≤ C * Real.log (T + 2) := by
  let K : Set (ℝ × ℝ) := Icc (1 : ℝ) (3 / 2) ×ˢ Icc (-2 : ℝ) 2
  have hK_cpt : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_cont : ContinuousOn
      (fun p : ℝ × ℝ ↦ (AnalyticTools.Gamma.digamma ((p.1 : ℂ) + ((p.2 / 2 : ℝ) : ℂ) * I)).re) K := by
    intro p hp
    have hnopole : ∀ m : ℕ, (p.1 : ℂ) + ((p.2 / 2 : ℝ) : ℂ) * I ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      linarith [hp.1.1]
    have hd : ContinuousAt AnalyticTools.Gamma.digamma ((p.1 : ℂ) + ((p.2 / 2 : ℝ) : ℂ) * I) :=
      (AnalyticTools.Gamma.differentiableAt_digamma hnopole).continuousAt
    have hinner : Continuous (fun q : ℝ × ℝ ↦ (q.1 : ℂ) + ((q.2 / 2 : ℝ) : ℂ) * I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp (continuous_snd.div_const 2)).mul continuous_const)
    have hcomp : ContinuousAt
        (fun q : ℝ × ℝ ↦ AnalyticTools.Gamma.digamma ((q.1 : ℂ) + ((q.2 / 2 : ℝ) : ℂ) * I)) p :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ ↦ (q.1 : ℂ) + ((q.2 / 2 : ℝ) : ℂ) * I)
        (g := AnalyticTools.Gamma.digamma) hd hinner.continuousAt
    exact (Complex.continuous_re.continuousAt.comp hcomp).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hK_cpt.exists_bound_of_continuousOn hK_cont
  let M_mid : ℝ := max M₀ 0
  let C_err : ℝ := (1 + 2 * (1 + 8 * ((3 / 2 : ℝ) ^ 2 + 1) ^ (3 / 2 : ℝ)) / 12) + 9 / 2
  have hC_err_pos : 0 ≤ C_err := by positivity
  let C : ℝ := 4 * M_mid + 2 * C_err + 6
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun a ha T hT ↦ ?_⟩
  let f : ℝ → ℝ := fun t ↦ (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
  have hf_cont : Continuous f := digamma_strip_continuous a ha.1
  have hsplit : ∫ t in (-T)..T, f t =
      (∫ t in (-T)..(-2 : ℝ), f t) + (∫ t in (-2 : ℝ)..(2 : ℝ), f t) + (∫ t in (2 : ℝ)..T, f t) := by
    have hi1 : IntervalIntegrable f volume (-T) (-2) := hf_cont.intervalIntegrable _ _
    have hi2 : IntervalIntegrable f volume (-2) 2 := hf_cont.intervalIntegrable _ _
    have hi3 : IntervalIntegrable f volume 2 T := hf_cont.intervalIntegrable _ _
    calc ∫ t in (-T)..T, f t
        = (∫ t in (-T)..(2 : ℝ), f t) + (∫ t in (2 : ℝ)..T, f t) :=
          (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
      _ = (∫ t in (-T)..(-2 : ℝ), f t) + (∫ t in (-2 : ℝ)..(2 : ℝ), f t) + (∫ t in (2 : ℝ)..T, f t) := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hmid_bd : |∫ t in (-2 : ℝ)..(2 : ℝ), f t| ≤ 4 * M_mid := by
    have hle : ∀ t ∈ Set.uIoc (-2 : ℝ) 2, ‖f t‖ ≤ M_mid := by
      intro t ht
      have ht' : t ∈ Icc (-2 : ℝ) 2 := by
        have := Set.uIoc_subset_uIcc ht
        simpa using this
      exact (hM₀ (a, t) ⟨ha, ht'⟩).trans (le_max_left _ _)
    have hnb := intervalIntegral.norm_integral_le_of_norm_le_const hle
    simpa [Real.norm_eq_abs] using hnb.trans_eq (by norm_num; ring)
  have htail_pt : ∀ t : ℝ, 2 ≤ |t| → |f t - Real.log (|t| / 2)| ≤ C_err / |t| := by
    intro t ht
    have h1 := stirling_digamma_tail_error a ha.1 ha.2 t ht
    have h2 := log_norm_strip_sub_log_half a ha.1 ha.2 t ht
    have hre_sub : |f t - (Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re| ≤
        ‖AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I) -
          Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
      simpa [f, Complex.sub_re] using
        Complex.abs_re_le_norm (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I) -
          Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I))
    calc |f t - Real.log (|t| / 2)|
        ≤ |f t - (Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re| +
            |(Complex.log ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re - Real.log (|t| / 2)| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hre_sub.trans h1) h2
      _ = C_err / |t| := by simp only [C_err]; ring
  have hpos_bd : |(∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)| ≤
      C_err * Real.log T := by
    rw [← stirling_log_half_integral hT]
    have hif : IntervalIntegrable f volume 2 T := hf_cont.intervalIntegrable _ _
    have hilog : IntervalIntegrable (fun t : ℝ ↦ Real.log (t / 2)) volume 2 T := by
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
      have ht' : t ∈ Icc (2 : ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
      have ht_pos : (t : ℝ) ≠ 0 := by linarith [ht'.1]
      exact (((continuous_id.div_const 2).continuousAt).log
        (show (id t / 2) ≠ 0 from div_ne_zero (by change t ≠ 0; linarith [ht'.1]) two_ne_zero)).continuousWithinAt
    rw [← intervalIntegral.integral_sub hif hilog]
    have hinv_int : IntervalIntegrable (fun t : ℝ ↦ C_err / t) volume 2 T := by
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
      have ht' : t ∈ Icc (2 : ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
      exact (continuousAt_const.div continuousAt_id (by change t ≠ 0; linarith [ht'.1])).continuousWithinAt
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.Ioc (2 : ℝ) T → ‖f t - Real.log (t / 2)‖ ≤ C_err / t := by
      refine ae_of_all _ fun t ht ↦ ?_
      have ht2 : 2 ≤ t := ht.1.le
      have h1 := htail_pt t (by rw [abs_of_nonneg (by linarith)]; exact ht2)
      rw [Real.norm_eq_abs]
      simpa only [abs_of_nonneg (by linarith : 0 ≤ t)] using h1
    have hle := intervalIntegral.norm_integral_le_of_norm_le hT hbound hinv_int
    have hinv_val : ∫ t in (2 : ℝ)..T, C_err / t = C_err * (Real.log T - Real.log 2) := by
      have : (fun t : ℝ ↦ C_err / t) = (fun t : ℝ ↦ C_err * t⁻¹) := by ext t; ring
      rw [this, intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < T),
        Real.log_div (by linarith) (by norm_num)]
    rw [Real.norm_eq_abs, hinv_val] at hle
    have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact hle.trans (by nlinarith)
  have hneg_bd : |(∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)| ≤
      C_err * Real.log T := by
    have hint_neg : ∫ t in (-T)..(-2 : ℝ), Real.log (|t| / 2) =
        T * Real.log (T / (2 * Real.exp 1)) + 2 := by
      rw [← intervalIntegral.integral_comp_neg (fun t : ℝ ↦ Real.log (|t| / 2))]
      simp only [abs_neg]
      rw [intervalIntegral.integral_congr (fun t ht ↦ by
        have ht' : t ∈ Icc (2 : ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
        rw [abs_of_nonneg (by linarith [ht'.1])])]
      exact stirling_log_half_integral hT
    rw [← hint_neg]
    have hif : IntervalIntegrable f volume (-T) (-2) := hf_cont.intervalIntegrable _ _
    have hilog : IntervalIntegrable (fun t : ℝ ↦ Real.log (|t| / 2)) volume (-T) (-2) := by
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
      have ht' : t ∈ Icc (-T) (-2 : ℝ) := by simpa [Set.uIcc_of_le (by linarith : -T ≤ -2)] using ht
      have htabs : 2 ≤ |t| := by rw [abs_of_nonpos (by linarith [ht'.2])]; linarith [ht'.2]
      exact (((continuous_abs.div_const 2).continuousAt).log
        (div_ne_zero (by linarith) two_ne_zero)).continuousWithinAt
    rw [← intervalIntegral.integral_sub hif hilog]
    have hinv_int : IntervalIntegrable (fun t : ℝ ↦ C_err / (-t)) volume (-T) (-2) := by
      refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
      have ht' : t ∈ Icc (-T) (-2 : ℝ) := by simpa [Set.uIcc_of_le (by linarith : -T ≤ -2)] using ht
      exact (continuousAt_const.div continuous_id.neg.continuousAt
        (show (-id) t ≠ 0 by dsimp; linarith [ht'.2])).continuousWithinAt
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.Ioc (-T) (-2 : ℝ) → ‖f t - Real.log (|t| / 2)‖ ≤ C_err / (-t) := by
      refine ae_of_all _ fun t ht ↦ ?_
      have htn : t ≤ -2 := ht.2
      have h1 := htail_pt t (by rw [abs_of_nonpos (by linarith)]; linarith)
      rw [Real.norm_eq_abs]
      simpa only [abs_of_nonpos (by linarith : t ≤ 0)] using h1
    have hle := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ -2) hbound hinv_int
    have hinv_val : ∫ t in (-T)..(-2 : ℝ), C_err / (-t) = C_err * (Real.log T - Real.log 2) := by
      rw [← intervalIntegral.integral_comp_neg (fun t : ℝ ↦ C_err / (-t))]
      simp only [neg_neg]
      have : (fun t : ℝ ↦ C_err / t) = (fun t : ℝ ↦ C_err * t⁻¹) := by ext t; ring
      rw [this, intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by linarith : (0 : ℝ) < T),
        Real.log_div (by linarith) (by norm_num)]
    rw [Real.norm_eq_abs, hinv_val] at hle
    have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact hle.trans (by nlinarith)
  have hlogT : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlog_ge1 : 1 ≤ Real.log (T + 2) := by
    have h4 : (4 : ℝ) ≤ T + 2 := by linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlt4 : 1 < Real.log 4 := by linarith [Real.log_two_gt_d9]
    exact hlt4.le.trans (Real.log_le_log (by norm_num) h4)
  change |(∫ t in (-T)..T, f t) - 2 * (T * Real.log (T / (2 * Real.exp 1)))| ≤ C * Real.log (T + 2)
  rw [hsplit]
  have hdiff_eq : ((∫ t in (-T)..(-2 : ℝ), f t) + (∫ t in (-2 : ℝ)..(2 : ℝ), f t) +
      (∫ t in (2 : ℝ)..T, f t)) - 2 * (T * Real.log (T / (2 * Real.exp 1))) =
      ((∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)) +
        ((∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)) +
        ((∫ t in (-2 : ℝ)..(2 : ℝ), f t) + 4) := by ring
  rw [hdiff_eq]
  calc |((∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)) +
          ((∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)) +
          ((∫ t in (-2 : ℝ)..(2 : ℝ), f t) + 4)|
      ≤ |(∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)| +
          |(∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)| +
          (|∫ t in (-2 : ℝ)..(2 : ℝ), f t| + 4) := by
          linarith [abs_add_le
            (((∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)) +
              ((∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)))
            ((∫ t in (-2 : ℝ)..(2 : ℝ), f t) + 4),
            abs_add_le
              ((∫ t in (-T)..(-2 : ℝ), f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2))
              ((∫ t in (2 : ℝ)..T, f t) - (T * Real.log (T / (2 * Real.exp 1)) + 2)),
            abs_add_le (∫ t in (-2 : ℝ)..(2 : ℝ), f t) (4 : ℝ),
            show |(4 : ℝ)| = 4 by norm_num]
    _ ≤ C_err * Real.log T + C_err * Real.log T + (4 * M_mid + 4) := by gcongr
    _ ≤ C_err * Real.log (T + 2) + C_err * Real.log (T + 2) +
          (4 * M_mid + 6) * Real.log (T + 2) := by
          have h46 : 4 * M_mid + 4 ≤ (4 * M_mid + 6) * Real.log (T + 2) := by
            have hM0' : 0 ≤ M_mid := le_max_right _ _
            nlinarith
          gcongr
    _ = C * Real.log (T + 2) := by simp only [C]; ring

/-- `parityExp χ` is always `≤ 1` (`0` for even `χ`, `1` for odd `χ`). -/
lemma parityExp_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    parityExp χ ≤ 1 := by
  have hsq : (χ (-1 : ZMod q)) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  rcases sq_eq_one_iff.mp hsq with he | ho
  · rw [parityExp_of_even he]; norm_num
  · rw [parityExp_of_odd ho]

/-- Unconditional Stirling asymptotic for the right-edge (`Re s = 2`) logarithmic derivative of
`completedLFunction χ`:
`(1 / (2 * π)) * (∫_{-T}^T Re (logDeriv (completedLFunction χ) (2 + t * I)) dt) = (T / (2 * π)) * log (T / (2 * π * e)) + O(log (T + 2))`. -/
theorem integral_re_logDeriv_completedLFunction_two_add_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ), 2 ≤ T →
      |(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) -
          (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log (T + 2) := by
  obtain ⟨C_dig, hC_dig0, hdig⟩ := integral_re_digamma_half_asymptotic
  let C : ℝ := C_dig / (4 * Real.pi) + 1
  refine ⟨C, by positivity, fun {q} _ χ T hT ↦ ?_⟩
  let a : ℝ := 1 + (parityExp χ : ℝ) / 2
  have ha_mem : a ∈ Icc (1 : ℝ) (3 / 2) := by
    have hpe : (parityExp χ : ℝ) ≤ 1 := by exact_mod_cast parityExp_le_one χ
    exact ⟨by simp [a]; positivity, by simp [a]; linarith⟩
  have hq2_fake : ∀ t : ℝ,
      (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re =
        (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re +
          (-(1 / 2 : ℝ) * Real.log Real.pi +
            (1 / 2 : ℝ) * (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) := by
    intro t
    have hs1 : χ ≠ 1 ∨ (2 : ℂ) + (t : ℂ) * I ≠ 1 := Or.inr fun h ↦ by
      have := congrArg Complex.re h
      simp at this
    have hLs : DirichletCharacter.LFunction χ ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h0
      have := re_LFunction_two_add_pos χ t
      simp [h0] at this
    have hGs : DirichletCharacter.gammaFactor χ ((2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
      gammaFactor_ne_zero_of_re_pos χ (by simp)
    have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 ((2 : ℂ) + (t : ℂ) * I)]
        DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ := by
      have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (by simp : 0 < ((2 : ℂ) + (t : ℂ) * I).re)] with w hw
      have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
      exact completedLFunction_eq_mul_gammaFactor χ (Or.inl hw0)
        (gammaFactor_ne_zero_of_re_pos χ hw)
    have hL_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I) :=
      DirichletCharacter.differentiableAt_LFunction χ _ hs1.symm
    have hG_diff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + (t : ℂ) * I) := by
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have heq : DirichletCharacter.gammaFactor χ =
          fun w ↦ (Real.pi : ℂ) ^ (-(w + (parityExp χ : ℂ)) / 2) *
            Complex.Gamma ((w + (parityExp χ : ℂ)) / 2) := by
        ext w; exact gammaFactor_eq_pi_mul_Gamma χ w
      rw [heq]
      refine DifferentiableAt.mul ?_ ?_
      · exact (((differentiableAt_id.add (differentiableAt_const _)).neg.div_const 2).const_cpow
          (Or.inl hpi_ne))
      · refine (Complex.differentiableAt_Gamma _ fun m hm ↦ ?_).comp _
          ((differentiableAt_id.add (differentiableAt_const _)).div_const 2)
        have hre := congrArg Complex.re hm
        simp at hre
        have : (0 : ℝ) ≤ parityExp χ := Nat.cast_nonneg _
        linarith
    have hsplit := (logDeriv_congr_nhds hev).eq_of_nhds
    rw [hsplit, logDeriv_mul _ hLs hGs hL_diff hG_diff, logDeriv_gammaFactor_eq χ hGs]
    have harg_eq : ((2 : ℂ) + (t : ℂ) * I + (parityExp χ : ℂ)) / 2 =
        (a : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      simp only [a, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast, Complex.ofReal_ofNat]
      ring
    rw [harg_eq]
    simp
  have hint_eq : ∫ t in (-T)..T,
      (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re =
      ∫ t in (-T)..T,
        ((logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re +
          (-(1 / 2 : ℝ) * Real.log Real.pi +
            (1 / 2 : ℝ) * (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)) :=
    intervalIntegral.integral_congr (fun t _ ↦ hq2_fake t)
  rw [hint_eq]
  have hi_L : IntervalIntegrable
      (fun t : ℝ ↦ (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re)
      volume (-T) T := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hL_ana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 1 < z.re} :=
      DifferentiableOn.analyticOnNhd
        (fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z
          (Or.inl fun h ↦ by simp [h] at hz)).differentiableWithinAt)
        hopen
    have hγ_cont : Continuous (fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hγ_mem : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ∈ {z : ℂ | 1 < z.re} := fun t ↦ by simp
    have hcont : Continuous
        (fun t : ℝ ↦ (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) :=
      Complex.continuous_re.comp <| Continuous.div
        (hL_ana.deriv.continuousOn.comp_continuous hγ_cont hγ_mem)
        (hL_ana.continuousOn.comp_continuous hγ_cont hγ_mem)
        fun t h0 ↦ by have := re_LFunction_two_add_pos χ t; simp [h0] at this
    exact hcont.intervalIntegrable _ _
  have hi_G : IntervalIntegrable
      (fun t : ℝ ↦ -(1 / 2 : ℝ) * Real.log Real.pi +
        (1 / 2 : ℝ) * (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
      volume (-T) T :=
    (continuous_const.add (continuous_const.mul (digamma_strip_continuous a ha_mem.1))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi_L hi_G]
  have hi_dig : IntervalIntegrable
      (fun t : ℝ ↦ (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
      volume (-T) T := (digamma_strip_continuous a ha_mem.1).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (hi_dig.const_mul (1 / 2)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  have hpi_alg : (1 / (2 * Real.pi)) * ((T - -T) • (-(1 / 2 : ℝ) * Real.log Real.pi) +
      (1 / 2 : ℝ) * (2 * (T * Real.log (T / (2 * Real.exp 1))))) -
      (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) = 0 := by
    have hlog_pi : Real.log (T / (2 * Real.pi * Real.exp 1)) =
        Real.log (T / (2 * Real.exp 1)) - Real.log Real.pi := by
      rw [show T / (2 * Real.pi * Real.exp 1) = (T / (2 * Real.exp 1)) / Real.pi by ring,
        Real.log_div (by positivity) Real.pi_ne_zero]
    rw [smul_eq_mul, hlog_pi]
    field_simp [Real.pi_ne_zero]
    ring
  have hL_bd := integral_re_logDeriv_LFunction_two_add_le χ (by linarith : -T ≤ T)
  have hdig_bd := hdig a ha_mem T hT
  have hlog4 : 1 ≤ Real.log (T + 2) := by
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlt4 : 1 < Real.log 4 := by linarith [Real.log_two_gt_d9]
    exact hlt4.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hrew : (1 / (2 * Real.pi)) *
        ((∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
          ((T - -T) • (-(1 / 2 : ℝ) * Real.log Real.pi) +
            (1 / 2 : ℝ) * (∫ t in (-T)..T,
              (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re))) -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) =
      (1 / (2 * Real.pi)) *
          (∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
        (1 / (4 * Real.pi)) *
          ((∫ t in (-T)..T, (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) -
            2 * (T * Real.log (T / (2 * Real.exp 1)))) := by
    linear_combination hpi_alg
  rw [hrew]
  calc |(1 / (2 * Real.pi)) *
          (∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
        (1 / (4 * Real.pi)) *
          ((∫ t in (-T)..T, (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) -
            2 * (T * Real.log (T / (2 * Real.exp 1))))|
      ≤ (1 / (2 * Real.pi)) *
          |∫ t in (-T)..T, (logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re| +
        (1 / (4 * Real.pi)) *
          |(∫ t in (-T)..T, (AnalyticTools.Gamma.digamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) -
            2 * (T * Real.log (T / (2 * Real.exp 1)))| := by
          calc _ ≤ _ := abs_add_le _ _
            _ = _ := by
                rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
                  abs_of_pos (by positivity : 0 < 1 / (4 * Real.pi))]
    _ ≤ (1 / (2 * Real.pi)) * Real.pi + (1 / (4 * Real.pi)) * (C_dig * Real.log (T + 2)) := by
        gcongr
    _ = 1 / 2 + (C_dig / (4 * Real.pi)) * Real.log (T + 2) := by
        field_simp [Real.pi_ne_zero]
    _ ≤ C * Real.log (T + 2) := by
        have : 1 / 2 ≤ 1 * Real.log (T + 2) := by linarith
        simp only [C]
        nlinarith

/-- Unconditional combined main-term asymptotic for the right and reflected-left vertical edges
in Riemann–von Mangoldt:
`I_right + I_left + (T / π) * log q = (T / π) * log (q * T / (2 * π * exp 1)) + O(log (T + 2))`. -/
theorem rvm_vertical_edges_main_term_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ), 2 ≤ T →
      |((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re)) +
        ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re)) +
        (T / Real.pi) * Real.log (q : ℝ) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log (T + 2) := by
  obtain ⟨C₁, hC₁0, hbd⟩ := integral_re_logDeriv_completedLFunction_two_add_asymptotic
  refine ⟨2 * C₁, by positivity, fun {q} _ χ T hT ↦ ?_⟩
  have h1 := hbd χ T hT
  have h2 := hbd (star χ) T hT
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog_alg : (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      2 * ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) +
        (T / Real.pi) * Real.log (q : ℝ) := by
    have heq : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) =
        (q : ℝ) * (T / (2 * Real.pi * Real.exp 1)) := by ring
    rw [heq, Real.log_mul hq0.ne' (by positivity)]
    ring
  rw [hlog_alg]
  have hrew : ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re)) +
      ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re)) +
      (T / Real.pi) * Real.log (q : ℝ) -
      (2 * ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) +
        (T / Real.pi) * Real.log (q : ℝ)) =
      ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) +
      ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) := by ring
  rw [hrew]
  exact (abs_add_le _ _).trans (by linarith)

/-- Rectangular contour argument-principle and horizontal argument-variation hypothesis bundle for
`completedLFunction χ` on `[-1, 2] × [-T, T]`, isolating the planar contour argument principle
for heights `T ≥ 2` free of critical-strip zeros on `Im ρ = ±T`. -/
structure RiemannVonMangoldtContourHypothesis {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Type where
  /-- Nonnegative constant controlling the horizontal-edge argument variation. -/
  horConst : ℝ
  /-- Proof that `horConst` is nonnegative. -/
  horConst_nonneg : 0 ≤ horConst
  /-- Rectangular argument-principle identity + horizontal variation bound at zero-free heights
  `T ≥ 2` (`∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ T ∧ ρ.im ≠ -T`). -/
  contour_bound : ∀ T : ℝ, 2 ≤ T →
    (∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ T ∧ ρ.im ≠ -T) →
    |(zeroCountL χ T : ℝ) -
      (((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
       ((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) +
       (T / Real.pi) * Real.log (q : ℝ))| ≤ horConst * Real.log ((q : ℝ) * T)

/-- Riemann–von Mangoldt asymptotic at zero-free heights `T ≥ 2` assuming
`RiemannVonMangoldtContourHypothesis χ`. -/
theorem zeroCountL_asymptotic_of_zeroFreeHeight {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (H : RiemannVonMangoldtContourHypothesis χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      (∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ T ∧ ρ.im ≠ -T) →
      |(zeroCountL χ T : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log ((q : ℝ) * T) := by
  obtain ⟨C_v, hC_v0, hv⟩ := rvm_vertical_edges_main_term_asymptotic
  refine ⟨H.horConst + 2 * C_v, by linarith [H.horConst_nonneg], fun T hT hzfree ↦ ?_⟩
  have h1 := H.contour_bound T hT hzfree
  have h2 := hv χ T hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog_T : Real.log (T + 2) ≤ 2 * Real.log ((q : ℝ) * T) := by
    have hT2 : T + 2 ≤ 2 * T := by linarith
    have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
    have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hqT
    have hTlqT : Real.log T ≤ Real.log ((q : ℝ) * T) :=
      Real.log_le_log (by linarith) (by nlinarith)
    calc Real.log (T + 2) ≤ Real.log (2 * T) := Real.log_le_log (by positivity) hT2
      _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log ((q : ℝ) * T) := by linarith
  have hsum := abs_add_le
    ((zeroCountL χ T : ℝ) -
      (((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
       ((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) +
       (T / Real.pi) * Real.log (q : ℝ)))
    ((((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
       ((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) +
       (T / Real.pi) * Real.log (q : ℝ)) -
      (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)))
  have heq : ((zeroCountL χ T : ℝ) -
      (((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
       ((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) +
       (T / Real.pi) * Real.log (q : ℝ))) +
    ((((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + (t : ℂ) * I)).re) +
       ((1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          (logDeriv (DirichletCharacter.completedLFunction (star χ)) ((2 : ℂ) + (t : ℂ) * I)).re) +
       (T / Real.pi) * Real.log (q : ℝ)) -
      (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))) =
      (zeroCountL χ T : ℝ) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by ring
  rw [heq] at hsum
  calc |(zeroCountL χ T : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))|
      ≤ H.horConst * Real.log ((q : ℝ) * T) + C_v * Real.log (T + 2) := hsum.trans (add_le_add h1 h2)
    _ ≤ H.horConst * Real.log ((q : ℝ) * T) + C_v * (2 * Real.log ((q : ℝ) * T)) := by
        gcongr
    _ = (H.horConst + 2 * C_v) * Real.log ((q : ℝ) * T) := by ring

private lemma mainTerm_shift_le {q : ℕ} [NeZero q] {T T' : ℝ} (hT : 2 ≤ T)
    (hTT' : T ≤ T') (hT'1 : T' ≤ T + 1) :
    |(T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      (2 / Real.pi + 1) * Real.log ((q : ℝ) * T) + 4 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hT'_pos : 0 < T' := by linarith
  let F : ℝ → ℝ := fun x ↦ (x / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))
  have hF_diff : DifferentiableOn ℝ F (Set.Icc T T') := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have harg : (q : ℝ) * x / (2 * Real.pi * Real.exp 1) ≠ 0 := by positivity
    exact ((differentiableAt_id.div_const Real.pi).mul
      (((differentiableAt_const _).mul differentiableAt_id |>.div_const _).log harg)).differentiableWithinAt
  have hF_cont : ContinuousOn F (Set.Icc T T') := hF_diff.continuousOn
  have hF_deriv : ∀ x ∈ Set.Ioo T T',
      HasDerivAt F ((1 / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi))) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hinner : HasDerivAt (fun y : ℝ ↦ (q : ℝ) * y / (2 * Real.pi * Real.exp 1))
        ((q : ℝ) / (2 * Real.pi * Real.exp 1)) x := by
      simpa using ((hasDerivAt_id x).const_mul (q : ℝ)).div_const _
    have harg : (q : ℝ) * x / (2 * Real.pi * Real.exp 1) ≠ 0 := by positivity
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log ((q : ℝ) * y / (2 * Real.pi * Real.exp 1)))
        (((q : ℝ) / (2 * Real.pi * Real.exp 1)) / ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))) x :=
      hinner.log harg
    have h1 : HasDerivAt (fun y : ℝ ↦ y / Real.pi) (1 / Real.pi) x := by
      simpa using (hasDerivAt_id x).div_const Real.pi
    have hm := h1.mul hlog
    refine hm.congr_deriv ?_
    have hlog_eq : Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1)) =
        Real.log ((q : ℝ) * x / (2 * Real.pi)) - 1 := by
      rw [show (q : ℝ) * x / (2 * Real.pi * Real.exp 1) =
          ((q : ℝ) * x / (2 * Real.pi)) / Real.exp 1 by ring,
        Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
    rw [hlog_eq]
    field_simp [Real.pi_ne_zero, hx0.ne']
    ring
  by_cases hEq : T = T'
  · subst hEq
    simp
    have h1 : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
    have hpi := Real.pi_pos
    positivity
  · have hlt : T < T' := lt_of_le_of_ne hTT' hEq
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope F
      (fun x ↦ (1 / Real.pi) * Real.log ((q : ℝ) * x / (2 * Real.pi))) hlt hF_cont hF_deriv
    have hslope : F T' - F T = (1 / Real.pi) * Real.log ((q : ℝ) * c / (2 * Real.pi)) * (T' - T) := by
      rw [hc_eq]
      field_simp [show T' - T ≠ 0 by linarith]
    change |F T' - F T| ≤ _
    rw [hslope, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi),
      abs_of_nonneg (by linarith : 0 ≤ T' - T)]
    have hc_lo : 2 ≤ c := by linarith [hc_mem.1]
    have hc_hi : c ≤ T + 1 := by linarith [hc_mem.2]
    have hlogc : |Real.log ((q : ℝ) * c / (2 * Real.pi))| ≤
        Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi) := by
      have hpos : 0 < (q : ℝ) * c / (2 * Real.pi) := by positivity
      rw [Real.log_div (by positivity) (by positivity)]
      have hup : Real.log ((q : ℝ) * c) ≤ Real.log ((q : ℝ) * T) + Real.log 2 := by
        have hqc : (q : ℝ) * c ≤ 2 * ((q : ℝ) * T) := by nlinarith
        calc Real.log ((q : ℝ) * c) ≤ Real.log (2 * ((q : ℝ) * T)) := Real.log_le_log (by positivity) hqc
          _ = Real.log 2 + Real.log ((q : ℝ) * T) := Real.log_mul (by norm_num) (by positivity)
          _ = Real.log ((q : ℝ) * T) + Real.log 2 := by ring
      have hlo : 0 ≤ Real.log ((q : ℝ) * c) := Real.log_nonneg (by nlinarith)
      have hlog2p : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
      have hl2 : Real.log 2 ≤ 2 := by linarith [Real.log_two_lt_d9]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hlog2pi : Real.log (2 * Real.pi) ≤ 4 * Real.pi := by
      have : 2 * Real.pi ≤ 4 * Real.pi := by linarith [Real.pi_pos]
      linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hpi0 := Real.pi_pos
    have hlogqT : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
    have hlog2p : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
    calc (1 / Real.pi) * |Real.log ((q : ℝ) * c / (2 * Real.pi))| * (T' - T)
        ≤ (1 / Real.pi) * (Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi)) * 1 := by
          have hmul1 : (1 / Real.pi) * |Real.log ((q : ℝ) * c / (2 * Real.pi))| ≤
              (1 / Real.pi) * (Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hlogc (by positivity)
          have hnn : 0 ≤ (1 / Real.pi) * (Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi)) :=
            by positivity
          calc (1 / Real.pi) * |Real.log ((q : ℝ) * c / (2 * Real.pi))| * (T' - T)
              ≤ (1 / Real.pi) * (Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi)) * (T' - T) :=
                mul_le_mul_of_nonneg_right hmul1 (by linarith)
            _ ≤ (1 / Real.pi) * (Real.log ((q : ℝ) * T) + 2 + Real.log (2 * Real.pi)) * 1 :=
                mul_le_mul_of_nonneg_left (by linarith) hnn
      _ = (1 / Real.pi) * Real.log ((q : ℝ) * T) + (2 + Real.log (2 * Real.pi)) / Real.pi := by ring
      _ ≤ (2 / Real.pi + 1) * Real.log ((q : ℝ) * T) + 4 := by
          have h1pi : (1 / Real.pi) * Real.log ((q : ℝ) * T) ≤
              (2 / Real.pi + 1) * Real.log ((q : ℝ) * T) := by
            have hcoeff : 1 / Real.pi ≤ 2 / Real.pi + 1 := by
              rw [show (2 : ℝ) / Real.pi = 2 * (1 / Real.pi) by ring]
              have : 0 ≤ 1 / Real.pi := by positivity
              linarith
            exact mul_le_mul_of_nonneg_right hcoeff hlogqT
          have h2pi : (2 + Real.log (2 * Real.pi)) / Real.pi ≤ 4 := by
            have hlt : Real.log (2 * Real.pi) ≤ 2 * Real.pi := by
              linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)]
            have hp3 : 3 < Real.pi := Real.pi_gt_three
            rw [div_le_iff₀ Real.pi_pos]
            linarith
          linarith

/-- Full Riemann–von Mangoldt asymptotic theorem for ALL `T ≥ 2` (whether or not zeros lie on
the horizontal lines `Im ρ = ±T`), proved by combining `RiemannVonMangoldtContourHypothesis` at a
nearby zero-free height `T' ∈ [T, T + 1]`, the unconditional Jensen unit-interval zero-density
bound `zeroCountL_add_one_sub_le`, and the unconditional Stirling vertical-edge asymptotic. -/
theorem zeroCountL_asymptotic {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (H : RiemannVonMangoldtContourHypothesis χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      |(zeroCountL χ T : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log ((q : ℝ) * T) := by
  obtain ⟨C_zf, hC_zf0, hzf⟩ := zeroCountL_asymptotic_of_zeroFreeHeight H
  let C : ℝ := 2 * C_zf + 6 * jensenUnitZeroDensityConst + (2 / Real.pi + 1) + 10
  have hC0 : 0 ≤ C := by
    have := jensenUnitZeroDensityConst_pos.le
    have := Real.pi_pos.le
    positivity
  refine ⟨C, hC0, fun T hT ↦ ?_⟩
  let S_bad : Finset ℝ :=
    (criticalStripZeroFinset χ (-(T + 1)) (T + 1)).image Complex.im ∪
      (criticalStripZeroFinset χ (-(T + 1)) (T + 1)).image (fun ρ ↦ -ρ.im)
  have hinf : (Set.Icc T (T + 1) \ (S_bad : Set ℝ)).Nonempty := by
    have hIcc_inf : (Set.Icc T (T + 1)).Infinite := Set.Icc_infinite (by linarith)
    exact (hIcc_inf.sdiff S_bad.finite_toSet).nonempty
  obtain ⟨T', hT'_mem, hT'_not⟩ := hinf
  have hTT' : T ≤ T' := hT'_mem.1
  have hT'1 : T' ≤ T + 1 := hT'_mem.2
  have hT'2 : 2 ≤ T' := by linarith
  have hzfree : ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ T' ∧ ρ.im ≠ -T' := by
    intro ρ ⟨h0, h1, hL0⟩
    by_cases him : |ρ.im| ≤ T + 1
    · have hmem : ρ ∈ criticalStripZeroFinset χ (-(T + 1)) (T + 1) := by
        rw [mem_criticalStripZeroFinset]
        exact ⟨h0, h1, (abs_le.mp him).1, (abs_le.mp him).2, hL0⟩
      constructor
      · intro h
        apply hT'_not
        exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ, hmem, h⟩))
      · intro h
        apply hT'_not
        refine Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ρ, hmem, ?_⟩))
        linarith
    · have him_gt : T + 1 < |ρ.im| := not_le.mp him
      constructor
      · intro h
        rw [h, abs_of_nonneg (by linarith)] at him_gt
        linarith
      · intro h
        have hneg : ρ.im = -T' := h
        rw [hneg, abs_neg, abs_of_nonneg (by linarith)] at him_gt
        linarith
  have hN_T' := hzf T' hT'2 hzfree
  have hN_diff : |(zeroCountL χ T : ℝ) - (zeroCountL χ T' : ℝ)| ≤
      6 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * T) := by
    have hlo : zeroCountL χ T ≤ zeroCountL χ T' := zeroCountL_mono χ hTT'
    have hhi : zeroCountL χ T' ≤ zeroCountL χ (T + 1) := zeroCountL_mono χ hT'1
    have hjens := zeroCountL_add_one_sub_le hχ (by linarith : 0 ≤ T)
    rw [abs_of_nonneg (by linarith)] at hjens
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hlog_T2 : Real.log ((q : ℝ) * (T + 2)) ≤ 2 * Real.log ((q : ℝ) * T) := by
      have harg : (q : ℝ) * (T + 2) ≤ 2 * ((q : ℝ) * T) := by nlinarith
      have hge2 : 2 ≤ (q : ℝ) * T := by nlinarith
      calc Real.log ((q : ℝ) * (T + 2)) ≤ Real.log (2 * ((q : ℝ) * T)) :=
            Real.log_le_log (by positivity) harg
        _ = Real.log 2 + Real.log ((q : ℝ) * T) := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 2 * Real.log ((q : ℝ) * T) := by linarith [Real.log_le_log (by norm_num) hge2]
    have habs_eq : |(zeroCountL χ T : ℝ) - (zeroCountL χ T' : ℝ)| =
        (zeroCountL χ T' : ℝ) - (zeroCountL χ T : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hlo)
    rw [habs_eq]
    have hle1 : (zeroCountL χ T' : ℝ) ≤ (zeroCountL χ (T + 1) : ℝ) := by exact_mod_cast hhi
    have hc0 : 0 ≤ jensenUnitZeroDensityConst := jensenUnitZeroDensityConst_pos.le
    nlinarith
  have hM_diff := mainTerm_shift_le (q := q) hT hTT' hT'1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog_T' : Real.log ((q : ℝ) * T') ≤ 2 * Real.log ((q : ℝ) * T) := by
    have harg : (q : ℝ) * T' ≤ 2 * ((q : ℝ) * T) := by nlinarith
    have hge2 : 2 ≤ (q : ℝ) * T := by nlinarith
    calc Real.log ((q : ℝ) * T') ≤ Real.log (2 * ((q : ℝ) * T)) :=
          Real.log_le_log (by positivity) harg
      _ = Real.log 2 + Real.log ((q : ℝ) * T) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 2 * Real.log ((q : ℝ) * T) := by linarith [Real.log_le_log (by norm_num) hge2]
  have hlog_qT_ge : 1 / 2 ≤ Real.log ((q : ℝ) * T) := by
    have hge2 : (2 : ℝ) ≤ (q : ℝ) * T := by nlinarith
    have hlt2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact hlt2.le.trans (Real.log_le_log (by norm_num) hge2)
  have htri : |(zeroCountL χ T : ℝ) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      |(zeroCountL χ T : ℝ) - (zeroCountL χ T' : ℝ)| +
        |(zeroCountL χ T' : ℝ) -
          (T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1))| +
        |(T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| := by
    have h0 := abs_add_le
      ((zeroCountL χ T : ℝ) - (zeroCountL χ T' : ℝ))
      (((zeroCountL χ T' : ℝ) -
          (T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1))) +
       ((T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))))
    have h1 := abs_add_le
      ((zeroCountL χ T' : ℝ) -
          (T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)))
      ((T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)))
    have halg : (zeroCountL χ T : ℝ) - (zeroCountL χ T' : ℝ) +
        (((zeroCountL χ T' : ℝ) -
            (T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1))) +
         ((T' / Real.pi) * Real.log ((q : ℝ) * T' / (2 * Real.pi * Real.exp 1)) -
            (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)))) =
        (zeroCountL χ T : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by ring
    rw [halg] at h0
    linarith
  have h4le : (4 : ℝ) ≤ 8 * Real.log ((q : ℝ) * T) := by linarith
  calc |(zeroCountL χ T : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))|
      ≤ 6 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * T) +
          C_zf * Real.log ((q : ℝ) * T') +
          ((2 / Real.pi + 1) * Real.log ((q : ℝ) * T) + 4) := htri.trans (add_le_add (add_le_add hN_diff hN_T') hM_diff)
    _ ≤ 6 * jensenUnitZeroDensityConst * Real.log ((q : ℝ) * T) +
          C_zf * (2 * Real.log ((q : ℝ) * T)) +
          ((2 / Real.pi + 1) * Real.log ((q : ℝ) * T) + 8 * Real.log ((q : ℝ) * T)) := by gcongr
    _ ≤ C * Real.log ((q : ℝ) * T) := by
        have : 0 ≤ Real.log ((q : ℝ) * T) := by linarith
        simp only [C]
        nlinarith

/-- Big-O formulation of the Riemann–von Mangoldt asymptotic formula for `zeroCountL χ T`:
`N(T, χ) = (T / π) * log (q * T / (2 * π * exp 1)) + O(log (q * T))` as `T → atTop`. -/
theorem zeroCountL_isBigO {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (H : RiemannVonMangoldtContourHypothesis χ) :
    (fun T : ℝ ↦ (zeroCountL χ T : ℝ) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))) =O[atTop]
      (fun T : ℝ ↦ Real.log ((q : ℝ) * T)) := by
  obtain ⟨C, _, hbd⟩ := zeroCountL_asymptotic hχ H
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0]
  exact hbd T hT

end ZeroCountingAndRiemannVonMangoldt

end AnalyticNumberTheory.DirichletLFunctions


