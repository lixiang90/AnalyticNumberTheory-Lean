import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin Summation Formula

This file develops the Euler–Maclaurin summation formula and its standard applications in analytic
number theory:

- The sawtooth function `sawtooth x := Int.fract x - 1 / 2` and periodic Bernoulli functions
  `periodicBernoulli k x` and `bernoulliKernel k x` (normalized by `1 / k!`), including periodicity,
  global continuity for `k ≥ 2`, piecewise derivatives, and explicit bounds.
- Rigorous 1st-order Euler–Maclaurin summation on arbitrary real intervals `a ≤ b` (`Finset.Ioc`)
  and integer/natural intervals (`Finset.Ioc` and `Finset.Icc`), proved by integration by parts
  and induction on unit-interval crossings.
- Higher-order (`l`-fold integration by parts) Euler–Maclaurin remainder identity for `C^l` functions.
- Harmonic asymptotic `∑_{n=1..N} 1/n = log N + γ + 1/(2N) + O(N⁻²)` bridging Mathlib's
  `Real.eulerMascheroniConstant` and `Real.tendsto_harmonic_sub_log`.
- Stirling / factorial log-sum asymptotics `∑_{n=1..N} log n = N log N - N + O(log N)` and
  `∑_{n=1..N} log n = N log N - N + (1/2) log N + O(1)`.
-/

noncomputable section

open Finset MeasureTheory Set Filter Asymptotics
open scoped Topology Nat

namespace AnalyticNumberTheory.AnalyticTools.Summation

section SawtoothAndBernoulli

/-- The 1-periodic sawtooth function `ψ(x) = {x} - 1/2`. -/
def sawtooth (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- The 1-periodic Bernoulli function `B_k({x})`. -/
def periodicBernoulli (k : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun k (Int.fract x)

/-- The normalized 1-periodic Bernoulli kernel `b_k(x) = B_k({x}) / k!`. -/
def bernoulliKernel (k : ℕ) (x : ℝ) : ℝ :=
  periodicBernoulli k x / (k ! : ℝ)

/-- `sawtooth` is 1-periodic. -/
theorem sawtooth_periodic : Function.Periodic sawtooth 1 := by
  intro x
  have hfract : Int.fract (x + 1) = Int.fract x := by simp
  rw [sawtooth, hfract, sawtooth]

/-- `sawtooth` is bounded in absolute value by `1 / 2`. -/
theorem sawtooth_abs_le (x : ℝ) : |sawtooth x| ≤ 1 / 2 := by
  rw [sawtooth, abs_le]
  constructor
  · linarith [Int.fract_nonneg x]
  · linarith [Int.fract_lt_one x]

/-- Value of `sawtooth` at any integer. -/
@[simp]
theorem sawtooth_intCast (n : ℤ) : sawtooth (n : ℝ) = -1 / 2 := by
  simp only [sawtooth, Int.fract_intCast]
  ring

/-- Value of `sawtooth` at any natural number. -/
@[simp]
theorem sawtooth_natCast (n : ℕ) : sawtooth (n : ℝ) = -1 / 2 := by
  simpa only [Int.cast_natCast] using sawtooth_intCast (n : ℤ)

/-- Formula for `sawtooth` on `[n, n + 1)`. -/
theorem sawtooth_eq_on_Ico {n : ℤ} {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) (n + 1)) :
    sawtooth x = x - n - 1 / 2 := by
  have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr hx
  rw [sawtooth, Int.fract, hfl]

/-- `periodicBernoulli` is 1-periodic for every order `k`. -/
theorem periodicBernoulli_periodic (k : ℕ) : Function.Periodic (periodicBernoulli k) 1 := by
  intro x
  have h1 : (1 : ℝ) = ((1 : ℤ) : ℝ) := Int.cast_one.symm
  rw [periodicBernoulli, h1, Int.fract_add_intCast, periodicBernoulli]

/-- `bernoulliKernel` is 1-periodic for every order `k`. -/
theorem bernoulliKernel_periodic (k : ℕ) : Function.Periodic (bernoulliKernel k) 1 := by
  intro x
  simp only [bernoulliKernel, periodicBernoulli_periodic k x]

/-- `periodicBernoulli 0 x = 1`. -/
@[simp]
theorem periodicBernoulli_zero (x : ℝ) : periodicBernoulli 0 x = 1 := by
  simp [periodicBernoulli, bernoulliFun_zero]

/-- `bernoulliKernel 0 x = 1`. -/
@[simp]
theorem bernoulliKernel_zero (x : ℝ) : bernoulliKernel 0 x = 1 := by
  simp [bernoulliKernel]

/-- `periodicBernoulli 1 x = sawtooth x`. -/
@[simp]
theorem periodicBernoulli_one (x : ℝ) : periodicBernoulli 1 x = sawtooth x := by
  simp [periodicBernoulli, bernoulliFun_one, sawtooth]

/-- `bernoulliKernel 1 x = sawtooth x`. -/
@[simp]
theorem bernoulliKernel_one (x : ℝ) : bernoulliKernel 1 x = sawtooth x := by
  simp [bernoulliKernel]

/-- Explicit formula for `periodicBernoulli 2 x`. -/
theorem periodicBernoulli_two (x : ℝ) :
    periodicBernoulli 2 x = (Int.fract x) ^ 2 - Int.fract x + 1 / 6 := by
  simp only [periodicBernoulli, bernoulliFun_two, one_div]

/-- Explicit formula for `bernoulliKernel 2 x`. -/
theorem bernoulliKernel_two (x : ℝ) :
    bernoulliKernel 2 x = ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 := by
  rw [bernoulliKernel, periodicBernoulli_two]
  norm_num [Nat.factorial]

/-- Explicit bound `|bernoulliKernel 2 x| ≤ 1 / 12` for all `x : ℝ`. -/
theorem bernoulliKernel_two_abs_le (x : ℝ) : |bernoulliKernel 2 x| ≤ 1 / 12 := by
  rw [bernoulliKernel_two]
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  have hquad : (Int.fract x - 1 / 2) ^ 2 = (Int.fract x) ^ 2 - Int.fract x + 1 / 4 := by ring
  have hsq_nonneg : 0 ≤ (Int.fract x - 1 / 2) ^ 2 := sq_nonneg _
  have hsq_le : (Int.fract x - 1 / 2) ^ 2 ≤ 1 / 4 := by
    nlinarith
  have hlo : -(1 / 12 : ℝ) ≤ ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 := by linarith
  have hhi : ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 ≤ 1 / 12 := by linarith
  rw [abs_le]
  exact ⟨hlo, hhi⟩

/-- Value of `periodicBernoulli k` at any integer. -/
@[simp]
theorem periodicBernoulli_intCast (k : ℕ) (n : ℤ) :
    periodicBernoulli k (n : ℝ) = (_root_.bernoulli k : ℝ) := by
  rw [periodicBernoulli, Int.fract_intCast, bernoulliFun_eval_zero]

/-- Value of `bernoulliKernel k` at any integer. -/
@[simp]
theorem bernoulliKernel_intCast (k : ℕ) (n : ℤ) :
    bernoulliKernel k (n : ℝ) = (_root_.bernoulli k : ℝ) / (k ! : ℝ) := by
  rw [bernoulliKernel, periodicBernoulli_intCast]

/-- Value of `bernoulliKernel 2` at any integer is `1 / 12`. -/
@[simp]
theorem bernoulliKernel_two_intCast (n : ℤ) : bernoulliKernel 2 (n : ℝ) = 1 / 12 := by
  rw [bernoulliKernel_two, Int.fract_intCast]
  norm_num

/-- Value of `bernoulliKernel 2` at any natural number is `1 / 12`. -/
@[simp]
theorem bernoulliKernel_two_natCast (n : ℕ) : bernoulliKernel 2 (n : ℝ) = 1 / 12 := by
  simpa only [Int.cast_natCast] using bernoulliKernel_two_intCast (n : ℤ)

/-- `periodicBernoulli k` agrees with Mathlib's `periodizedBernoulli k` on `UnitAddCircle`. -/
theorem periodicBernoulli_eq_periodizedBernoulli (k : ℕ) (x : ℝ) :
    periodicBernoulli k x = periodizedBernoulli k (x : UnitAddCircle) := by
  have hfrac : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    rw [zero_add]
    exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hcoe : (x : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
    have hper : Function.Periodic (fun y : ℝ => (y : UnitAddCircle)) 1 :=
      fun y => AddCircle.coe_add_period 1 y
    have hsplit : x = Int.fract x + (⌊x⌋ : ℤ) * 1 := by
      have h := Int.floor_add_fract x
      linarith
    nth_rw 1 [hsplit]
    exact hper.int_mul ⌊x⌋ (Int.fract x)
  rw [hcoe, periodizedBernoulli, AddCircle.liftIco_coe_apply hfrac, periodicBernoulli]

/-- For `k ≠ 1` (in particular all `k ≥ 2`), `periodicBernoulli k` is continuous everywhere on `ℝ`. -/
theorem continuous_periodicBernoulli {k : ℕ} (hk : k ≠ 1) :
    Continuous (periodicBernoulli k) := by
  have hfun : periodicBernoulli k = fun x : ℝ => periodizedBernoulli k (x : UnitAddCircle) :=
    funext (periodicBernoulli_eq_periodizedBernoulli k)
  rw [hfun]
  exact (periodizedBernoulli.continuous hk).comp (AddCircle.continuous_mk' 1)

/-- For `k ≠ 1` (in particular all `k ≥ 2`), `bernoulliKernel k` is continuous everywhere on `ℝ`. -/
theorem continuous_bernoulliKernel {k : ℕ} (hk : k ≠ 1) :
    Continuous (bernoulliKernel k) :=
  (continuous_periodicBernoulli hk).div_const _

/-- On any closed unit interval `[n, n + 1]` (`n : ℤ`), `bernoulliKernel (k + 1)` (for `k ≥ 1`)
equals `bernoulliFun (k + 1) (t - n) / (k + 1)!` at every point, including the right endpoint. -/
theorem bernoulliKernel_eq_on_Icc {k : ℕ} (hk : 1 ≤ k) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (n : ℝ) (n + 1)) :
    bernoulliKernel (k + 1) t = bernoulliFun (k + 1) (t - n) / ((k + 1)! : ℝ) := by
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · have hne1 : k + 1 ≠ 1 := by omega
    rw [bernoulliKernel, periodicBernoulli,
      show (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) by push_cast; rfl,
      Int.fract_intCast, Int.cast_add, Int.cast_one, add_sub_cancel_left,
      bernoulliFun_endpoints_eq_of_ne_one hne1]
  · have hfl : ⌊t⌋ = n := Int.floor_eq_iff.mpr ⟨ht.1, hlt⟩
    rw [bernoulliKernel, periodicBernoulli, Int.fract, hfl]

/-- On the half-open unit interval `[n, n + 1)`, `bernoulliKernel k` equals
`bernoulliFun k (t - n) / k!`. -/
theorem bernoulliKernel_eq_on_Ico (k : ℕ) (n : ℤ) {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) (n + 1)) :
    bernoulliKernel k t = bernoulliFun k (t - n) / (k ! : ℝ) := by
  have hfl : ⌊t⌋ = n := Int.floor_eq_iff.mpr ht
  rw [bernoulliKernel, periodicBernoulli, Int.fract, hfl]

/-- Global boundedness of `bernoulliKernel k` on `ℝ`. -/
theorem bernoulliKernel_bounded (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |bernoulliKernel k x| ≤ M := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hcont : ContinuousOn (fun y : ℝ => |bernoulliFun k y| / (k ! : ℝ)) (Set.Icc 0 1) :=
    ((continuous_bernoulliFun k).abs.div_const _).continuousOn
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hcont
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have hx : Int.fract x ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hval : |bernoulliKernel k x| = |bernoulliFun k (Int.fract x)| / (k ! : ℝ) := by
    rw [bernoulliKernel, periodicBernoulli, abs_div]
    nth_rw 2 [abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  rw [hval]
  exact (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)

/-- Interval integrability of `bernoulliKernel k * g` for any continuous `g` on `[a, b]`. -/
theorem intervalIntegrable_bernoulliKernel_mul (k : ℕ) {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    IntervalIntegrable (fun t => bernoulliKernel k t * g t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  obtain ⟨M, _, hM⟩ := bernoulliKernel_bounded k
  have hbound : IntegrableOn (fun t => M * ‖g t‖) (Set.Icc a b) :=
    (hg.norm.integrableOn_Icc).const_mul M
  have hmeas_b : AEStronglyMeasurable (bernoulliKernel k) (volume.restrict (Set.Icc a b)) := by
    refine ((continuous_bernoulliFun k).div_const _).aestronglyMeasurable.comp_aemeasurable
      measurable_fract.aemeasurable
  refine Integrable.mono' hbound
    (hmeas_b.mul (hg.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM t) (abs_nonneg _)

/-- Integral of `sawtooth` over any unit interval `[n, n + 1]` is `0`. -/
theorem integral_sawtooth_unit (n : ℤ) : ∫ t in (n : ℝ)..(n + 1), sawtooth t = 0 := by
  have hcongr : ∫ t in (n : ℝ)..(n + 1), sawtooth t =
      ∫ t in (n : ℝ)..(n + 1), (t - n - 1 / 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t ∂volume, t ≠ (n : ℝ) + 1 := ae_iff.mpr (by simp)
    filter_upwards [hne] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith)] at ht_mem
    exact sawtooth_eq_on_Ico ⟨ht_mem.1.le, lt_of_le_of_ne ht_mem.2 ht_ne⟩
  rw [hcongr]
  have hd : ∀ t ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun u : ℝ => (u - n - 1 / 2) ^ 2 / 2) (t - n - 1 / 2) t := by
    intro t _
    convert ((((hasDerivAt_id' t).sub_const (n : ℝ)).sub_const (1 / 2 : ℝ)).pow 2).div_const 2
      using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

end SawtoothAndBernoulli

section FirstOrderEulerMaclaurin

private lemma euler_maclaurin_first_order_subinterval {n : ℤ} {t₁ t₂ : ℝ}
    (ht₁ : (n : ℝ) ≤ t₁) (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ n + 1)
    {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc t₁ t₂, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc t₁ t₂)) :
    (if t₂ = n + 1 ∧ t₁ < t₂ then f (n + 1) else 0) =
      (∫ t in t₁..t₂, f t) + (∫ t in t₁..t₂, sawtooth t * f' t) -
        (sawtooth t₂ * f t₂ - sawtooth t₁ * f t₁) := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · simp [sub_self]
  have ht₁_lt : t₁ < (n : ℝ) + 1 := lt_of_lt_of_le hlt ht₂
  have hsaw1 : sawtooth t₁ = t₁ - n - 1 / 2 := sawtooth_eq_on_Ico ⟨ht₁, ht₁_lt⟩
  let u : ℝ → ℝ := fun t => t - n - 1 / 2
  have hu_deriv : ∀ t ∈ Set.uIcc t₁ t₂, HasDerivAt u 1 t := fun t _ => by
    have hd := ((hasDerivAt_id' t).sub_const (n : ℝ)).sub_const (1 / 2 : ℝ)
    simpa only [sub_zero] using hd
  have hf_uIcc : ∀ t ∈ Set.uIcc t₁ t₂, HasDerivAt f (f' t) t := by
    rw [Set.uIcc_of_le h12]
    exact hf
  have hf_cont : ContinuousOn f (Set.Icc t₁ t₂) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hf_int : IntervalIntegrable f volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h12).mpr hf_cont.integrableOn_Icc
  have hf'_int : IntervalIntegrable f' volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h12).mpr hf'.integrableOn_Icc
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hf_uIcc
    (Continuous.intervalIntegrable continuous_const _ _) hf'_int
  have hcongr_u : ∫ t in t₁..t₂, u t * f' t = ∫ t in t₁..t₂, sawtooth t * f' t := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t ∂volume, t ≠ (n : ℝ) + 1 := ae_iff.mpr (by simp)
    filter_upwards [hne] with t ht_ne ht_mem
    rw [Set.uIoc_of_le h12] at ht_mem
    have hmem : t ∈ Set.Ico (n : ℝ) (n + 1) :=
      ⟨ht₁.trans ht_mem.1.le, lt_of_le_of_ne (ht_mem.2.trans ht₂) ht_ne⟩
    rw [sawtooth_eq_on_Ico hmem]
  have hcongr_f : ∫ t in t₁..t₂, 1 * f t = ∫ t in t₁..t₂, f t := by
    simp only [one_mul]
  rw [hcongr_u, hcongr_f] at hibp
  rcases eq_or_lt_of_le ht₂ with rfl | ht₂_lt
  · have hsaw2 : sawtooth ((n : ℝ) + 1) = -1 / 2 := by
      have hcast : (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) := by push_cast; rfl
      rw [hcast, sawtooth_intCast]
    have hu2 : u ((n : ℝ) + 1) = 1 / 2 := by norm_num [u]
    have hu1 : u t₁ = sawtooth t₁ := hsaw1.symm
    rw [hu2, hu1] at hibp
    split_ifs with h
    · rw [hsaw2]
      linarith
    · exfalso
      exact h ⟨rfl, hlt⟩
  · have hsaw2 : sawtooth t₂ = u t₂ := sawtooth_eq_on_Ico ⟨ht₁.trans hlt.le, ht₂_lt⟩
    have hu1 : u t₁ = sawtooth t₁ := hsaw1.symm
    rw [← hsaw2, hu1] at hibp
    split_ifs with h
    · exfalso
      exact ht₂_lt.ne h.1
    · linarith

private lemma euler_maclaurin_first_order_natSteps :
    ∀ (m : ℕ) (a b : ℝ) (_hab : a ≤ b) (_hm : ⌊a⌋ + m = ⌊b⌋)
      (f f' : ℝ → ℝ)
      (_hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
      (_hf' : ContinuousOn f' (Set.Icc a b)),
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (n : ℝ) =
        (∫ t in a..b, f t) + (∫ t in a..b, sawtooth t * f' t) -
          (sawtooth b * f b - sawtooth a * f a) := by
  intro m
  induction m with
  | zero =>
    intro a b hab hm f f' hf hf'
    have hfl : ⌊a⌋ = ⌊b⌋ := by omega
    rw [← hfl, Finset.Ioc_self, Finset.sum_empty]
    have ha_ge : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
    have hb_le : b ≤ (⌊a⌋ : ℝ) + 1 := by
      rw [hfl]
      exact (Int.lt_floor_add_one b).le
    have hsub := euler_maclaurin_first_order_subinterval ha_ge hab hb_le hf hf'
    have hnot : ¬ (b = (⌊a⌋ : ℝ) + 1 ∧ a < b) := by
      intro ⟨hb_eq, _⟩
      have hlt := Int.lt_floor_add_one b
      rw [← hfl] at hlt
      linarith
    simp only [hnot, ite_false] at hsub
    exact hsub
  | succ m ih =>
    intro a b hab hm f f' hf hf'
    let c : ℝ := ((⌊a⌋ + 1 : ℤ) : ℝ)
    have hac : a ≤ c := by
      simp only [c, Int.cast_add, Int.cast_one]
      exact (Int.lt_floor_add_one a).le
    have hcb : c ≤ b := by
      have h1 : ⌊a⌋ + 1 ≤ ⌊b⌋ := by omega
      have h2 : ((⌊a⌋ + 1 : ℤ) : ℝ) ≤ (⌊b⌋ : ℝ) := Int.cast_le.mpr h1
      exact h2.trans (Int.floor_le b)
    have hfl_c : ⌊c⌋ = ⌊a⌋ + 1 := Int.floor_intCast _
    have hm' : ⌊c⌋ + m = ⌊b⌋ := by omega
    have hac_lt : a < c := by
      simp only [c, Int.cast_add, Int.cast_one]
      exact Int.lt_floor_add_one a
    have hc_eq : c = (⌊a⌋ : ℝ) + 1 := by simp [c]
    have h1 : f c = (∫ t in a..c, f t) + (∫ t in a..c, sawtooth t * f' t) -
        (sawtooth c * f c - sawtooth a * f a) := by
      have hsub := euler_maclaurin_first_order_subinterval (Int.floor_le a) hac hc_eq.le
        (fun t ht => hf t ⟨ht.1, ht.2.trans hcb⟩)
        (hf'.mono (Set.Icc_subset_Icc_right hcb))
      rw [← hc_eq] at hsub
      have hcond : c = c ∧ a < c := ⟨rfl, hac_lt⟩
      simp only [hcond] at hsub
      exact hsub
    have h2 := ih c b hcb hm' f f'
      (fun t ht => hf t ⟨hac.trans ht.1, ht.2⟩)
      (hf'.mono (Set.Icc_subset_Icc_left hac))
    have hsplit_sum : ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (n : ℝ) =
        f c + ∑ n ∈ Finset.Ioc ⌊c⌋ ⌊b⌋, f (n : ℝ) := by
      have hle : ⌊a⌋ + 1 ≤ ⌊b⌋ := by omega
      have hcons : Finset.Ioc ⌊a⌋ ⌊b⌋ = insert (⌊a⌋ + 1) (Finset.Ioc (⌊a⌋ + 1) ⌊b⌋) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [hfl_c, hcons, Finset.sum_insert (by simp)]
    have hf_cont : ContinuousOn f (Set.Icc a b) :=
      fun t ht => (hf t ht).continuousAt.continuousWithinAt
    have hf_ac : IntervalIntegrable f volume a c :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hac).mpr
        (hf_cont.mono (Set.Icc_subset_Icc_right hcb)).integrableOn_Icc
    have hf_cb : IntervalIntegrable f volume c b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hcb).mpr
        (hf_cont.mono (Set.Icc_subset_Icc_left hac)).integrableOn_Icc
    have hs_ac : IntervalIntegrable (fun t => sawtooth t * f' t) volume a c := by
      simpa only [bernoulliKernel_one] using
        intervalIntegrable_bernoulliKernel_mul 1 hac (hf'.mono (Set.Icc_subset_Icc_right hcb))
    have hs_cb : IntervalIntegrable (fun t => sawtooth t * f' t) volume c b := by
      simpa only [bernoulliKernel_one] using
        intervalIntegrable_bernoulliKernel_mul 1 hcb (hf'.mono (Set.Icc_subset_Icc_left hac))
    simp only [c, Int.cast_add, Int.cast_one] at h1 h2 hsplit_sum hf_ac hf_cb hs_ac hs_cb ⊢
    rw [hsplit_sum, h1, h2, ← intervalIntegral.integral_add_adjacent_intervals hf_ac hf_cb,
      ← intervalIntegral.integral_add_adjacent_intervals hs_ac hs_cb]
    ring

/-- **First-order Euler–Maclaurin summation formula** on an arbitrary real interval `[a, b]`
(`a ≤ b`) indexed over `Finset.Ioc ⌊a⌋ ⌊b⌋`, with explicit derivative function `f'`. -/
theorem euler_maclaurin_first_order_Ioc_int {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc a b)) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (n : ℝ) =
      (∫ t in a..b, f t) + (∫ t in a..b, sawtooth t * f' t) -
        (sawtooth b * f b - sawtooth a * f a) := by
  have hfl : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  let m := Int.toNat (⌊b⌋ - ⌊a⌋)
  have hm : ⌊a⌋ + m = ⌊b⌋ := by
    dsimp only [m]
    omega
  exact euler_maclaurin_first_order_natSteps m a b hab hm f f' hf hf'

/-- **First-order Euler–Maclaurin summation formula** on `[a, b]` (`0 ≤ a ≤ b`) indexed over
`Finset.Ioc ⌊a⌋₊ ⌊b⌋₊`. -/
theorem euler_maclaurin_first_order_Ioc_nat {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc a b)) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f (n : ℝ) =
      (∫ t in a..b, f t) + (∫ t in a..b, sawtooth t * f' t) -
        (sawtooth b * f b - sawtooth a * f a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hsum : ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f (n : ℝ) =
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (n : ℝ) := by
    have ha' : (⌊a⌋₊ : ℤ) = ⌊a⌋ := Int.natCast_floor_eq_floor ha
    have hb' : (⌊b⌋₊ : ℤ) = ⌊b⌋ := Int.natCast_floor_eq_floor hb
    rw [← ha', ← hb']
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ioc] at hn ⊢
      exact ⟨Int.ofNat_lt.mpr hn.1, Int.ofNat_le.mpr hn.2⟩
    · intro n₁ _ n₂ _ h
      exact Int.ofNat.inj h
    · intro z hz
      simp only [Finset.mem_Ioc] at hz
      have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg ⌊a⌋₊) hz.1.le
      refine ⟨Int.toNat z, ?_, Int.toNat_of_nonneg hz0⟩
      simp only [Finset.mem_Ioc]
      omega
    · intro n _
      simp
  rw [hsum]
  exact euler_maclaurin_first_order_Ioc_int hab hf hf'

/-- **First-order Euler–Maclaurin summation formula** on `Finset.Ioc M N` for natural numbers
`M ≤ N`. -/
theorem euler_maclaurin_first_order_Ioc {M N : ℕ} (hMN : M ≤ N) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Ioc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f N - f M) / 2 + ∫ t in (M : ℝ)..N, sawtooth t * f' t := by
  have h := euler_maclaurin_first_order_Ioc_nat (Nat.cast_nonneg M) (Nat.cast_le.mpr hMN) hf hf'
  rw [Nat.floor_natCast, Nat.floor_natCast, sawtooth_natCast, sawtooth_natCast] at h
  rw [h]
  ring

/-- **First-order Euler–Maclaurin summation formula** on `Finset.Icc M N` for natural numbers
`M ≤ N`. -/
theorem euler_maclaurin_first_order_Icc {M N : ℕ} (hMN : M ≤ N) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (M : ℝ) N, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Icc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) + (f M + f N) / 2 + ∫ t in (M : ℝ)..N, sawtooth t * f' t := by
  rw [Finset.Icc_eq_cons_Ioc hMN, Finset.sum_cons,
    euler_maclaurin_first_order_Ioc hMN hf hf']
  ring

end FirstOrderEulerMaclaurin

section HigherOrderEulerMaclaurin

private lemma integral_bernoulliKernel_mul_eq_sub_subinterval {j : ℕ} (hj : 1 ≤ j)
    {n : ℤ} {t₁ t₂ : ℝ} (ht₁ : (n : ℝ) ≤ t₁) (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ n + 1)
    {g g' : ℝ → ℝ}
    (hg : ∀ t ∈ Set.Icc t₁ t₂, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Set.Icc t₁ t₂)) :
    ∫ t in t₁..t₂, bernoulliKernel j t * g t =
      (bernoulliKernel (j + 1) t₂ * g t₂ - bernoulliKernel (j + 1) t₁ * g t₁) -
        ∫ t in t₁..t₂, bernoulliKernel (j + 1) t * g' t := by
  let u : ℝ → ℝ := fun t => bernoulliFun (j + 1) (t - n) / ((j + 1)! : ℝ)
  let u' : ℝ → ℝ := fun t => bernoulliFun j (t - n) / (j ! : ℝ)
  have hu_deriv : ∀ t ∈ Set.uIcc t₁ t₂, HasDerivAt u (u' t) t := by
    intro t _
    have hcomp : HasDerivAt (fun y : ℝ => bernoulliFun (j + 1) (y - n))
        (((j + 1 : ℕ) : ℝ) * bernoulliFun j (t - n)) t := by
      have h1 := hasDerivAt_bernoulliFun (j + 1) (t - n)
      have h2 : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 t := (hasDerivAt_id' t).sub_const _
      have hc := h1.comp t h2
      simpa only [Function.comp_def, Nat.add_sub_cancel, mul_one] using hc
    convert hcomp.div_const ((j + 1)! : ℝ) using 1
    simp only [u', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hj1]
  have hu'_cont : IntervalIntegrable u' volume t₁ t₂ :=
    (((continuous_bernoulliFun j).comp (continuous_id.sub continuous_const)).div_const _).intervalIntegrable _ _
  have hg_uIcc : ∀ t ∈ Set.uIcc t₁ t₂, HasDerivAt g (g' t) t := by
    rw [Set.uIcc_of_le h12]
    exact hg
  have hg'_int : IntervalIntegrable g' volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h12).mpr hg'.integrableOn_Icc
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hg_uIcc hu'_cont hg'_int
  have hcongr_left : ∫ t in t₁..t₂, u t * g' t = ∫ t in t₁..t₂, bernoulliKernel (j + 1) t * g' t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le h12] at ht
    have ht_icc : t ∈ Set.Icc (n : ℝ) (n + 1) := ⟨ht₁.trans ht.1, ht.2.trans ht₂⟩
    rw [bernoulliKernel_eq_on_Icc hj n ht_icc]
  have hcongr_right : ∫ t in t₁..t₂, u' t * g t = ∫ t in t₁..t₂, bernoulliKernel j t * g t := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t ∂volume, t ≠ (n : ℝ) + 1 := ae_iff.mpr (by simp)
    filter_upwards [hne] with t ht_ne ht_mem
    rw [Set.uIoc_of_le h12] at ht_mem
    have ht_ico : t ∈ Set.Ico (n : ℝ) (n + 1) :=
      ⟨ht₁.trans ht_mem.1.le, lt_of_le_of_ne (ht_mem.2.trans ht₂) ht_ne⟩
    rw [bernoulliKernel_eq_on_Ico j n ht_ico]
  have hu1 : u t₁ = bernoulliKernel (j + 1) t₁ :=
    (bernoulliKernel_eq_on_Icc hj n ⟨ht₁, h12.trans ht₂⟩).symm
  have hu2 : u t₂ = bernoulliKernel (j + 1) t₂ :=
    (bernoulliKernel_eq_on_Icc hj n ⟨ht₁.trans h12, ht₂⟩).symm
  rw [hcongr_left, hcongr_right, hu1, hu2] at hibp
  linarith

private lemma integral_bernoulliKernel_mul_eq_sub_natSteps {j : ℕ} (hj : 1 ≤ j) :
    ∀ (m : ℕ) (a b : ℝ) (_hab : a ≤ b) (_hm : ⌊a⌋ + m = ⌊b⌋)
      (g g' : ℝ → ℝ)
      (_hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
      (_hg' : ContinuousOn g' (Set.Icc a b)),
      ∫ t in a..b, bernoulliKernel j t * g t =
        (bernoulliKernel (j + 1) b * g b - bernoulliKernel (j + 1) a * g a) -
          ∫ t in a..b, bernoulliKernel (j + 1) t * g' t := by
  intro m
  induction m with
  | zero =>
    intro a b hab hm g g' hg hg'
    have hfl : ⌊a⌋ = ⌊b⌋ := by omega
    have hb_le : b ≤ (⌊a⌋ : ℝ) + 1 := by
      rw [hfl]
      exact (Int.lt_floor_add_one b).le
    exact integral_bernoulliKernel_mul_eq_sub_subinterval hj (Int.floor_le a) hab hb_le hg hg'
  | succ m ih =>
    intro a b hab hm g g' hg hg'
    let c : ℝ := ((⌊a⌋ + 1 : ℤ) : ℝ)
    have hac : a ≤ c := by
      simp only [c, Int.cast_add, Int.cast_one]
      exact (Int.lt_floor_add_one a).le
    have hcb : c ≤ b := by
      have h1 : ⌊a⌋ + 1 ≤ ⌊b⌋ := by omega
      exact (Int.cast_le.mpr h1).trans (Int.floor_le b)
    have hc_eq : c = (⌊a⌋ : ℝ) + 1 := by simp [c]
    have hfl_c : ⌊c⌋ = ⌊a⌋ + 1 := Int.floor_intCast _
    have hm' : ⌊c⌋ + m = ⌊b⌋ := by omega
    have hg_cont : ContinuousOn g (Set.Icc a b) :=
      fun t ht => (hg t ht).continuousAt.continuousWithinAt
    have h1 := integral_bernoulliKernel_mul_eq_sub_subinterval hj (Int.floor_le a) hac hc_eq.le
      (fun t ht => hg t ⟨ht.1, ht.2.trans hcb⟩) (hg'.mono (Set.Icc_subset_Icc_right hcb))
    have h2 := ih c b hcb hm' g g'
      (fun t ht => hg t ⟨hac.trans ht.1, ht.2⟩) (hg'.mono (Set.Icc_subset_Icc_left hac))
    have hJ_ac : IntervalIntegrable (fun t => bernoulliKernel j t * g t) volume a c :=
      intervalIntegrable_bernoulliKernel_mul j hac (hg_cont.mono (Set.Icc_subset_Icc_right hcb))
    have hJ_cb : IntervalIntegrable (fun t => bernoulliKernel j t * g t) volume c b :=
      intervalIntegrable_bernoulliKernel_mul j hcb (hg_cont.mono (Set.Icc_subset_Icc_left hac))
    have hJ1_ac : IntervalIntegrable (fun t => bernoulliKernel (j + 1) t * g' t) volume a c :=
      intervalIntegrable_bernoulliKernel_mul (j + 1) hac (hg'.mono (Set.Icc_subset_Icc_right hcb))
    have hJ1_cb : IntervalIntegrable (fun t => bernoulliKernel (j + 1) t * g' t) volume c b :=
      intervalIntegrable_bernoulliKernel_mul (j + 1) hcb (hg'.mono (Set.Icc_subset_Icc_left hac))
    rw [← intervalIntegral.integral_add_adjacent_intervals hJ_ac hJ_cb,
      ← intervalIntegral.integral_add_adjacent_intervals hJ1_ac hJ1_cb, h1, h2]
    ring

/-- **Integration-by-parts step for periodic Bernoulli kernels** (`1 ≤ j`, `a ≤ b`). -/
theorem integral_bernoulliKernel_mul_eq_sub {j : ℕ} (hj : 1 ≤ j) {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℝ}
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Set.Icc a b)) :
    ∫ t in a..b, bernoulliKernel j t * g t =
      (bernoulliKernel (j + 1) b * g b - bernoulliKernel (j + 1) a * g a) -
        ∫ t in a..b, bernoulliKernel (j + 1) t * g' t := by
  have hfl : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  let m := Int.toNat (⌊b⌋ - ⌊a⌋)
  have hm : ⌊a⌋ + m = ⌊b⌋ := by
    dsimp only [m]
    omega
  exact integral_bernoulliKernel_mul_eq_sub_natSteps hj m a b hab hm g g' hg hg'

/-- **Higher-order Euler–Maclaurin summation formula** (`l ≥ 1`) on an arbitrary real interval
`[a, b]` (`a ≤ b`) indexed over `Finset.Ioc ⌊a⌋ ⌊b⌋`. -/
theorem euler_maclaurin_higher_order_Ioc_int {l : ℕ} (hl : 1 ≤ l) {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ}
    (hf : ∀ j < l, ∀ t ∈ Set.Icc a b,
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t)
    (hfl : ContinuousOn (iteratedDeriv l f) (Set.Icc a b)) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (n : ℝ) =
      (∫ t in a..b, f t) +
        (∑ j ∈ Finset.Icc 1 l, (-1 : ℝ) ^ j *
          (bernoulliKernel j b * iteratedDeriv (j - 1) f b -
            bernoulliKernel j a * iteratedDeriv (j - 1) f a)) +
        (-1 : ℝ) ^ (l + 1) * (∫ t in a..b, bernoulliKernel l t * iteratedDeriv l f t) := by
  induction l, hl using Nat.le_induction with
  | base =>
    have hf0 : ∀ t ∈ Set.Icc a b, HasDerivAt f (iteratedDeriv 1 f t) t := by
      simpa only [iteratedDeriv_zero] using hf 0 zero_lt_one
    have h1 := euler_maclaurin_first_order_Ioc_int hab hf0 hfl
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, neg_mul, one_mul, Nat.sub_self,
      iteratedDeriv_zero, bernoulliKernel_one, show (1 + 1 : ℕ) = 2 by rfl, neg_one_sq]
    linarith
  | succ l hl ih =>
    have hf_prev : ∀ j < l, ∀ t ∈ Set.Icc a b,
        HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t :=
      fun j hj => hf j (Nat.lt_succ_of_lt hj)
    have hcont_l : ContinuousOn (iteratedDeriv l f) (Set.Icc a b) := fun t ht =>
      (hf l (Nat.lt_succ_self l) t ht).continuousAt.continuousWithinAt
    have hprev := ih hf_prev hcont_l
    have hibp := integral_bernoulliKernel_mul_eq_sub hl hab (hf l (Nat.lt_succ_self l)) hfl
    rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hl), Nat.add_sub_cancel, hprev, hibp]
    have hpow : (-1 : ℝ) ^ (l + 1 + 1) = -((-1 : ℝ) ^ (l + 1)) := by
      rw [pow_succ]
      ring
    rw [hpow]
    ring

/-- **Higher-order Euler–Maclaurin summation formula** (`l ≥ 1`) on `Finset.Ioc M N` for natural
numbers `M ≤ N`. -/
theorem euler_maclaurin_higher_order_Ioc {l : ℕ} (hl : 1 ≤ l) {M N : ℕ} (hMN : M ≤ N)
    {f : ℝ → ℝ}
    (hf : ∀ j < l, ∀ t ∈ Set.Icc (M : ℝ) N,
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t)
    (hfl : ContinuousOn (iteratedDeriv l f) (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Ioc M N, f (n : ℝ) =
      (∫ t in (M : ℝ)..N, f t) +
        (∑ j ∈ Finset.Icc 1 l, (-1 : ℝ) ^ j *
          (bernoulliKernel j N * iteratedDeriv (j - 1) f N -
            bernoulliKernel j M * iteratedDeriv (j - 1) f M)) +
        (-1 : ℝ) ^ (l + 1) * (∫ t in (M : ℝ)..N, bernoulliKernel l t * iteratedDeriv l f t) := by
  have h := euler_maclaurin_higher_order_Ioc_int hl (Nat.cast_le.mpr hMN) hf hfl
  have hsum : ∑ n ∈ Finset.Ioc ⌊(M : ℝ)⌋ ⌊(N : ℝ)⌋, f (n : ℝ) = ∑ n ∈ Finset.Ioc M N, f (n : ℝ) := by
    rw [Int.floor_natCast, Int.floor_natCast]
    refine Finset.sum_bij (fun (z : ℤ) _ => Int.toNat z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_Ioc] at hz ⊢
      omega
    · intro z₁ hz₁ z₂ hz₂ h
      simp only [Finset.mem_Ioc] at hz₁ hz₂
      omega
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      refine ⟨(n : ℤ), ?_, Int.toNat_natCast n⟩
      simp only [Finset.mem_Ioc]
      exact ⟨Int.ofNat_lt.mpr hn.1, Int.ofNat_le.mpr hn.2⟩
    · intro z hz
      simp only [Finset.mem_Ioc] at hz
      rw [← Int.cast_natCast z.toNat, Int.toNat_of_nonneg (by omega)]
  rw [← hsum]
  exact h

/-- **Higher-order Euler–Maclaurin summation formula** (`l ≥ 1`) on `Finset.Icc M N` for natural
numbers `M ≤ N`. -/
theorem euler_maclaurin_higher_order_Icc {l : ℕ} (hl : 1 ≤ l) {M N : ℕ} (hMN : M ≤ N)
    {f : ℝ → ℝ}
    (hf : ∀ j < l, ∀ t ∈ Set.Icc (M : ℝ) N,
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t)
    (hfl : ContinuousOn (iteratedDeriv l f) (Set.Icc (M : ℝ) N)) :
    ∑ n ∈ Finset.Icc M N, f (n : ℝ) =
      f M + (∫ t in (M : ℝ)..N, f t) +
        (∑ j ∈ Finset.Icc 1 l, (-1 : ℝ) ^ j *
          (bernoulliKernel j N * iteratedDeriv (j - 1) f N -
            bernoulliKernel j M * iteratedDeriv (j - 1) f M)) +
        (-1 : ℝ) ^ (l + 1) * (∫ t in (M : ℝ)..N, bernoulliKernel l t * iteratedDeriv l f t) := by
  rw [Finset.Icc_eq_cons_Ioc hMN, Finset.sum_cons,
    euler_maclaurin_higher_order_Ioc hl hMN hf hfl]
  ring

end HigherOrderEulerMaclaurin

section HarmonicAsymptotic

private lemma hasDerivAt_inv_iterated {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x⁻¹) (-(t ^ 2)⁻¹) t ∧
      iteratedDeriv 1 (fun x : ℝ => x⁻¹) t = -(t ^ 2)⁻¹ ∧
      HasDerivAt (iteratedDeriv 1 (fun x : ℝ => x⁻¹)) (2 * (t ^ 3)⁻¹) t ∧
      iteratedDeriv 2 (fun x : ℝ => x⁻¹) t = 2 * (t ^ 3)⁻¹ := by
  have hd1 : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => u⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv hx.ne'
  have heq1 : Set.EqOn (iteratedDeriv 1 (fun u : ℝ => u⁻¹)) (fun x : ℝ => -(x ^ 2)⁻¹)
      (Set.Ioi (0 : ℝ)) := by
    intro x hx
    rw [iteratedDeriv_one]
    exact (hd1 x hx).deriv
  have hd2_aux : HasDerivAt (fun x : ℝ => -(x ^ 2)⁻¹) (2 * (t ^ 3)⁻¹) t := by
    have hsq := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.ne')
    convert hsq.neg using 1
    field_simp [ht.ne']
    ring
  have hev : iteratedDeriv 1 (fun u : ℝ => u⁻¹) =ᶠ[𝓝 t] fun x : ℝ => -(x ^ 2)⁻¹ :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (0 : ℝ) from ht)) heq1
  have hd2 : HasDerivAt (iteratedDeriv 1 (fun u : ℝ => u⁻¹)) (2 * (t ^ 3)⁻¹) t :=
    hd2_aux.congr_of_eventuallyEq hev
  have hid2 : iteratedDeriv 2 (fun u : ℝ => u⁻¹) t = 2 * (t ^ 3)⁻¹ := by
    rw [iteratedDeriv_succ]
    exact hd2.deriv
  exact ⟨hd1 t ht, heq1 ht, hd2, hid2⟩

private lemma integrableOn_bernoulliKernel_two_div_cube {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => bernoulliKernel 2 t / t ^ 3) (Set.Ioi x) ∧
      |∫ t in Set.Ioi x, bernoulliKernel 2 t / t ^ 3| ≤ 1 / (24 * x ^ 2) := by
  have hpow_int : IntegrableOn (fun t : ℝ => (1 / 12 : ℝ) * t ^ (-3 : ℝ)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx).const_mul (1 / 12)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => bernoulliKernel 2 t / t ^ 3)
      (volume.restrict (Set.Ioi x)) := by
    have hcont : ContinuousOn (fun t : ℝ => bernoulliKernel 2 t / t ^ 3) (Set.Ioi x) :=
      (continuous_bernoulliKernel (by omega)).continuousOn.div (continuous_pow 3).continuousOn
        fun t ht => pow_ne_zero 3 (hx.trans ht).ne'
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => bernoulliKernel 2 t / t ^ 3) (Set.Ioi x) := by
    refine Integrable.mono' hpow_int hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 3), div_eq_mul_inv,
      ← Real.rpow_natCast t 3, ← Real.rpow_neg ht0.le]
    exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le t) (Real.rpow_nonneg ht0.le _)
  have hIoi_cube : ∫ t in Set.Ioi x, t ^ (-3 : ℝ) = 1 / (2 * x ^ 2) := by
    have htend : Tendsto (fun R : ℝ => ∫ t in x..R, t ^ (-3 : ℝ)) atTop
        (𝓝 (∫ t in Set.Ioi x, t ^ (-3 : ℝ))) :=
      intervalIntegral_tendsto_integral_Ioi x (integrableOn_Ioi_rpow_of_lt (by norm_num) hx)
        tendsto_id
    have heval : ∀ᶠ R in atTop, ∫ t in x..R, t ^ (-3 : ℝ) =
        1 / (2 * x ^ 2) - 1 / (2 * R ^ 2) := by
      filter_upwards [eventually_ge_atTop x] with R hR
      have h0 : (0 : ℝ) ∉ Set.uIcc x R := by
        rw [Set.uIcc_of_le hR]
        exact fun h => lt_irrefl (0 : ℝ) (hx.trans_le h.1)
      have hR0 : 0 < R := hx.trans_le hR
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      have hexp : (-3 : ℝ) + 1 = (-2 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg hR0.le, Real.rpow_neg hx.le, Real.rpow_two, Real.rpow_two]
      ring
    have hlim : Tendsto (fun R : ℝ => 1 / (2 * x ^ 2) - 1 / (2 * R ^ 2)) atTop
        (𝓝 (1 / (2 * x ^ 2))) := by
      have h0 : Tendsto (fun R : ℝ => 1 / (2 * R ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop zero_lt_two)
      simpa only [sub_zero] using tendsto_const_nhds.sub h0
    exact tendsto_nhds_unique htend (hlim.congr' (heval.mono fun _ h => h.symm))
  have hbd : |∫ t in Set.Ioi x, bernoulliKernel 2 t / t ^ 3| ≤ 1 / (24 * x ^ 2) := by
    calc |∫ t in Set.Ioi x, bernoulliKernel 2 t / t ^ 3|
        ≤ ∫ t in Set.Ioi x, ‖bernoulliKernel 2 t / t ^ 3‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi x, (1 / 12 : ℝ) * t ^ (-3 : ℝ) := by
          refine setIntegral_mono_on hint.norm hpow_int measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hx.trans ht
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 3), div_eq_mul_inv,
            ← Real.rpow_natCast t 3, ← Real.rpow_neg ht0.le]
          exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le t)
            (Real.rpow_nonneg ht0.le _)
      _ = (1 / 12 : ℝ) * ∫ t in Set.Ioi x, t ^ (-3 : ℝ) := integral_const_mul _ _
      _ = 1 / (24 * x ^ 2) := by rw [hIoi_cube]; ring
  exact ⟨hint, hbd⟩

/-- Exact 2nd-order Euler–Maclaurin formula for the harmonic sum `∑_{1 ≤ n ≤ N} 1/n` (`1 ≤ N`). -/
theorem harmonic_euler_maclaurin_second_order {N : ℕ} (hN : 1 ≤ N) :
    (harmonic N : ℝ) = Real.log N + 1 / 2 + 1 / (2 * (N : ℝ)) + 1 / 12 -
      1 / (12 * (N : ℝ) ^ 2) - 2 * ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 3 := by
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le h1N
  have hsum : (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
    rw [← Nat.floor_natCast (R := ℝ) N, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.floor_natCast]
  have hf : ∀ j < 2, ∀ t ∈ Set.Icc (1 : ℝ) N,
      HasDerivAt (iteratedDeriv j (fun x : ℝ => x⁻¹))
        (iteratedDeriv (j + 1) (fun x : ℝ => x⁻¹) t) t := by
    intro j hj t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have hd := hasDerivAt_inv_iterated ht0
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj0 | rfl
    · have hj_zero : j = 0 := by omega
      subst hj_zero
      rw [iteratedDeriv_zero, zero_add, hd.2.1]
      exact hd.1
    · rw [hd.2.2.2]
      exact hd.2.2.1
  have hfl : ContinuousOn (iteratedDeriv 2 (fun x : ℝ => x⁻¹)) (Set.Icc (1 : ℝ) N) := by
    have heq : Set.EqOn (iteratedDeriv 2 (fun x : ℝ => x⁻¹)) (fun t : ℝ => 2 * (t ^ 3)⁻¹)
        (Set.Icc (1 : ℝ) N) := fun t ht => (hasDerivAt_inv_iterated (zero_lt_one.trans_le ht.1)).2.2.2
    refine ContinuousOn.congr ?_ heq
    refine continuousOn_const.mul
      ((continuousOn_pow 3).inv₀ fun (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) => ?_)
    exact pow_ne_zero 3 (zero_lt_one.trans_le ht.1).ne'
  have hem := euler_maclaurin_higher_order_Icc (l := 2) (by norm_num) hN hf hfl
  have h1_deriv : iteratedDeriv 1 (fun x : ℝ => x⁻¹) 1 = -1 := by
    have h := (hasDerivAt_inv_iterated zero_lt_one).2.1
    simpa only [one_pow, inv_one] using h
  have hN_deriv : iteratedDeriv 1 (fun x : ℝ => x⁻¹) N = -((N : ℝ) ^ 2)⁻¹ :=
    (hasDerivAt_inv_iterated hN0).2.1
  have hint_main : ∫ t in (1 : ℝ)..N, t⁻¹ = Real.log N := by
    rw [integral_inv_of_pos zero_lt_one hN0, div_one]
  have hint_rem : ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t * iteratedDeriv 2 (fun x : ℝ => x⁻¹) t =
      2 * ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 3 := by
    have hcongr : ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t * iteratedDeriv 2 (fun x : ℝ => x⁻¹) t =
        ∫ t in (1 : ℝ)..N, 2 * (bernoulliKernel 2 t / t ^ 3) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le h1N] at ht
      have h2 := (hasDerivAt_inv_iterated (zero_lt_one.trans_le ht.1)).2.2.2
      rw [h2, div_eq_mul_inv]
      ring
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hIcc_sum : ∑ j ∈ Finset.Icc 1 2, (-1 : ℝ) ^ j *
        (bernoulliKernel j N * iteratedDeriv (j - 1) (fun x : ℝ => x⁻¹) N -
          bernoulliKernel j 1 * iteratedDeriv (j - 1) (fun x : ℝ => x⁻¹) 1) =
      -((-1 / 2 : ℝ) * (N : ℝ)⁻¹ - (-1 / 2 : ℝ) * 1⁻¹) +
        ((1 / 12 : ℝ) * (-((N : ℝ) ^ 2)⁻¹) - (1 / 12 : ℝ) * (-1)) := by
    have hbk1N : bernoulliKernel 1 (N : ℝ) = -1 / 2 := by
      rw [bernoulliKernel_one, sawtooth_natCast]
    have hbk11 : bernoulliKernel 1 (1 : ℝ) = -1 / 2 := by
      rw [bernoulliKernel_one]
      exact sawtooth_intCast 1
    have hbk2N : bernoulliKernel 2 (N : ℝ) = 1 / 12 := bernoulliKernel_two_natCast N
    have hbk21 : bernoulliKernel 2 (1 : ℝ) = 1 / 12 := by simpa using bernoulliKernel_two_natCast 1
    rw [Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]
    simp only [Nat.sub_self, show (2 - 1 : ℕ) = 1 by rfl, iteratedDeriv_zero, hbk1N, hbk11, hbk2N,
      hbk21, h1_deriv, hN_deriv]
    norm_num
  rw [← hsum, Nat.cast_one] at hem
  rw [hem, hint_main, hIcc_sum, hint_rem]
  ring

/-- Expression for the Euler–Mascheroni constant `γ` via the 2nd-order Bernoulli remainder:
`γ = 7/12 - 2 * ∫ t in Ioi 1, bernoulliKernel 2 t / t³`. -/
theorem eulerMascheroniConstant_eq_bernoulliKernel_two_integral :
    Real.eulerMascheroniConstant =
      7 / 12 - 2 * ∫ t in Set.Ioi (1 : ℝ), bernoulliKernel 2 t / t ^ 3 := by
  have hlim1 : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N)
      atTop (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have htail := (integrableOn_bernoulliKernel_two_div_cube zero_lt_one).1
  have hlim2 : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N)
      atTop (𝓝 (7 / 12 - 2 * ∫ t in Set.Ioi (1 : ℝ), bernoulliKernel 2 t / t ^ 3)) := by
    have hcongr : (fun N : ℕ => (harmonic N : ℝ) - Real.log N) =ᶠ[atTop]
        (fun N : ℕ => 7 / 12 + 1 / (2 * (N : ℝ)) - 1 / (12 * (N : ℝ) ^ 2) -
          2 * ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 3) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h := harmonic_euler_maclaurin_second_order hN
      linarith
    refine Tendsto.congr' hcongr.symm ?_
    have h1 : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two)
    have h2 : Tendsto (fun N : ℕ => 1 / (12 * (N : ℝ) ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num))
    have h3 : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 3) atTop
        (𝓝 (∫ t in Set.Ioi (1 : ℝ), bernoulliKernel 2 t / t ^ 3)) :=
      intervalIntegral_tendsto_integral_Ioi 1 htail tendsto_natCast_atTop_atTop
    simpa only [add_zero, sub_zero] using
      ((tendsto_const_nhds.add h1).sub h2).sub (h3.const_mul 2)
  exact tendsto_nhds_unique hlim1 hlim2

/-- Explicit `O(N⁻²)` bound for the 2nd-order harmonic asymptotic (`1 ≤ N`):
`|(harmonic N : ℝ) - (log N + γ + 1 / (2 * N))| ≤ 1 / (6 * N²)`. -/
theorem abs_harmonic_sub_log_sub_gamma_sub_half_inv_le {N : ℕ} (hN : 1 ≤ N) :
    |(harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant + 1 / (2 * (N : ℝ)))| ≤
      1 / (6 * (N : ℝ) ^ 2) := by
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le h1N
  have htail1 := (integrableOn_bernoulliKernel_two_div_cube zero_lt_one).1
  have h1 : IntegrableOn (fun t : ℝ => bernoulliKernel 2 t / t ^ 3) (Set.Ioc 1 N) :=
    htail1.mono_set Set.Ioc_subset_Ioi_self
  have h2 := integrableOn_bernoulliKernel_two_div_cube hN0
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), bernoulliKernel 2 t / t ^ 3 =
      (∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 3) +
        ∫ t in Set.Ioi (N : ℝ), bernoulliKernel 2 t / t ^ 3 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi h1N,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2.1,
      intervalIntegral.integral_of_le h1N]
  have hdiff : (harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant + 1 / (2 * (N : ℝ))) =
      2 * (∫ t in Set.Ioi (N : ℝ), bernoulliKernel 2 t / t ^ 3) - 1 / (12 * (N : ℝ) ^ 2) := by
    rw [harmonic_euler_maclaurin_second_order hN,
      eulerMascheroniConstant_eq_bernoulliKernel_two_integral, hsplit]
    ring
  rw [hdiff]
  have h12_abs : |1 / (12 * (N : ℝ) ^ 2)| = 1 / (12 * (N : ℝ) ^ 2) := abs_of_nonneg (by positivity)
  calc |2 * (∫ t in Set.Ioi (N : ℝ), bernoulliKernel 2 t / t ^ 3) - 1 / (12 * (N : ℝ) ^ 2)|
      ≤ |2 * (∫ t in Set.Ioi (N : ℝ), bernoulliKernel 2 t / t ^ 3)| + |1 / (12 * (N : ℝ) ^ 2)| :=
        abs_sub _ _
    _ = 2 * |∫ t in Set.Ioi (N : ℝ), bernoulliKernel 2 t / t ^ 3| + 1 / (12 * (N : ℝ) ^ 2) := by
        rw [abs_mul, abs_of_pos zero_lt_two, h12_abs]
    _ ≤ 2 * (1 / (24 * (N : ℝ) ^ 2)) + 1 / (12 * (N : ℝ) ^ 2) := by gcongr; exact h2.2
    _ = 1 / (6 * (N : ℝ) ^ 2) := by ring

/-- Big-O 2nd-order harmonic asymptotic:
`∑_{n=1..N} 1/n = log N + γ + 1/(2N) + O(N⁻²)` as `N → ∞`. -/
theorem harmonic_asymptotic_isBigO :
    (fun N : ℕ => (harmonic N : ℝ) -
        (Real.log N + Real.eulerMascheroniConstant + 1 / (2 * (N : ℝ))))
      =O[atTop] (fun N : ℕ => ((N : ℝ) ^ 2)⁻¹) := by
  refine isBigO_iff.mpr ⟨1 / 6, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have h := abs_harmonic_sub_log_sub_gamma_sub_half_inv_le hN
  have hrhs : 1 / (6 * (N : ℝ) ^ 2) = 1 / 6 * ((N : ℝ) ^ 2)⁻¹ := by ring
  linarith [h, hrhs]

end HarmonicAsymptotic

section StirlingLogSum

/-- The sum `∑_{1 ≤ n ≤ N} log n` equals `Real.log (N ! : ℝ)`. -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) = Real.log (N ! : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos N), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- First-order Euler–Maclaurin formula for `∑_{1 ≤ n ≤ N} log n` (`1 ≤ N`):
`∑_{n=1..N} log n = N log N - N + 1 + (1/2) log N + ∫_1^N sawtooth(t) / t dt`. -/
theorem sum_log_first_order_formula {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) =
      (N : ℝ) * Real.log N - N + 1 + Real.log N / 2 +
        ∫ t in (1 : ℝ)..N, sawtooth t / t := by
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hf : ∀ t ∈ Set.Icc (1 : ℝ) N, HasDerivAt Real.log t⁻¹ t := fun t ht =>
    Real.hasDerivAt_log (zero_lt_one.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (1 : ℝ) N) :=
    continuousOn_inv₀.mono fun t ht => (zero_lt_one.trans_le ht.1).ne'
  have hem := euler_maclaurin_first_order_Icc hN hf hcont
  rw [Nat.cast_one, integral_log, Real.log_one] at hem
  have hcongr : ∫ t in (1 : ℝ)..N, sawtooth t * t⁻¹ = ∫ t in (1 : ℝ)..N, sawtooth t / t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [div_eq_mul_inv]
  rw [hcongr] at hem
  linarith

/-- Explicit `log N + 1` error bound for `∑_{1 ≤ n ≤ N} log n - (N log N - N)` (`1 ≤ N`). -/
theorem abs_sum_log_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log N - N)| ≤ Real.log N + 1 := by
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le h1N
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg h1N
  have hdiff : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log N - N) =
      1 + Real.log N / 2 + ∫ t in (1 : ℝ)..N, sawtooth t / t := by
    rw [sum_log_first_order_formula hN]
    ring
  have hint_bd : |∫ t in (1 : ℝ)..N, sawtooth t / t| ≤ Real.log N / 2 := by
    have hsaw_int : IntervalIntegrable (fun t : ℝ => sawtooth t / t) volume 1 N := by
      have hEq : (fun t : ℝ => sawtooth t / t) = fun t : ℝ => bernoulliKernel 1 t * t⁻¹ := by
        ext t; simp [bernoulliKernel_one, div_eq_mul_inv]
      rw [hEq]
      exact intervalIntegrable_bernoulliKernel_mul 1 h1N
        (continuousOn_inv₀.mono fun (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) =>
          (zero_lt_one.trans_le ht.1).ne')
    have hinv_int : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) * t⁻¹) volume 1 N :=
      (intervalIntegral.intervalIntegrable_inv (fun t ht => by
        rw [Set.uIcc_of_le h1N] at ht
        exact (zero_lt_one.trans_le ht.1).ne') (by fun_prop)).const_mul (1 / 2)
    have hnorm : |∫ t in (1 : ℝ)..N, sawtooth t / t| ≤
        ∫ t in (1 : ℝ)..N, ‖sawtooth t / t‖ :=
      intervalIntegral.norm_integral_le_integral_norm h1N
    have hmono : ∫ t in (1 : ℝ)..N, ‖sawtooth t / t‖ ≤
        ∫ t in (1 : ℝ)..N, (1 / 2 : ℝ) * t⁻¹ := by
      refine intervalIntegral.integral_mono_on h1N hsaw_int.norm hinv_int fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (sawtooth_abs_le t) (inv_nonneg.mpr ht0.le)
    have heval : ∫ t in (1 : ℝ)..N, (1 / 2 : ℝ) * t⁻¹ = Real.log N / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hN0, div_one]
      ring
    exact hnorm.trans (hmono.trans_eq heval)
  rw [hdiff]
  calc |1 + Real.log N / 2 + ∫ t in (1 : ℝ)..N, sawtooth t / t|
      ≤ |1 + Real.log N / 2| + |∫ t in (1 : ℝ)..N, sawtooth t / t| := abs_add_le _ _
    _ = 1 + Real.log N / 2 + |∫ t in (1 : ℝ)..N, sawtooth t / t| := by
        rw [abs_of_nonneg (by linarith)]
    _ ≤ 1 + Real.log N / 2 + Real.log N / 2 := by linarith
    _ = Real.log N + 1 := by ring

/-- Stirling / factorial log-sum asymptotic:
`∑_{n=1..N} log n = N log N - N + O(log N)` as `N → ∞`. -/
theorem sum_log_sub_isBigO_log :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) - ((N : ℝ) * Real.log N - N))
      =O[atTop] (fun N : ℕ => Real.log N) := by
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with N hN
  have h1N : 1 ≤ N := by omega
  have h3N : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1log : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by linarith))
  have hpos : 0 ≤ Real.log N := zero_le_one.trans h1log
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos]
  exact (abs_sum_log_sub_le h1N).trans (by linarith)

/-- Refined Stirling log-sum bound with explicit `(1/2) log N` term (`1 ≤ N`):
`|(∑_{n=1..N} log n) - (N log N - N + (1/2) log N)| ≤ 5 / 4`. -/
theorem abs_sum_log_sub_half_log_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) -
        ((N : ℝ) * Real.log N - N + Real.log N / 2)| ≤ 5 / 4 := by
  have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hN0 : 0 < (N : ℝ) := zero_lt_one.trans_le h1N
  have hg : ∀ t ∈ Set.Icc (1 : ℝ) N, HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t :=
    fun t ht => hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
  have hg' : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) N) :=
    ((continuousOn_pow 2).inv₀ fun (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) =>
      pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne').neg
  have hibp := integral_bernoulliKernel_mul_eq_sub (j := 1) le_rfl h1N hg hg'
  have hbk21 : bernoulliKernel 2 (1 : ℝ) = 1 / 12 := by simpa using bernoulliKernel_two_natCast 1
  have hbk2N : bernoulliKernel 2 (N : ℝ) = 1 / 12 := bernoulliKernel_two_natCast N
  simp only [bernoulliKernel_one, show (1 + 1 : ℕ) = 2 by rfl, hbk21, hbk2N] at hibp
  have hcongr1 : ∫ t in (1 : ℝ)..N, sawtooth t * t⁻¹ = ∫ t in (1 : ℝ)..N, sawtooth t / t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [div_eq_mul_inv]
  have hcongr2 : ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t * -(t ^ 2)⁻¹ =
      -∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hcongr1, hcongr2] at hibp
  have hdiff : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) -
        ((N : ℝ) * Real.log N - N + Real.log N / 2) =
      1 + (1 / 12 * (N : ℝ)⁻¹ - 1 / 12) + ∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 2 := by
    rw [sum_log_first_order_formula hN, hibp]
    ring
  have hint_bd : |∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 2| ≤ 1 / 12 := by
    have h_int : IntervalIntegrable (fun t : ℝ => bernoulliKernel 2 t / t ^ 2) volume 1 N := by
      have hEq : (fun t : ℝ => bernoulliKernel 2 t / t ^ 2) =
          fun t : ℝ => bernoulliKernel 2 t * (t ^ 2)⁻¹ := by
        ext t; rw [div_eq_mul_inv]
      rw [hEq]
      exact intervalIntegrable_bernoulliKernel_mul 2 h1N
        ((continuousOn_pow 2).inv₀ fun (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) =>
          pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne')
    have hpow_int : IntervalIntegrable (fun t : ℝ => (1 / 12 : ℝ) * t ^ (-2 : ℝ)) volume 1 N := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le h1N]
      refine ((continuousOn_of_forall_continuousAt fun (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) N) =>
        Real.continuousAt_rpow_const t (-2) (Or.inl (zero_lt_one.trans_le ht.1).ne')).const_smul
          (1 / 12 : ℝ)).integrableOn_Icc
    have hnorm : |∫ t in (1 : ℝ)..N, bernoulliKernel 2 t / t ^ 2| ≤
        ∫ t in (1 : ℝ)..N, ‖bernoulliKernel 2 t / t ^ 2‖ :=
      intervalIntegral.norm_integral_le_integral_norm h1N
    have hmono : ∫ t in (1 : ℝ)..N, ‖bernoulliKernel 2 t / t ^ 2‖ ≤
        ∫ t in (1 : ℝ)..N, (1 / 12 : ℝ) * t ^ (-2 : ℝ) := by
      refine intervalIntegral.integral_mono_on h1N h_int.norm hpow_int fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0), div_eq_mul_inv,
        ← Real.rpow_two t, ← Real.rpow_neg ht0.le]
      exact mul_le_mul_of_nonneg_right (bernoulliKernel_two_abs_le t)
        (Real.rpow_nonneg ht0.le _)
    have heval : ∫ t in (1 : ℝ)..N, (1 / 12 : ℝ) * t ^ (-2 : ℝ) = (1 / 12 : ℝ) * (1 - (N : ℝ)⁻¹) := by
      have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) N := by
        rw [Set.uIcc_of_le h1N]
        exact fun h => lt_irrefl (0 : ℝ) (zero_lt_one.trans_le h.1)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      have hexp : (-2 : ℝ) + 1 = (-1 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg hN0.le, Real.rpow_one, Real.one_rpow]
      ring
    have hle1 : (1 / 12 : ℝ) * (1 - (N : ℝ)⁻¹) ≤ 1 / 12 := by
      have : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0.le
      linarith
    exact hnorm.trans ((hmono.trans_eq heval).trans hle1)
  rw [hdiff]
  have hinv_le : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1N
  have hinv_nn : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0.le
  rw [abs_le] at hint_bd
  rw [abs_le]
  constructor <;> linarith

/-- Refined Stirling log-sum asymptotic:
`∑_{n=1..N} log n = N log N - N + (1/2) log N + O(1)` as `N → ∞`. -/
theorem sum_log_sub_half_log_isBigO_one :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) -
        ((N : ℝ) * Real.log N - N + Real.log N / 2))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨5 / 4, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact abs_sum_log_sub_half_log_le hN

end StirlingLogSum

end AnalyticNumberTheory.AnalyticTools.Summation

