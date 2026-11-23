import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Abel Summation and Elementary Asymptotics

This file develops discrete and continuous Abel summation (summation by parts) over `Finset.Ioc`
and `Finset.Icc`, together with standard asymptotic formulas in analytic number theory:

- Discrete summation by parts (`abel_discrete_by_parts`, `abel_discrete_Ioc`,
  `abel_discrete_Ioc_from`, `abel_discrete_Icc_one`, `abel_discrete_Icc`).
- Continuous Abel summation wrappers over `Finset.Ioc` and `Finset.Icc 1 ⌊x⌋₊` without requiring
  `c 0 = 0`, using `ContinuousOn (deriv f)` or explicit `HasDerivAt` hypotheses.
- Harmonic sum bounds and exact asymptotic `∑_{1 ≤ n ≤ x} 1/n = log x + γ + O(1/x)`.
- Log-harmonic sum asymptotic `∑_{1 ≤ n ≤ x} (log n)/n = (log x)² / 2 + γ₁ + O((log x)/x)`.
- Power sum asymptotics `∑_{1 ≤ n ≤ x} n^(-α)` for all real `α ≠ 1`.
-/

noncomputable section

open Finset MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools.Summation

section DiscreteAbel

/-- General discrete summation by parts on `Finset.Ioc a b` for any partial-sum sequence `S`
satisfying `S (k + 1) - S k = c (k + 1)`. -/
theorem abel_discrete_by_parts {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (c S : ℕ → M) (f : ℕ → R) (hS : ∀ k, S (k + 1) - S k = c (k + 1))
    {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, f k • c k =
      f b • S b - f a • S a - ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) • S k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih,
      Finset.sum_Ico_succ_top hab, ← hS b, smul_sub, sub_smul]
    abel

/-- Discrete summation by parts on `Finset.Ioc a b` using cumulative partial sums from `1`. -/
theorem abel_discrete_Ioc {R : Type*} [CommRing R] (bseq f : ℕ → R) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, bseq k * f k =
      (∑ i ∈ Finset.Icc 1 b, bseq i) * f b - (∑ i ∈ Finset.Icc 1 a, bseq i) * f a -
        ∑ k ∈ Finset.Ico a b, (∑ i ∈ Finset.Icc 1 k, bseq i) * (f (k + 1) - f k) := by
  let S : ℕ → R := fun k => ∑ i ∈ Finset.Icc 1 k, bseq i
  have hS : ∀ k, S (k + 1) - S k = bseq (k + 1) := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    simp only [S, Finset.sum_Icc_succ_top hk]
    ring
  have h := abel_discrete_by_parts bseq S f hS hab
  simp only [smul_eq_mul] at h
  simpa only [mul_comm (f _), mul_comm (f _ - f _)] using h

/-- Discrete summation by parts on `Finset.Ioc a b` using partial sums anchored at `a`. -/
theorem abel_discrete_Ioc_from {R : Type*} [CommRing R] (bseq f : ℕ → R) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, bseq k * f k =
      (∑ i ∈ Finset.Ioc a b, bseq i) * f b -
        ∑ k ∈ Finset.Ico a b, (∑ i ∈ Finset.Ioc a k, bseq i) * (f (k + 1) - f k) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih,
      Finset.sum_Ico_succ_top hab, Finset.sum_Ioc_succ_top hab]
    ring

/-- Discrete summation by parts on `Finset.Icc 1 N`. -/
theorem abel_discrete_Icc_one {R : Type*} [CommRing R] (bseq f : ℕ → R) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, bseq k * f k =
      (∑ i ∈ Finset.Icc 1 N, bseq i) * f N -
        ∑ k ∈ Finset.Ico 1 N, (∑ i ∈ Finset.Icc 1 k, bseq i) * (f (k + 1) - f k) := by
  rcases Nat.eq_zero_or_pos N with rfl | _hN
  · simp
  · have h := abel_discrete_Ioc_from bseq f (a := 0) (b := N) (Nat.zero_le N)
    have hIoc : ∀ m, Finset.Ioc 0 m = Finset.Icc 1 m := fun m => by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    have hIco : Finset.Ico 0 N = insert 0 (Finset.Ico 1 N) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hIoc N, hIco, Finset.sum_insert (by simp)] at h
    simpa only [Finset.Ioc_self, Finset.sum_empty, zero_mul, zero_add, hIoc] using h

/-- Discrete summation by parts on `Finset.Icc a b` for `a ≤ b`. -/
theorem abel_discrete_Icc {R : Type*} [CommRing R] (bseq f : ℕ → R) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, bseq k * f k =
      (∑ i ∈ Finset.Icc a b, bseq i) * f b -
        ∑ k ∈ Finset.Ico a b, (∑ i ∈ Finset.Icc a k, bseq i) * (f (k + 1) - f k) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hab), ih,
      Finset.sum_Ico_succ_top hab, Finset.sum_Icc_succ_top (Nat.le_succ_of_le hab)]
    ring

end DiscreteAbel

section ContinuousAbel

variable {𝕜 : Type*} [RCLike 𝕜]

private lemma sum_Icc_zero_ite_eq {c : ℕ → 𝕜} (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (if k = 0 then (0 : 𝕜) else c k) = ∑ k ∈ Finset.Icc 1 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc,
    zero_add]
  simp only [↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  split_ifs with h
  · exact absurd h hk0
  · rfl

/-- Continuous Abel summation on `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊` for `0 ≤ a ≤ b` with partial sums
starting at `0`. -/
theorem abel_summation_Ioc (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_cont : ContinuousOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c k * f k =
      (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) * f b - (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, c k) * f a -
        ∫ t in a..b, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) * deriv f t := by
  have h := sum_mul_eq_sub_sub_integral_mul c ha hab hf_diff hf_cont.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at h
  have hsum : ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c k * f k =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hsum, h, mul_comm (f b), mul_comm (f a)]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mul_comm]

/-- Continuous Abel summation on `Finset.Ioc ⌊a⌋₊ ⌊b⌋₊` for `0 ≤ a ≤ b` using partial sums
anchored at `1` (`∑ k ∈ Icc 1 ⌊t⌋₊, c k`), without needing `c 0 = 0`. -/
theorem abel_summation_Ioc_one (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_cont : ContinuousOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c k * f k =
      (∑ k ∈ Finset.Icc 1 ⌊b⌋₊, c k) * f b - (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, c k) * f a -
        ∫ t in a..b, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * deriv f t := by
  let c₀ : ℕ → 𝕜 := fun k => if k = 0 then 0 else c k
  have h := abel_summation_Ioc c₀ ha hab hf_diff hf_cont
  have hLHS : ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c₀ k * f k =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c k * f k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Ioc.mp hk).1
      omega
    simp [c₀, hk0]
  rw [hLHS] at h
  simp_rw [c₀, sum_Icc_zero_ite_eq] at h
  exact h

/-- Continuous Abel summation on `Finset.Icc 1 ⌊x⌋₊` for `1 ≤ x`. -/
theorem abel_summation_Icc_one (c : ℕ → 𝕜) {f : ℝ → 𝕜} {x : ℝ}
    (hx : 1 ≤ x)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ f t)
    (hf_cont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) x)) :
    ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, c k * f k =
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, c k) * f x -
        ∫ t in (1 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * deriv f t := by
  have hIoc := abel_summation_Ioc_one c zero_le_one hx hf_diff hf_cont
  have hfloor1 : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
  have hle : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hsplit : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, c k * f k =
      c 1 * f 1 + ∑ k ∈ Finset.Ioc 1 ⌊x⌋₊, c k * f k := by
    rw [Finset.Icc_eq_cons_Ioc hle, Finset.sum_cons, Nat.cast_one]
  rw [hfloor1, Finset.Icc_self, Finset.sum_singleton] at hIoc
  rw [hsplit, hIoc]
  ring

/-- Continuous Abel summation on `Finset.Icc 1 ⌊x⌋₊` for `1 ≤ x`, taking an explicit derivative
function `f'` instead of `deriv f`. -/
theorem abel_summation_Icc_one_hasDerivAt (c : ℕ → 𝕜) {f f' : ℝ → 𝕜} {x : ℝ}
    (hx : 1 ≤ x)
    (hf_deriv : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc (1 : ℝ) x)) :
    ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, c k * f k =
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, c k) * f x -
        ∫ t in (1 : ℝ)..x, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * f' t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ f t := fun t ht =>
    (hf_deriv t ht).differentiableAt
  have hEq : Set.EqOn (deriv f) f' (Set.Icc (1 : ℝ) x) := fun t ht =>
    (hf_deriv t ht).deriv
  have hcont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) x) := hf'_cont.congr hEq
  rw [abel_summation_Icc_one c hx hdiff hcont]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hx] at ht
  rw [hEq ht]

/-- Continuous Abel summation on `Finset.Icc 1 N` for a natural number `N ≥ 1`. -/
theorem abel_summation_Icc_nat (c : ℕ → 𝕜) {f : ℝ → 𝕜} {N : ℕ} (hN : 1 ≤ N)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t)
    (hf_cont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) N)) :
    ∑ k ∈ Finset.Icc 1 N, c k * f k =
      (∑ k ∈ Finset.Icc 1 N, c k) * f N -
        ∫ t in (1 : ℝ)..N, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * deriv f t := by
  have hx : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  simpa only [Nat.floor_natCast] using abel_summation_Icc_one c hx hf_diff hf_cont

/-- Continuous Abel summation on `Finset.Ioc M N` for natural numbers `M ≤ N`. -/
theorem abel_summation_Ioc_nat (c : ℕ → 𝕜) {f : ℝ → 𝕜} {M N : ℕ} (hMN : M ≤ N)
    (hf_diff : ∀ t ∈ Set.Icc (M : ℝ) N, DifferentiableAt ℝ f t)
    (hf_cont : ContinuousOn (deriv f) (Set.Icc (M : ℝ) N)) :
    ∑ k ∈ Finset.Ioc M N, c k * f k =
      (∑ k ∈ Finset.Icc 1 N, c k) * f N - (∑ k ∈ Finset.Icc 1 M, c k) * f M -
        ∫ t in (M : ℝ)..N, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * deriv f t := by
  simpa only [Nat.floor_natCast] using
    abel_summation_Ioc_one c (Nat.cast_nonneg M) (Nat.cast_le.mpr hMN) hf_diff hf_cont

end ContinuousAbel

section InternalAux

private lemma sum_one_Icc_eq_sub_fract {t : ℝ} (ht : 0 ≤ t) :
    ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) = t - Int.fract t := by
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
    ← Int.cast_natCast, Int.natCast_floor_eq_floor ht]
  have h := Int.floor_add_fract t
  linarith

private lemma intervalIntegrable_fract_mul {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    IntervalIntegrable (fun t => Int.fract t * g t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hbound : IntegrableOn (fun t => ‖g t‖) (Set.Icc a b) := hg.norm.integrableOn_Icc
  refine Integrable.mono' hbound
    (measurable_fract.aestronglyMeasurable.mul (hg.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  have h0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t < 1 := Int.fract_lt_one t
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg _) h1.le

private lemma integral_Ioi_rpow_neg_sub_one {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ (-α - 1)) (Set.Ioi x) ∧
      ∫ t : ℝ in Set.Ioi x, t ^ (-α - 1) = x ^ (-α) / α := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-α - 1)) (Set.Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hx
  refine ⟨hint, ?_⟩
  have htend : Tendsto (fun R : ℝ => ∫ t in x..R, t ^ (-α - 1)) atTop
      (𝓝 (∫ t in Set.Ioi x, t ^ (-α - 1))) :=
    intervalIntegral_tendsto_integral_Ioi x hint tendsto_id
  have heval : ∀ᶠ R in atTop, ∫ t in x..R, t ^ (-α - 1) = x ^ (-α) / α - R ^ (-α) / α := by
    filter_upwards [eventually_ge_atTop x] with R hR
    have h0 : (0 : ℝ) ∉ Set.uIcc x R := by
      rw [Set.uIcc_of_le hR]
      exact fun h => lt_irrefl (0 : ℝ) (hx.trans_le h.1)
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have hexp : (-α - 1) + 1 = -α := by ring
    rw [hexp]
    field_simp [hα.ne']
    ring
  have hlim : Tendsto (fun R : ℝ => x ^ (-α) / α - R ^ (-α) / α) atTop (𝓝 (x ^ (-α) / α)) := by
    have h0 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
    simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (h0.div_const α)
  exact tendsto_nhds_unique htend (hlim.congr' (heval.mono fun _ h => h.symm))

private lemma integrableOn_fract_mul_rpow_neg_sub_one {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Int.fract t * t ^ (-α - 1)) (Set.Ioi x) := by
  have hint := (integral_Ioi_rpow_neg_sub_one hα hx).1
  refine Integrable.mono' hint ?_ ?_
  · refine measurable_fract.aestronglyMeasurable.mul ?_
    refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact Real.continuousAt_rpow_const t (-α - 1) (Or.inl (hx.trans ht).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg t),
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le

end InternalAux

section HarmonicBounds

/-- The partial harmonic sum over `Finset.Icc 1 ⌊x⌋₊` equals `(harmonic ⌊x⌋₊ : ℝ)`. -/
theorem sum_inv_eq_harmonic (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ = (harmonic ⌊x⌋₊ : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Lower bound for the harmonic sum: `Real.log x ≤ ∑_{1 ≤ n ≤ x} 1/n` for `0 ≤ x`. -/
theorem log_le_sum_inv {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ := by
  rw [sum_inv_eq_harmonic]
  exact log_le_harmonic_floor x hx

/-- Upper bound for the harmonic sum: `∑_{1 ≤ n ≤ x} 1/n ≤ 1 + Real.log x` for `1 ≤ x`. -/
theorem sum_inv_le_one_add_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ ≤ 1 + Real.log x := by
  rw [sum_inv_eq_harmonic]
  exact harmonic_floor_le_one_add_log x hx

/-- Exact Abel summation identity for the harmonic sum (`1 ≤ x`):
`∑_{1 ≤ n ≤ x} 1/n = Real.log x + 1 - Int.fract x / x - ∫ t in 1..x, Int.fract t / t²`. -/
theorem sum_inv_abel_formula {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ =
      Real.log x + 1 - Int.fract x / x - ∫ t in (1 : ℝ)..x, Int.fract t / t ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt (fun u : ℝ => u⁻¹) (-t ^ (-2 : ℝ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht.1).ne'
    convert hasDerivAt_inv ht0 using 1
    rw [Real.rpow_neg (lt_of_lt_of_le zero_lt_one ht.1).le, Real.rpow_two]
  have hcont : ContinuousOn (fun t : ℝ => -t ^ (-2 : ℝ)) (Set.Icc (1 : ℝ) x) := by
    refine ContinuousOn.neg (continuousOn_of_forall_continuousAt fun t ht => ?_)
    exact Real.continuousAt_rpow_const t (-2) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
  have hAbel := abel_summation_Icc_one_hasDerivAt (fun _ : ℕ => (1 : ℝ)) hx hderiv hcont
  simp only [one_mul] at hAbel
  have h1 : (∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ)) * x⁻¹ = 1 - Int.fract x / x := by
    rw [sum_one_Icc_eq_sub_fract hx0.le, sub_mul, mul_inv_cancel₀ hx0.ne', div_eq_mul_inv]
  have hint : ∫ t in (1 : ℝ)..x, (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * (-t ^ (-2 : ℝ)) =
      -Real.log x + ∫ t in (1 : ℝ)..x, Int.fract t / t ^ 2 := by
    have hcongr : ∫ t in (1 : ℝ)..x, (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * (-t ^ (-2 : ℝ)) =
        ∫ t in (1 : ℝ)..x, (-(t⁻¹) + Int.fract t / t ^ 2) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      rw [sum_one_Icc_eq_sub_fract ht0.le, Real.rpow_neg ht0.le, Real.rpow_two]
      field_simp [ht0.ne']
      ring
    rw [hcongr, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_neg, integral_inv_of_pos zero_lt_one hx0, div_one]
    · exact (intervalIntegral.intervalIntegrable_inv (fun t ht => by
        rw [Set.uIcc_of_le hx] at ht
        exact (lt_of_lt_of_le zero_lt_one ht.1).ne') (by fun_prop)).neg
    · have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc (1 : ℝ) x) :=
        (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (lt_of_lt_of_le zero_lt_one ht.1).ne'
      simpa only [div_eq_mul_inv] using intervalIntegrable_fract_mul hx hc
  rw [hAbel, h1, hint]
  ring

/-- Integrability of `t ↦ Int.fract t / t²` on `(1, ∞)`. -/
theorem integrableOn_fract_div_sq :
    IntegrableOn (fun t : ℝ => Int.fract t / t ^ 2) (Set.Ioi (1 : ℝ)) := by
  have h := integrableOn_fract_mul_rpow_neg_sub_one (α := 1) (x := 1) zero_lt_one zero_lt_one
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hexp : (-1 - 1 : ℝ) = (-2 : ℝ) := by norm_num
  dsimp only
  rw [hexp, Real.rpow_neg ht0, Real.rpow_two, div_eq_mul_inv]

/-- Representation of the Euler–Mascheroni constant `γ` via the fractional-part integral
`γ = 1 - ∫ t in Ioi 1, Int.fract t / t²`. -/
theorem eulerMascheroniConstant_eq_one_sub_integral :
    Real.eulerMascheroniConstant = 1 - ∫ t in Set.Ioi (1 : ℝ), Int.fract t / t ^ 2 := by
  have hlim1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ - Real.log N)
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun N => ?_
    rw [← Nat.floor_natCast (R := ℝ) N, ← sum_inv_eq_harmonic, Nat.floor_natCast]
  have hlim2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ - Real.log N)
      atTop (𝓝 (1 - ∫ t in Set.Ioi (1 : ℝ), Int.fract t / t ^ 2)) := by
    have hcongr : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ - Real.log N) =ᶠ[atTop]
        (fun N : ℕ => 1 - Int.fract (N : ℝ) / N -
          ∫ t in (1 : ℝ)..N, Int.fract t / t ^ 2) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
      have hform := sum_inv_abel_formula h1N
      rw [Nat.floor_natCast] at hform
      linarith
    refine Tendsto.congr' hcongr.symm ?_
    have hfract : Tendsto (fun N : ℕ => Int.fract (N : ℝ) / N) atTop (𝓝 0) := by
      simp [Int.fract_natCast]
    have hint : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..N, Int.fract t / t ^ 2) atTop
        (𝓝 (∫ t in Set.Ioi (1 : ℝ), Int.fract t / t ^ 2)) :=
      intervalIntegral_tendsto_integral_Ioi 1 integrableOn_fract_div_sq
        tendsto_natCast_atTop_atTop
    simpa only [sub_zero] using (tendsto_const_nhds.sub hfract).sub hint
  exact tendsto_nhds_unique hlim1 hlim2

/-- Explicit `1/x` error bound for the harmonic asymptotic (`1 ≤ x`):
`|∑_{1 ≤ n ≤ x} 1/n - (log x + γ)| ≤ 1 / x`. -/
theorem abs_sum_inv_sub_log_sub_gamma_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ - (Real.log x + Real.eulerMascheroniConstant)| ≤ x⁻¹ := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : IntegrableOn (fun t : ℝ => Int.fract t / t ^ 2) (Set.Ioc 1 x) :=
    integrableOn_fract_div_sq.mono_set Set.Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => Int.fract t / t ^ 2) (Set.Ioi x) :=
    integrableOn_fract_div_sq.mono_set (Set.Ioi_subset_Ioi hx)
  have hunion : Set.Ioi (1 : ℝ) = Set.Ioc 1 x ∪ Set.Ioi x := (Set.Ioc_union_Ioi_eq_Ioi hx).symm
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), Int.fract t / t ^ 2 =
      (∫ t in (1 : ℝ)..x, Int.fract t / t ^ 2) + ∫ t in Set.Ioi x, Int.fract t / t ^ 2 := by
    rw [hunion, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le hx]
  have hdiff : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ - (Real.log x + Real.eulerMascheroniConstant) =
      (∫ t in Set.Ioi x, Int.fract t / t ^ 2) - Int.fract x / x := by
    rw [sum_inv_abel_formula hx, eulerMascheroniConstant_eq_one_sub_integral, hsplit]
    ring
  rw [hdiff]
  have ha0 : 0 ≤ Int.fract x / x := div_nonneg (Int.fract_nonneg x) hx0.le
  have ha1 : Int.fract x / x ≤ x⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr hx0.le) (Int.fract_lt_one x).le
  have hb0 : 0 ≤ ∫ t in Set.Ioi x, Int.fract t / t ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => div_nonneg (Int.fract_nonneg t) (sq_nonneg t)
  have htail := integral_Ioi_rpow_neg_sub_one (α := 1) zero_lt_one hx0
  have hb1 : ∫ t in Set.Ioi x, Int.fract t / t ^ 2 ≤ x⁻¹ := by
    have hle : ∫ t in Set.Ioi x, Int.fract t / t ^ 2 ≤ ∫ t in Set.Ioi x, t ^ (-1 - 1 : ℝ) := by
      refine setIntegral_mono_on h2 htail.1 measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := hx0.trans ht
      have hexp : (-1 - 1 : ℝ) = (-2 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg ht0.le, Real.rpow_two, div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg t)) (Int.fract_lt_one t).le
    refine hle.trans_eq ?_
    simpa only [Real.rpow_neg_one, div_one] using htail.2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Big-O harmonic asymptotic: `∑_{1 ≤ n ≤ x} 1/n - log x - γ = O(1/x)` as `x → ∞`. -/
theorem sum_inv_sub_log_sub_gamma_isBigO :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ - Real.log x - Real.eulerMascheroniConstant)
      =O[atTop] (fun x : ℝ => x⁻¹) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hx0.le)]
  simpa only [sub_add_eq_sub_sub] using abs_sum_inv_sub_log_sub_gamma_le hx

/-- Continuous-variable limit `∑_{1 ≤ n ≤ x} 1/n - log x → γ` as `x → ∞`. -/
theorem tendsto_sum_inv_sub_log :
    Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)⁻¹ - Real.log x)
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs]
  simpa only [sub_add_eq_sub_sub] using abs_sum_inv_sub_log_sub_gamma_le hx

end HarmonicBounds

section LogHarmonicSum

/-- Exact Abel summation identity for `∑_{1 ≤ n ≤ x} (log n)/n` (`1 ≤ x`). -/
theorem sum_log_div_abel_formula {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n =
      (Real.log x) ^ 2 / 2 - Int.fract x * Real.log x / x +
        ∫ t in (1 : ℝ)..x, Int.fract t * (1 - Real.log t) / t ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => Real.log u / u) ((1 - Real.log t) / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht.1).ne'
    convert (Real.hasDerivAt_log ht0).div (hasDerivAt_id' t) ht0 using 1
    field_simp [ht0]
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Icc (1 : ℝ) x) := by
    refine ContinuousOn.div (continuousOn_const.sub (Real.continuousOn_log.mono ?_))
      (continuousOn_pow 2) ?_
    · intro t ht
      exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
    · intro t ht
      exact pow_ne_zero 2 (lt_of_lt_of_le zero_lt_one ht.1).ne'
  have hAbel := abel_summation_Icc_one_hasDerivAt (fun _ : ℕ => (1 : ℝ)) hx hderiv hcont
  simp only [one_mul] at hAbel
  have h1 : (∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ)) * (Real.log x / x) =
      Real.log x - Int.fract x * Real.log x / x := by
    rw [sum_one_Icc_eq_sub_fract hx0.le]
    field_simp [hx0.ne']
  have hlog_div : ∫ t in (1 : ℝ)..x, Real.log t / t = (Real.log x) ^ 2 / 2 := by
    have hd : ∀ t ∈ Set.uIcc (1 : ℝ) x,
        HasDerivAt (fun u : ℝ => (Real.log u) ^ 2 / 2) (Real.log t / t) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht.1).ne'
      convert (((Real.hasDerivAt_log ht0).pow 2).div_const 2) using 1
      ring
    have hc : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc (1 : ℝ) x) := by
      refine ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id ?_
      · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
      · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hc.integrableOn_Icc)]
    simp [Real.log_one]
  have hint : ∫ t in (1 : ℝ)..x, (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * ((1 - Real.log t) / t ^ 2) =
      Real.log x - (Real.log x) ^ 2 / 2 -
        ∫ t in (1 : ℝ)..x, Int.fract t * (1 - Real.log t) / t ^ 2 := by
    have hcongr : ∫ t in (1 : ℝ)..x,
        (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * ((1 - Real.log t) / t ^ 2) =
        ∫ t in (1 : ℝ)..x, ((t⁻¹ - Real.log t / t) - Int.fract t * (1 - Real.log t) / t ^ 2) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      rw [sum_one_Icc_eq_sub_fract ht0.le]
      field_simp [ht0.ne']
    rw [hcongr, intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_sub]
      · rw [integral_inv_of_pos zero_lt_one hx0, div_one, hlog_div]
      · exact intervalIntegral.intervalIntegrable_inv (fun t ht => by
          rw [Set.uIcc_of_le hx] at ht
          exact (lt_of_lt_of_le zero_lt_one ht.1).ne') (by fun_prop)
      · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        refine ContinuousOn.integrableOn_Icc (ContinuousOn.div (Real.continuousOn_log.mono ?_)
          continuousOn_id ?_)
        · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
        · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      refine ContinuousOn.integrableOn_Icc (ContinuousOn.sub (continuousOn_inv₀.mono ?_)
        (ContinuousOn.div (Real.continuousOn_log.mono ?_) continuousOn_id ?_))
      · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
      · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
      · intro t ht; exact (lt_of_lt_of_le zero_lt_one ht.1).ne'
    · simpa only [mul_div_assoc] using intervalIntegrable_fract_mul hx hcont
  rw [hAbel, h1, hint]
  ring

/-- Integrability of `t ↦ Int.fract t * (1 - Real.log t) / t²` on `(1, ∞)`. -/
theorem integrableOn_fract_mul_one_sub_log_div_sq :
    IntegrableOn (fun t : ℝ => Int.fract t * (1 - Real.log t) / t ^ 2) (Set.Ioi (1 : ℝ)) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have h2 : IntegrableOn (fun t : ℝ => 2 * t ^ (-3 / 2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 2
  refine Integrable.mono' (h1.add h2) ?_ ?_
  · have hEq : (fun t : ℝ => Int.fract t * (1 - Real.log t) / t ^ 2) =
        fun t : ℝ => Int.fract t * ((1 - Real.log t) / t ^ 2) := by
      ext t; ring
    rw [hEq]
    refine measurable_fract.aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht =>
      (lt_trans zero_lt_one ht).ne')) (continuousOn_pow 2) (fun t ht =>
      pow_ne_zero 2 (lt_trans zero_lt_one ht).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hlog_le : Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by
      have hsqrt : (1 / 2 : ℝ) * Real.log t = Real.log (t ^ (1 / 2 : ℝ)) := by
        rw [Real.log_rpow ht0]
      have hle := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (1 / 2 : ℝ))
      linarith
    have hnum : |1 - Real.log t| ≤ 1 + 2 * t ^ (1 / 2 : ℝ) := by
      calc |1 - Real.log t|
          ≤ 1 + |Real.log t| := abs_sub 1 (Real.log t)
        _ = 1 + Real.log t := by rw [abs_of_nonneg hlog_nonneg]
        _ ≤ 1 + 2 * t ^ (1 / 2 : ℝ) := by linarith
    have hfract : |Int.fract t| ≤ 1 := by
      rw [abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hrhs : (1 + 2 * t ^ (1 / 2 : ℝ)) / t ^ 2 = t ^ (-2 : ℝ) + 2 * t ^ (-3 / 2 : ℝ) := by
      rw [add_div, one_div, ← Real.rpow_two t, ← Real.rpow_neg ht0.le]
      congr 1
      rw [mul_div_assoc, ← Real.rpow_sub ht0]
      norm_num
    rw [Pi.add_apply, ← hrhs, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg t)
    calc |Int.fract t| * |1 - Real.log t|
        ≤ 1 * (1 + 2 * t ^ (1 / 2 : ℝ)) :=
          mul_le_mul hfract hnum (abs_nonneg _) zero_le_one
      _ = 1 + 2 * t ^ (1 / 2 : ℝ) := one_mul _

/-- The first Stieltjes constant `γ₁ = lim_{x → ∞} (∑_{1 ≤ n ≤ x} (log n)/n - (log x)² / 2)`. -/
def stieltjesOne : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ), Int.fract t * (1 - Real.log t) / t ^ 2

private lemma integral_Ioi_log_sub_one_div_sq {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => (Real.log t - 1) / t ^ 2) (Set.Ioi x) ∧
      ∫ t in Set.Ioi x, (Real.log t - 1) / t ^ 2 = Real.log x / x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
  have h2 : IntegrableOn (fun t : ℝ => 2 * t ^ (-3 / 2 : ℝ)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul 2
  have hint : IntegrableOn (fun t : ℝ => (Real.log t - 1) / t ^ 2) (Set.Ioi x) := by
    refine Integrable.mono' (h1.add h2) ?_ ?_
    · refine ((Real.continuousOn_log.mono fun t ht => (hx0.trans ht).ne').sub
        continuousOn_const).div (continuousOn_pow 2) (fun t ht => pow_ne_zero 2
        (hx0.trans ht).ne') |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := hx.trans_lt ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hlog_le : Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by
        have hsqrt : (1 / 2 : ℝ) * Real.log t = Real.log (t ^ (1 / 2 : ℝ)) := by
          rw [Real.log_rpow ht0]
        have hle := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (1 / 2 : ℝ))
        linarith
      have hnum : |Real.log t - 1| ≤ 1 + 2 * t ^ (1 / 2 : ℝ) := by
        calc |Real.log t - 1|
            ≤ |Real.log t| + 1 := abs_sub (Real.log t) 1
          _ = Real.log t + 1 := by rw [abs_of_nonneg hlog_nonneg]
          _ ≤ 1 + 2 * t ^ (1 / 2 : ℝ) := by linarith
      have hrhs : (1 + 2 * t ^ (1 / 2 : ℝ)) / t ^ 2 = t ^ (-2 : ℝ) + 2 * t ^ (-3 / 2 : ℝ) := by
        rw [add_div, one_div, ← Real.rpow_two t, ← Real.rpow_neg ht0.le]
        congr 1
        rw [mul_div_assoc, ← Real.rpow_sub ht0]
        norm_num
      rw [Pi.add_apply, ← hrhs, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg t)
  refine ⟨hint, ?_⟩
  have htend : Tendsto (fun R : ℝ => ∫ t in x..R, (Real.log t - 1) / t ^ 2) atTop
      (𝓝 (∫ t in Set.Ioi x, (Real.log t - 1) / t ^ 2)) :=
    intervalIntegral_tendsto_integral_Ioi x hint tendsto_id
  have heval : ∀ᶠ R in atTop, ∫ t in x..R, (Real.log t - 1) / t ^ 2 =
      Real.log x / x - Real.log R / R := by
    filter_upwards [eventually_ge_atTop x] with R hR
    have hd : ∀ t ∈ Set.uIcc x R,
        HasDerivAt (fun u : ℝ => -Real.log u / u) ((Real.log t - 1) / t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hR] at ht
      have ht0 : t ≠ 0 := (hx0.trans_le ht.1).ne'
      have hderiv := ((Real.hasDerivAt_log ht0).neg.div (hasDerivAt_id' t) ht0)
      refine hderiv.congr_deriv ?_
      simp only [Pi.neg_apply]
      field_simp [ht0]
      ring
    have hc : ContinuousOn (fun t : ℝ => (Real.log t - 1) / t ^ 2) (Set.Icc x R) := by
      refine ContinuousOn.div ((Real.continuousOn_log.mono ?_).sub continuousOn_const)
        (continuousOn_pow 2) ?_
      · intro t ht; exact (hx0.trans_le ht.1).ne'
      · intro t ht; exact pow_ne_zero 2 (hx0.trans_le ht.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr hc.integrableOn_Icc)]
    ring
  have hlim : Tendsto (fun R : ℝ => Real.log x / x - Real.log R / R) atTop (𝓝 (Real.log x / x)) := by
    have h0 : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using
        (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
    simpa only [sub_zero] using tendsto_const_nhds.sub h0
  exact tendsto_nhds_unique htend (hlim.congr' (heval.mono fun _ h => h.symm))

/-- Explicit `(log x)/x` error bound for `∑_{1 ≤ n ≤ x} (log n)/n` when `exp 1 ≤ x`. -/
theorem abs_sum_log_div_sub_sq_sub_stieltjes_le {x : ℝ} (hx : Real.exp 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n - ((Real.log x) ^ 2 / 2 + stieltjesOne)| ≤
      Real.log x / x := by
  have h1x : 1 ≤ x := (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one h1x
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg h1x
  have h1 : IntegrableOn (fun t : ℝ => Int.fract t * (1 - Real.log t) / t ^ 2) (Set.Ioc 1 x) :=
    integrableOn_fract_mul_one_sub_log_div_sq.mono_set Set.Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => Int.fract t * (1 - Real.log t) / t ^ 2) (Set.Ioi x) :=
    integrableOn_fract_mul_one_sub_log_div_sq.mono_set (Set.Ioi_subset_Ioi h1x)
  have hsplit : stieltjesOne =
      (∫ t in (1 : ℝ)..x, Int.fract t * (1 - Real.log t) / t ^ 2) +
        ∫ t in Set.Ioi x, Int.fract t * (1 - Real.log t) / t ^ 2 := by
    rw [stieltjesOne, ← Set.Ioc_union_Ioi_eq_Ioi h1x,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le h1x]
  have hneg : ∫ t in Set.Ioi x, Int.fract t * (1 - Real.log t) / t ^ 2 =
      -∫ t in Set.Ioi x, Int.fract t * (Real.log t - 1) / t ^ 2 := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hdiff : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n - ((Real.log x) ^ 2 / 2 + stieltjesOne) =
      (∫ t in Set.Ioi x, Int.fract t * (Real.log t - 1) / t ^ 2) -
        Int.fract x * Real.log x / x := by
    rw [sum_log_div_abel_formula h1x, hsplit, hneg]
    ring
  rw [hdiff]
  have ha0 : 0 ≤ Int.fract x * Real.log x / x :=
    div_nonneg (mul_nonneg (Int.fract_nonneg x) hlogx) hx0.le
  have ha1 : Int.fract x * Real.log x / x ≤ Real.log x / x := by
    rw [mul_div_assoc]
    exact mul_le_of_le_one_left (div_nonneg hlogx hx0.le) (Int.fract_lt_one x).le
  have htail := integral_Ioi_log_sub_one_div_sq h1x
  have h2' : IntegrableOn (fun t : ℝ => Int.fract t * (Real.log t - 1) / t ^ 2) (Set.Ioi x) := by
    refine h2.neg.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [Pi.neg_apply]
    ring
  have hb0 : 0 ≤ ∫ t in Set.Ioi x, Int.fract t * (Real.log t - 1) / t ^ 2 := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have hlogt : 1 ≤ Real.log t := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hx.trans (le_of_lt ht))
    exact div_nonneg (mul_nonneg (Int.fract_nonneg t) (sub_nonneg.mpr hlogt)) (sq_nonneg t)
  have hb1 : ∫ t in Set.Ioi x, Int.fract t * (Real.log t - 1) / t ^ 2 ≤ Real.log x / x := by
    have hle : ∫ t in Set.Ioi x, Int.fract t * (Real.log t - 1) / t ^ 2 ≤
        ∫ t in Set.Ioi x, (Real.log t - 1) / t ^ 2 := by
      refine setIntegral_mono_on h2' htail.1 measurableSet_Ioi fun t ht => ?_
      have hlogt : 1 ≤ Real.log t := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (hx.trans (le_of_lt ht))
      rw [mul_div_assoc]
      exact mul_le_of_le_one_left (div_nonneg (sub_nonneg.mpr hlogt) (sq_nonneg t))
        (Int.fract_lt_one t).le
    exact hle.trans_eq htail.2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Big-O asymptotic for `∑_{1 ≤ n ≤ x} (log n)/n`:
`∑_{1 ≤ n ≤ x} (log n)/n - ((log x)² / 2 + γ₁) = O((log x) / x)`. -/
theorem sum_log_div_sub_sq_sub_stieltjes_isBigO :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n - ((Real.log x) ^ 2 / 2 + stieltjesOne))
      =O[atTop] (fun x : ℝ => Real.log x / x) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have h1x : 1 ≤ x := (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hpos : 0 ≤ Real.log x / x := div_nonneg (Real.log_nonneg h1x) (zero_le_one.trans h1x)
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg hpos]
  exact abs_sum_log_div_sub_sq_sub_stieltjes_le hx

/-- Convergence `∑_{1 ≤ n ≤ x} (log n)/n - (log x)² / 2 → γ₁` as `x → ∞`. -/
theorem tendsto_sum_log_div_sub_half_log_sq :
    Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n - (Real.log x) ^ 2 / 2)
      atTop (𝓝 stieltjesOne) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  rw [Real.norm_eq_abs]
  simpa only [sub_add_eq_sub_sub] using abs_sum_log_div_sub_sq_sub_stieltjes_le hx

/-- Bounded remainder form: `∑_{1 ≤ n ≤ x} (log n)/n - (log x)² / 2 = O(1)` as `x → ∞`. -/
theorem sum_log_div_sub_half_log_sq_isBigO_one :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log n / n - (Real.log x) ^ 2 / 2)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  tendsto_sum_log_div_sub_half_log_sq.isBigO_one (F := ℝ)

end LogHarmonicSum

section PowerSums

/-- Exact Abel summation identity for the power sum `∑_{1 ≤ n ≤ x} n^(-α)` when `α ≠ 1` and
`1 ≤ x`. -/
theorem sum_rpow_neg_abel_formula {α x : ℝ} (hα : α ≠ 1) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) =
      x ^ (1 - α) / (1 - α) - α / (1 - α) - Int.fract x * x ^ (-α) -
        α * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1α : 1 - α ≠ 0 := sub_ne_zero.mpr hα.symm
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => u ^ (-α)) (-α * t ^ (-α - 1)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => -α * t ^ (-α - 1)) (Set.Icc (1 : ℝ) x) := by
    refine ContinuousOn.const_smul (continuousOn_of_forall_continuousAt fun t ht => ?_) (-α)
    exact Real.continuousAt_rpow_const t (-α - 1) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
  have hAbel := abel_summation_Icc_one_hasDerivAt (fun _ : ℕ => (1 : ℝ)) hx hderiv hcont
  simp only [one_mul] at hAbel
  have h1 : (∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ)) * x ^ (-α) =
      x ^ (1 - α) - Int.fract x * x ^ (-α) := by
    rw [sum_one_Icc_eq_sub_fract hx0.le, sub_mul]
    congr 1
    rw [← Real.rpow_one_add' hx0.le (by rw [← sub_eq_add_neg]; exact h1α), ← sub_eq_add_neg]
  have hint : ∫ t in (1 : ℝ)..x, (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * (-α * t ^ (-α - 1)) =
      -α * ((x ^ (1 - α) - 1) / (1 - α)) +
        α * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) := by
    have hcongr : ∫ t in (1 : ℝ)..x,
        (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ)) * (-α * t ^ (-α - 1)) =
        ∫ t in (1 : ℝ)..x, (-α * t ^ (-α) - (-α) * (Int.fract t * t ^ (-α - 1))) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      rw [sum_one_Icc_eq_sub_fract ht0.le]
      have hmul : t * t ^ (-α - 1) = t ^ (-α) := by
        nth_rw 1 [← Real.rpow_one t]
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc (t - Int.fract t) * (-α * t ^ (-α - 1))
          = -α * (t * t ^ (-α - 1)) - (-α) * (Int.fract t * t ^ (-α - 1)) := by ring
        _ = -α * t ^ (-α) - (-α) * (Int.fract t * t ^ (-α - 1)) := by rw [hmul]
    have hc1 : IntervalIntegrable (fun t : ℝ => -α * t ^ (-α)) volume 1 x := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      refine (ContinuousOn.const_smul (continuousOn_of_forall_continuousAt fun t ht => ?_)
        (-α)).integrableOn_Icc
      exact Real.continuousAt_rpow_const t (-α) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
    have hc2 : IntervalIntegrable (fun t : ℝ => (-α) * (Int.fract t * t ^ (-α - 1))) volume 1 x := by
      refine IntervalIntegrable.const_mul ?_ (-α)
      refine intervalIntegrable_fract_mul hx (continuousOn_of_forall_continuousAt fun t ht => ?_)
      exact Real.continuousAt_rpow_const t (-α - 1) (Or.inl (lt_of_lt_of_le zero_lt_one ht.1).ne')
    rw [hcongr, intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 x := by
      rw [Set.uIcc_of_le hx]
      exact fun h => lt_irrefl (0 : ℝ) (zero_lt_one.trans_le h.1)
    rw [integral_rpow (Or.inr ⟨by intro h; apply hα; linarith, h0⟩), Real.one_rpow]
    have hexp : -α + 1 = 1 - α := by ring
    rw [hexp]
    ring
  rw [hAbel, h1, hint]
  field_simp [h1α]
  ring

/-- Constant term in the asymptotic expansion of `∑_{1 ≤ n ≤ x} n^(-α)` for `0 < α`, `α ≠ 1`.
When `1 < α`, this equals `ζ(α)`. -/
def powerSumConstant (α : ℝ) : ℝ :=
  -α / (1 - α) - α * ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-α - 1)

/-- Explicit `x^(-α)` error bound for `∑_{1 ≤ n ≤ x} n^(-α)` when `0 < α`, `α ≠ 1`, `1 ≤ x`. -/
theorem abs_sum_rpow_neg_sub_le_of_pos {α x : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        (x ^ (1 - α) / (1 - α) + powerSumConstant α)| ≤ x ^ (-α) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : IntegrableOn (fun t : ℝ => Int.fract t * t ^ (-α - 1)) (Set.Ioc 1 x) :=
    (integrableOn_fract_mul_rpow_neg_sub_one hα zero_lt_one).mono_set Set.Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => Int.fract t * t ^ (-α - 1)) (Set.Ioi x) :=
    (integrableOn_fract_mul_rpow_neg_sub_one hα zero_lt_one).mono_set (Set.Ioi_subset_Ioi hx)
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-α - 1) =
      (∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1)) +
        ∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2,
      intervalIntegral.integral_of_le hx]
  have hdiff : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        (x ^ (1 - α) / (1 - α) + powerSumConstant α) =
      α * (∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1)) - Int.fract x * x ^ (-α) := by
    rw [sum_rpow_neg_abel_formula hα1 hx, powerSumConstant, hsplit]
    ring
  rw [hdiff]
  have ha0 : 0 ≤ Int.fract x * x ^ (-α) :=
    mul_nonneg (Int.fract_nonneg x) (Real.rpow_nonneg hx0.le _)
  have ha1 : Int.fract x * x ^ (-α) ≤ x ^ (-α) :=
    mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le
  have htail := integral_Ioi_rpow_neg_sub_one hα hx0
  have hb0 : 0 ≤ α * ∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1) := by
    refine mul_nonneg hα.le (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    exact mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (hx0.trans ht).le _)
  have hb1 : α * ∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1) ≤ x ^ (-α) := by
    have hle : ∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1) ≤
        ∫ t in Set.Ioi x, t ^ (-α - 1) := by
      refine setIntegral_mono_on h2 htail.1 measurableSet_Ioi fun t ht => ?_
      exact mul_le_of_le_one_left (Real.rpow_nonneg (hx0.trans ht).le _) (Int.fract_lt_one t).le
    calc α * ∫ t in Set.Ioi x, Int.fract t * t ^ (-α - 1)
        ≤ α * ∫ t in Set.Ioi x, t ^ (-α - 1) := mul_le_mul_of_nonneg_left hle hα.le
      _ = α * (x ^ (-α) / α) := by rw [htail.2]
      _ = x ^ (-α) := mul_div_cancel₀ _ hα.ne'
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- For `1 < α`, `powerSumConstant α` equals both the infinite series `∑' n : ℕ, (n + 1 : ℝ) ^ (-α)`
and `(riemannZeta α).re`. -/
theorem powerSumConstant_eq_tsum_and_zeta {α : ℝ} (hα : 1 < α) :
    powerSumConstant α = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) ∧
      powerSumConstant α = (riemannZeta α).re := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hα1 : α ≠ 1 := hα.ne'
  have hsumm : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-α) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 α).mpr hα
    refine h.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos, one_div, Real.rpow_neg hpos.le]
  have hlim1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-α))
      atTop (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α))) := by
    have hcongr : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-α)) =
        fun N : ℕ => ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-α) := by
      ext N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_Icc_succ_top (Nat.succ_pos N), Finset.sum_range_succ, ih,
          Nat.cast_add, Nat.cast_one]
    rw [hcongr]
    exact hsumm.hasSum.tendsto_sum_nat
  have hlim2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-α))
      atTop (𝓝 (powerSumConstant α)) := by
    have hmain : Tendsto (fun x : ℝ => x ^ (1 - α) / (1 - α) + powerSumConstant α)
        atTop (𝓝 (powerSumConstant α)) := by
      have h0 : Tendsto (fun x : ℝ => x ^ (1 - α)) atTop (𝓝 0) := by
        simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hα)
      simpa only [zero_div, zero_add] using (h0.div_const (1 - α)).add tendsto_const_nhds
    have herr : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        (x ^ (1 - α) / (1 - α) + powerSumConstant α)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_rpow_neg_atTop hα0) (Eventually.of_forall fun _ => norm_nonneg _) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [Real.norm_eq_abs]
      exact abs_sum_rpow_neg_sub_le_of_pos hα0 hα1 hx
    have hcont := herr.add hmain
    have hcomb : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α))
        atTop (𝓝 (powerSumConstant α)) := by
      simpa only [sub_add_cancel, zero_add] using hcont
    refine (hcomb.comp tendsto_natCast_atTop_atTop).congr fun N => ?_
    simp only [Function.comp_apply, Nat.floor_natCast]
  have htsum : powerSumConstant α = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) :=
    tendsto_nhds_unique hlim2 hlim1
  refine ⟨htsum, ?_⟩
  rw [htsum]
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (α : ℂ)) (by simpa only [Complex.ofReal_re] using hα)
  have hcast : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (α : ℂ)) =
      ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [← Complex.ofReal_one, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
      ← Complex.ofReal_cpow hpos.le, ← Complex.ofReal_div, one_div, Real.rpow_neg hpos.le]
  rw [hz, hcast, Complex.ofReal_re]

/-- Power sum asymptotic for `1 < α`:
`∑_{1 ≤ n ≤ x} n^(-α) = ζ(α) + x^(1 - α) / (1 - α) + O(x^(-α))`. -/
theorem sum_rpow_neg_asymptotic_gt_one {α : ℝ} (hα : 1 < α) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        ((riemannZeta α).re + x ^ (1 - α) / (1 - α)))
      =O[atTop] (fun x : ℝ => x ^ (-α)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hζ := (powerSumConstant_eq_tsum_and_zeta hα).2
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), ← hζ, add_comm]
  exact abs_sum_rpow_neg_sub_le_of_pos (zero_lt_one.trans hα) hα.ne' hx

/-- Power sum asymptotic for `0 < α < 1`:
`∑_{1 ≤ n ≤ x} n^(-α) = x^(1 - α) / (1 - α) + powerSumConstant α + O(x^(-α))`. -/
theorem sum_rpow_neg_asymptotic_pos_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        (x ^ (1 - α) / (1 - α) + powerSumConstant α))
      =O[atTop] (fun x : ℝ => x ^ (-α)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact abs_sum_rpow_neg_sub_le_of_pos hα0 hα1.ne hx

/-- Explicit `x^(-α)` bound for `∑_{1 ≤ n ≤ x} n^(-α)` when `α ≤ 0` and `1 ≤ x`:
`|∑_{1 ≤ n ≤ x} n^(-α) - x^(1 - α) / (1 - α)| ≤ x^(-α)`. -/
theorem abs_sum_rpow_neg_sub_le_of_nonpos {α x : ℝ} (hα : α ≤ 0) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) - x ^ (1 - α) / (1 - α)| ≤ x ^ (-α) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hα1 : α ≠ 1 := by linarith
  have hdiff : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) - x ^ (1 - α) / (1 - α) =
      (-α / (1 - α) + (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1)) -
        Int.fract x * x ^ (-α) := by
    rw [sum_rpow_neg_abel_formula hα1 hx]
    ring
  rw [hdiff]
  have ha0 : 0 ≤ Int.fract x * x ^ (-α) :=
    mul_nonneg (Int.fract_nonneg x) (Real.rpow_nonneg hx0.le _)
  have ha1 : Int.fract x * x ^ (-α) ≤ x ^ (-α) :=
    mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le
  have hb0 : 0 ≤ -α / (1 - α) + (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) := by
    have h1 : 0 ≤ -α / (1 - α) := div_nonneg (neg_nonneg.mpr hα) (by linarith)
    have h2 : 0 ≤ (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) := by
      refine mul_nonneg (neg_nonneg.mpr hα) ?_
      rw [intervalIntegral.integral_of_le hx]
      refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
      exact mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (zero_lt_one.trans ht.1).le _)
    linarith
  have hb1 : -α / (1 - α) + (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) ≤ x ^ (-α) := by
    rcases eq_or_lt_of_le hα with rfl | hα_neg
    · simp [Real.rpow_zero]
    · have h1 : -α / (1 - α) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hInt : ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) ≤
          ∫ t in (1 : ℝ)..x, t ^ (-α - 1) := by
        refine intervalIntegral.integral_mono_on hx ?_ ?_ fun t ht => ?_
        · refine (intervalIntegrable_fract_mul hx ?_)
          refine continuousOn_of_forall_continuousAt fun u hu => ?_
          exact Real.continuousAt_rpow_const u (-α - 1)
            (Or.inl (lt_of_lt_of_le zero_lt_one hu.1).ne')
        · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
          refine (continuousOn_of_forall_continuousAt fun u hu => ?_).integrableOn_Icc
          exact Real.continuousAt_rpow_const u (-α - 1)
            (Or.inl (lt_of_lt_of_le zero_lt_one hu.1).ne')
        · exact mul_le_of_le_one_left
            (Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one ht.1).le _) (Int.fract_lt_one t).le
      have h0 : (0 : ℝ) ∉ Set.uIcc 1 x := by
        rw [Set.uIcc_of_le hx]
        exact fun h => lt_irrefl (0 : ℝ) (zero_lt_one.trans_le h.1)
      have hpow : ∫ t in (1 : ℝ)..x, t ^ (-α - 1) = (x ^ (-α) - 1) / (-α) := by
        rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.one_rpow]
        have hexp : (-α - 1) + 1 = -α := by ring
        rw [hexp]
      have hmul : (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1) ≤ x ^ (-α) - 1 := by
        calc (-α) * ∫ t in (1 : ℝ)..x, Int.fract t * t ^ (-α - 1)
            ≤ (-α) * ∫ t in (1 : ℝ)..x, t ^ (-α - 1) :=
              mul_le_mul_of_nonneg_left hInt (neg_nonneg.mpr hα)
          _ = (-α) * ((x ^ (-α) - 1) / (-α)) := by rw [hpow]
          _ = x ^ (-α) - 1 := mul_div_cancel₀ _ (neg_ne_zero.mpr hα_neg.ne)
      linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Power sum asymptotic for `α ≤ 0`:
`∑_{1 ≤ n ≤ x} n^(-α) = x^(1 - α) / (1 - α) + O(x^(-α))`. -/
theorem sum_rpow_neg_asymptotic_nonpos {α : ℝ} (hα : α ≤ 0) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) - x ^ (1 - α) / (1 - α))
      =O[atTop] (fun x : ℝ => x ^ (-α)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact abs_sum_rpow_neg_sub_le_of_nonpos hα hx

/-- Unified asymptotic for `∑_{1 ≤ n ≤ x} n^(-α)` for every `α ≠ 1`:
- When `1 < α`, the error from `(riemannZeta α).re + x^(1 - α) / (1 - α)` is `O(x^(-α))`.
- When `α < 1`, the error from `x^(1 - α) / (1 - α)` is `O(max 1 (x^(-α)))`. -/
theorem sum_rpow_neg_sub_main_isBigO_lt_one {α : ℝ} (hα : α < 1) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) - x ^ (1 - α) / (1 - α))
      =O[atTop] (fun x : ℝ => max 1 (x ^ (-α))) := by
  rcases le_or_gt α 0 with hle | hpos
  · refine (sum_rpow_neg_asymptotic_nonpos hle).trans (isBigO_iff.mpr ⟨1, ?_⟩)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hmax : 0 ≤ max (1 : ℝ) (x ^ (-α)) := le_trans zero_le_one (le_max_left _ _)
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.norm_of_nonneg hmax]
    exact le_max_right _ _
  · have hbig := sum_rpow_neg_asymptotic_pos_lt_one hpos hα
    have hconst : (fun _ : ℝ => powerSumConstant α) =O[atTop] (fun x : ℝ => max (1 : ℝ) (x ^ (-α))) := by
      refine isBigO_iff.mpr ⟨|powerSumConstant α|, Eventually.of_forall fun x => ?_⟩
      have hmax : 1 ≤ max (1 : ℝ) (x ^ (-α)) := le_max_left _ _
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (zero_le_one.trans hmax)]
      exact le_mul_of_one_le_right (abs_nonneg _) hmax
    have herr : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ (-α) -
        (x ^ (1 - α) / (1 - α) + powerSumConstant α)) =O[atTop] (fun x : ℝ => max 1 (x ^ (-α))) := by
      refine hbig.trans (isBigO_iff.mpr ⟨1, ?_⟩)
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      have hmax : 0 ≤ max (1 : ℝ) (x ^ (-α)) := le_trans zero_le_one (le_max_left _ _)
      rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.norm_of_nonneg hmax]
      exact le_max_right _ _
    simpa only [sub_add_eq_sub_sub, sub_add_cancel] using herr.add hconst

end PowerSums

end AnalyticNumberTheory.AnalyticTools.Summation
