import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalWeights
import AnalyticNumberTheory.PrimeDistribution.PageRegion
import AnalyticNumberTheory.DirichletLFunctions.EffectiveRealZero

/-! # Effective decay of the exceptional major-arc weights -/

noncomputable section
open Finset Real AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A witnessing Page zero forces its conductor to be large. The coefficient
comes from the explicit separation of a real character zero from one. -/
theorem page_exceptional_reciprocal_sqrt {K c : ℝ} (hK : 2≤K)
    {d : ℕ} {χ : DirichletCharacter ℂ d} (he : PageExceptionalCharacter K c χ) :
    1/sqrt d ≤ 12960*c*log ((d:ℝ)+2)^3/log (K+2) := by
  obtain ⟨hnz,hd,_,_,hr,hχ,β,hβ,hzero⟩ := he
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hL : 0<log (K+2) := log_pos (by linarith)
  have hD : 0<log ((d:ℝ)+2) := log_pos (by linarith)
  have hs : 0<sqrt (d:ℝ) := sqrt_pos.mpr (by linarith)
  have hgap := real_zero_effective_gap hd hr hχ hzero
  have hle : 1/(12960*sqrt d*log ((d:ℝ)+2)^3)≤c/log (K+2) := by linarith [hβ.1]
  apply (div_le_div_iff₀ hs hL).2
  have hh := (div_le_div_iff₀ (by positivity) hL).1 hle
  linarith only [show c*(12960*sqrt d*log ((d:ℝ)+2)^3)=
    12960*c*log ((d:ℝ)+2)^3*sqrt d by ring,hh]

/-- The Gauss weights of all exceptional denominators in `[1,M]` admit
a bound tending to zero when `(log M)^5 = o(log K)`. -/
theorem page_exceptional_weight_sum {K c : ℝ} (hK : 2≤K) (hc : 0<c)
    {d M : ℕ} {χ : DirichletCharacter ℂ d} (he : PageExceptionalCharacter K c χ)
    (hM : 1≤M) :
    ∑q∈(Icc 1 M).filter (d∣·), (sqrt d)^3/(q.totient:ℝ)^2 ≤
      77760*Real.pi^2*c*(1+log M)^2*log ((M:ℝ)+2)^3/log (K+2) := by
  have hL : 0<log (K+2) := log_pos (by linarith)
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hMlog : 0<log ((M:ℝ)+2) := log_pos (by linarith)
  have hd := he.choose_spec.1
  by_cases hdM : d≤M
  · have hdR : (2:ℝ)≤d := by exact_mod_cast hd
    have hl := Real.log_le_log (by positivity : 0<(d:ℝ)+2) (show (d:ℝ)+2≤M+2 by exact_mod_cast Nat.add_le_add_right hdM 2)
    have hinv := page_exceptional_reciprocal_sqrt hK he
    apply (exceptional_gauss_weight_sum (by omega) hM).trans
    rw [div_eq_mul_one_div]
    calc _ ≤ (6*Real.pi^2*(1+log M)^2)*(12960*c*log ((M:ℝ)+2)^3/log (K+2)) :=
              mul_le_mul_of_nonneg_left (hinv.trans (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_nonneg (by linarith)) hl 3)
                (by positivity)) hL.le)) (by positivity)
         _ = _ := by ring
  · have hnil : (Icc 1 M).filter (d∣·)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have h := mem_Icc.mp (mem_filter.mp hq).1
      exact hdM ((Nat.le_of_dvd h.1 (mem_filter.mp hq).2).trans h.2)
    rw [hnil,sum_empty]
    positivity

end AnalyticNumberTheory.AdditiveNumberTheory
