import AnalyticNumberTheory.AnalyticTools.LogarithmicPoleSlope
import AnalyticNumberTheory.DirichletSeries.PositiveLogMean
import AnalyticNumberTheory.PrimeDistribution.IntegratedExplicitFormula
import AnalyticNumberTheory.RiemannZeta.TrivialZeroBounds

/-!
# One-sided logarithmic slopes of the Chebyshev mean

At each cutoff the left and right slopes bracket the inclusive prime-power
count, including at its jumps. Their common explicit formula works for either
sign of the logarithmic step.
-/

noncomputable section

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The signed-step slope of the logarithmically weighted von Mangoldt sum. -/
def logarithmicMangoldtSlope (u h : ℝ) : ℝ :=
  (logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp (u+h)) -
    logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp u)).re/h

private theorem ofReal_logarithmicMangoldtSlope (u h : ℝ) :
    (logarithmicMangoldtSlope u h : ℂ) = (logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp (u+h)) -
      logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp u))/(h:ℂ) := by
  have H (x : ℝ) : ((logWeightedSum (fun n => (Λ n : ℂ)) x).re : ℂ) =
      logWeightedSum (fun n => (Λ n : ℂ)) x := by
    simp only [logWeightedSum,←Complex.ofReal_mul,←Complex.ofReal_sum,Complex.ofReal_re]
  rw [logarithmicMangoldtSlope,Complex.ofReal_div,Complex.sub_re,Complex.ofReal_sub,H,H]

/-- Left and right logarithmic slopes bracket ψ at each real logarithmic cutoff,
also when exp(u) is itself a prime power. -/
theorem logarithmicMangoldtSlope_brackets (u : ℝ) {h : ℝ} (hh : 0 < h) :
    logarithmicMangoldtSlope u (-h) ≤ Chebyshev.psi (Real.exp u) ∧
      Chebyshev.psi (Real.exp u) ≤ logarithmicMangoldtSlope u h := by
  have H (v : ℝ) : Chebyshev.psi (Real.exp v) ≤ logarithmicMangoldtSlope v h ∧
      logarithmicMangoldtSlope v h ≤ Chebyshev.psi (Real.exp (v+h)) := by
    have hs := logWeightedSum_increment_bounds (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      (Real.exp_pos v) (Real.exp_le_exp.mpr (by linarith : v ≤ v+h))
    simp only [←Real.exp_sub,add_sub_cancel_left,Real.log_exp] at hs
    exact ⟨(le_div_iff₀ hh).mpr hs.1,(div_le_iff₀ hh).mpr hs.2⟩
  have he : logarithmicMangoldtSlope u (-h) = logarithmicMangoldtSlope (u-h) h := by
    simp only [logarithmicMangoldtSlope,sub_add_cancel,←sub_eq_add_neg,Complex.sub_re,div_neg]
    ring
  rw [he]
  exact ⟨by simpa only [sub_add_cancel] using (H (u-h)).2,(H u).1⟩

/-- The exact signed-slope formula has absolutely convergent zero sums and
the constant from the logarithmic derivative at zero. -/
theorem exists_logarithmicMangoldtSlope_explicit_formula :
    ∃ Z : ZetaZeroEnumeration, ∀ {u h : ℝ}, 0 ≤ u → 0 ≤ u+h → h ≠ 0 →
      (logarithmicMangoldtSlope u h : ℂ) = logarithmicPoleSlope 1 u h -
        Complex.log (2*(Real.pi:ℂ)) - (∑' n, logarithmicPoleSlope (Z.zero n) u h) -
          ∑' n, logarithmicPoleSlope (trivialZetaZero n) u h := by
  obtain ⟨Z,H⟩ := exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum
  refine ⟨Z,?_⟩
  intro u h hu hv hh
  have HF (v : ℝ) (hv' : 0 ≤ v) : logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp v) = integratedZetaZeroSum Z v := by
    simpa only [Real.log_exp] using H (Real.one_le_exp_iff.mpr hv')
  have hN := hasSum_logarithmicPoleSlope (fun n => (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le)
    Z.summable_inv_sq hu hv
  have ht (n : ℕ) : (trivialZetaZero n).re ≤ 0 := by
    rw [re_trivialZetaZero]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hT := hasSum_logarithmicPoleSlope ht summable_trivialZetaZero_inv_sq hu hv
  rw [ofReal_logarithmicMangoldtSlope,HF _ hv,HF _ hu,logarithmicPoleSlope_eq_difference 1 hu hv,
    hN.tsum_eq,hT.tsum_eq]
  simp only [integratedZetaZeroSum,Complex.ofReal_add]
  field_simp [Complex.ofReal_ne_zero.mpr hh]
  ring

/-- The trivial zeros contribute at most two to either one-sided slope when
both logarithmic endpoints are at least one. -/
theorem norm_tsum_logarithmicPoleSlope_trivial_le {u h : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ u+h) (hh : h ≠ 0) :
    ‖∑' n, logarithmicPoleSlope (trivialZetaZero n) u h‖ ≤ 2 := by
  have hg := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_right (1/2)).mul_left 2
  apply (tsum_of_norm_bounded hg ?_).trans_eq (by norm_num)
  intro n
  calc
    _ ≤ (Real.exp ((trivialZetaZero n).re*(u+h))+Real.exp ((trivialZetaZero n).re*u))/‖trivialZetaZero n‖ :=
      norm_logarithmicPoleSlope_le_endpoints (trivialZetaZero_ne_zero n) u hh
    _ ≤ Real.exp ((trivialZetaZero n).re*(u+h))+Real.exp ((trivialZetaZero n).re*u) :=
      div_le_self (by positivity) (one_le_norm_trivialZetaZero n)
    _ ≤ (1/2:ℝ)^(n+1)+(1/2:ℝ)^(n+1) :=
      add_le_add (exp_re_trivialZetaZero_le_half_pow n hv) (exp_re_trivialZetaZero_le_half_pow n hu)
    _ = _ := by rw [pow_succ]; ring

end AnalyticNumberTheory.PrimeDistribution
