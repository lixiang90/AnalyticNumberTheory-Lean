import AnalyticNumberTheory.PrimeDistribution.ZeroFrequencyMean
import AnalyticNumberTheory.PrimeDistribution.HighTruncation
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The logarithmic mean square of the Chebyshev error under RH -/

noncomputable section

open Real Complex Filter Finset Set MeasureTheory Asymptotics
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- On RH the sharp zero sum is √x times an exponential polynomial in log x. -/
theorem sharpZetaZeroSum_eq_frequencyPolynomial_of_rh (hRH : RiemannHypothesisProp)
    {x : ℝ} (hx : 0 < x) (T : ℝ) :
    sharpZetaZeroSum x T = (Real.sqrt x:ℂ)*frequencyPolynomial (nontrivialZerosUpTo T)
      (fun z => (zeroMultiplicity z:ℂ)/z) Complex.im (Real.log x) := by
  rw [sharpZetaZeroSum,frequencyPolynomial,Finset.mul_sum]
  apply sum_congr rfl
  intro z hz
  obtain ⟨hz,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
  have hr := hRH z hz h₀ h₁
  have he : ((Real.log x:ℝ):ℂ)*z = ((Real.log x/2:ℝ):ℂ)+((z.im*Real.log x:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hr] <;> ring
  have hs : Real.sqrt x = Real.exp (Real.log x/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 1; ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),←Complex.ofReal_log hx.le,
    he,Complex.exp_add,← Complex.ofReal_exp,←hs]
  ring

private theorem integrable_psi_relative_error_square {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => ((Chebyshev.psi x-x)/x)^2) volume a b := by
  let C := Real.log 4+5
  have hC : 1 ≤ C := by dsimp only [C]; linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hm : Measurable (fun x : ℝ => ((Chebyshev.psi x-x)/x)^2) :=
    ((Chebyshev.psi_mono.measurable.sub measurable_id).div measurable_id).pow_const 2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply (integrableOn_const (C := C^2) (hs := (measure_Ioc_lt_top : volume (Set.Ioc a b) < ⊤).ne)).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
  have hx₀ := ha.trans hx.1
  have hb : |Chebyshev.psi x-x| ≤ C*x := by
    have hh := Chebyshev.psi_le_const_mul_self hx₀.le
    have hl := Chebyshev.psi_nonneg (x := x)
    have hcx := le_mul_of_one_le_left hx₀.le hC
    apply abs_le.mpr
    constructor <;> dsimp only [C] at * <;> linarith
  change |((Chebyshev.psi x-x)/x)^2| ≤ C^2
  rw [abs_pow,abs_div,abs_of_pos hx₀]
  exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hx₀.le) ((div_le_iff₀ hx₀).mpr hb) 2

/-- Under RH the mean square of (ψ(x)−x)/√x with logarithmic measure dx/x
is bounded per unit logarithmic length. The endpoints are arbitrary real X. -/
theorem chebyshev_error_mean_square_of_rh (hRH : RiemannHypothesisProp) :
    (fun X : ℝ => ∫ x in (1:ℝ)..X, ((Chebyshev.psi x-x)/x)^2) =O[atTop] Real.log := by
  obtain ⟨D,hD,HD⟩ := zeroFrequencyPolynomial_mean_square
  obtain ⟨K,hK,herr⟩ := sharp_explicit_formula_high_truncation
  obtain ⟨a,ha⟩ := eventually_atTop.mp herr
  let A := max 1 a
  let f (x : ℝ) := ((Chebyshev.psi x-x)/x)^2
  let J := ∫ x in (1:ℝ)..A, f x
  have hA : 1 ≤ A := le_max_left ..
  have hA₀ := zero_lt_one.trans_le hA
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg hA (fun x _ => sq_nonneg _)
  apply IsBigO.of_bound (J+8*K^2+2*D)
  filter_upwards [eventually_ge_atTop A,Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hX hLX
  let T := X^8
  let S := nontrivialZerosUpTo T
  let P := frequencyPolynomial S (fun z => (zeroMultiplicity z:ℂ)/z) Complex.im
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc A X) :
      f x ≤ (8*K^2+2*‖P (Real.log x)‖^2)*x⁻¹ := by
    have hx₀ := hA₀.trans_le hx.1
    have herr := ha x ((le_max_right ..).trans hx.1) (T := T) (pow_le_pow_left₀ hx₀.le hx.2 8)
    have hdiff : |Chebyshev.psi x-x| ≤ K*Real.log x+Real.sqrt x*‖P (Real.log x)‖ := by
      have hn := norm_sub_le (((Chebyshev.psi x:ℂ)-x)+sharpZetaZeroSum x T) (sharpZetaZeroSum x T)
      rw [add_sub_cancel_right,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hn
      apply hn.trans (add_le_add (by simpa only [Complex.ofReal_sub] using herr) _)
      rw [sharpZetaZeroSum_eq_frequencyPolynomial_of_rh hRH hx₀,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg x)]
    have hlog : Real.log x ≤ 2*Real.sqrt x := by
      have h := Real.log_le_rpow_div hx₀.le (by norm_num : (0:ℝ)<1/2)
      rw [←Real.sqrt_eq_rpow] at h
      linarith
    have he : |Chebyshev.psi x-x| ≤ (2*K+‖P (Real.log x)‖)*Real.sqrt x := by
      nlinarith only [hdiff,mul_le_mul_of_nonneg_left hlog hK.le]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) he 2
    rw [sq_abs,mul_pow,Real.sq_sqrt hx₀.le] at hsq
    dsimp only [f]
    rw [div_pow,← div_eq_mul_inv]
    calc
      _ ≤ ((2*K+‖P (Real.log x)‖)^2*x)/x^2 := div_le_div_of_nonneg_right hsq (sq_nonneg _)
      _ = (2*K+‖P (Real.log x)‖)^2/x := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (2*K-‖P (Real.log x)‖)]) hx₀.le
  let Q (u : ℝ) := 8*K^2+2*‖P u‖^2
  have hQ : Continuous Q := by unfold Q P frequencyPolynomial; fun_prop
  have hQ₀ (t : ℝ) : 0 ≤ Q t := by dsimp only [Q]; positivity
  have h₁X := hA.trans hX
  have hpos {t : ℝ} (ht : t ∈ uIcc 1 X) : 0 < t := zero_lt_one.trans_le ((uIcc_of_le h₁X ▸ ht).1)
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc 1 X) :=
    continuousOn_id.inv₀ fun _ ht => (hpos ht).ne'
  have hG : IntervalIntegrable (fun x : ℝ => Q (Real.log x)*x⁻¹) volume 1 X :=
    ((hQ.comp_continuousOn (Real.continuousOn_log.mono (fun _ ht => (hpos ht).ne'))).mul hinv).intervalIntegrable
  have hsub := intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun x : ℝ => x⁻¹)
    (a := 1) (b := X) (fun x hx => Real.hasDerivAt_log (hpos hx).ne') hinv hQ
  simp only [Function.comp_apply,Real.log_one] at hsub
  have hS (z : ℂ) (hz : z ∈ S) : z ∈ CriticalStripZeros := by
    obtain ⟨h,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    exact mem_criticalStripZeros.mpr ⟨h,h₀,h₁⟩
  have hpol := HD S hS hLX
  have hP : Continuous (fun u => ‖P u‖^2) := by unfold P frequencyPolynomial; fun_prop
  have hlast : (∫ u in (0:ℝ)..Real.log X, Q u) ≤ (8*K^2+2*D)*Real.log X := by
    dsimp only [Q]
    rw [intervalIntegral.integral_add intervalIntegrable_const ((hP.intervalIntegrable _ _).const_mul 2),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,smul_eq_mul,sub_zero]
    change (Real.log X)*(8*K^2)+2*(∫ u in (0:ℝ)..Real.log X, ‖P u‖^2) ≤ _
    linarith only [hpol]
  have hint : (∫ x in A..X, f x) ≤ (8*K^2+2*D)*Real.log X := by
    calc
      _ ≤ ∫ x in A..X, Q (Real.log x)*x⁻¹ :=
        intervalIntegral.integral_mono_on hX (integrable_psi_relative_error_square hA₀ hX)
          (hG.mono_set (by rw [uIcc_of_le hX,uIcc_of_le h₁X]; exact Set.Icc_subset_Icc_left hA)) hpoint
      _ ≤ ∫ x in (1:ℝ)..X, Q (Real.log x)*x⁻¹ := intervalIntegral.integral_mono_interval hA hX le_rfl
        ((ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun t ht =>
          mul_nonneg (hQ₀ _) (inv_nonneg.mpr (zero_le_one.trans ht.1.le))) hG
      _ ≤ _ := hsub.trans_le hlast
  change ‖∫ x in (1:ℝ)..X, f x‖ ≤ _
  rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg h₁X (fun _ _ => sq_nonneg _)),
    ← intervalIntegral.integral_add_adjacent_intervals (integrable_psi_relative_error_square zero_lt_one hA)
      (integrable_psi_relative_error_square hA₀ hX),Real.norm_of_nonneg (zero_le_one.trans hLX)]
  change J+_ ≤ _
  nlinarith only [hint,le_mul_of_one_le_right hJ hLX]

end AnalyticNumberTheory.PrimeDistribution
