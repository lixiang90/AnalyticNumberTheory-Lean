import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integral bounds for finite Dirichlet kernels

The sum over consecutive Fourier modes has logarithmic integral norm.
The bounds apply to arbitrary subintervals in the first three quarters
of a period and allow multiplication by a bounded weight.
-/

open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.ExponentialSums

/-- A Dirichlet kernel for consecutive integer frequencies. -/
noncomputable def intervalDirichletKernel (A B : ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc A B, e (-(t:ℝ)*(n:ℝ))

theorem continuous_intervalDirichletKernel (A B : ℤ) : Continuous (intervalDirichletKernel A B) := by
  unfold intervalDirichletKernel e; fun_prop

private theorem kernel_length {A B : ℤ} (hAB : A≤B) (t : ℝ) :
    ‖intervalDirichletKernel A B t‖ ≤ (B:ℝ)-A := by
  apply (norm_sum_le _ _).trans
  simp only [norm_e,Finset.sum_const,Int.card_Ioc,nsmul_eq_mul,mul_one]
  rw [←Int.cast_sub]; exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.mpr hAB)).le

/-- A continuous majorant for the kernel near an integer, including the integer
itself. Its integral is logarithmic in the number of frequencies. -/
theorem norm_intervalDirichletKernel_le {A B i : ℤ} (hAB : A<B) {t : ℝ}
    (ht : (i:ℝ)≤t) (ht' : t≤(i:ℝ)+3/4) :
    ‖intervalDirichletKernel A B t‖ ≤
      4*((B:ℝ)-A)/(1+((B:ℝ)-A)*(t-i)) := by
  let N : ℝ := (B:ℝ)-A
  let x := t-(i:ℝ)
  have hN : 0<N := sub_pos.mpr (by exact_mod_cast hAB)
  have hx : 0≤x := sub_nonneg.mpr ht
  have hx' : x≤3/4 := by dsimp [x]; linarith
  have hd : 0<1+N*x := by positivity
  change ‖intervalDirichletKernel A B t‖ ≤ 4*N/(1+N*x)
  by_cases h : N*x≤1
  · apply (kernel_length hAB.le t).trans
    apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_left h hN.le,hN]
  have hxp : 0<x := lt_of_le_of_ne hx (by rintro he; rw [←he,mul_zero] at h; norm_num at h)
  have hfl : ⌊x⌋=0 := Int.floor_eq_zero_iff.mpr ⟨hx,by linarith⟩
  have hdist : x/3≤distToInt (-t) := by
    rw [distToInt_neg,show t=x+i by dsimp [x]; ring,distToInt_add_int,distToInt_eq_min,Int.fract, hfl,Int.cast_zero,sub_zero]
    exact le_min (by linarith) (by linarith)
  have hdist' : 0<distToInt (-t) := lt_of_lt_of_le (by positivity : 0<x/3) hdist
  have hker := (norm_sum_Ioc_int_e_le_min (-t) ((distToInt_pos_iff _).mp hdist') hAB.le).trans (min_le_right _ _)
  apply hker.trans
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hdist hN.le, not_le.mp h]

/-- Integrated endpoint kernel bound for a continuous complex weight. -/
theorem norm_integral_mul_intervalDirichletKernel_le {A B i : ℤ} (hAB : A<B)
    {l u : ℝ} (hl : (i:ℝ)≤l) (hlu : l≤u) (hu : u≤(i:ℝ)+3/4)
    {F : ℝ→ℂ} (hc : ContinuousOn F (Icc l u)) (hF : ∀ t∈Icc l u, ‖F t‖≤1) :
    ‖∫ t in l..u,F t*intervalDirichletKernel A B t‖ ≤ 4*Real.log (1+((B:ℝ)-A)) := by
  let N : ℝ := (B:ℝ)-A
  let W (t : ℝ) := 4*N/(1+N*(t-i))
  have hN : 0<N := sub_pos.mpr (by exact_mod_cast hAB)
  have hpos (t : ℝ) (ht : l≤t) : 0<1+N*(t-i) := by
    have H := mul_nonneg hN.le (sub_nonneg.mpr (hl.trans ht)); linarith
  have hW : ContinuousOn W (Icc l u) := by
    unfold W
    apply ContinuousOn.div (f:=fun _ : ℝ => 4*N) (g:=fun t : ℝ => 1+N*(t-i)) continuousOn_const (by fun_prop)
    exact fun t ht => (hpos t ht.1).ne'
  have hD (t : ℝ) (ht : t∈uIcc l u) :
      HasDerivAt (fun t : ℝ => 4*Real.log (1+N*(t-i))) (W t) t := by
    have H := (((((hasDerivAt_id t).sub_const (i:ℝ)).const_mul N).const_add 1).log (hpos t ((uIcc_of_le hlu ▸ ht).1)).ne').const_mul 4
    apply H.congr_deriv; dsimp [W]; ring
  calc
    ‖∫ t in l..u,F t*intervalDirichletKernel A B t‖ ≤ ∫ t in l..u, ‖F t*intervalDirichletKernel A B t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlu
    _ ≤ ∫ t in l..u, W t := by
      apply intervalIntegral.integral_mono_on hlu
        ((hc.mul (continuous_intervalDirichletKernel A B).continuousOn).norm.intervalIntegrable_of_Icc hlu) (hW.intervalIntegrable_of_Icc hlu)
      intro t ht
      change ‖F t*intervalDirichletKernel A B t‖ ≤ W t
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF t ht)).trans (norm_intervalDirichletKernel_le hAB (hl.trans ht.1) (ht.2.trans hu))
    _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hW.intervalIntegrable_of_Icc hlu)
    _ ≤ _ := by
      have hlo := Real.log_nonneg (show 1≤1+N*(l-i) by linarith [mul_nonneg hN.le (sub_nonneg.mpr hl)])
      have hup := Real.log_le_log (hpos u hlu) (show 1+N*(u-i)≤1+N by nlinarith only [mul_le_mul_of_nonneg_left (show u-i≤1 by linarith) hN.le])
      linarith

end AnalyticNumberTheory.ExponentialSums
