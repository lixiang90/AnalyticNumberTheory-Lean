import AnalyticNumberTheory.AnalyticTools.Summation.WeightedIntegrals

/-!
# First-derivative estimates with monotone signed weights
-/
open Real Complex MeasureTheory Set
namespace AnalyticNumberTheory.AnalyticTools.Summation

/-- A monotone signed amplitude of absolute size A costs at most 3A times
a uniform bound for primitives on initial subintervals. -/
theorem norm_integral_monotone_weight {a b H A : ℝ} (hab : a≤b)
    (f : ℝ → ℂ) (w w' : ℝ → ℝ) (hf : ∀ x∈Icc a b,ContinuousAt f x)
    (hfmeas : StronglyMeasurable f)
    (hw : ∀ x∈Icc a b,HasDerivAt w (w' x) x) (hc : ContinuousOn w' (Icc a b))
    (hsign : (∀ x∈Icc a b,w' x≤0) ∨ (∀ x∈Icc a b,0≤w' x))
    (hbd : ∀ x∈Icc a b,|w x|≤A) (hF : ∀ x∈Icc a b, ‖∫ u in a..x,f u‖≤H) :
    ‖∫ u in a..b,(w u:ℂ)*f u‖≤3*A*H := by
  have how (v v' : ℝ → ℝ) (hv : ∀ x∈Icc a b,HasDerivAt v (v' x) x)
      (hv' : ContinuousOn v' (Icc a b)) (hneg : ∀ x∈Icc a b,v' x≤0) (h : ∀ x∈Icc a b,|v x|≤A) :
      ‖∫ u in a..b,(v u:ℂ)*f u‖≤3*A*H := by
    have hba := abs_le.mp (h a (left_mem_Icc.mpr hab))
    have hbb := abs_le.mp (h b (right_mem_Icc.mpr hab))
    have hA : 0≤A := (abs_nonneg _).trans (h a (left_mem_Icc.mpr hab))
    have hFb := hF b (right_mem_Icc.mpr hab)
    have hH : 0≤H := (norm_nonneg _).trans hFb
    have h₁ := norm_integral_decreasing_weight hab f (fun u => v u+A) v' hf hfmeas
      (fun u hu => (hv u hu).add_const A) hv' hneg (by linarith) hF
    have hfc : ContinuousOn f (Icc a b) := fun u hu => (hf u hu).continuousWithinAt
    have hvc : ContinuousOn (fun u => (v u:ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn (fun u hu => (hv u hu).continuousAt.continuousWithinAt)
    simp_rw [Complex.ofReal_add,add_mul] at h₁
    rw [intervalIntegral.integral_add (f:=fun u => (v u:ℂ)*f u) (g:=fun u => (A:ℂ)*f u) ((hvc.mul hfc).intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul hfc).intervalIntegrable_of_Icc hab),intervalIntegral.integral_const_mul] at h₁
    set W := ∫ u in a..b,(v u:ℂ)*f u
    set F := ∫ u in a..b,f u
    have he : W=(W+(A:ℂ)*F)-(A:ℂ)*F := by abel
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba.2) hH,mul_le_mul_of_nonneg_left hFb hA]
  rcases hsign with hn|hp
  · exact how w w' hw hc hn hbd
  · have hh := how (fun x => -w x) (fun x => -w' x) (fun x hx => (hw x hx).neg)
      hc.neg (fun x hx => neg_nonpos.mpr (hp x hx)) (fun x hx => by simpa using hbd x hx)
    simpa only [Complex.ofReal_neg,neg_mul,intervalIntegral.integral_neg,norm_neg] using hh

end AnalyticNumberTheory.AnalyticTools.Summation
