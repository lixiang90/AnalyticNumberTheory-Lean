import AnalyticNumberTheory.AnalyticTools.DyadicIntegrals

/-!
# Uniform summation of dyadic integral bounds

The constant is independent of the integrand and the nondecreasing majorant.
Controlling the first unit interval is sufficient for uniform families.
-/
open Real Set MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

/-- Dyadic summation starting at zero, with an explicit factor two and an
arbitrary positive nondecreasing weight. -/
theorem integral_zero_to_of_weighted_dyadic {f w : ℝ→ℝ}
    (hf : Continuous f) (h₀ : ∀t,0≤f t) (hw : MonotoneOn w (Ici 1)) (hw₀ : ∀u,1≤u → 0≤w u)
    (hunit : (∫t in (0:ℝ)..1,f t)≤w 1)
    (hdy : ∀u : ℝ,1≤u → (∫t in u..(2*u),f t)≤u*w u) {T : ℝ} (hT : 1≤T) :
    (∫t in (0:ℝ)..T,f t)≤2*T*w T := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hT (by norm_num : (1:ℝ)<2)
  have hsum (j : ℕ) (hj : j≤k+1) : (∫t in (0:ℝ)..(2:ℝ)^j,f t)≤(2:ℝ)^j*w T := by
    induction j with
    | zero => simpa using hunit.trans (hw (a:=(1:ℝ)) (b:=T) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT)
    | succ j ih =>
      have hjk : j≤k := by omega
      let u := (2:ℝ)^j
      have hu : 1≤u := one_le_pow₀ (by norm_num)
      have huT : u≤T := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hjk).trans hk
      have h₂ : (2:ℝ)^(j+1)=2*u := by dsimp [u];rw [pow_succ,mul_comm]
      rw [h₂,←intervalIntegral.integral_add_adjacent_intervals (a:=0) (b:=u) (c:=2*u)
        (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]
      apply (add_le_add (ih (by omega)) (hdy u hu)).trans
      change u*w T+u*w u≤2*u*w T
      nlinarith only [mul_le_mul_of_nonneg_left (hw hu hT huT) (by linarith : 0≤u)]
  have hmono := intervalIntegral.integral_mono_interval (μ:=volume) (a:=(0:ℝ)) le_rfl (by linarith : (0:ℝ)≤T)
    hk'.le (Filter.Eventually.of_forall h₀) (hf.intervalIntegrable ..)
  apply (hmono.trans (hsum (k+1) le_rfl)).trans
  apply mul_le_mul_of_nonneg_right _ (hw₀ _ hT)
  rw [pow_succ];linarith

end AnalyticNumberTheory.AnalyticTools
