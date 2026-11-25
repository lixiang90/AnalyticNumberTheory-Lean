import AnalyticNumberTheory.DivisorProblems.VoronoiFourierBlocks

/-!
# The dual square-root sums in the divisor problem
-/

open Real Complex Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- The square-root-frequency sum before grouping the divisor pairs by product. -/
noncomputable def divisorDualBlocks (x : ℝ) (N : ℕ) : ℂ :=
  ∑ h∈Icc 1 N.sqrt,(((h:ℝ)⁻¹:ℝ):ℂ)*∑ m∈Ioc h (N/h),reciprocalSaddleTerm (h*x) m

/-- Replacing all reciprocal Fourier sums by their dual square-root sums. -/
theorem norm_divisorFourierBlocks_sub_dual_le {x : ℝ} {N : ℕ} (hN : 1≤N)
    (hNx : (N:ℝ)≤x) :
    let R := Real.sqrt (x/N)
    ‖(∑ h∈Icc 1 ⌊Real.sqrt x/R⌋₊,(((h:ℝ)⁻¹:ℝ):ℂ)*
        ∑ n∈Ioc ⌊(h:ℝ)*R⌋ ⌊Real.sqrt x⌋,e ((h:ℝ)*x/n)) - divisorDualBlocks x N‖ ≤
      249*(⌈Real.log x/Real.log 2⌉₊:ℝ)*(1+Real.sqrt (Real.sqrt x))*
        (1+Real.log (6+4*x))*(1+Real.log x) := by
  let R := Real.sqrt (x/N)
  let b := Real.sqrt x
  let J : ℕ := ⌈Real.log x/Real.log 2⌉₊
  let C := 249*(J:ℝ)*(1+Real.sqrt b)*(1+Real.log (6+4*x))
  let S (h : ℕ) := ∑ n∈Ioc ⌊(h:ℝ)*R⌋ ⌊b⌋,e ((h:ℝ)*x/n)
  let T (h : ℕ) := ∑ m∈Ioc h (N/h),reciprocalSaddleTerm (h*x) m
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hn' : 0<(N:ℝ) := by linarith
  have hx := hn.trans hNx
  have hx0 : 0<x := by linarith
  have hb : 1≤b := Real.one_le_sqrt.mpr hx
  have hbpos : 0<b := by linarith
  have hR : 1≤R := Real.one_le_sqrt.mpr ((le_div_iff₀ hn').mpr (by simpa))
  have hR' : 0<R := by linarith
  have hsq : R^2=x/(N:ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : b^2=x := Real.sq_sqrt hx0.le
  have hid : b/R=Real.sqrt (N:ℝ) := by
    dsimp [R,b]; rw [Real.sqrt_div hx0.le,div_div_eq_mul_div]; field_simp
  have hH : ⌊b/R⌋₊=N.sqrt := by rw [hid,Real.nat_floor_real_sqrt_eq_nat_sqrt]
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hJ : x≤(2:ℝ)^J := by
    apply (Real.log_le_log_iff hx0 (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have hC : 0≤C := by
    have hh := Real.log_nonneg (by linarith : 1≤6+4*x); dsimp [C]; positivity
  have hterm {h : ℕ} (hh : h∈Icc 1 N.sqrt) : ‖S h-T h‖≤C := by
    have ⟨hh1,hh2⟩ := mem_Icc.mp hh
    have hh0 : 0<(h:ℝ) := by exact_mod_cast hh1
    have hh' : 1≤(h:ℝ) := by exact_mod_cast hh1
    let a := (h:ℝ)*R
    let A := (h:ℝ)*x
    have ha : 1≤a := one_le_mul_of_one_le_of_one_le hh' hR
    have hA : 0<A := mul_pos hh0 hx0
    have hab : a≤b := (le_div_iff₀ hR').mp (Nat.le_floor_iff (div_nonneg hbpos.le hR'.le) |>.mp (hH ▸ hh2))
    have hbJ : b≤(2:ℝ)^J*a := by
      have hb' : b≤x := by nlinarith only [hb2,hb,mul_nonneg hbpos.le (sub_nonneg.mpr hb)]
      exact hb'.trans (hJ.trans (le_mul_of_one_le_right (by positivity) ha))
    have hlow : A/b^2=(h:ℝ) := by dsimp [A]; rw [hb2]; field_simp
    have hhi : A/a^2=(N:ℝ)/h := by dsimp [A,a]; rw [mul_pow,hsq]; field_simp
    have hT : T h=∑ m∈Ioc ⌊A/b^2⌋ ⌊A/a^2⌋,reciprocalSaddleTerm A m := by
      rw [hlow,hhi,←sum_natFloor_eq_intFloor hh0.le (div_nonneg hn'.le hh0.le)]
      simp only [Nat.floor_natCast,nat_floor_div_nat hn'.le hh1,Int.cast_natCast,T,A]
    have H := reciprocal_vanDerCorput_interval ha hab hA J hbJ
    change ‖S h-T h‖≤C
    rw [hT]; apply H.trans
    have hG : Real.sqrt (b^3/A)≤Real.sqrt b := by
      apply Real.sqrt_le_sqrt
      apply (div_le_iff₀ hA).mpr
      have hAx : x≤A := le_mul_of_one_le_left hx0.le hh'
      calc b^3 = b*x := by rw [←hb2]; ring
           _ ≤ b*A := mul_le_mul_of_nonneg_left hAx hbpos.le
    have hsl : A/a^2≤x := by
      rw [hhi]; apply (div_le_self hn'.le hh').trans hNx
    have hlog := Real.log_le_log (by positivity : 0<6+4*A/a^2)
      (by linarith only [show 4*A/a^2=4*(A/a^2) by ring,hsl] : 6+4*A/a^2≤6+4*x)
    change (J:ℝ)*249*(1+Real.sqrt (b^3/A))*(1+Real.log (6+4*A/a^2))≤249*J*(1+Real.sqrt b)*(1+Real.log (6+4*x))
    rw [mul_comm (J:ℝ) 249]; gcongr
    linarith [Real.log_nonneg (by linarith [show 0≤4*A/a^2 by positivity] : 1≤6+4*A/a^2)]
  have hHarm : (∑ h∈Icc 1 N.sqrt,(h:ℝ)⁻¹)≤1+Real.log x := by
    have H := harmonic_le_one_add_log N.sqrt
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at H
    simp only [Rat.cast_inv,Rat.cast_natCast] at H
    apply H.trans; gcongr
    exact (Nat.cast_le.mpr (Nat.sqrt_le_self N)).trans hNx
  change ‖(∑ h∈Icc 1 ⌊b/R⌋₊,(((h:ℝ)⁻¹:ℝ):ℂ)*S h)-(∑ h∈Icc 1 N.sqrt,(((h:ℝ)⁻¹:ℝ):ℂ)*T h)‖≤C*(1+Real.log x)
  rw [hH,←sum_sub_distrib]; simp_rw [←mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ h∈Icc 1 N.sqrt,(h:ℝ)⁻¹*C := by
      apply sum_le_sum; intro h hh
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤(h:ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_left (hterm hh) (by positivity)
    _ ≤ _ := by rw [←sum_mul,mul_comm C]; exact mul_le_mul_of_nonneg_right hHarm hC

end AnalyticNumberTheory.DivisorProblems
