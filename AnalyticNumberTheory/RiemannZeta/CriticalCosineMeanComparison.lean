import AnalyticNumberTheory.RiemannZeta.CriticalCosineExpansion
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelElementaryPhase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Comparing the Hardy and cosine second moments

Young's inequality with a height-dependent parameter balances the known
Hardy square mean against the integral of the pointwise squared error.
This costs T^(3/4) times the square root of a logarithm.
-/
open Real Complex MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.RiemannZeta

private theorem sq_error_young (z p : ℝ) {η : ℝ} (hη : 0<η) :
    |z^2-p^2| ≤ η*z^2+(1+η⁻¹)*(z-p)^2 := by
  let d := z-p
  have he : z^2-p^2=2*z*d-d^2 := by dsimp [d];ring
  have H : 2*(|z| *|d|)≤η*z^2+η⁻¹*d^2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have hc := sq_nonneg (η*|z|-|d|)
    rw [mul_add,show η*(η⁻¹*d^2)=d^2 by field_simp]
    nlinarith only [hc,sq_abs z,sq_abs d,
      show (η*|z|)^2=η^2*z^2 by rw [mul_pow,sq_abs] ]
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg d),abs_of_pos (by norm_num : (0:ℝ)<2)]
  change _≤η*z^2+(1+η⁻¹)*d^2
  linarith only [H]

/-- The integrated error made by replacing Hardy's function squared by
the square of the elementary sharp cosine sum. -/
theorem hardyZ_square_cosine_mean_error : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},8*Real.pi≤T →
    |(∫t in (8*Real.pi)..T,hardyZ t^2)-(∫t in (8*Real.pi)..T,hardyCosineMain t^2)|≤
      C*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  obtain ⟨D,hD,Hd⟩ := hardyZ_elementary_cosine_error
  obtain ⟨K,hK,Hk⟩ := mean_sq_hardyZ_upper_bound
  let a := 8*Real.pi
  have ha : 1≤a := by dsimp [a];linarith [Real.pi_gt_three]
  have ha' : 0<a := by linarith
  refine ⟨K+4*D^2,by positivity,?_⟩
  intro T hT
  change a≤T at hT
  have ht : 1≤T := ha.trans hT
  have ht' : 0<T := by linarith
  let L := Real.sqrt (Real.log (T+2))
  let U := T^(1/4:ℝ)
  let η := (U*L)⁻¹
  have hl₁ : 1≤Real.log (T+2) := by
    rw [←Real.log_exp 1];apply Real.log_le_log (Real.exp_pos _);linarith [Real.exp_one_lt_d9]
  have hL : 1≤L := Real.le_sqrt_of_sq_le (by simpa using hl₁)
  have hU : 1≤U := Real.one_le_rpow ht (by norm_num)
  have hL' : 0<L := by linarith
  have hU' : 0<U := by linarith
  have hη : 0<η := by dsimp [η];positivity
  have hzz := Hk ht
  have hza : 0≤∫ t in (1:ℝ)..a,hardyZ t^2 := intervalIntegral.integral_nonneg ha (fun _ _ => sq_nonneg _)
  have hiz {x y : ℝ} : IntervalIntegrable (fun t => hardyZ t^2) volume x y :=
    (continuous_hardyZ.pow 2).intervalIntegrable ..
  rw [←intervalIntegral.integral_add_adjacent_intervals (hiz (x:=1) (y:=a)) (hiz (y:=T))] at hzz
  have hz : (∫ t in a..T,hardyZ t^2)≤K*T*L^2 := by
    rw [show L^2=Real.log (T+2) from Real.sq_sqrt (by linarith)]
    field_simp at hzz
    linarith
  have hr : ContinuousOn (fun t : ℝ => t^(-(1/2:ℝ))) (uIcc a T) := by
    rw [uIcc_of_le hT]
    exact continuousOn_id.rpow_const fun t ht => Or.inl (ha'.trans_le ht.1).ne'
  have hi : (∫t in a..T,t^(-(1/2:ℝ)))≤2*T^(1/2:ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : -1< -(1/2:ℝ))),show -(1/2:ℝ)+1=1/2 by norm_num]
    linarith [Real.rpow_nonneg ha'.le (1/2:ℝ)]
  have H := intervalIntegral.norm_integral_le_of_norm_le (a:=a) (b:=T) (μ:=volume)
    (f:=fun t => hardyZ t^2-hardyCosineMain t^2)
    (g:=fun t => η*hardyZ t^2+((1+η⁻¹)*D^2)*t^(-(1/2:ℝ))) hT
    (Filter.Eventually.of_forall (fun t ht => by
      have ht' := ha'.trans ht.1
      have hd := Hd ht.1.le
      change |hardyZ t-hardyCosineMain t|≤D*t^(-(1/4:ℝ)) at hd
      have hs := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [sq_abs,mul_pow,←Real.rpow_natCast (t^(-(1/4:ℝ))) 2,←Real.rpow_mul ht'.le,
        show -(1/4:ℝ)*(2:ℕ)= -(1/2) by norm_num] at hs
      rw [Real.norm_eq_abs]
      apply (sq_error_young _ _ hη).trans
      have HH := mul_le_mul_of_nonneg_left hs (show 0≤1+η⁻¹ by positivity)
      linarith only [HH]))
    (((continuousOn_const.mul (continuous_hardyZ.pow 2).continuousOn).add (continuousOn_const.mul hr)).intervalIntegrable)
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (f:=fun t=>hardyZ t^2) (g:=fun t=>hardyCosineMain t^2)
    hiz (hardyCosineMain_sq_intervalIntegrable ha'.le hT),
    intervalIntegral.integral_add (f:=fun t => η*hardyZ t^2) (g:=fun t => ((1+η⁻¹)*D^2)*t^(-(1/2:ℝ)))
      (hiz.const_mul η) (hr.intervalIntegrable.const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
  have HS : U*U=T^(1/2:ℝ) := by dsimp [U];rw [←Real.rpow_add ht'];norm_num
  have HC : U*T^(1/2:ℝ)=T^(3/4:ℝ) := by dsimp [U];rw [←Real.rpow_add ht'];norm_num
  have HQ : U*T^(3/4:ℝ)=T := by dsimp [U];rw [←Real.rpow_add ht'];norm_num
  have hη' : η⁻¹=U*L := inv_inv _
  have hfirst : η*(K*T*L^2)=K*T^(3/4:ℝ)*L := by dsimp only [η];nth_rw 1 [←HQ];field_simp
  have hlast : ((1+η⁻¹)*D^2)*(2*T^(1/2:ℝ))≤4*D^2*T^(3/4:ℝ)*L := by
    rw [hη',←HC]
    have h₁ := one_le_mul_of_one_le_of_one_le hU hL
    have hh := mul_le_mul_of_nonneg_right (show 1+U*L≤2*(U*L) by linarith) (show 0≤D^2*(2*T^(1/2:ℝ)) by positivity)
    linarith only [hh]
  have HH := add_le_add (mul_le_mul_of_nonneg_left hz hη.le) (mul_le_mul_of_nonneg_left hi
    (show 0≤(1+η⁻¹)*D^2 by positivity))
  rw [hfirst] at HH
  exact H.trans (by linarith only [HH,hlast])

end AnalyticNumberTheory.RiemannZeta
