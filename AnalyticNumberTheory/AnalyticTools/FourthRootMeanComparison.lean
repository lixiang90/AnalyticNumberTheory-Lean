import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Quantitative comparison of two critical-line mean squares

A pointwise fourth-root error and a logarithmic mean-square bound
suffice to compare the integrals of two squares.
-/
open Real MeasureTheory Set
open scoped Interval
namespace AnalyticNumberTheory.AnalyticTools

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

/-- Integrated square comparison with a fourth-root pointwise error.
The approximant may be discontinuous or depend on the upper endpoint. -/
theorem fourth_root_mean_square_comparison {z p : ℝ→ℝ} {a T D K : ℝ} (ha : 8*Real.pi≤a)
    (hT : a≤T) (hzc : Continuous z) (hK : 0<K) (hD : 0<D)
    (Hk : (∫t in a..T,z t^2)≤K*T*Real.log (T+2))
    (Hd : ∀t∈Icc a T,|z t-p t|≤D*t^(-(1/4:ℝ))) :
    |∫t in a..T,z t^2-p t^2|≤(K+4*D^2)*T^(3/4:ℝ)*Real.sqrt (Real.log (T+2)) := by
  have ha' : 0<a := (by positivity : 0<8*Real.pi).trans_le ha
  have ht : 1≤T := by linarith [Real.pi_gt_three]
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
  have hz : (∫t in a..T,z t^2)≤K*T*L^2 := by
    rw [show L^2=Real.log (T+2) from Real.sq_sqrt (by linarith)];exact Hk
  have hr : ContinuousOn (fun t : ℝ => t^(-(1/2:ℝ))) (uIcc a T) := by
    rw [uIcc_of_le hT]
    exact continuousOn_id.rpow_const fun t ht => Or.inl (ha'.trans_le ht.1).ne'
  have hi : (∫t in a..T,t^(-(1/2:ℝ)))≤2*T^(1/2:ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : -1< -(1/2:ℝ))),show -(1/2:ℝ)+1=1/2 by norm_num]
    linarith [Real.rpow_nonneg ha'.le (1/2:ℝ)]
  have H := intervalIntegral.norm_integral_le_of_norm_le (a:=a) (b:=T) (μ:=volume)
    (f:=fun t => z t^2-p t^2)
    (g:=fun t => η*z t^2+((1+η⁻¹)*D^2)*t^(-(1/2:ℝ))) hT
    (Filter.Eventually.of_forall (fun t ht => by
      have ht' := ha'.trans ht.1
      have hd := Hd t ⟨ht.1.le,ht.2⟩
      change |z t-p t|≤D*t^(-(1/4:ℝ)) at hd
      have hs := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [sq_abs,mul_pow,←Real.rpow_natCast (t^(-(1/4:ℝ))) 2,←Real.rpow_mul ht'.le,
        show -(1/4:ℝ)*(2:ℕ)= -(1/2) by norm_num] at hs
      rw [Real.norm_eq_abs]
      apply (sq_error_young _ _ hη).trans
      have HH := mul_le_mul_of_nonneg_left hs (show 0≤1+η⁻¹ by positivity)
      linarith only [HH]))
    (((continuousOn_const.mul (hzc.pow 2).continuousOn).add (continuousOn_const.mul hr)).intervalIntegrable)
  rw [Real.norm_eq_abs,
    intervalIntegral.integral_add (f:=fun t => η*z t^2) (g:=fun t => ((1+η⁻¹)*D^2)*t^(-(1/2:ℝ)))
      (((hzc.pow 2).intervalIntegrable (μ:=volume) a T).const_mul η) (hr.intervalIntegrable.const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
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

end AnalyticNumberTheory.AnalyticTools
