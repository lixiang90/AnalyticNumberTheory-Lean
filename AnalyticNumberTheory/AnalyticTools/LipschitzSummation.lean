import AnalyticNumberTheory.AnalyticTools.GammaLaplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lipschitz summation at complex weight

Poisson summation applied to the gamma density identifies a row of
an Eisenstein lattice with an exponentially convergent Fourier series.
-/

open Complex Real Filter MeasureTheory Set Asymptotics
open scoped Topology FourierTransform
namespace AnalyticNumberTheory.AnalyticTools

/-- Principal complex powers are bounded by real powers with a uniform
factor for the argument of the base. -/
theorem norm_cpow_le_arg_bound (z s : ℂ) :
    ‖z^s‖≤‖z‖^s.re*Real.exp (Real.pi*|s.im|) := by
  apply (Complex.norm_cpow_le z s).trans
  rw [div_eq_mul_inv,←Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have ha : |z.arg|≤Real.pi := abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le,Complex.arg_le_pi z⟩
  calc _ ≤ |z.arg*s.im| := neg_le_abs _
       _ = _ := abs_mul _ _
       _ ≤ _ := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

private noncomputable def positiveGammaDensity (s v : ℂ) : ℝ→ℂ :=
  (Ioi 0).indicator (gammaLaplaceKernel s v)

private theorem continuous_positiveGammaDensity {s : ℂ} (hs : 1<s.re) (v : ℂ) :
    Continuous (positiveGammaDensity s v) := by
  have h : 0<(s-1).re := by simpa using sub_pos.mpr hs
  have hne : s-1≠0 := by intro hz; simp [hz] at h
  apply continuous_indicator
  · intro t ht
    have ht' : t=0 := by simpa only [frontier_Ioi,mem_singleton_iff] using ht
    simp [ht',gammaLaplaceKernel,Complex.zero_cpow hne]
  · exact (Continuous.mul (by fun_prop) (Complex.continuous_ofReal_cpow_const h)).continuousOn

private theorem fourier_positiveGammaDensity {s v : ℂ} (hs : 0<s.re) (hv : 0<v.re) (ξ : ℝ) :
    𝓕 (positiveGammaDensity s v) ξ =
      (v+((2*Real.pi*ξ:ℝ):ℂ)*I)^(-s)*Complex.Gamma s := by
  have hz : 0<(v+((2*Real.pi*ξ:ℝ):ℂ)*I).re := by simpa using hv
  rw [←integral_gammaLaplaceKernel_rightHalfPlane hs hz,Real.fourier_eq',←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  by_cases ht : t∈Ioi (0:ℝ)
  · simp only [positiveGammaDensity,indicator_of_mem ht,smul_eq_mul,RCLike.inner_apply,conj_trivial,
      gammaLaplaceKernel,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
    rw [←mul_assoc,←Complex.exp_add]
    congr 2; ring
  · simp [positiveGammaDensity,indicator_of_notMem ht]

private theorem gammaDensity_decay {s v : ℂ} (hv : 0<v.re) :
    positiveGammaDensity s v =O[cocompact ℝ] (fun t : ℝ => |t|^(-(2:ℝ))) := by
  rw [cocompact_eq_atBot_atTop,isBigO_sup]
  constructor
  · apply IsBigO.of_bound 0
    filter_upwards [eventually_le_atBot (0:ℝ)] with t ht
    simp [positiveGammaDensity,indicator_of_notMem (show t∉Ioi (0:ℝ) from not_lt.mpr ht)]
  · have h := (isLittleO_exp_neg_mul_rpow_atTop hv (-2-(s.re-1))).isBigO
    obtain ⟨C,hC,H⟩ := h.exists_pos
    apply IsBigO.of_bound C
    filter_upwards [H.bound,eventually_gt_atTop (0:ℝ)] with t ht hp
    simp only [Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)] at ht
    rw [positiveGammaDensity,indicator_of_mem hp, norm_gammaLaplaceKernel _ _ hp,abs_of_pos hp,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
    calc _ ≤ t^(s.re-1)*(C*t^(-2-(s.re-1))) := mul_le_mul_of_nonneg_left ht (by positivity)
         _ = _ := by rw [mul_left_comm,←Real.rpow_add hp]; congr 2; ring

private theorem summable_row_cpow {s z : ℂ} (hs : 1<s.re) :
    Summable fun n : ℤ => (z+(n:ℂ))^(-s) := by
  apply summable_norm_iff.mp
  apply Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow hs).mul_left ((2:ℝ)^s.re*Real.exp (π*|s.im|)))
  have he : ∀ᶠ n : ℤ in cofinite, 2*‖z‖+1≤‖(n:ℝ)‖ :=
    (tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite) (eventually_ge_atTop _)
  filter_upwards [he] with n hn
  have hn' : ‖(n:ℂ)‖=|(n:ℝ)| := by rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [Real.norm_eq_abs] at hn
  have hp : 0 < |(n:ℝ)| := by linarith [norm_nonneg z]
  have hzn : |(n:ℝ)|/2≤‖z+(n:ℂ)‖ := by
    have h := norm_sub_le (z+(n:ℂ)) z
    rw [add_sub_cancel_left,hn'] at h
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (half_pos hp) hzn (by linarith : -s.re≤0)
  have heq : (|(n:ℝ)|/2)^(-s.re)=(2:ℝ)^s.re*|(n:ℝ)|^(-s.re) := by
    rw [Real.div_rpow hp.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul,mul_comm]
  rw [heq] at hpow
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have H := norm_cpow_le_arg_bound (z+n) (-s)
  simp only [Complex.neg_im,Complex.neg_re,abs_neg] at H
  calc _ ≤ _ := H
       _ ≤ ((2:ℝ)^s.re*|(n:ℝ)|^(-s.re))*Real.exp (π*|s.im|) :=
         mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
       _ = _ := by ring

/-- The Lipschitz summation formula for every complex weight with real
part greater than one. The row is written with its natural Laplace
normalization `-2πi(z+n)`. -/
theorem lipschitz_summation_laplace {s z : ℂ} (hs : 1<s.re) (hz : 0<z.im) :
    (∑' n : ℕ, ((n+1:ℕ):ℂ)^(s-1)*Complex.exp (2*π*I*z*(n+1))) =
      (∑' n : ℤ,(-2*π*I*(z+n))^(-s))*Complex.Gamma s := by
  let v := -2*(Real.pi:ℂ)*I*z
  have hv : 0<v.re := by simpa [v,Complex.mul_re] using mul_pos (show 0<2*π by positivity) hz
  have Hf (n : ℤ) : 𝓕 (positiveGammaDensity s v) (n:ℝ)=(-2*π*I*(z+(-n:ℤ)))^(-s)*Complex.Gamma s := by
    rw [fourier_positiveGammaDensity (by linarith) hv]
    dsimp [v]; push_cast; ring_nf
  have hsG : Summable fun n : ℤ => (-2*π*I*(z+n))^(-s) := by
    have hπ : (-2*(π:ℂ)*I).arg= -(π/2) := by
      rw [show -2*(π:ℂ)*I=((2*π:ℝ):ℂ)*(-I) by push_cast; ring,
        Complex.arg_real_mul _ (by positivity),Complex.arg_neg_I]
    have he (n : ℤ) : (-2*π*I*(z+n))^(-s)=(-2*π*I)^(-s)*(z+n)^(-s) := by
      apply Complex.mul_cpow
      rw [hπ]
      have hn : 0≤(z+(n:ℂ)).arg := Complex.arg_nonneg_iff.mpr (by simpa using hz.le)
      have h := Complex.arg_le_pi (z+(n:ℂ))
      constructor <;> linarith [Real.pi_pos]
    simpa only [he] using (summable_row_cpow (z:=z) hs).mul_left ((-2*(π:ℂ)*I)^(-s))
  have H := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_positiveGammaDensity hs v)
    (by norm_num : (1:ℝ)<2) (gammaDensity_decay hv) (by
      simpa only [Hf,Function.comp_def,Equiv.neg_apply] using (hsG.mul_right (Complex.Gamma s)).comp_injective (Equiv.neg ℤ).injective) 0
  simp only [zero_add,Hf,QuotientAddGroup.mk_zero,fourier_eval_zero,mul_one] at H
  have hsum : Summable (fun n : ℤ => positiveGammaDensity s v (n:ℝ)) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    simpa only [Function.comp_def] using (gammaDensity_decay (s:=s) hv).comp_tendsto Int.tendsto_coe_cofinite
  have hz0 : positiveGammaDensity s v 0=0 := by apply indicator_of_notMem; simp
  have hp (n : ℕ) : positiveGammaDensity s v ((n+1:ℕ):ℝ)=
      ((n+1:ℕ):ℂ)^(s-1)*Complex.exp (2*π*I*z*(n+1)) := by
    rw [positiveGammaDensity,indicator_of_mem (show (0:ℝ)<(n+1:ℕ) by positivity),gammaLaplaceKernel,mul_comm]
    push_cast; dsimp [v]; ring_nf
  rw [tsum_int_eq_zero_add_tsum_pnat hsum] at H
  have hneg : (∑' n : ℕ+,positiveGammaDensity s v ((Int.cast (R:=ℝ)) (-(n:ℤ))))=0 := by
    calc _ = ∑' _n : ℕ+,(0:ℂ) := by
           apply tsum_congr; intro n
           apply indicator_of_notMem; simp
         _ = 0 := tsum_zero
  simp only [hneg,add_zero,Int.cast_zero,hz0,zero_add,Int.cast_natCast] at H
  rw [tsum_pnat_eq_tsum_succ (f:=fun n : ℕ => positiveGammaDensity s v (n:ℝ))] at H
  simp only [hp,tsum_mul_right] at H
  apply H.trans
  congr 1
  exact tsum_comp_neg (f:=fun n : ℤ => (-2*π*I*(z+n))^(-s))

/-- Lipschitz summation with the principal power in the upper
half-plane. The Fourier coefficients have the factor `(-2πi)^s/Γ(s)`. -/
theorem lipschitz_summation {s z : ℂ} (hs : 1<s.re) (hz : 0<z.im) :
    (∑' n : ℤ,(z+n)^(-s))=((-2*π*I)^s/Complex.Gamma s)*
      ∑' n : ℕ+,((n:ℕ):ℂ)^(s-1)*Complex.exp (2*π*I*z*n) := by
  let c : ℂ := -2*π*I
  have hc : c≠0 := by dsimp [c]; exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have harg : c.arg= -(π/2) := by
    rw [show c=((2*π:ℝ):ℂ)*(-I) by dsimp [c]; push_cast; ring,
      Complex.arg_real_mul _ (by positivity),Complex.arg_neg_I]
  have hf (n : ℤ) : (c*(z+n))^(-s)=c^(-s)*(z+n)^(-s) := by
    apply Complex.mul_cpow; rw [harg]
    have hn : 0≤(z+(n:ℂ)).arg := Complex.arg_nonneg_iff.mpr (by simpa using hz.le)
    have h := Complex.arg_le_pi (z+(n:ℂ))
    constructor <;> linarith [Real.pi_pos]
  have H := lipschitz_summation_laplace hs hz
  change _=(∑' n : ℤ,(c*(z+n))^(-s))*Complex.Gamma s at H
  simp_rw [hf] at H
  rw [tsum_mul_left,Complex.cpow_neg] at H
  rw [tsum_pnat_eq_tsum_succ (f:=fun n : ℕ => (n:ℂ)^(s-1)*Complex.exp (2*π*I*z*n))]
  simp only [Nat.cast_add_one] at H ⊢
  rw [H]
  change _=c^s/Complex.Gamma s*((c^s)⁻¹*_ *Complex.Gamma s)
  field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hc),Complex.Gamma_ne_zero_of_re_pos (by linarith : 0<s.re)]

end AnalyticNumberTheory.AnalyticTools
