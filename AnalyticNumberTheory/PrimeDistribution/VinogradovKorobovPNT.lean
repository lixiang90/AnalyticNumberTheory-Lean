import AnalyticNumberTheory.RiemannZeta.VinogradovKorobov
import AnalyticNumberTheory.PrimeDistribution.VinogradovKorobovPNTScale
import AnalyticNumberTheory.PrimeDistribution.ImprovedPrimeNumberTheorem
import AnalyticNumberTheory.PrimeDistribution.HuxleyZeroSums

/-!
# Prime number theorem with the Vinogradov–Korobov error

The exponential height balances the cost of truncating the explicit formula
against the width of the zero-free region. Prime powers and Abel summation
transfer the resulting estimate to theta and prime counting.
-/
noncomputable section
open Finset Real Filter
namespace AnalyticNumberTheory.PrimeDistribution

/-- The classical Vinogradov–Korobov prime number theorem error for psi. -/
theorem psi_error_of_vinogradovKorobov (hz : VinogradovKorobovZeroFreeHypothesis) :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x-x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) := by
  obtain ⟨c,hc,hgap⟩ := vinogradovKorobov_box_gap hz
  obtain ⟨A,hA,hzero⟩ := huxley_zero_sum_margin
  obtain ⟨B,hB,hexpl⟩ := explicit_formula_global_weight
  let d := min (c/4) (1/2)
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  have hdc : d≤c/4 := min_le_left ..
  have hd1 : d≤1/2 := min_le_right ..
  let T (x : ℝ) := Real.exp (vinogradovKorobovErrorScale x)
  have hT : Tendsto T atTop atTop := Real.tendsto_exp_atTop.comp tendsto_vinogradovKorobovErrorScale
  refine ⟨d,hd,B*(3+A),by positivity,?_⟩
  filter_upwards [vinogradovKorobov_error_parameters (A:=48/d) (B:=5) (by positivity) (by norm_num),
    hT.eventually_ge_atTop 2,hT.eventually hgap,(tendsto_vinogradovKorobovDenom.comp hT).eventually_ge_atTop 1,
    eventually_ge_atTop (2:ℝ)] with x hp hT2 hbox hD1 hx
  let L := Real.log x
  let l := Real.log L
  let v := vinogradovKorobovErrorScale x
  let D := vinogradovKorobovDenom (T x)
  let E := Real.exp (-d*v)
  change 1≤l ∧ 4≤L ∧ 1≤v ∧ 48/d*l≤v ∧ 5*v≤L ∧ v*D≤L at hp
  obtain ⟨hl,hL,hv,habs,hmargin,hbal⟩ := hp
  have hx' : 0<x := by linarith
  have hLp : 0<L := by linarith
  have hvp : 0<v := by linarith
  have hD : 0<D := zero_lt_one.trans_le hD1
  have he : 0<E := Real.exp_pos _
  have hlogT : Real.log (T x)=v := Real.log_exp _
  have hδ (z : ℂ) (hz : z∈nontrivialZerosUpTo (T x)) : c*v/L≤1-z.re := by
    have h := (div_le_iff₀ hD).mpr (hbox z hz)
    apply le_trans _ h
    apply (div_le_div_iff₀ hLp hD).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hbal hc.le]
  have H := hzero (by linarith : 1<x) hT2 (by linarith : 0≤L/2)
    (by rw [hlogT]; change _≤L; linarith : (12/5)*Real.log (T x)+L/2≤Real.log x) hδ
  have hlog : Real.log (1+L) ≤ 2*l := by
    have h := Real.log_le_log (by linarith : 0<1+L) (by linarith : 1+L≤2*L)
    rw [Real.log_mul (by norm_num) hLp.ne'] at h
    dsimp only [l]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have ha : 48*l≤d*v := by
    have heq : 48/d*l=(48*l)/d := by ring
    rw [heq,div_le_iff₀ hd] at habs; linarith only [habs]
  have hsave : (1+L)^24*Real.exp (-(L/2)*(c*v/L))≤E := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by linarith : 0<1+L),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show -(L/2)*(c*v/L)=-(c*v/2) by field_simp]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hlog,ha,mul_le_mul_of_nonneg_right hdc hvp.le]
  have hs : (∑ z∈nontrivialZerosUpTo (T x),(zeroMultiplicity z:ℝ)*x^(z.re-1))≤A*E :=
    H.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsave hA.le)
  have hTx : T x≤x := (Real.exp_le_exp.mpr (by change v≤L; linarith)).trans_eq (Real.exp_log hx')
  have htr : x*L^2/T x≤x*E := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hx'.le
    rw [div_le_iff₀ (Real.exp_pos _)]
    change L^2≤Real.exp (-d*v)*Real.exp v
    rw [←Real.exp_add,←Real.rpow_two,Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    change l*2≤ -d*v+v
    nlinarith only [ha,mul_le_mul_of_nonneg_right hd1 hvp.le,hl]
  have hltr : L≤x*L^2/T x := by
    have hq := (one_le_div (Real.exp_pos _)).mpr hTx
    have hh := mul_le_mul_of_nonneg_right hq (sq_nonneg L)
    nlinarith only [hh,mul_nonneg hLp.le (by linarith : 0≤L-1),show x/T x*L^2=x*L^2/T x by ring]
  have hg := hexpl hx hT2 hTx
  have hsmall : L≤x*E := hltr.trans htr
  have hone : 1≤x*E := (by linarith : 1≤L).trans hsmall
  change |Chebyshev.psi x-x|≤B*(3+A)*x*E
  exact hg.trans ((mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hone htr) hsmall) (mul_le_mul_of_nonneg_left hs hx'.le)) hB.le).trans_eq (by ring))

private theorem eventually_sqrt_le_vk_error {d : ℝ} (hd : 0<d) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x≤x*Real.exp (-d*vinogradovKorobovErrorScale x) := by
  filter_upwards [vinogradovKorobov_error_parameters (A:=1) (by norm_num) (show 0<2*d by positivity),
    eventually_gt_atTop (0:ℝ)] with x hp hx
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]
  conv_rhs => lhs; rw [←Real.exp_log hx]
  rw [←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hp.2.2.2.2.1])

/-- The classical Vinogradov–Korobov error for Chebyshev theta. -/
theorem theta_error_of_vinogradovKorobov (hz : VinogradovKorobovZeroFreeHypothesis) :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x-x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) := by
  obtain ⟨d,hd,C,hC,H⟩ := psi_error_of_vinogradovKorobov hz
  let K := (Real.log 4+4)*3
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨d,hd,K+C,by positivity,?_⟩
  filter_upwards [H,eventually_sqrt_le_vk_error hd] with x h hs
  have hp := abs_psi_sub_theta_le_mul_sqrt x
  rw [abs_sub_comm (Chebyshev.psi x)] at hp
  change _≤K*√x at hp
  nlinarith only [abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x,hp,h,
    mul_le_mul_of_nonneg_left hs hK.le]

/-- The error in prime counting relative to the logarithmic integral has the
same three-fifths exponential scale. -/
theorem primePi_error_of_vinogradovKorobov (hz : VinogradovKorobovZeroFreeHypothesis) :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |primePi x-logIntegral x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) := by
  obtain ⟨d,hd,C,hC,H⟩ := theta_error_of_vinogradovKorobov hz
  refine ⟨d/2,by positivity,?_⟩
  apply primePi_error_of_theta_weight (F:=fun x => Real.exp (-d*vinogradovKorobovErrorScale x))
    (fun _ => (Real.exp_pos _).le) ⟨C,hC,H⟩ (eventually_sqrt_le_vk_error (by positivity))
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 4,eventually_ge_atTop (2:ℝ)] with x hL hx t ht htx
  have hx' : 0<x := by linarith
  have hs := Real.sqrt_pos.mpr hx'
  have ht' := hs.trans_le ht
  have h₁ := Real.log_le_log hs ht
  rw [Real.log_sqrt hx'.le] at h₁
  have h₂ := Real.log_le_log ht' htx
  have hL' : 0<Real.log t := by linarith
  have hl' := Real.log_pos (by linarith : 1<Real.log t)
  have hll := Real.log_le_log hL' h₂
  have hnum : (Real.log x)^(3/5:ℝ) ≤ 2*(Real.log t)^(3/5:ℝ) := by
    have hh := Real.rpow_le_rpow (by linarith : 0≤Real.log x) (by linarith : Real.log x≤2*Real.log t)
      (by norm_num : (0:ℝ)≤3/5)
    rw [Real.mul_rpow (by norm_num) hL'.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (3/5:ℝ)≤1)).trans_eq (Real.rpow_one _))
      (Real.rpow_nonneg hL'.le _))
  have hscale : vinogradovKorobovErrorScale x≤2*vinogradovKorobovErrorScale t := by
    dsimp only [vinogradovKorobovErrorScale]
    rw [←mul_div_assoc]
    exact div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hl' _)
      (Real.rpow_le_rpow hl'.le hll (by norm_num))
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hscale hd.le]

/-- The unconditional Vinogradov–Korobov error estimate for the von Mangoldt summatory function. -/
theorem psi_error_vinogradovKorobov :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x-x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) :=
  psi_error_of_vinogradovKorobov RiemannZeta.vinogradovKorobov_zero_gap

/-- The unconditional Vinogradov–Korobov error estimate for the first Chebyshev function. -/
theorem theta_error_vinogradovKorobov :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x-x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) :=
  theta_error_of_vinogradovKorobov RiemannZeta.vinogradovKorobov_zero_gap

/-- The unconditional Vinogradov–Korobov error estimate for the prime counting function relative to the logarithmic integral. -/
theorem primePi_error_vinogradovKorobov :
    ∃ d>(0:ℝ), ∃ C>(0:ℝ), ∀ᶠ x : ℝ in atTop,
      |primePi x-logIntegral x|≤C*x*Real.exp (-d*vinogradovKorobovErrorScale x) :=
  primePi_error_of_vinogradovKorobov RiemannZeta.vinogradovKorobov_zero_gap

end AnalyticNumberTheory.PrimeDistribution
