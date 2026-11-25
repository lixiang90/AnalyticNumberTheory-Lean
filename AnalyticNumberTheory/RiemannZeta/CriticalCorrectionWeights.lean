import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCoefficientRegularity
import AnalyticNumberTheory.RiemannZeta.CriticalCosineExpansion

/-!
# The first correction on a single Riemann–Siegel block

Between successive entry heights, the fractional-part parameter traces
[0,2]. The correction amplitude has size O(j^(-1/2)) and its derivative
has size O(j^(-3/2)) on the full closed block.
-/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.RiemannZeta

def hardySaddleRoot (t : ℝ) := Real.sqrt (t/(2*Real.pi))

def hardyCorrectionWeight (j : ℕ) (t : ℝ) :=
  (hardySaddleRoot t)^(-(1/2:ℝ))*riemannSiegelCorrection (2*(hardySaddleRoot t-j))

def hardyCorrectionWeightDeriv (j : ℕ) (t : ℝ) :=
  let x := hardySaddleRoot t
  let c := 2*(x-j)
  ((-(1/2:ℝ))*x^(-(3/2:ℝ))*riemannSiegelCorrection c+
    x^(-(1/2:ℝ))*(2*deriv riemannSiegelCorrection c))*(4*Real.pi*x)⁻¹

theorem hardySaddleRoot_pos {t : ℝ} (ht : 0<t) : 0<hardySaddleRoot t := by dsimp [hardySaddleRoot];positivity

theorem hardySaddleRoot_hasDerivAt {t : ℝ} (ht : 0<t) :
    HasDerivAt hardySaddleRoot ((4*Real.pi*hardySaddleRoot t)⁻¹) t := by
  have hh := (Real.hasDerivAt_sqrt (show 0<t/(2*Real.pi) by positivity).ne').comp t
    ((hasDerivAt_id t).div_const (2*Real.pi))
  convert hh using 1
  · rfl
  · dsimp [hardySaddleRoot];ring

theorem hardySaddleRoot_mem {j : ℕ} {t : ℝ} (ht : t∈Icc (hardyCutoff j) (hardyCutoff (j+1))) :
    hardySaddleRoot t∈Icc (j:ℝ) ((j:ℝ)+1) := by
  have hπ : 0<2*Real.pi := by positivity
  have ht' : 0≤t := (show 0≤hardyCutoff j by dsimp [hardyCutoff];positivity).trans ht.1
  have hx := Real.sq_sqrt (show 0≤t/(2*Real.pi) by positivity)
  change (j:ℝ)≤Real.sqrt (t/(2*Real.pi)) ∧ Real.sqrt (t/(2*Real.pi))≤(j:ℝ)+1
  rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity),Real.sqrt_le_iff]
  refine ⟨(le_div_iff₀ hπ).mpr (by dsimp [hardyCutoff] at ht;nlinarith only [ht.1]),by positivity,
    (div_le_iff₀ hπ).mpr ?_⟩
  dsimp [hardyCutoff] at ht;push_cast at ht;nlinarith only [ht.2]

theorem hardyCorrectionWeight_hasDerivAt (j : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (hardyCorrectionWeight j) (hardyCorrectionWeightDeriv j t) t := by
  let x := hardySaddleRoot t
  let c := 2*(x-j)
  have hx : 0<x := hardySaddleRoot_pos ht
  have hroot := hardySaddleRoot_hasDerivAt ht
  have h₁ := (Real.hasDerivAt_rpow_const (p:= -(1/2:ℝ)) (Or.inl hx.ne')).comp t hroot
  have h₂ := (analyticAt_riemannSiegelCorrection c).differentiableAt.hasDerivAt.comp t
    ((hroot.sub_const (j:ℝ)).const_mul 2)
  convert h₁.mul h₂ using 1
  · rfl
  · dsimp [hardyCorrectionWeightDeriv,x,c]
    rw [show (-(1/2:ℝ))-1= -(3/2) by norm_num];ring

theorem continuousOn_hardyCorrectionWeightDeriv (j : ℕ) : ContinuousOn (hardyCorrectionWeightDeriv j) (Ioi (0:ℝ)) := by
  have hroot : Continuous hardySaddleRoot := (Real.continuous_sqrt.comp (continuous_id.div_const _))
  have hcd : ContDiff ℝ 1 riemannSiegelCorrection :=
    (show AnalyticOnNhd ℝ riemannSiegelCorrection univ from fun x _ => analyticAt_riemannSiegelCorrection x).contDiff
  have hd := hcd.continuous_deriv (by norm_num)
  intro t ht
  have hx := hardySaddleRoot_pos ht
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun t => (_+_)*((4*Real.pi*hardySaddleRoot t)⁻¹)) t
  have hx₀ : ContinuousAt hardySaddleRoot t := hroot.continuousAt
  have harg : ContinuousAt (fun u => 2*(hardySaddleRoot u-j)) t := continuousAt_const.mul (hx₀.sub continuousAt_const)
  exact (((continuousAt_const.mul (hx₀.rpow_const (Or.inl hx.ne'))).mul (continuous_riemannSiegelCorrection.continuousAt.comp harg)).add
    ((hx₀.rpow_const (Or.inl hx.ne')).mul (continuousAt_const.mul (hd.continuousAt.comp harg)))).mul
    ((continuousAt_const.mul hx₀).inv₀ (mul_ne_zero (by positivity : (4*Real.pi)≠0) hx.ne'))

theorem hardyCorrectionWeight_bounds : ∃ C : ℝ,0<C ∧ ∀{j : ℕ} {t : ℝ},1≤j →
    t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) →
    |hardyCorrectionWeight j t|≤C*(j:ℝ)^(-(1/2:ℝ)) ∧
    |hardyCorrectionWeightDeriv j t|≤C*(j:ℝ)^(-(3/2:ℝ)) := by
  obtain ⟨D,hD,H⟩ := riemannSiegelCorrection_C1_bound
  refine ⟨3*D,by positivity,?_⟩
  intro j t hj ht
  let x := hardySaddleRoot t
  let c := 2*(x-j)
  have hX := hardySaddleRoot_mem ht
  change (j:ℝ)≤x ∧ x≤(j:ℝ)+1 at hX
  have hj' : (1:ℝ)≤j := by exact_mod_cast hj
  have hx' : 0<x := by linarith [hX.1]
  have hx : 1≤x := by linarith [hX.1]
  have hJ : 0<(j:ℝ) := by linarith
  have hc : c∈Icc (0:ℝ) 2 := ⟨by dsimp [c];linarith [hX.1],by dsimp [c];linarith [hX.2]⟩
  obtain ⟨h₁,h₂⟩ := H hc
  have hm (v : ℝ) (hv : v≤0) : x^v≤(j:ℝ)^v := Real.rpow_le_rpow_of_nonpos hJ hX.1 hv
  have hx₁ : 0≤x^(-(1/2:ℝ)) := by positivity
  have hx₂ : 0≤x^(-(3/2:ℝ)) := by positivity
  constructor
  · change |x^(-(1/2:ℝ))*riemannSiegelCorrection c|≤_
    rw [abs_mul,abs_of_nonneg hx₁]
    have hh := mul_le_mul (hm _ (by norm_num : -(1/2:ℝ)≤0)) h₁ (abs_nonneg _) (Real.rpow_nonneg hJ.le _)
    linarith only [hh,mul_nonneg hD.le (Real.rpow_nonneg hJ.le (-(1/2:ℝ)))]
  · change |(_+_)*((4*Real.pi*x)⁻¹)|≤_
    rw [abs_mul,abs_of_pos (by positivity : 0<(4*Real.pi*x)⁻¹)]
    have hcmp : x^(-(3/2:ℝ))≤x^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hh₁ : |(-(1/2:ℝ))*x^(-(3/2:ℝ))*riemannSiegelCorrection c|≤x^(-(1/2:ℝ))*D := by
      rw [abs_mul,abs_mul,abs_of_nonneg hx₂];norm_num
      have h := mul_le_mul hcmp h₁ (abs_nonneg _) hx₁
      have h' := mul_nonneg hx₂ (abs_nonneg (riemannSiegelCorrection c))
      linarith only [h,h']
    have hh₂ : |x^(-(1/2:ℝ))*(2*deriv riemannSiegelCorrection c)|≤2*(x^(-(1/2:ℝ))*D) := by
      rw [abs_mul,abs_of_nonneg hx₁,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith only [mul_le_mul_of_nonneg_left h₂ hx₁]
    have hh := (abs_add_le ..).trans (add_le_add hh₁ hh₂)
    have hden : (4*Real.pi*x)⁻¹≤x⁻¹ := inv_anti₀ hx' (by nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le hx'.le])
    apply (mul_le_mul hh hden (by positivity) (by positivity)).trans
    change (x^(-(1/2:ℝ))*D+2*(x^(-(1/2:ℝ))*D))*x⁻¹≤_
    rw [show (x^(-(1/2:ℝ))*D+2*(x^(-(1/2:ℝ))*D))*x⁻¹=(3*D)*(x^(-(1/2:ℝ))/x) by ring,
      ←Real.rpow_sub_one hx'.ne',show -(1/2:ℝ)-1= -(3/2) by norm_num]
    exact mul_le_mul_of_nonneg_left (hm _ (by norm_num)) (by positivity)

end AnalyticNumberTheory.RiemannZeta
