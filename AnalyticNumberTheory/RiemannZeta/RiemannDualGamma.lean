import AnalyticNumberTheory.RiemannZeta.RiemannSharpApproximation
import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling

/-!
# Functional-equation identities for the reciprocal gamma multiplier
-/
noncomputable section
open Real Complex
open AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

theorem riemannDualGamma_eq_gamma_cos (s : ℂ) :
    riemannDualGamma s=Gammaℂ (1-s)*Complex.cos (Real.pi*(1-s)/2) := by
  have hπ : 0<2*Real.pi := by positivity
  have hp := hurwitzDualMode_scale s 1 hπ
  have hm := hurwitzDualMode_scale s (-1) hπ
  simp only [mul_one,mul_neg,neg_mul] at hp hm
  rw [riemannDualGamma,hp,neg_mul,hm]
  dsimp only [hurwitzDualMode,hurwitzFrequency]
  simp only [Complex.ofReal_one,Complex.ofReal_neg,neg_neg,one_mul,neg_mul]
  rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero,Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.log_I,Complex.log_neg_I,Gammaℂ_def,Complex.cos]
  push_cast
  rw [show -(1-s)=s-1 by ring,
    show -(Real.pi/2:ℂ)*I*(s-1)=Real.pi*(1-s)/2*I by ring,
    show (Real.pi/2:ℂ)*I*(s-1)= -(Real.pi*(1-s)/2*I) by ring]
  ring

theorem riemannDualGamma_eq_ratio {s : ℂ} (ht : s.im≠0) :
    riemannDualGamma s=Gammaℝ (1-s)/Gammaℝ s := by
  have h : ∀ n : ℕ,1-s≠ -(2*(n:ℂ)+1) := by
    intro n he
    have h' := congrArg Complex.im he
    simp [Complex.mul_im] at h'
    exact ht h'
  rw [riemannDualGamma_eq_gamma_cos,←Gammaℝ_div_Gammaℝ_one_sub h]
  simp

theorem riemannDualGamma_reciprocal {s : ℂ} (ht : s.im≠0) :
    riemannDualGamma s*riemannDualGamma (1-s)=1 := by
  have h (z : ℂ) (hz : z.im≠0) : Gammaℝ z≠0 := by
    rw [Ne,Gammaℝ_eq_zero_iff]
    rintro ⟨n,hn⟩
    have H := congrArg Complex.im hn
    exact hz (by simpa [Complex.mul_im] using H)
  have ht' : (1-s).im≠0 := by simpa using ht
  rw [riemannDualGamma_eq_ratio ht,riemannDualGamma_eq_ratio ht',sub_sub_cancel]
  field_simp [h s ht,h _ ht']

theorem riemannZeta_dualGamma_functional_equation {s : ℂ} (ht : s.im≠0) :
    riemannZeta s=riemannDualGamma s*riemannZeta (1-s) := by
  have hne (z : ℂ) (hz : z.im≠0) : z≠0 := fun he => hz (by rw [he];rfl)
  have ht' : (1-s).im≠0 := by simpa using ht
  have hg : Gammaℝ (1-s)≠0 := by
    rw [Ne,Gammaℝ_eq_zero_iff]
    rintro ⟨n,hn⟩
    exact ht' (by simpa [Complex.mul_im] using congrArg Complex.im hn)
  rw [riemannZeta_def_of_ne_zero (hne s ht),riemannZeta_def_of_ne_zero (hne _ ht'),
      completedRiemannZeta_one_sub,riemannDualGamma_eq_ratio ht]
  field_simp [hg]

/-- Polynomial growth of the gamma multiplier in the closed strip. -/
theorem norm_riemannDualGamma_strip_bound : ∃ C : ℝ,0<C ∧ ∀ s : ℂ,s.re∈Set.Icc (0:ℝ) 1 → 1≤|s.im| →
    ‖riemannDualGamma s‖≤C*|s.im|^(1/2-s.re) := by
  obtain ⟨c,C,hc,hC,H⟩ := norm_complex_gamma_strip_bounds 0 1
  refine ⟨2*C,by linarith,?_⟩
  intro s hσ ht
  let v := 1-s
  have hv : v.re∈Set.Icc (0:ℝ) 1 := by change 0≤1-s.re ∧ 1-s.re≤1;constructor <;> linarith [hσ.1,hσ.2]
  have hvi : |v.im|=|s.im| := by simp [v]
  have hg := (H hv (hvi ▸ ht)).2
  rw [Complex.re_add_im,hvi] at hg
  have hCn := (hc.trans_le hC).le
  have hcos (z : ℂ) : ‖Complex.cos z‖≤Real.exp |z.im| := by
    rw [Complex.cos,norm_div,Complex.norm_two,div_le_iff₀ (by norm_num : (0:ℝ)<2)]
    apply (norm_add_le _ _).trans
    simp only [Complex.norm_exp,Complex.mul_I_re,neg_im,neg_neg]
    linarith [Real.exp_le_exp.mpr (le_abs_self z.im),Real.exp_le_exp.mpr (neg_le_abs z.im)]
  have hcp : ‖(2*(Real.pi:ℂ))^(-v)‖≤1 := by
    rw [show (2*(Real.pi:ℂ))=((2*Real.pi:ℝ):ℂ) by push_cast;rfl,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith [hv.1])
  have hcos' := hcos (Real.pi*v/2)
  have he : |(Real.pi*v/2).im|=Real.pi/2*|s.im| := by
    have h : (Real.pi*v/2).im=Real.pi*v.im/2 := by simp [Complex.div_ofNat_im,Complex.mul_im]
    rw [h,abs_div,abs_mul,abs_of_pos Real.pi_pos,hvi,abs_of_pos (by norm_num : (0:ℝ)<2)];ring
  rw [he] at hcos'
  rw [riemannDualGamma_eq_gamma_cos]
  change ‖Gammaℂ v*Complex.cos (Real.pi*v/2)‖≤_
  rw [Gammaℂ_def,norm_mul,norm_mul,norm_mul,Complex.norm_two]
  apply (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcp (by norm_num : (0:ℝ)≤2)) hg
    (norm_nonneg _) (by positivity)) hcos' (norm_nonneg _) (by positivity)).trans_eq
  rw [show v.re-1/2=1/2-s.re by change 1-s.re-1/2=1/2-s.re;ring]
  rw [show -(Real.pi/2)*|s.im| = -(Real.pi/2*|s.im|) by ring,Real.exp_neg]
  field_simp

end AnalyticNumberTheory.RiemannZeta
