import AnalyticNumberTheory.RiemannZeta.RiemannDualGamma

/-!
# The weight in the reflected second moment

Taking the ratio of the two real gamma factors cancels the common
exponential decay. The squared multiplier differs from its leading
power by a relative error bounded by a constant divided by the height.
-/
noncomputable section
open Complex Real Set
open AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.RiemannZeta

private theorem gammaReal_log_weight {z : ℂ} (hσ : z.re∈Icc (0:ℝ) 1) (ht : 2≤ |z.im|) :
    ∃ r : ℝ, ‖Gammaℝ z‖=Real.pi^(-z.re/2)*
      (Real.sqrt (2*Real.pi)*Real.exp (-(Real.pi/2)*(|z.im|/2))*(|z.im|/2)^(z.re/2-1/2))*Real.exp r ∧
      |r|≤2*stirlingStripErrorConst 0 1/|z.im| := by
  have hh : z.re/2∈Icc (0:ℝ) 1 := ⟨by linarith [hσ.1],by linarith [hσ.2]⟩
  have hab : |z.im/2|= |z.im|/2 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  obtain ⟨r,H,hr⟩ := norm_complex_gamma_strip_log_error_le hh (show 1≤ |z.im/2| by rw [hab];linarith)
  have he : ((z.re/2:ℝ):ℂ)+((z.im/2:ℝ):ℂ)*I=z/2 := by
    push_cast;rw [show z.re/2+(z.im:ℂ)/2*I=((z.re:ℂ)+z.im*I)/2 by ring,Complex.re_add_im]
  rw [he,hab] at H
  rw [hab] at hr
  refine ⟨r,?_,by convert hr using 1 <;> ring⟩
  rw [Gammaℝ_def,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,Complex.div_ofNat_re,neg_re,H]
  ring

/-- Uniform logarithmic remainder of the squared gamma multiplier on the
closed critical strip at heights of magnitude at least two. -/
theorem norm_sq_riemannDualGamma_log_error {s : ℂ} (hσ : s.re∈Icc (0:ℝ) 1) (ht : 2≤ |s.im|) :
    ∃ r : ℝ, ‖riemannDualGamma s‖^2=(|s.im|/(2*Real.pi))^(1-2*s.re)*Real.exp r ∧
      |r|≤8*stirlingStripErrorConst 0 1/|s.im| := by
  have hp : 0< |s.im| := by linarith
  have him : |(1-s).im|= |s.im| := by simp
  have hre : (1-s).re=1-s.re := by simp
  have hσ' : (1-s).re∈Icc (0:ℝ) 1 := ⟨by rw [hre];linarith [hσ.2],by rw [hre];linarith [hσ.1]⟩
  obtain ⟨a,ha,ha'⟩ := gammaReal_log_weight hσ ht
  obtain ⟨b,hb,hb'⟩ := gammaReal_log_weight hσ' (him ▸ ht)
  rw [him,hre] at hb
  rw [him] at hb'
  let k := 1/2-s.re
  have hnorm : ‖riemannDualGamma s‖=(|s.im|/(2*Real.pi))^k*Real.exp (b-a) := by
    rw [riemannDualGamma_eq_ratio (abs_pos.mp hp),norm_div,ha,hb,Real.exp_sub]
    have hc : Real.sqrt (2*Real.pi)*Real.exp (-(Real.pi/2)*(|s.im|/2))≠0 := by positivity
    have hpow : (|s.im|/(2*Real.pi))^k=(|s.im|/2)^k*Real.pi^(-k) := by
      rw [show |s.im|/(2*Real.pi)=(|s.im|/2)/Real.pi by ring,
        Real.div_rpow (by positivity) Real.pi_pos.le,Real.rpow_neg Real.pi_pos.le,div_eq_mul_inv]
    have hπ : Real.pi^(-(1-s.re)/2)=Real.pi^(-s.re/2)*Real.pi^(-k) := by
      rw [←Real.rpow_add Real.pi_pos];congr 1;dsimp [k];ring
    have hx : (|s.im|/2)^((1-s.re)/2-1/2)=(|s.im|/2)^(s.re/2-1/2)*(|s.im|/2)^k := by
      rw [←Real.rpow_add (by positivity : 0< |s.im|/2)];congr 1;dsimp [k];ring
    rw [hpow,hπ,hx]
    field_simp [hc,Real.rpow_pos_of_pos Real.pi_pos _,Real.rpow_pos_of_pos (by positivity : 0< |s.im|/2) _] <;> ring
  refine ⟨2*(b-a),?_,?_⟩
  · rw [hnorm,mul_pow,←Real.rpow_natCast ((|s.im|/(2*Real.pi))^k) 2,←Real.rpow_mul (by positivity : 0≤ |s.im|/(2*Real.pi)),
      ←Real.exp_nat_mul]
    congr 1 <;> simp [k] <;> ring
  · calc |2*(b-a)| = 2*|b-a| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
         _ ≤ 2*(|b|+|a|) := by gcongr;exact abs_sub _ _
         _ ≤ _ := by field_simp at ha' hb' ⊢ <;> nlinarith

private theorem abs_real_exp_sub_one {r B : ℝ} (hB : 0≤B) (hr : |r|≤B) :
    |Real.exp r-1|≤Real.exp B*|r| := by
  rcases le_total 0 r with h|h
  · rw [abs_of_nonneg h,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp h))]
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-r)) (Real.exp_pos r).le
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
    have h' := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self r).trans hr)) h
    linarith
  · rw [abs_of_nonpos h,abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr h))]
    exact (by linarith [Real.add_one_le_exp r, mul_le_mul_of_nonneg_right (Real.one_le_exp hB) (neg_nonneg.mpr h)])

/-- For the squared functional-equation factor, the absolute error is at
most the main power times an absolute constant divided by the height. -/
theorem norm_sq_riemannDualGamma_error : ∃ C : ℝ,0<C ∧ ∀ {s : ℂ},
    s.re∈Icc (0:ℝ) 1 → 2≤ |s.im| →
    |‖riemannDualGamma s‖^2-(|s.im|/(2*Real.pi))^(1-2*s.re)|≤
      C/|s.im| *(|s.im|/(2*Real.pi))^(1-2*s.re) := by
  let B := 8*stirlingStripErrorConst 0 1
  have hB : 0≤B := by dsimp [B];positivity [stirlingStripErrorConst_nonneg 0 1]
  refine ⟨Real.exp B*(B+1),by positivity,?_⟩
  intro s hσ ht
  have hp : 0< |s.im| := by linarith
  obtain ⟨r,hr,h⟩ := norm_sq_riemannDualGamma_log_error hσ ht
  change |r|≤B/|s.im| at h
  have H := abs_real_exp_sub_one hB (h.trans (div_le_self hB (by linarith)))
  let m := (|s.im|/(2*Real.pi))^(1-2*s.re)
  change |‖riemannDualGamma s‖^2-m|≤_ * m
  change ‖riemannDualGamma s‖^2=m*Real.exp r at hr
  have hm : 0≤m := by dsimp [m];positivity
  rw [hr,←mul_sub_one,abs_mul,abs_of_nonneg hm]
  calc m*|Real.exp r-1| ≤ m*(Real.exp B*(B/|s.im|)) :=
         mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left h (Real.exp_pos B).le)) hm
       _ ≤ _ := by
         have := mul_le_mul_of_nonneg_left (show B/|s.im|≤(B+1)/|s.im| by gcongr;linarith) (show 0≤m*Real.exp B by positivity)
         convert this using 1 <;> ring

end AnalyticNumberTheory.RiemannZeta
