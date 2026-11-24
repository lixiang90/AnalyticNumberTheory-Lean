import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalLineShift
import AnalyticNumberTheory.RiemannZeta.GaussianWeights
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Freedom of the displacement in a smoothed Dirichlet weight

In the right half-plane the only pole of the Mellin weight that can be
crossed by moving a vertical line is at zero. Two strictly positive
displacements therefore define the same weight.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

private theorem norm_Gamma_le_real {z : ℂ} (hz : 0 < z.re) : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral,Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private theorem completionFactor_polynomial_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖xiCompletionFactor z‖ ≤ C*(1+‖z‖)^2 := by
  have hi : (Icc (a/2) (b/2)).Nonempty := ⟨a/2,le_rfl,by linarith⟩
  have hg : ContinuousOn Real.Gamma (Icc (a/2) (b/2)) := Real.differentiableOn_Gamma_Ioi.continuousOn.mono
    (fun x hx => by have := hx.1; exact show 0 < x by linarith)
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMaxOn (f := Real.Gamma) hi hg
  let C := Real.Gamma v
  have hC : 0 < C := Real.Gamma_pos_of_pos (by linarith [hv.1])
  refine ⟨C,hC,?_⟩
  intro z hz
  have hp : ‖(π:ℂ)^(-z/2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith [hz.1]
  have hzr : (z/2).re = z.re/2 := by simp
  have hGa := (norm_Gamma_le_real (z := z/2) (by rw [hzr]; linarith [hz.1])).trans
    (hm (by rw [hzr]; exact ⟨by linarith [hz.1],by linarith [hz.2]⟩))
  have hmz : ‖z-1‖ ≤ 1+‖z‖ := by simpa [add_comm] using norm_sub_le z 1
  unfold xiCompletionFactor Gammaℝ
  simp only [norm_mul,norm_div,norm_one,Complex.norm_ofNat]
  calc _ ≤ (1/2)*‖z‖*(1+‖z‖)*(1*C) := mul_le_mul
            (mul_le_mul_of_nonneg_left hmz (by positivity)) (mul_le_mul hp hGa (norm_nonneg _) zero_le_one)
            (by positivity) (by positivity)
       _ ≤ _ := by nlinarith [norm_nonneg z, mul_nonneg hC.le (sq_nonneg ‖z‖), mul_nonneg hC.le (norm_nonneg z)]

/-- Uniform quadratic decay of the numerator of a Gaussian weight on every strip
where the shifted completion factor is holomorphic. -/
theorem xiGaussianNumerator_strip_bound (s : ℂ) (k n : ℕ) (hn : 0 < n)
    {a b : ℝ} (ha : 0 < s.re+a) (hab : a ≤ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      let w := (x:ℂ)+t*I
      ‖xiCompletionFactor (s+w)^k * Complex.exp (w^2) / (n:ℂ)^w‖ ≤ D/(1+t^2) := by
  obtain ⟨C,hC,hbound⟩ := completionFactor_polynomial_strip (a := s.re+a) (b := s.re+b) ha (by linarith)
  let m := max |a| |b|
  have hm : 0 ≤ m := (abs_nonneg a).trans (le_max_left ..)
  let d := ‖s‖+m
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let B := (C*(1+d)^2)^k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnr : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  refine ⟨B*Real.exp (m^2+(k+1:ℝ)^2)/(n:ℝ)^a,by positivity,?_⟩
  intro x hx t
  let w := (x:ℂ)+t*I
  have hxm : |x| ≤ m := abs_le.mpr ⟨by linarith [hx.1,neg_le_abs a,(le_max_left |a| |b| : |a| ≤ m)],
    by linarith [hx.2,le_abs_self b,(le_max_right |a| |b| : |b| ≤ m)]⟩
  have hden : (n:ℝ)^a ≤ ‖(n:ℂ)^w‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn,show w.re=x by simp [w]]
    exact Real.rpow_le_rpow_of_exponent_le hnr hx.1
  have hsw : ‖s+w‖ ≤ d+|t| := by
    have hh := norm_add_le (x:ℂ) ((t:ℂ)*I)
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hh
    have hh' := norm_add_le s w
    dsimp [d]; linarith
  have hbase : 1+‖s+w‖ ≤ (1+d)*Real.exp |t| := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp |t|) (show 0 ≤ 1+d by linarith)
    nlinarith [mul_nonneg hd (abs_nonneg t)]
  have harch := hbound (s+w) (by simp [w]; exact hx)
  have hG : ‖xiCompletionFactor (s+w)‖^k ≤ B*Real.exp ((2*k:ℝ)*|t|) := by
    have hh := harch.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 2) hC.le)
    apply (pow_le_pow_left₀ (norm_nonneg _) hh k).trans_eq
    dsimp [B]
    rw [mul_pow (1+d),← Real.exp_nat_mul,show C*((1+d)^2*Real.exp ((2:ℕ)*|t|)) =
      C*(1+d)^2*Real.exp ((2:ℕ)*|t|) by ring,mul_pow,← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hj : (w^2).re ≤ m^2-t^2 := by
    simp [w,pow_two]
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hxm 2,sq_abs x]
  have hpoly : 1+t^2 ≤ Real.exp (2*|t|) := by
    have hh := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp |t|) 2
    rw [← Real.exp_nat_mul] at hh
    norm_cast at hh
    nlinarith [abs_nonneg t,sq_abs t]
  have htotal : (2*k:ℝ)*|t|+(w^2).re+2*|t| ≤ m^2+(k+1:ℝ)^2 := by
    nlinarith [sq_nonneg (|t|-(k+1:ℝ)),sq_abs t]
  change ‖xiCompletionFactor (s+w)^k*Complex.exp (w^2)/(n:ℂ)^w‖ ≤ _
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_exp]
  apply (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le)
    (Real.rpow_pos_of_pos hn0 a) hden).trans
  rw [le_div_iff₀ (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ B*Real.exp ((2*k:ℝ)*|t|)*Real.exp (w^2).re/(n:ℝ)^a by positivity)
  apply hh.trans
  rw [show B*Real.exp ((2*k:ℝ)*|t|)*Real.exp (w^2).re/(n:ℝ)^a*Real.exp (2*|t|) =
    B*(Real.exp ((2*k:ℝ)*|t|)*Real.exp (w^2).re*Real.exp (2*|t|))/(n:ℝ)^a by ring,← Real.exp_add,← Real.exp_add]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotal) hB) (by positivity)

private theorem weight_eq_of_le (s : ℂ) (hs : 0 < s.re) (k n : ℕ) (hn : 0 < n)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    xiDirichletWeight s k a n = xiDirichletWeight s k b n := by
  let F (w : ℂ) := xiGaussianKernel s k w/(n:ℂ)^w
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hF : DifferentiableOn ℂ F {w : ℂ | w.re ∈ Icc a b} := by
    intro w hw
    have hw0 : w ≠ 0 := by intro hh; have h := hw.1; rw [hh,Complex.zero_re] at h; linarith
    have hz : 0 < (s+w).re := by rw [Complex.add_re]; linarith [hw.1]
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div _ (by change DifferentiableAt ℂ (fun w : ℂ => (n:ℂ)^w) w; simp_rw [Complex.cpow_def_of_ne_zero hnc]; fun_prop)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hnc))
    apply DifferentiableAt.div _ differentiableAt_id hw0
    exact (((differentiableAt_xiCompletionFactor hz).comp w ((differentiableAt_const _).add differentiableAt_id)).pow k).mul
      (Complex.differentiableAt_exp.comp w (differentiableAt_id.pow 2))
  obtain ⟨D,hD,hbound⟩ := xiGaussianNumerator_strip_bound s k n hn (by linarith : 0 < s.re+a) hab
  apply integral_verticalLine_eq_of_strip hab hF (D := D/a) (by positivity)
  intro x hx t
  let w := (x:ℂ)+t*I
  have hw : a ≤ ‖w‖ := hx.1.trans (by simpa [w] using Complex.re_le_norm w)
  have he : F w = (xiCompletionFactor (s+w)^k * Complex.exp (w^2) / (n:ℂ)^w)/w := by dsimp [F,xiGaussianKernel]; ring
  change ‖F w‖ ≤ _
  rw [he,norm_div]
  calc _ ≤ (D/(1+t^2))/a := div_le_div₀ (by positivity) (hbound x hx t) ha hw
       _ = _ := by ring


/-- For every positive index the smoothed weight is independent of the positive displacement. -/
theorem xiDirichletWeight_eq_of_pos (s : ℂ) (hs : 0 < s.re) (k n : ℕ) (hn : 0 < n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : xiDirichletWeight s k a n = xiDirichletWeight s k b n := by
  rcases le_total a b with h | h
  · exact weight_eq_of_le s hs k n hn ha h
  · exact (weight_eq_of_le s hs k n hn hb h).symm

end AnalyticNumberTheory.RiemannZeta
