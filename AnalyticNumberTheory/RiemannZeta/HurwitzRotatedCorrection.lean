import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalModel
import AnalyticNumberTheory.RiemannZeta.HurwitzRiemannSiegel
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# Rotation of the shifted first-corrected formula

At positive heights both polynomials have elementary phases. The square-root
bound for the reciprocal polynomial preserves the full first-correction error.
-/

noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

theorem norm_hurwitzReciprocalPoly_le_sqrt {s : ℂ} (hs : s.re=1/2) (a : ℝ) (q : ℕ) :
    ‖hurwitzReciprocalPoly a q s‖≤2*Real.sqrt q := by
  apply (norm_sum_le ..).trans
  apply le_trans _ (sum_Icc_inv_sqrt_le q)
  have hsum (N : ℕ) : (∑m∈range N,(Real.sqrt ((m:ℝ)+1))⁻¹)=
      ∑n∈Finset.Icc 1 N,(Real.sqrt n)⁻¹ := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih];simp
  rw [←hsum]
  apply sum_le_sum;intro m _
  rw [norm_mul,norm_hurwitzShift,one_mul,←ofReal_natCast,←ofReal_one,←ofReal_add,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),sub_re,Complex.ofReal_re,hs,
    show (1/2:ℝ)-1= -(1/2) by norm_num,Real.rpow_neg (by positivity),←Real.sqrt_eq_rpow]

/-- Elementary Hardy rotation of the ordinary reciprocal gamma factor. -/
theorem hurwitz_rotated_gamma_error {t : ℝ} (ht : 2≤t) :
    let E := Complex.exp ((hardyPhase t:ℂ)*I)
    ‖E*riemannDualGamma (1/2+(t:ℂ)*I)-conj E‖≤8/t := by
  intro E
  let U := hardyGammaUnit t
  let G := riemannDualGamma (1/2+(t:ℂ)*I)
  have h : U*G=conj U := hardyUnit_mul_dualGamma (by linarith : t≠0)
  have hg := congrArg norm h
  rw [norm_mul,Complex.norm_conj,show ‖U‖=1 from norm_hardyGammaUnit t,one_mul] at hg
  have he : ‖U-E‖≤4/t := norm_hardyGammaUnit_sub_exp_le ht
  change ‖E*G-conj E‖≤_
  rw [show E*G-conj E=(E-U)*G+conj (U-E) by rw [map_sub,←h];ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,hg,mul_one,Complex.norm_conj,norm_sub_rev E U]
  calc _ ≤ 4/t+4/t := add_le_add he he
       _ = _ := by ring

/-- The two moving elementary polynomials and the rotated Mordell correction
approximate every Hurwitz shift with an absolute error of order `x^(-3/2)`,
where the height is `2πx²`. -/
theorem hurwitz_critical_rotated_first_correction : ∃ C : ℝ, 0<C ∧ ∀ {a x t : ℝ},
    a∈Ioc (0:ℝ) 1 → 2≤x → t=2*Real.pi*x^2 →
    let s := (1/2:ℂ)+(t:ℂ)*I
    let E := Complex.exp ((hardyPhase t:ℂ)*I)
    ‖E*HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-
      (E*hurwitzDirectSum a x s+conj E*hurwitzReciprocalPoly a ⌊x⌋₊ s)-
      E*hurwitzFirstCorrection a x s‖≤C*x^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_first_correction_balanced
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ))
  refine ⟨C+16+4*Real.Gamma (1/2),by positivity,?_⟩
  intro a x t ha hx ht s E
  have hx' : 0<x := by linarith
  have ht' : x^2≤t := by
    rw [ht]
    nlinarith [mul_le_mul_of_nonneg_right (show 1≤2*Real.pi by linarith [Real.pi_gt_three]) (sq_nonneg x)]
  have ht₀ : 0<t := by nlinarith
  have hσ : s.re=1/2 := by simp [s]
  have hi : s.im=t := by simp [s]
  have hc : ‖E‖=1 := Complex.norm_exp_ofReal_mul_I _
  let N := ⌊x⌋₊
  let B := hurwitzReciprocalPoly a N s
  let G := riemannDualGamma s
  let S := hurwitzDualSum a x s
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let A := hurwitzDirectSum a x s
  let F := hurwitzFirstCorrection a x s
  let P := x^(-(3/2:ℝ))
  have hmain : ‖Z-A-S-F‖≤C*P := H ha hx hσ (hi.trans ht)
  have hdiv : Real.sqrt N/t≤P := by
    calc Real.sqrt N/t ≤ Real.sqrt x/x^2 :=
              div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (Nat.floor_le hx'.le)) (by positivity) ht'
         _ = P := by
             dsimp only [P];rw [Real.sqrt_eq_rpow,←Real.rpow_natCast x 2,←Real.rpow_sub hx']
             norm_num
  have hExp : Real.exp (-(Real.pi/2)*t)≤2/(x^2)^2 := by
    rw [neg_mul,Real.exp_neg]
    have hh := Real.pow_div_factorial_le_exp (Real.pi/2*t) (by positivity) 2
    norm_num at hh
    have hpi : x^2≤Real.pi/2*t := ht'.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right (show 1≤Real.pi/2 by linarith [Real.pi_gt_three]) ht₀.le])
    apply (le_div_iff₀ (by positivity)).mpr
    rw [←div_eq_inv_mul]
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hh,pow_le_pow_left₀ (sq_nonneg x) hpi 2])
  have hneg (u : ℝ) : ‖hurwitzNegativeDual s u N‖≤2*Real.Gamma (1/2)*P := by
    apply (norm_hurwitzNegativeDual_critical hσ u N).trans
    rw [hi]
    calc _ ≤ (x*Real.Gamma (1/2))*(2/(x^2)^2) := mul_le_mul
              (mul_le_mul_of_nonneg_right (Nat.floor_le hx'.le) hΓ.le) hExp (Real.exp_pos _).le (by positivity)
         _ = 2*Real.Gamma (1/2)*x^(-(3:ℝ)) := by
              rw [Real.rpow_neg hx'.le,show x^(3:ℝ)=x^3 by norm_cast];field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤x) (by norm_num)) (by positivity)
  have hS : ‖S-G*B‖≤4*Real.Gamma (1/2)*P := by
    rw [show S-G*B=hurwitzNegativeDual s a N-hurwitzNegativeDual s (-a) N from hurwitzDualSum_sub_gamma ..]
    linarith only [norm_sub_le (hurwitzNegativeDual s a N) (hurwitzNegativeDual s (-a) N),hneg a,hneg (-a)]
  have hG : ‖(E*G-conj E)*B‖≤16*P := by
    rw [norm_mul]
    calc _ ≤ (8/t)*(2*Real.sqrt N) := mul_le_mul (hurwitz_rotated_gamma_error (by nlinarith : 2≤t))
              (norm_hurwitzReciprocalPoly_le_sqrt hσ a N) (norm_nonneg _) (by positivity)
         _ = 16*(Real.sqrt N/t) := by ring
         _ ≤ _ := by linarith only [hdiv]
  change ‖E*Z-(E*A+conj E*B)-E*F‖≤_
  rw [show E*Z-(E*A+conj E*B)-E*F=E*(Z-A-S-F)+(E*(S-G*B)+(E*G-conj E)*B) by ring]
  apply (norm_add_le ..).trans
  apply (add_le_add le_rfl (norm_add_le ..)).trans
  rw [norm_mul,norm_mul,hc,one_mul,one_mul]
  change ‖Z-A-S-F‖+(‖S-G*B‖+‖(E*G-conj E)*B‖)≤(C+16+4*Real.Gamma (1/2))*P
  linarith only [hmain,hS,hG]

end AnalyticNumberTheory.RiemannZeta
