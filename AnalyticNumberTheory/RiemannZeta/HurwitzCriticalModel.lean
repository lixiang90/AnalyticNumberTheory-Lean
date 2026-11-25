import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCosine
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleEndpoints

/-!
# The two elementary phases in the shifted critical-line approximation

At positive height the negative-frequency gamma terms decay exponentially.
The remaining reciprocal gamma factor rotates by the opposite Hardy phase.
The same numerical error bound works for all positive shifts up to one.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
namespace AnalyticNumberTheory.RiemannZeta

/-- The additive Fourier phase for a shifted Hurwitz polynomial at positive height. -/
def hurwitzReciprocalPoly (a : ℝ) (q : ℕ) (s : ℂ) :=
  ∑m∈range q,hurwitzShift a (hurwitzOmega m)*((m:ℂ)+1)^(s-1)

theorem hurwitzDualSum_sub_gamma (a x : ℝ) (s : ℂ) :
    hurwitzDualSum a x s-riemannDualGamma s*hurwitzReciprocalPoly a ⌊x⌋₊ s=
      hurwitzNegativeDual s a ⌊x⌋₊-hurwitzNegativeDual s (-a) ⌊x⌋₊ := by
  rw [hurwitzDualSum,hurwitzReciprocalPoly,hurwitzNegativeDual,hurwitzNegativeDual,mul_sum,←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl;intro m _
  have hp : hurwitzOmega m=((m:ℝ)+1)*(2*Real.pi) := by unfold hurwitzOmega;ring
  have hm : -hurwitzOmega m=((m:ℝ)+1)*(-2*Real.pi) := by rw [hp];ring
  have hs : hurwitzShift (-a) (-hurwitzOmega m)=hurwitzShift a (hurwitzOmega m) := by
    unfold hurwitzShift;congr 2;push_cast;ring
  simp only [hurwitzPair,hs,riemannDualGamma]
  have h₁ := hurwitzDualMode_scale s (2*Real.pi) (v:=(m:ℝ)+1) (by positivity)
  have h₂ := hurwitzDualMode_scale s (-2*Real.pi) (v:=(m:ℝ)+1) (by positivity)
  rw [←hp] at h₁
  rw [←hm] at h₂
  push_cast at h₁ h₂
  rw [h₁,h₂]
  ring

theorem norm_hurwitzReciprocalPoly_le {s : ℂ} (hs : s.re=1/2) (a : ℝ) (q : ℕ) :
    ‖hurwitzReciprocalPoly a q s‖≤q := by
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑_m∈range q,(1:ℝ) := by
            apply sum_le_sum;intro m _
            rw [norm_mul,norm_hurwitzShift,one_mul,←ofReal_natCast,←ofReal_one,←ofReal_add,
              Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),sub_re,Complex.ofReal_re,hs]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α:=ℝ) m]) (by norm_num)
       _ = _ := by simp

private theorem rotated_gamma_error {t : ℝ} (ht : 2≤t) :
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

/-- Rotation of the actual Hurwitz zeta function to a direct polynomial
and a single additive reciprocal polynomial. The error is absolute and
uniform in the shift. -/
theorem hurwitz_critical_rotated_error {a x t : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x)
    (ht : t=2*Real.pi*x^2) :
    let s := (1/2:ℂ)+(t:ℂ)*I
    let E := Complex.exp ((hardyPhase t:ℂ)*I)
    ‖E*HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-
      (E*hurwitzDirectSum a x s+conj E*hurwitzReciprocalPoly a ⌊x⌋₊ s)‖≤
      (612+2*Real.Gamma (1/2))*x^(-(1/2:ℝ)) := by
  intro s E
  have hx' : 0<x := by linarith
  have hsq : 1≤x^2 := by nlinarith
  have ht' : x^2≤t := by rw [ht];nlinarith [mul_le_mul_of_nonneg_right (show 1≤2*Real.pi by linarith [Real.pi_gt_three]) (sq_nonneg x)]
  have ht₀ : 0<t := by linarith
  have hσ : s.re=1/2 := by simp [s]
  have hi : s.im=t := by simp [s]
  have hc : ‖E‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0<(1/2:ℝ))
  have hq : (⌊x⌋₊:ℝ)≤x := Nat.floor_le hx'.le
  have ha₁ := hurwitzZeta_logFree_sharp_afe (s:=s) ha hx le_rfl (by rw [hσ];constructor <;>norm_num)
    (by rw [hi,abs_of_pos ht₀,ht];ring)
  rw [hσ] at ha₁
  let N := ⌊x⌋₊
  let B := hurwitzReciprocalPoly a N s
  let G := riemannDualGamma s
  let S := hurwitzDualSum a x s
  let P := x^(-(1/2:ℝ))
  have hdiv : (N:ℝ)/t≤P := by
    calc (N:ℝ)/t ≤ x/x^2 := div_le_div₀ hx'.le hq (by positivity) ht'
         _ = x^(-(1:ℝ)) := by rw [Real.rpow_neg hx'.le,Real.rpow_one];field_simp
         _ ≤ P := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hExp : Real.exp (-(Real.pi/2)*t)≤1/t := by
    rw [neg_mul,Real.exp_neg,one_div]
    apply inv_anti₀ ht₀
    have h := Real.add_one_le_exp (Real.pi/2*t)
    linarith [mul_le_mul_of_nonneg_right (show 1≤Real.pi/2 by linarith [Real.pi_gt_three]) ht₀.le]
  have hneg (u : ℝ) : ‖hurwitzNegativeDual s u N‖≤Real.Gamma (1/2)*P := by
    apply (norm_hurwitzNegativeDual_critical hσ u N).trans
    rw [hi]
    calc _ ≤ ((N:ℝ)*Real.Gamma (1/2))*(1/t) := mul_le_mul_of_nonneg_left hExp (by positivity)
         _ = Real.Gamma (1/2)*((N:ℝ)/t) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hΓ.le
  have hS : ‖S-G*B‖≤2*Real.Gamma (1/2)*P := by
    rw [show S-G*B=hurwitzNegativeDual s a N-hurwitzNegativeDual s (-a) N from hurwitzDualSum_sub_gamma ..]
    linarith only [norm_sub_le (hurwitzNegativeDual s a N) (hurwitzNegativeDual s (-a) N),hneg a,hneg (-a)]
  have hG : ‖(E*G-conj E)*B‖≤8*P := by
    rw [norm_mul]
    calc _ ≤ (8/t)*(N:ℝ) := mul_le_mul (rotated_gamma_error (by nlinarith : 2≤t)) (norm_hurwitzReciprocalPoly_le hσ a N) (norm_nonneg _) (by positivity)
         _ = 8*((N:ℝ)/t) := by ring
         _ ≤ _ := by linarith only [hdiv]
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let A := hurwitzDirectSum a x s
  change ‖Z-A-S‖≤604*P at ha₁
  change ‖E*Z-(E*A+conj E*B)‖≤_
  rw [show E*Z-(E*A+conj E*B)=E*(Z-A-S)+(E*(S-G*B)+(E*G-conj E)*B) by ring]
  apply (norm_add_le ..).trans
  apply (add_le_add le_rfl (norm_add_le ..)).trans
  rw [norm_mul,norm_mul,hc,one_mul,one_mul]
  change ‖Z-A-S‖+(‖S-G*B‖+‖(E*G-conj E)*B‖)≤(612+2*Real.Gamma (1/2))*P
  linarith only [ha₁,hS,hG]

end AnalyticNumberTheory.RiemannZeta
