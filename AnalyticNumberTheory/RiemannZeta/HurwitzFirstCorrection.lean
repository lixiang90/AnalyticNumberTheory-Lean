import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleIntegral
import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleEndpoints
import AnalyticNumberTheory.RiemannZeta.HurwitzRadialHeads

/-!
# The first corrected Hurwitz Riemann–Siegel formula

At positive height t=2πx² on the critical line, subtracting the two sharp
polynomials and the explicit Mordell coefficient leaves O(x^(-3/2)).
The constant is uniform in the shift 0<a≤1.
-/
noncomputable section
open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.RiemannZeta

/-- Displacement of the saddle from the last shifted lattice point. -/
def hurwitzSaddleFraction (a x : ℝ) := x-a-⌊x-a⌋₊

/-- First correction to the two-polynomial formula at the balanced cutoff.
The real coefficient is evaluated continuously at half-integral arguments. -/
def hurwitzFirstCorrection (a x : ℝ) (s : ℂ) : ℂ :=
  let l := hurwitzSaddleFraction a x
  let q := ⌊x⌋₊
  (x:ℂ)^(-s)*Complex.exp (((Real.pi*(2*x*l+l^2-(x+l-q)^2/2-7/8):ℝ):ℂ)*I)*
    (riemannSiegelCorrection (x+l-q):ℂ)

private theorem inverse_sqrt_bound {x r : ℝ} (hx : 0<x) (hr : x/4≤r) :
    r^(-(1/2:ℝ))≤2*x^(-(1/2:ℝ)) := by
  apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0<x/4) hr (by norm_num : -(1/2:ℝ)≤0)).trans_eq
  rw [Real.div_rpow hx.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤4),←Real.sqrt_eq_rpow];norm_num;ring

private theorem exp_tail_scale {x : ℝ} (hx : 1≤x) :
    x^2*Real.exp (-x^2/4)≤32*x^(-(3/2:ℝ)) := by
  have hx' : 0<x := by linarith
  have he := Real.pow_div_factorial_le_exp (x^2/4) (by positivity) 2
  norm_num at he
  rw [show -x^2/4= -(x^2/4) by ring,Real.exp_neg,←div_eq_mul_inv]
  calc _ ≤ 32/x^2 := by
         apply (div_le_div_iff₀ (Real.exp_pos _) (sq_pos_of_pos hx')).mpr;nlinarith
       _ = 32*x^(-2:ℝ) := by rw [Real.rpow_neg hx'.le,←Real.rpow_natCast x 2];norm_num;ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (by norm_num)

/-- First Riemann–Siegel correction for a Hurwitz shift, uniform for
0<a≤1. The error in the textbook height variable is O(t^(-3/4)). -/
theorem hurwitzZeta_first_correction : ∃ C : ℝ,0<C ∧ ∀ {a x : ℝ} {s : ℂ},
    a∈Ioc (0:ℝ) 1 → 1024≤x → s.re=1/2 → s.im=2*Real.pi*x^2 →
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a x s-
      hurwitzFirstCorrection a x s‖≤C*x^(-(3/2:ℝ)) := by
  obtain ⟨A,hA,hmain⟩ := hurwitz_saddle_integral_first_correction
  obtain ⟨B,hB,hneg⟩ := norm_hurwitzGeometricTail_negative
  obtain ⟨D,hD,hlow⟩ := norm_hurwitzLowerGeometric_zero
  let Γ := Real.Gamma (1/2)
  have hΓ : 0<Γ := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨A+2+2*B+2*D+128+32*Γ,by positivity,?_⟩
  intro a x s ha hx hσ ht
  let q := ⌊x⌋₊
  let m := ⌊x-a⌋₊
  let l := hurwitzSaddleFraction a x
  let b := a+m+1/2
  have hx' : 0<x := by linarith
  have hxa : 0≤x-a := by linarith [ha.2]
  have hl : l∈Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (Nat.floor_le hxa),(by dsimp [l,hurwitzSaddleFraction];linarith [Nat.lt_floor_add_one (x-a)])⟩
  have hb : b=x-l+1/2 := by dsimp [b,l,m,hurwitzSaddleFraction];ring
  have hb' : 1≤b := by linarith [hl.2]
  have hq : x-1≤q := by dsimp [q];linarith [Nat.lt_floor_add_one x]
  have hq' : (q:ℝ)≤x := Nat.floor_le hx'.le
  have ht' : 0<s.im := by rw [ht];positivity
  have hsig : 0≤s.re := by linarith
  have hT : b/s.im≤1/x := by
    apply (div_le_div_iff₀ ht' hx').mpr
    nlinarith [mul_le_mul_of_nonneg_right (show b≤2*x by linarith [hl.1]) hx'.le,
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg x)]
  let P := x^(-(1/2:ℝ))
  let M := x^(-(3/2:ℝ))
  have hP : 0≤P := Real.rpow_nonneg hx'.le _
  have hM : 0≤M := Real.rpow_nonneg hx'.le _
  have hPM : P*(1/x)=M := by dsimp [P,M];rw [←div_eq_mul_one_div,←Real.rpow_sub_one hx'.ne'];norm_num
  have hM' {r : ℝ} (hr : x/4≤r) : r^(-s.re)*b/s.im≤2*M := by
    rw [hσ,mul_div_assoc]
    exact (mul_le_mul (inverse_sqrt_bound hx' hr) hT (div_nonneg (by linarith) ht'.le) (by positivity)).trans_eq (by rw [mul_assoc,hPM])
  have hzero : ‖(b:ℂ)^(1-s)/(1-s)‖≤2*M := by
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),sub_re,one_re,
      show 1-s.re= -s.re+1 by ring,Real.rpow_add_one (by linarith : b≠0)]
    have him := Complex.abs_im_le_norm (1-s)
    rw [sub_im,one_im,zero_sub,abs_neg,abs_of_pos ht'] at him
    exact (div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)) ht' him).trans (hM' (by linarith [hl.2]))
  have hGN : ‖hurwitzGeometricTail s b (-1) 0‖≤B*(2*M) :=
    (hneg hsig ht' hb').trans (by rw [show B*b^(-s.re)*b/s.im=B*(b^(-s.re)*b/s.im) by ring];exact mul_le_mul_of_nonneg_left (hM' (by linarith [hl.2])) hB.le)
  have hGD : ‖hurwitzLowerGeometric s b 0‖≤D*(2*M) :=
    (hlow hsig ht' (by linarith)).trans (by rw [show D*(b/2)^(-s.re)*b/s.im=D*((b/2)^(-s.re)*b/s.im) by ring];exact mul_le_mul_of_nonneg_left (hM' (by linarith [hl.2])) hD.le)
  have hX := exp_tail_scale (by linarith : 1≤x)
  have hRad : ‖hurwitzRadialHeads s a b q‖≤128*M :=
    (norm_hurwitzRadialHeads_balanced (by linarith) (by linarith [hl.1]) (by linarith) hσ ht a hq').trans (by dsimp only [M];nlinarith)
  have hNd : ‖hurwitzNegativeDual s a q‖≤32*Γ*M := by
    apply (norm_hurwitzNegativeDual_critical hσ a q).trans
    have hE : Real.exp (-(Real.pi/2)*s.im)≤Real.exp (-x^2/4) := by
      rw [ht];apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (show 1≤Real.pi^2 by nlinarith [Real.pi_gt_three]) (sq_nonneg x)]
    have hq2 : (q:ℝ)≤x^2 := by nlinarith
    calc _ ≤ (x^2*Γ)*Real.exp (-x^2/4) := mul_le_mul (mul_le_mul_of_nonneg_right hq2 hΓ.le) hE (Real.exp_nonneg _) (by positivity)
         _ ≤ _ := by change x^2*Γ*_≤_;dsimp only [M];nlinarith [mul_le_mul_of_nonneg_left hX hΓ.le]
  have hdir : hurwitzDirectSum a x s=hurwitzDirectSum a b s := by
    have hf : ⌊b-a⌋₊=m := Nat.floor_eq_iff (by linarith [ha.2] : 0≤b-a) |>.mpr ⟨by dsimp [b];linarith,by dsimp [b];linarith⟩
    simp only [hurwitzDirectSum,hf];rfl
  have hdual : hurwitzDualSum a x s=hurwitzDualSum a q s := by simp [hurwitzDualSum,q]
  have H := hurwitzZeta_saddle_decomposition (by linarith : 0<s.re) (by linarith : s.re<1) ha m q (show b=a+m+1/2 by rfl)
  have hm : ‖hurwitzGeometricTail s b 1 q+hurwitzLowerGeometric s b q-hurwitzFirstCorrection a x s‖≤A*M :=
    hmain hx hl hb hq hq' hσ ht
  let U := hurwitzGeometricTail s b 1 q+hurwitzLowerGeometric s b q-hurwitzFirstCorrection a x s
  have he : HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a x s-hurwitzFirstCorrection a x s=
      U-(b:ℂ)^(1-s)/(1-s)+hurwitzGeometricTail s b (-1) 0-hurwitzLowerGeometric s b 0-hurwitzRadialHeads s a b q-hurwitzNegativeDual s a q := by
    rw [hdir,hdual,H];dsimp only [U];ring
  rw [he]
  have h₁ := (norm_sub_le U ((b:ℂ)^(1-s)/(1-s))).trans (add_le_add hm hzero)
  have h₂ := (norm_add_le _ (hurwitzGeometricTail s b (-1) 0)).trans (add_le_add h₁ hGN)
  have h₃ := (norm_sub_le _ (hurwitzLowerGeometric s b 0)).trans (add_le_add h₂ hGD)
  have h₄ := (norm_sub_le _ (hurwitzRadialHeads s a b q)).trans (add_le_add h₃ hRad)
  exact (norm_sub_le _ _).trans ((add_le_add h₄ hNd).trans_eq (by dsimp only [M];ring))

end AnalyticNumberTheory.RiemannZeta
