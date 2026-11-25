import AnalyticNumberTheory.RiemannZeta.HurwitzRotatedTails
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Decay of the phase along the Hurwitz saddle contour

The derivative of the argument of b+(1+i)v is b/((b+v)²+v²).
On the central segment this forces a Gaussian majorant. Outside it,
monotonicity of the derivative gives straight-line exponential tails.
-/

open Real Complex Set Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

/-- Real logarithmic size of the exponential on the upper Hurwitz saddle contour. -/
noncomputable def hurwitzSaddleHeight (x b q v : ℝ) : ℝ :=
  2*π*x^2*(hurwitzRay b 1 v).arg-2*π*q*v

private def den (b v : ℝ) := (b+v)^2+v^2
private noncomputable def slope (x b q v : ℝ) := 2*π*x^2*b/den b v-2*π*q

private theorem den_pos {b v : ℝ} (h : 0<b+v) : 0<den b v := add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg _)

private theorem hasDerivAt_height (x b q v : ℝ) (hb : 0<b+v) :
    HasDerivAt (hurwitzSaddleHeight x b q) (slope x b q v) v := by
  have hg := (((hasDerivAt_id v).div ((hasDerivAt_id v).const_add b) hb.ne').arctan.const_mul (2*π*x^2)).sub
    ((hasDerivAt_id v).const_mul (2*π*q))
  have hh : HasDerivAt (fun z : ℝ => 2*π*x^2*Real.arctan (z/(b+z))-2*π*q*z) (slope x b q v) v := by
    convert hg using 1
    · rfl
    · dsimp [slope,den]
      have hden : 0<(b+v)^2+v^2 := den_pos hb
      field_simp [hb.ne',hden.ne'] <;> ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [(lt_mem_nhds (show -b<v by linarith))] with z hz
  have hz' : 0<(hurwitzRay b 1 z).re := by rw [hurwitzRay_re];linarith
  unfold hurwitzSaddleHeight
  rw [←Real.arctan_tan (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz'))
      (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz')),Complex.tan_arg]
  simp [hurwitzRay_re,hurwitzRay_im]

private theorem height_zero (x q : ℝ) {b : ℝ} (hb : 0<b) : hurwitzSaddleHeight x b q 0=0 := by
  simp [hurwitzSaddleHeight,hurwitzRay,Complex.arg_ofReal_of_nonneg hb.le]

private theorem slope_zero_bound {x b q : ℝ} (hx : 1024≤x) (hb : |b-x|≤1/2)
    (hq : x-1≤q) (hq' : q≤x) : |slope x b q 0|≤16 := by
  obtain ⟨hbl,hbr⟩ := abs_le.mp hb
  have bpos : 0<b := by linarith
  have xpos : 0<x := by linarith
  have hbnd : |x^2/b-q|≤2 := by
    apply abs_le.mpr
    constructor
    · have H := mul_le_mul_of_nonneg_right hbr xpos.le
      have H' := mul_le_mul_of_nonneg_right hq' bpos.le
      rw [le_sub_iff_add_le,le_div_iff₀ bpos]; nlinarith
    · have H := mul_le_mul_of_nonneg_right hbl xpos.le
      have H' := mul_le_mul_of_nonneg_right hq bpos.le
      rw [sub_le_iff_le_add,div_le_iff₀ bpos]; nlinarith
  have he : slope x b q 0=2*π*(x^2/b-q) := by dsimp [slope,den];simp only [add_zero,zero_pow (by decide : 2≠0)];field_simp <;> ring
  rw [he,abs_mul,abs_of_pos (by positivity : 0<2*π)]
  nlinarith [mul_le_mul_of_nonneg_left hbnd (show 0≤2*π by positivity),Real.pi_lt_four]

private noncomputable def curvature (x b v : ℝ) := 4*π*x^2*(b+v)/(b*den b v)

private theorem slope_eq {x b q v : ℝ} (hb : 0<b) (hv : 0<b+v) :
    slope x b q v=slope x b q 0-curvature x b v*v := by
  have hd := den_pos hv
  dsimp only [slope,curvature]
  simp only [den,add_zero,zero_pow (by decide : 2≠0)] at hd ⊢
  field_simp [hb.ne',hd.ne']; ring

private theorem curvature_central {x b v : ℝ} (hx : 1024≤x) (hb : |b-x|≤1/2) (hv : |v|≤b/4) :
    1/4≤curvature x b v := by
  obtain ⟨hbl,hbr⟩ := abs_le.mp hb
  obtain ⟨hl,hr⟩ := abs_le.mp hv
  have bpos : 0<b := by linarith
  have bv : 0<b+v := by linarith
  have hden : den b v≤2*b^2 := by
    have h1 := abs_le.mp (show |b+v|≤5*b/4 by rw [abs_of_pos bv];linarith)
    have h2 : (b+v)^2≤(5*b/4)^2 := by apply sq_le_sq₀ bv.le (by positivity) |>.mpr;linarith
    have h3 := (sq_le_sq₀ (abs_nonneg v) (by positivity : 0≤b/4)).mpr hv
    rw [sq_abs] at h3;unfold den;nlinarith only [h2,h3]
  have h1 : 8*(b/2)^2*(b/2)≤4*π*x^2*(b+v) := by
    gcongr
    · linarith [Real.pi_gt_three]
    · linarith
    · linarith
  unfold curvature
  rw [le_div_iff₀ (mul_pos bpos (den_pos bv))]
  nlinarith only [mul_le_mul_of_nonneg_left hden bpos.le,h1,
    mul_nonneg (sq_nonneg b) bpos.le]

private theorem slope_antitone_right {x b q u v : ℝ} (hb : 0<b) (hu : -b/2≤u) (huv : u≤v) :
    slope x b q v≤slope x b q u := by
  have HD : den b u≤den b v := by dsimp [den];nlinarith [mul_nonneg (sub_nonneg.mpr huv) (show 0≤b+u+v by linarith)]
  unfold slope; apply sub_le_sub_right
  exact div_le_div_of_nonneg_left (by positivity) (den_pos (by linarith)) HD

private theorem mean_increment {a b : ℝ} (hab : a≤b) {f g : ℝ→ℝ} (hf : ∀ t∈Icc a b,HasDerivAt f (g t) t) :
    ∃t∈Icc a b, f b-f a=g t*(b-a) := by
  rcases hab.eq_or_lt with rfl|hlt
  · exact ⟨a,by simp,by ring⟩
  obtain ⟨t,ht,H⟩ := exists_hasDerivAt_eq_slope f g hlt (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t ⟨ht.1.le,ht.2.le⟩)
  exact ⟨t,⟨ht.1.le,ht.2.le⟩,((eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp H).symm⟩

/-- On the central segment the real phase has Gaussian decay uniformly in both cutoff offsets. -/
theorem hurwitzSaddleHeight_central {x b q v : ℝ} (hx : 1024≤x) (hb : |b-x|≤1/2)
    (hq : x-1≤q) (hq' : q≤x) (hv : |v|≤b/4) :
    hurwitzSaddleHeight x b q v≤1024-v^2/16 := by
  obtain ⟨hbl,hbr⟩ := abs_le.mp hb
  obtain ⟨hl,hr⟩ := abs_le.mp hv
  have bp : 0<b := by linarith
  let A := slope x b q 0
  let f (z : ℝ) := hurwitzSaddleHeight x b q z-A*z+z^2/8
  let g (z : ℝ) := slope x b q z-A+z/4
  have hder z (hz : |z|≤b/4) : HasDerivAt f (g z) z := by
    have hz' := (abs_le.mp hz).1
    change HasDerivAt ((hurwitzSaddleHeight x b q-(fun y : ℝ => A*y))+(fun y : ℝ => y^2/8)) (g z) z
    convert ((hasDerivAt_height x b q z (by linarith)).sub ((hasDerivAt_id z).const_mul A)).add ((hasDerivAt_pow 2 z).div_const 8) using 1 <;> dsimp [f,g] <;> ring
  have hg z (hz : |z|≤b/4) : g z=(1/4-curvature x b z)*z := by
    have h := (abs_le.mp hz).1
    dsimp [g,A];rw [slope_eq bp (show 0<b+z by linarith)];ring
  have hf : f v≤f 0 := by
    rcases le_total 0 v with hp|hp
    · obtain ⟨t,ht,H⟩ := mean_increment hp (fun t (ht : t∈Icc 0 v) => hder t (by rw [abs_of_nonneg ht.1];linarith [ht.2]))
      have ht' : |t|≤b/4 := by rw [abs_of_nonneg ht.1];linarith [ht.2]
      rw [hg t ht',sub_zero] at H
      linarith only [H,mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (curvature_central hx hb ht')) ht.1) hp]
    · obtain ⟨t,ht,H⟩ := mean_increment hp (fun t (ht : t∈Icc v 0) => hder t (by rw [abs_of_nonpos ht.2];linarith [ht.1]))
      have ht' : |t|≤b/4 := by rw [abs_of_nonpos ht.2];linarith [ht.1]
      rw [hg t ht'] at H
      linarith only [H,mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (curvature_central hx hb ht')) ht.2) (sub_nonneg.mpr hp)]
  have H := abs_le.mp (slope_zero_bound hx hb hq hq')
  have hav : A*v≤16*|v| := (le_abs_self _).trans (by rw [abs_mul];gcongr; exact slope_zero_bound hx hb hq hq')
  dsimp [f] at hf;rw [height_zero x q bp] at hf
  nlinarith only [hf,hav,sq_nonneg (|v|-128),sq_abs v]

/-- Beyond the central segment the height is bounded by its endpoint majorant minus
a linear distance penalty, on the full right half of the contour. -/
theorem hurwitzSaddleHeight_outer {x b q v : ℝ} (hx : 1024≤x) (hb : |b-x|≤1/2)
    (hq : x-1≤q) (hq' : q≤x) (hl : -b/2≤v) (hv : b/4≤|v|) :
    hurwitzSaddleHeight x b q v≤1024-b^2/256-(b/32)*(|v|-b/4) := by
  obtain ⟨hbl,hbr⟩ := abs_le.mp hb
  have bp : 0<b := by linarith
  have H := abs_le.mp (slope_zero_bound hx hb hq hq')
  rcases le_total 0 v with hs|hs
  · rw [abs_of_nonneg hs] at hv ⊢
    have h₁ : |b/4|≤b/4 := by rw [abs_of_nonneg (by positivity)]
    have hc := hurwitzSaddleHeight_central (q:=q) hx hb hq hq' h₁
    have hd := slope_eq (x:=x) (q:=q) bp (show 0<b+b/4 by linarith)
    have hd' : slope x b q (b/4)≤ -(b/32) := by nlinarith only [hd,H.2,hbl,hx,mul_le_mul_of_nonneg_right (curvature_central hx hb h₁) (show 0≤b/4 by positivity)]
    obtain ⟨t,ht,he⟩ := mean_increment hv (fun t (ht : t∈Icc (b/4) v) => hasDerivAt_height x b q t (by linarith [ht.1]))
    have hh := (slope_antitone_right (x:=x) (q:=q) bp (by linarith : -b/2≤b/4) ht.1).trans hd'
    nlinarith only [he,hc,mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hv)]
  · rw [abs_of_nonpos hs] at hv ⊢
    have h₁ : |-(b/4)|≤b/4 := by rw [abs_neg,abs_of_nonneg (by positivity)]
    have hc := hurwitzSaddleHeight_central (q:=q) hx hb hq hq' h₁
    have hd := slope_eq (x:=x) (q:=q) bp (show 0<b+ -(b/4) by linarith)
    have hd' : b/32≤slope x b q (-(b/4)) := by nlinarith only [hd,H.1,hbl,hx,mul_le_mul_of_nonneg_right (curvature_central hx hb h₁) (show 0≤b/4 by positivity)]
    have hv' : v≤ -(b/4) := by linarith
    obtain ⟨t,ht,he⟩ := mean_increment hv' (fun t (ht : t∈Icc v (-(b/4))) => hasDerivAt_height x b q t (by linarith [ht.1]))
    have hh := hd'.trans (slope_antitone_right (x:=x) (q:=q) bp (by linarith [ht.1] : -b/2≤t) ht.2)
    nlinarith only [he,hc,mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hv')]

end AnalyticNumberTheory.RiemannZeta
