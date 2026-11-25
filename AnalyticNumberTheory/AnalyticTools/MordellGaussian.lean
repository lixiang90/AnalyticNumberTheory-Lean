import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The oblique Gaussian in Mordell's contour integral

The slope-one contour crosses the imaginary axis at an arbitrary height.
Completing the square shows explicitly that this translation leaves the
Gaussian integral unchanged.
-/
noncomputable section
open Real Complex MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

/-- The diagonal of slope one through the point of imaginary part `d`. -/
def mordellLine (d t : ℝ) : ℂ := (1+I)*t+I*d

/-- Oscillatory Gaussian continued to the steepest descent line. -/
def mordellGaussian (c : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (I*w^2/(4*Real.pi)+(c:ℂ)*w)

/-- The translated Gaussian is integrable for every real center and height. -/
theorem integrable_mordellGaussian (c d : ℝ) : Integrable (fun t : ℝ => mordellGaussian c (mordellLine d t)) := by
  let b : ℂ := ((-1/(2*Real.pi):ℝ):ℂ)
  have hb : b.re<0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have H := integrable_cexp_quadratic' hb ((1+I)*(c-d/(2*Real.pi))) (-I*(d:ℂ)^2/(4*Real.pi)+I*c*d)
  apply H.congr
  filter_upwards with t
  unfold mordellGaussian mordellLine;congr 1
  dsimp [b];push_cast;field_simp;ring_nf;simp [I_sq,I_pow_three] <;> ring

/-- Integral of the completed Gaussian along the whole translated diagonal,
with its complex line element. -/
theorem integral_mordellGaussian (c d : ℝ) :
    (1+I)*(∫ t : ℝ, mordellGaussian c (mordellLine d t)) =
      2*Real.pi*Complex.exp (I*Real.pi/4+I*Real.pi*(c:ℂ)^2) := by
  let b : ℂ := -1/(2*Real.pi)
  let u : ℂ := (1+I)*(c-d/(2*Real.pi))
  let v : ℂ := -I*(d:ℂ)^2/(4*Real.pi)+I*c*d
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hb : b.re<0 := by
    rw [show b=((-1/(2*Real.pi):ℝ):ℂ) by dsimp [b];push_cast;rfl,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have H := integral_cexp_quadratic hb u v
  have hfun (t : ℝ) : mordellGaussian c (mordellLine d t)=Complex.exp (b*(t:ℂ)^2+u*t+v) := by
    unfold mordellGaussian mordellLine
    congr 1; dsimp [b,u,v];field_simp;ring_nf;simp [I_sq,I_pow_three] <;> ring
  have he : v-u^2/(4*b)=I*Real.pi*(c:ℂ)^2 := by
    dsimp [b,u,v];field_simp;ring_nf;simp [I_sq] <;> ring
  have hπ : (Real.pi:ℂ)/ -b=((Real.pi*Real.sqrt 2:ℝ):ℂ)^2 := by
    dsimp [b];push_cast;field_simp
    have hs : ((Real.sqrt 2:ℝ):ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : 0≤(2:ℝ))
    ring_nf;rw [hs]
  have hrt : ((Real.pi:ℂ)/ -b)^(1/2:ℂ)=(Real.pi*Real.sqrt 2:ℝ) := by
    rw [hπ,one_div]
    apply Complex.sq_cpow_two_inv
    simp;positivity
  have htrig : (1+I)*((Real.pi*Real.sqrt 2:ℝ):ℂ)=2*Real.pi*Complex.exp (I*Real.pi/4) := by
    rw [show I*(Real.pi:ℂ)/4=(((Real.pi/4:ℝ):ℂ))*I by push_cast;ring,Complex.exp_mul_I]
    rw [←Complex.ofReal_cos,←Complex.ofReal_sin,Real.cos_pi_div_four,Real.sin_pi_div_four]
    push_cast;ring
  simp_rw [hfun];rw [H,hrt,he,Complex.exp_add,←mul_assoc,htrig];ring

end AnalyticNumberTheory.AnalyticTools
