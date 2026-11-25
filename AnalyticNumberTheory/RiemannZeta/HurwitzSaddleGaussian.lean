import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCorrection
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The quadratic saddle contribution in the Hurwitz equation

The quadratic approximation to the complex power on the balanced diagonal
is a conjugate Mordell integral. Its evaluation fixes both the phase and the
normalization of the first correction.
-/
noncomputable section
open Real Complex MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- Local coordinate about the saddle. Here l is the fractional part of x−a. -/
def hurwitzSaddleOffset (l v : ℝ) : ℂ := (1/2-(l:ℂ))+(1+I)*v

/-- Angular variable for summing consecutive frequencies at the saddle. -/
def hurwitzSaddleVariable (v : ℝ) : ℂ := conj (mordellLine Real.pi (2*Real.pi*v))

/-- The whole-line quadratic model after the common Dirichlet power has
been taken out. The variable q is the frequency cutoff. -/
def hurwitzSaddleModel (x l q v : ℝ) : ℂ :=
  Complex.exp (-2*Real.pi*I*x*hurwitzSaddleOffset l v+Real.pi*I*(hurwitzSaddleOffset l v)^2)*
    Complex.exp (-(q:ℂ)*hurwitzSaddleVariable v)/(Complex.exp (hurwitzSaddleVariable v)-1)

theorem saddleOffset_in_variable (l v : ℝ) :
    hurwitzSaddleOffset l v= -(l:ℂ)+I*hurwitzSaddleVariable v/(2*Real.pi) := by
  simp [hurwitzSaddleOffset,hurwitzSaddleVariable,mordellLine,map_add,map_mul,Complex.conj_I]
  field_simp;ring_nf;simp [I_sq, map_ofNat] <;> ring

private theorem saddleModel_factor (x l q v : ℝ) :
    hurwitzSaddleModel x l q v =
      Complex.exp (((Real.pi*(2*x*l+l^2):ℝ):ℂ)*I)*
      conj (mordellKernel (x+l-q) (mordellLine Real.pi (2*Real.pi*v))) := by
  let w := hurwitzSaddleVariable v
  rw [hurwitzSaddleModel,saddleOffset_in_variable]
  unfold mordellKernel mordellGaussian
  simp only [map_div₀,map_sub,map_one,←Complex.exp_conj,map_add,map_mul,map_pow,map_ofNat,map_neg,Complex.conj_I,Complex.conj_ofReal]
  change _ = _*(Complex.exp (-I*w^2/(4*Real.pi)+((x+l-q:ℝ):ℂ)*w)/(Complex.exp w-1))
  rw [←mul_div_assoc,←Complex.exp_add,←Complex.exp_add];congr 2
  dsimp only [w];generalize hurwitzSaddleVariable v=z
  push_cast;field_simp;ring_nf;simp [I_sq,I_pow_three] <;> ring

/-- The quadratic model is integrable on the entire steepest descent line. -/
theorem integrable_hurwitzSaddleModel (x l q : ℝ) : Integrable (hurwitzSaddleModel x l q) := by
  change Integrable (fun v : ℝ => hurwitzSaddleModel x l q v)
  simp_rw [saddleModel_factor]
  apply Integrable.const_mul
  have hv := integrable_mordellKernel_upper (x+l-q)
  have h : Integrable (fun v : ℝ => conj (mordellKernel (x+l-q) (mordellLine Real.pi v))) :=
    hv.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable) (Filter.Eventually.of_forall fun v => by simp)
  exact h.comp_mul_left' (by positivity : (2*Real.pi)≠0)

/-- Exact evaluation of the complete quadratic contribution. -/
theorem integral_hurwitzSaddleModel (x l q : ℝ) :
    (1+I)*(∫ v : ℝ,hurwitzSaddleModel x l q v) =
      Complex.exp (((Real.pi*(2*x*l+l^2-(x+l-q)^2/2-7/8):ℝ):ℂ)*I)*
        (riemannSiegelCorrection (x+l-q):ℂ) := by
  let c := x+l-q
  let A := Complex.exp (((Real.pi*(2*x*l+l^2):ℝ):ℂ)*I)
  simp_rw [saddleModel_factor]
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun u : ℝ => conj (mordellKernel c (mordellLine Real.pi u))) (2*Real.pi),
    Complex.real_smul,abs_of_pos (by positivity),integral_conj]
  have hm := congrArg (fun z : ℂ => conj z) (mordellIntegral_eq_riemannSiegelCorrection c)
  simp only [mordellIntegral,map_mul,map_add,map_one,Complex.conj_I,Complex.conj_ofReal,map_ofNat,←Complex.exp_conj] at hm
  have hp : (1+I) = I*(1+ -I) := by ring_nf;simp [I_sq,add_comm]
  have hh : I*A*Complex.exp ((((Real.pi*(c^2/2-5/8):ℝ):ℂ))*(-I)) =
      Complex.exp (((Real.pi*(2*x*l+l^2-c^2/2-7/8):ℝ):ℂ)*I) := by
    unfold A
    nth_rw 1 [←Complex.exp_pi_div_two_mul_I]
    rw [←Complex.exp_add,←Complex.exp_add]
    have he : (Real.pi:ℂ)/2*I+((Real.pi*(2*x*l+l^2):ℝ):ℂ)*I+
        ((Real.pi*(c^2/2-5/8):ℝ):ℂ)*(-I)=((Real.pi*(2*x*l+l^2-c^2/2-7/8):ℝ):ℂ)*I+2*Real.pi*I := by push_cast;ring
    rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  change (1+I)*(A*(_*conj (∫ u : ℝ,mordellKernel c (mordellLine Real.pi u)))) = _
  rw [hp]
  calc
    _ = I*A*((((2*Real.pi:ℝ)⁻¹:ℝ):ℂ)*((1+ -I)*conj (∫ u : ℝ,mordellKernel c (mordellLine Real.pi u)))) := by push_cast;ring
    _ = _ := by rw [hm,←hh];push_cast;field_simp;ring

end AnalyticNumberTheory.RiemannZeta
