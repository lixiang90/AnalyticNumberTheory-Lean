import AnalyticNumberTheory.RiemannZeta.HurwitzSaddleGaussian
import AnalyticNumberTheory.RiemannZeta.HurwitzGeometricTails

/-!
# The exact saddle kernel on the half-lattice diagonal

Rewriting the geometric denominator in the Mordell variable aligns the
exact integrand and its quadratic approximation on the whole diagonal.
-/
noncomputable section
open Real Complex MeasureTheory Set
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

theorem saddleVariable_coordinates (v : ℝ) :
    hurwitzSaddleVariable v=⟨2*Real.pi*v,-(2*Real.pi*v+Real.pi)⟩ := by
  apply Complex.ext <;> simp [hurwitzSaddleVariable,mordellLine,mul_re,mul_im] <;> ring

theorem exp_neg_saddleVariable (v : ℝ) :
    Complex.exp (-hurwitzSaddleVariable v)=hurwitzRayRatio 1 v := by
  have he : -hurwitzSaddleVariable v=Real.pi*I+((2*Real.pi*v:ℝ):ℂ)*(-1+(1:ℂ)*I) := by
    rw [saddleVariable_coordinates];apply Complex.ext <;> simp [mul_re,mul_im] <;> ring
  rw [he,Complex.exp_add,Complex.exp_pi_mul_I,hurwitzRayRatio]
  push_cast;ring

theorem rayRatio_neg (v : ℝ) : hurwitzRayRatio 1 (-v)=(hurwitzRayRatio 1 v)⁻¹ := by
  unfold hurwitzRayRatio
  push_cast
  rw [show 2*(Real.pi:ℂ)*(-(v:ℂ))*(-1+1*I)= -(2*Real.pi*v*(-1+1*I)) by ring,Complex.exp_neg,inv_neg]

/-- The geometric denominator is uniformly regular on the entire diagonal. -/
theorem saddleVariable_inv_bound : ∃ C : ℝ, 0<C ∧ ∀ v : ℝ, ‖(Complex.exp (hurwitzSaddleVariable v)-1)⁻¹‖≤C := by
  obtain ⟨C,hC,h⟩ := hurwitzRayRatio_inv_bound 1
  refine ⟨C,hC,?_⟩
  intro v
  let r := hurwitzRayRatio 1 v
  have h0 : r≠0 := by dsimp only [r];rw [←exp_neg_saddleVariable];exact Complex.exp_ne_zero _
  have h1 : r≠1 := hurwitzRayRatio_ne_one 1 v
  have he : Complex.exp (hurwitzSaddleVariable v)=r⁻¹ := by dsimp only [r];rw [←exp_neg_saddleVariable,Complex.exp_neg,inv_inv]
  rw [he]
  rcases le_or_gt 0 v with hv|hv
  · have hd : (r⁻¹-1)⁻¹=r*(1-r)⁻¹ := by field_simp
    rw [hd,norm_mul];apply (mul_le_of_le_one_left (norm_nonneg _) _).trans (h v hv)
    rw [norm_hurwitzRayRatio,Real.exp_le_one_iff];nlinarith [mul_nonneg Real.pi_pos.le hv]
  · have H := h (-v) (by linarith)
    rw [rayRatio_neg,norm_inv,norm_sub_rev,←norm_inv] at H
    exact H

/-- Exact integrand of the saddle contribution after summing the Fourier modes. -/
def hurwitzSaddleKernel (s : ℂ) (b q v : ℝ) : ℂ :=
  (hurwitzRay b 1 v)^(-s)*Complex.exp (-(q:ℂ)*hurwitzSaddleVariable v)/(Complex.exp (hurwitzSaddleVariable v)-1)

theorem hurwitzSaddleKernel_eq_geometric (s : ℂ) (b : ℝ) (q : ℕ) (v : ℝ) :
    hurwitzSaddleKernel s b q v=
      (hurwitzRay b 1 v)^(-s)*(hurwitzRayRatio 1 v)^(q+1)/(1-hurwitzRayRatio 1 v) := by
  let r := hurwitzRayRatio 1 v
  have h0 : r≠0 := by dsimp only [r];rw [←exp_neg_saddleVariable];exact Complex.exp_ne_zero _
  have h1 : r≠1 := hurwitzRayRatio_ne_one 1 v
  have he : Complex.exp (hurwitzSaddleVariable v)=r⁻¹ := by dsimp only [r];rw [←exp_neg_saddleVariable,Complex.exp_neg,inv_inv]
  have hq : Complex.exp (-(q:ℂ)*hurwitzSaddleVariable v)=r^q := by
    rw [show -(q:ℂ)*hurwitzSaddleVariable v=q*(-hurwitzSaddleVariable v) by ring,Complex.exp_nat_mul,exp_neg_saddleVariable]
  unfold hurwitzSaddleKernel;push_cast;rw [he,hq]
  change _=(hurwitzRay b 1 v)^(-s)*r^(q+1)/(1-r)
  rw [pow_succ];field_simp

/-- The common multiplier in the saddle comparison has an exact real
exponential modulus, apart from the uniformly bounded denominator. -/
theorem norm_saddle_carrier (q v : ℝ) :
    ‖Complex.exp (-(q:ℂ)*hurwitzSaddleVariable v)‖=Real.exp (-2*Real.pi*q*v) := by
  rw [Complex.norm_exp,saddleVariable_coordinates];congr 1;simp [mul_re];ring

end AnalyticNumberTheory.RiemannZeta
