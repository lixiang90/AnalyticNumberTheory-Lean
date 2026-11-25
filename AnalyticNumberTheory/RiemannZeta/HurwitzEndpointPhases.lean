import AnalyticNumberTheory.RiemannZeta.HurwitzStationaryWindow
import AnalyticNumberTheory.RiemannZeta.HurwitzFrequencyWindow
import AnalyticNumberTheory.ExponentialSums.ShiftedSineHarmonics

/-!
# Discrete phases of the sharp Hurwitz endpoint terms
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

/-- The phase at the endpoint is a geometric progression in the integral frequency. -/
def hurwitzEndpointPhase (b : ℝ) := Complex.exp ((2*Real.pi*b:ℝ)*I)

@[simp] theorem norm_hurwitzEndpointPhase (b : ℝ) : ‖hurwitzEndpointPhase b‖=1 := by
  rw [hurwitzEndpointPhase,Complex.norm_exp];simp

theorem hurwitzPhase_pow (b : ℝ) (n : ℕ) :
    Complex.exp ((2*Real.pi*n*b:ℝ)*I)=(hurwitzEndpointPhase b)^n := by
  rw [hurwitzEndpointPhase,←Complex.exp_nat_mul];congr 1;push_cast;ring

theorem hurwitzPhase_neg_pow (b : ℝ) (n : ℕ) :
    Complex.exp ((-(2*Real.pi*n)*b:ℝ)*I)=(conj (hurwitzEndpointPhase b))^n := by
  rw [←map_pow,←hurwitzPhase_pow,←Complex.exp_conj];congr 1;push_cast;simp [Complex.conj_ofNat] <;>ring

theorem hurwitzPhase_sub (b : ℝ) {Y j : ℕ} (hj : j≤Y) :
    (hurwitzEndpointPhase b)^(Y-j)=(hurwitzEndpointPhase b)^Y*(conj (hurwitzEndpointPhase b))^j := by
  let z := hurwitzEndpointPhase b
  have h : z*conj z=1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq];simp [z]
  change z^(Y-j)=z^Y*(conj z)^j
  conv_rhs => rw [←Nat.sub_add_cancel hj,pow_add]
  rw [mul_assoc,←mul_pow,h,one_pow,mul_one]

/-- After removing the coefficient shift the retained endpoint is a
geometric phase divided by the signed distance from the reciprocal cutoff. -/
theorem hurwitzShift_mul_endpoint {s : ℂ} {a x y : ℝ} (hx : 0<x) (hxy : s.im=2*Real.pi*x*y) (n : ℕ) :
    hurwitzShift a (2*Real.pi*n)*hurwitzEndpoint s (2*Real.pi*n) x =
      -(I/(2*Real.pi)*(x:ℂ)^(-s))*(hurwitzEndpointPhase (x-a))^n/((n:ℂ)-y) := by
  rw [hurwitzEndpoint,show hurwitzShift a (2*Real.pi*n)*
      (-I*(x:ℂ)/((2*Real.pi*(n:ℝ)*x-s.im:ℝ):ℂ)*hurwitzMode s (2*Real.pi*n) x)=
      (-I*(x:ℂ)/((2*Real.pi*(n:ℝ)*x-s.im:ℝ):ℂ))*(hurwitzShift a (2*Real.pi*n)*hurwitzMode s (2*Real.pi*n) x) by ring,
    hurwitzShift_mul_mode,hurwitzPhase_pow,hxy]
  have hd : ((2*Real.pi*(n:ℝ)*x-2*Real.pi*x*y:ℝ):ℂ)=
      (2*Real.pi*(x:ℂ))*((n:ℂ)-y) := by push_cast;ring
  rw [hd,div_eq_mul_inv,mul_inv_rev]
  have hxc := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp [hxc] <;>ring

/-- The two endpoint corrections from Euler–Maclaurin summation cancel as
a sine harmonic polynomial, uniformly in both the shift and the cutoff. -/
theorem hurwitz_frequency_boundary_uniform (a x : ℝ) (hx : 0<x) (s : ℂ) (L : ℕ) :
    ‖∑ m∈range L,hurwitzPair a m (fun ω => hurwitzMode s ω x/hurwitzFrequency ω)‖ ≤ 2*x^(-s.re) := by
  let z := hurwitzEndpointPhase (x-a)
  let C := I/(2*Real.pi)*(x:ℂ)^(-s)
  have he (m : ℕ) : hurwitzPair a m (fun ω => hurwitzMode s ω x/hurwitzFrequency ω)=
      C*(z^(m+1)-(conj z)^(m+1))/((m:ℂ)+1) := by
    have hw : hurwitzOmega m=2*Real.pi*(m+1:ℕ) := by dsimp [hurwitzOmega];push_cast;ring
    rw [hurwitzPair,←mul_div_assoc,←mul_div_assoc,hurwitzShift_mul_mode,hurwitzShift_mul_mode,hw,
      hurwitzPhase_pow,hurwitzPhase_neg_pow]
    dsimp only [hurwitzFrequency,C,z];push_cast
    have hn : (m:ℂ)+1≠0 := by exact_mod_cast (by omega : m+1≠0)
    field_simp [hn];simp [Complex.I_sq] <;>ring
  simp_rw [he,show ∀ m : ℕ,C*(z^(m+1)-(conj z)^(m+1))/((m:ℂ)+1)=
      C*((z^(m+1)-(conj z)^(m+1))/((m:ℂ)+1)) by intro m;ring,←mul_sum]
  rw [norm_mul]
  have hC : ‖C‖=x^(-s.re)/(2*Real.pi) := by
    dsimp [C];rw [norm_mul,norm_div,Complex.norm_I,Complex.norm_cpow_eq_rpow_re_of_pos hx,neg_re,
      show (2*(Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast;rfl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)];ring
  rw [hC]
  apply (mul_le_mul_of_nonneg_left (norm_symmetric_harmonic_sum_le L (norm_hurwitzEndpointPhase _)) (by positivity)).trans
  have hp : 2≤Real.pi := by linarith [Real.pi_gt_three]
  have ha := Real.rpow_nonneg hx.le (-s.re)
  field_simp
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hp)]

end AnalyticNumberTheory.RiemannZeta
