import AnalyticNumberTheory.ModularAndPartitions.PartitionLaplace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The inverse Laplace integral in Rademacher's formula

Expanding the reciprocal exponential term gives the power series of a
modified Bessel function. At order `3/2` the series reduces to hyperbolic functions.
-/

open Complex Real MeasureTheory Filter NormedSpace
open scoped Topology

namespace AnalyticNumberTheory.ModularAndPartitions

/-- The holomorphic exponential kernel on the right half-plane. -/
noncomputable def rademacherVerticalKernel (s b A : ℝ) (w : ℂ) : ℂ :=
  w ^ (-(s:ℂ)) * Complex.exp (b*w + A/w)

private theorem vertical_ne (t : ℝ) : 1+(t:ℂ)*I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- The convergent Bessel series obtained by integrating each inverse-power term on the
vertical line. The exponential factor `exp(b)` in the kernel cancels the `exp(-b)`
from Fourier inversion. -/
theorem hasSum_rademacherVerticalKernel {s b A : ℝ} (hs : 2 ≤ s) (hb : 0 < b) (hA : 0 ≤ A) :
    HasSum (fun m : ℕ => ((2*π * A^m / m.factorial * b^(s+m-1) / Real.Gamma (s+m) : ℝ):ℂ))
      (∫ t : ℝ, rademacherVerticalKernel s b A (1+(t:ℂ)*I)) := by
  let w (t : ℝ) := 1+(t:ℂ)*I
  let c (m : ℕ) := A^m / (m.factorial:ℝ)
  let G (t : ℝ) := ‖(w t)^(-(s:ℂ))‖
  let f (m : ℕ) (t : ℝ) := ((Real.exp b * c m : ℝ):ℂ) *
    (Complex.exp (I*b*t) * (w t)^(-((s+(m:ℝ):ℝ):ℂ)))
  have hc (m : ℕ) : 0 ≤ c m := by dsimp [c]; positivity
  have hi : Integrable G := (integrable_vertical_cpow hs).norm
  have hi' (m : ℕ) : Integrable (f m) := by
    have hm := integrable_vertical_cpow (show 2 ≤ s+(m:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) m])
    apply Integrable.const_mul
    apply hm.bdd_mul _ ?_ (c := 1)
    · fun_prop
    · exact ae_of_all _ fun t => by simp [Complex.norm_exp, Complex.mul_re, mul_comm]
  have hsplit (t : ℝ) (m : ℕ) :
      (w t)^(-((s+(m:ℝ):ℝ):ℂ)) = (w t)^(-(s:ℂ)) * ((w t)^m)⁻¹ := by
    push_cast
    rw [neg_add, Complex.cpow_add _ _ (vertical_ne t), Complex.cpow_neg _ (m:ℂ), Complex.cpow_natCast]
  have hpoint (m : ℕ) (t : ℝ) : ‖f m t‖ ≤ Real.exp b * c m * G t := by
    have hw : 1 ≤ ‖w t‖ := by simpa [w] using Complex.re_le_norm (w t)
    have he : ‖Complex.exp (I*b*t)‖ = 1 := by simp [Complex.norm_exp, Complex.mul_re]
    dsimp only [f]
    rw [hsplit]
    simp only [norm_mul, he, one_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hc m), abs_of_pos (Real.exp_pos b)]
    change _ ≤ _ * G t
    calc _ ≤ Real.exp b * c m * (G t * 1) := by
               apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos b).le (hc m))
               apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
               exact inv_le_one_of_one_le₀ (one_le_pow₀ hw)
         _ = _ := by ring
  have hsum : Summable fun m => ∫ t : ℝ, ‖f m t‖ := by
    apply (((expSeries_div_hasSum_exp A).summable.mul_left (Real.exp b)).mul_right (∫ t, G t)).of_nonneg_of_le
      (fun m => integral_nonneg (fun _ => norm_nonneg _))
    intro m
    rw [← integral_const_mul]
    apply integral_mono (hi' m).norm (hi.const_mul _)
    exact hpoint m
  have hterm (m : ℕ) : (∫ t : ℝ, f m t) = ((2*π*A^m / m.factorial * b^(s+m-1)/Real.Gamma (s+m):ℝ):ℂ) := by
    dsimp only [f, w]
    rw [integral_const_mul, integral_vertical_cpow_exp (by linarith [Nat.cast_nonneg (α := ℝ) m]) hb, ← Complex.ofReal_mul]
    congr 1
    dsimp only [c]
    rw [Real.exp_neg]
    field_simp
  have hseries (t : ℝ) : (∑' m, f m t) = rademacherVerticalKernel s b A (w t) := by
    have he := (expSeries_div_hasSum_exp ((A:ℂ)/w t)).mul_left
      ((Real.exp b:ℂ) * Complex.exp (I*b*t) * (w t)^(-(s:ℂ)))
    have hcoef (m : ℕ) : f m t = ((Real.exp b:ℂ)*Complex.exp (I*b*t)*(w t)^(-(s:ℂ))) *
        (((A:ℂ)/w t)^m / m.factorial) := by
      dsimp only [f, c]
      rw [hsplit, div_pow]
      push_cast
      ring
    simp_rw [hcoef]
    rw [he.tsum_eq, ← Complex.exp_eq_exp_ℂ, rademacherVerticalKernel, Complex.exp_add]
    rw [show (b:ℂ)*w t = (b:ℂ) + I*b*t by dsimp [w]; ring, Complex.exp_add, Complex.ofReal_exp]
    ring
  have h := hasSum_integral_of_summable_integral_norm hi' hsum
  simpa only [hseries, hterm] using h

private theorem factorial_mul_gamma_half (m : ℕ) :
    (m.factorial : ℝ) * Real.Gamma (5/2+(m:ℝ)) * 2^(2*m+3) * (m+1) =
      √π * ((2*m+3).factorial:ℝ) := by
  induction m with
  | zero =>
      have h1 := Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0)
      have h2 := Real.Gamma_add_one (by norm_num : (3/2:ℝ) ≠ 0)
      rw [Real.Gamma_one_half_eq] at h1
      norm_num at h1 h2 ⊢
      linarith
  | succ m ih =>
      rw [show 2*(m+1)+3 = (2*m+3)+1+1 by omega, Nat.factorial_succ ((2*m+3)+1),
        Nat.factorial_succ (2*m+3), Nat.factorial_succ m, pow_succ, pow_succ, Nat.cast_succ,
        show 5/2+((m:ℝ)+1) = (5/2+m)+1 by ring, Real.Gamma_add_one (by positivity)]
      push_cast
      linear_combination (2*(m:ℝ)+4)*(2*m+5)*ih

private theorem hasSum_cosh_sub_sinh (y : ℝ) :
    HasSum (fun m : ℕ => (2*m+2)*y^(2*m+3) / ((2*m+3).factorial:ℝ)) (y*Real.cosh y-Real.sinh y) := by
  have h := (hasSum_nat_add_iff' 1).mpr (((Real.hasSum_cosh y).mul_left y).sub (Real.hasSum_sinh y))
  simp only [Finset.sum_range_one] at h
  norm_num at h
  apply h.congr_fun
  intro m
  symm
  rw [show 2*(m+1)+1 = (2*m+2)+1 by omega, show 2*(m+1) = 2*m+2 by omega,
    Nat.factorial_succ (2*m+2), show 2*m+3 = (2*m+2)+1 by omega, pow_succ]
  push_cast
  field_simp
  ring

/-- The half-integer Bessel integral is an elementary hyperbolic expression. -/
theorem integral_rademacherVerticalKernel_half {b A : ℝ} (hb : 0 < b) (hA : 0 < A) :
    (∫ t : ℝ, rademacherVerticalKernel (5/2) b A (1+(t:ℂ)*I)) =
      let y := 2*√b*√A
      ((√π / (A*√A) * (y*Real.cosh y-Real.sinh y) : ℝ):ℂ) := by
  let y := 2*√b*√A
  have h := hasSum_rademacherVerticalKernel (by norm_num : (2:ℝ) ≤ 5/2) hb hA.le
  have hreal := (hasSum_cosh_sub_sinh y).mul_left (√π/(A*√A))
  have hc := Complex.ofRealCLM.hasSum hreal
  apply h.unique
  apply hc.congr_fun
  intro m
  symm
  change ((√π / (A*√A) * ((2*m+2)*y^(2*m+3)/((2*m+3).factorial:ℝ)) : ℝ):ℂ) = _
  congr 1
  have hpow : y^(2*m+3) = 2^(2*m+3) * b^m * A^m * (√b)^3 * (√A)^3 := by
    dsimp [y]
    rw [mul_pow, mul_pow, pow_add (√b), pow_add (√A), pow_mul, pow_mul,
      Real.sq_sqrt hb.le, Real.sq_sqrt hA.le]
    ring
  have hbpow : b^(5/2+(m:ℝ)-1) = b^m * (√b)^3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (b^(1/2:ℝ)) 3, ← Real.rpow_mul hb.le,
      ← Real.rpow_natCast b m, ← Real.rpow_add hb]
    congr 1; norm_num; ring
  rw [hpow, hbpow]
  have hgpos := Real.Gamma_pos_of_pos (show 0 < 5/2+(m:ℝ) by positivity)
  have he : √π*(2*(m:ℝ)+2)*2^(2*m+3)/((2*m+3).factorial:ℝ) =
      2*π/((m.factorial:ℝ)*Real.Gamma (5/2+(m:ℝ))) := by
    apply (div_eq_div_iff (by positivity) (mul_ne_zero (by positivity) hgpos.ne')).mpr
    calc _ = 2*√π*((m.factorial:ℝ)*Real.Gamma (5/2+m)*2^(2*m+3)*(m+1)) := by ring
         _ = _ := by rw [factorial_mul_gamma_half]; nlinarith [congrArg (fun v : ℝ => v*((2*m+3).factorial:ℝ)) (Real.sq_sqrt Real.pi_pos.le)]
  rw [show (√A)^3 = A*√A by rw [pow_succ, Real.sq_sqrt hA.le]]
  calc _ = (√π*(2*(m:ℝ)+2)*2^(2*m+3)/((2*m+3).factorial:ℝ))*(b^m*A^m*(√b)^3) := by
             field_simp [Real.sqrt_ne_zero'.mpr hA]
             <;> ring
       _ = _ := by rw [he]; ring

end AnalyticNumberTheory.ModularAndPartitions
