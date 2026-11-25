import AnalyticNumberTheory.DivisorProblems.VoronoiTransformedBlocks
import AnalyticNumberTheory.DivisorProblems.DivisorPairWeights
import Mathlib.Analysis.PSeries

/-!
# The cosine sum in the truncated Voronoï formula
-/

open Real Complex Finset
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- The oscillating coefficient attached to each positive integer in
Voronoï's formula for the classical divisor error. -/
noncomputable def voronoiCosineWeight (x : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(-(3/4):ℝ)*Real.cos (4*Real.pi*Real.sqrt ((n:ℝ)*x)-Real.pi/4)

/-- The finite Voronoï approximant of the divisor error. -/
noncomputable def voronoiDivisorSum (x : ℝ) (N : ℕ) : ℝ :=
  x^(1/4:ℝ)/(Real.pi*Real.sqrt 2) * ∑ n∈Icc 1 N,(n.divisors.card:ℝ)*voronoiCosineWeight x n

private theorem saddle_term_im {h m : ℕ} {x : ℝ} (hh : 0<h) (hm : 0<m) (hx : 0<x) :
    ((((h:ℝ)⁻¹:ℝ):ℂ)*reciprocalSaddleTerm (h*x) m).im =
      x^(1/4:ℝ)/Real.sqrt 2*voronoiCosineWeight x (h*m) := by
  let y := 4*Real.pi*Real.sqrt (((h*m:ℕ):ℝ)*x)
  have hh' : 0<(h:ℝ) := by exact_mod_cast hh
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have phase : 2*Real.pi*(2*Real.sqrt (((h:ℝ)*x)*m))=y := by
    dsimp [y]; push_cast; rw [mul_right_comm (h:ℝ) x]; ring
  have hR (u : ℝ) : (e u).re=Real.cos (2*Real.pi*u) := by simp [e,Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have hI (u : ℝ) : (e u).im=Real.sin (2*Real.pi*u) := by simp [e,Complex.exp_im,Complex.mul_re,Complex.mul_im]
  have hcR : ((1+Complex.I)/2).re=1/2 := by norm_num [Complex.div_re]
  have hcI : ((1+Complex.I)/2).im=1/2 := by norm_num [Complex.div_im]
  have htrig : (Real.sin y+Real.cos y)/2=Real.cos (y-Real.pi/4)/Real.sqrt 2 := by
    rw [Real.cos_sub,Real.cos_pi_div_four,Real.sin_pi_div_four]; field_simp; ring
  have hp : (h:ℝ)⁻¹*((h:ℝ)*x)^(1/4:ℝ)*(m:ℝ)^(-(3/4):ℝ) =
      x^(1/4:ℝ)*((h*m:ℕ):ℝ)^(-(3/4):ℝ) := by
    push_cast; rw [Real.mul_rpow hh'.le hx.le,Real.mul_rpow hh'.le hm'.le]
    rw [show (h:ℝ)⁻¹=(h:ℝ)^(-1:ℝ) by rw [Real.rpow_neg_one]]
    rw [←mul_assoc,←Real.rpow_add hh',show (-1:ℝ)+1/4= -(3/4) by norm_num]
    ring
  unfold reciprocalSaddleTerm voronoiCosineWeight
  simp only [Complex.mul_im,Complex.mul_re,hI,hR,hcI,hcR,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,zero_add,add_zero,sub_zero,phase]
  change _=x^(1/4:ℝ)/Real.sqrt 2*(((h*m:ℕ):ℝ)^(-(3/4):ℝ)*Real.cos (y-Real.pi/4))
  calc
    _ = ((h:ℝ)⁻¹*((h:ℝ)*x)^(1/4:ℝ)*(m:ℝ)^(-(3/4):ℝ))*((Real.sin y+Real.cos y)/2) := by ring
    _ = _ := by rw [hp,htrig]; ring

/-- The dual square-root-frequency sum grouped by `n=h*m`. The unpaired
squares carry precisely the missing diagonal term. -/
theorem divisorDualBlocks_im_eq_voronoi_sub_diagonal {x : ℝ} (hx : 0<x) (N : ℕ) :
    2*(divisorDualBlocks x N).im/Real.pi =
      voronoiDivisorSum x N-x^(1/4:ℝ)/(Real.pi*Real.sqrt 2)*
        ∑ h∈Icc 1 N.sqrt,voronoiCosineWeight x (h^2) := by
  have he : (divisorDualBlocks x N).im = (x^(1/4:ℝ)/Real.sqrt 2)*
      ∑ h∈Icc 1 N.sqrt,∑ m∈Ioc h (N/h),voronoiCosineWeight x (h*m) := by
    unfold divisorDualBlocks
    rw [Complex.im_sum,Finset.mul_sum]
    apply sum_congr rfl; intro h hh
    rw [Finset.mul_sum,Finset.mul_sum,Complex.im_sum]
    apply sum_congr rfl; intro m hm
    exact saddle_term_im (mem_Icc.mp hh).1 ((mem_Icc.mp hh).1.trans (mem_Ioc.mp hm).1.le) hx
  rw [he,voronoiDivisorSum,sum_divisor_weights_eq_strict_pairs]; ring

/-- A single absolute constant bounds all of the square corrections after
the common factor `x^(1/4)` is removed. -/
theorem abs_voronoi_diagonal_le (x : ℝ) (N : ℕ) :
    |∑ h∈Icc 1 N.sqrt,voronoiCosineWeight x (h^2)| ≤ ∑' h:ℕ,(h:ℝ)^(-(3/2):ℝ) := by
  have hs := Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ) < -1)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum ?_).trans (hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  intro h hh
  unfold voronoiCosineWeight
  rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  apply (mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) (Real.abs_cos_le_one _)).trans_eq
  push_cast; rw [←Real.rpow_natCast (h:ℝ) 2,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; norm_num

end AnalyticNumberTheory.DivisorProblems
