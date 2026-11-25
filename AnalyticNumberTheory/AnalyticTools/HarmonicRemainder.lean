import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Harmonic sums at a real cutoff

The harmonic sum at floor x differs from log x + Euler's constant by at most
1/x for every positive x. The estimate also covers cutoffs below the first term.
-/

open Real
namespace AnalyticNumberTheory.AnalyticTools

/-- Uniform real-cutoff bound, including nonintegral x. -/
theorem harmonic_floor_remainder {x : ℝ} (hx : 0<x) :
    |(harmonic ⌊x⌋₊:ℝ)-log x-eulerMascheroniConstant|≤1/x := by
  let n := ⌊x⌋₊
  have hlo : (n:ℝ)≤x := Nat.floor_le hx.le
  have hhi : x<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hpos : 0<(n:ℝ)+1 := by positivity
  have hu := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hl := eulerMascheroniConstant_lt_eulerMascheroniSeq' (n+1)
  simp only [eulerMascheroniSeq] at hu
  simp only [eulerMascheroniSeq',Nat.succ_ne_zero,ite_false,harmonic_succ,Rat.cast_add,Rat.cast_inv,
    Rat.cast_natCast,Nat.cast_add,Nat.cast_one] at hl
  have hlog := Real.log_le_log hx hhi.le
  have hinv := one_div_le_one_div_of_le hx hhi.le
  have hdiff := Real.log_le_sub_one_of_pos (div_pos hpos hx)
  rw [Real.log_div hpos.ne' hx.ne'] at hdiff
  have hh : ((n:ℝ)+1)/x≤1+1/x := by
    rw [div_le_iff₀ hx,add_mul,one_mul,div_mul_cancel₀ _ hx.ne']
    linarith
  change |(harmonic n:ℝ)-log x-eulerMascheroniConstant|≤_
  rw [abs_le];constructor <;> linarith [show ((n:ℝ)+1)⁻¹=1/((n:ℝ)+1) by rw [one_div]]

end AnalyticNumberTheory.AnalyticTools
