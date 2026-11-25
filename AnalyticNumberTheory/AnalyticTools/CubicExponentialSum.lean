import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# A cubic exponential sum at a varying scale

Summing dyadic blocks in a Vinogradov estimate leads to a real sequence
whose natural length is the two-thirds power of the logarithmic parameter.
-/

open Real
namespace AnalyticNumberTheory.AnalyticTools

/-- Uniform decay on a discrete cubic scale. The constant is explicit for every positive `c`. -/
theorem cubic_exponential_sum_le {c L : ℝ} (hc : 0<c) (hL : 1≤L) :
    Summable (fun j : ℕ => exp (-c*(j:ℝ)^3/L^2)) ∧
    ∑' j : ℕ, exp (-c*(j:ℝ)^3/L^2) ≤ exp c*(1+1/c)*L^(2/3:ℝ) := by
  let U := L^(2/3:ℝ)
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hU : 1≤U := Real.one_le_rpow hL (by norm_num)
  have hup : 0<U := zero_lt_one.trans_le hU
  have hu3 : U^3=L^2 := by
    dsimp only [U];rw [←rpow_natCast _ 3,←rpow_mul hLp.le]
    norm_num
  let r := exp (-c/U)
  have hr : 0<r := exp_pos _
  have hr' : r<1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hc) hup)
  have hs := (summable_geometric_of_lt_one hr.le hr').mul_left (exp c)
  have hterm (j : ℕ) : exp (-c*(j:ℝ)^3/L^2) ≤ exp c*r^j := by
    have hpow : r^j=exp (-(c*(j:ℝ)/U)) := by dsimp only [r];rw [←Real.exp_nat_mul];congr 1;ring
    rw [hpow,←Real.exp_add,Real.exp_le_exp,←hu3]
    let y := (j:ℝ)/U
    have hy : 0≤y := div_nonneg (Nat.cast_nonneg _) hup.le
    have hy3 : y≤1+y^3 := by
      rcases le_total y 1 with h|h
      · linarith only [h,pow_nonneg hy 3]
      · have := pow_le_pow_right₀ h (by decide : 1≤3);simp only [pow_one] at this;linarith
    have he : -c*(j:ℝ)^3/U^3= -c*y^3 := by dsimp only [y];ring
    have he' : c*(j:ℝ)/U=c*y := by dsimp only [y];ring
    rw [he,he'];nlinarith only [mul_le_mul_of_nonneg_left hy3 hc.le]
  have hsum := hs.of_nonneg_of_le (fun j => (exp_pos _).le) hterm
  refine ⟨hsum,(hsum.tsum_le_tsum hterm hs).trans ?_⟩
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr.le hr']
  have hx : 0<c/U := div_pos hc hup
  have hexp : (1+c/U)*r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (c/U)) hr.le
    have he : exp (c/U)*r=1 := by dsimp only [r];rw [←exp_add];simp [neg_div]
    linarith only [h,he]
  have hgeom : (1-r)⁻¹≤1+U/c := by
    rw [inv_le_iff_one_le_mul₀ (sub_pos.mpr hr')]
    apply (mul_le_mul_iff_right₀ hx).mp
    have he : (c/U)*((1+U/c)*(1-r))=(1-r)*(c/U+1) := by field_simp <;> ring
    rw [he];nlinarith only [hexp]
  change exp c*(1-r)⁻¹≤exp c*(1+1/c)*U
  apply (mul_le_mul_of_nonneg_left hgeom (exp_pos c).le).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (exp_pos c).le
  linarith only [hU,show (1+1/c)*U=U+U/c by ring]

end AnalyticNumberTheory.AnalyticTools
