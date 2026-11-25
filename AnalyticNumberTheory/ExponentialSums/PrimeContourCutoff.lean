import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-! # Optimizing the cutoff in the smoothed prime contour estimate -/

open Real

namespace AnalyticNumberTheory.ExponentialSums

/-- The integer fourth-root cutoff simultaneously controls the lengths on
the critical line and the reciprocal length on the absolute line. All
inequalities also hold at q=x and at q=x=1. -/
theorem exists_primeContour_cutoff {q x : ℝ} (hq : 1≤q) (hqx : q≤x) :
    ∃ A : ℕ, 1≤A ∧ ((A*A : ℕ) : ℝ)≤x ∧
      Real.sqrt x * Real.sqrt q * (Real.sqrt q + A) ≤ 2*(x*q)^(3/4 : ℝ) ∧
      x*(q/A) ≤ 2*(x*q)^(3/4 : ℝ) := by
  let Y := Real.sqrt (Real.sqrt (x*q))
  let A := ⌊Y⌋₊
  have hx := hq.trans hqx
  have hx₀ := zero_le_one.trans hx
  have hq₀ := zero_le_one.trans hq
  have hX := mul_nonneg hx₀ hq₀
  have hY₀ : 0≤Y := Real.sqrt_nonneg _
  have hYsq : Y^2 = Real.sqrt (x*q) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hY₁ : 1≤Y := by
    dsimp only [Y]
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hx hq))
  have hA : 1≤A := (Nat.one_le_floor_iff Y).mpr hY₁
  have ha : (A : ℝ)≤Y := Nat.floor_le hY₀
  have hA₁ : (1 : ℝ)≤A := by exact_mod_cast hA
  have hlo : Y≤2*A := by linarith only [Nat.lt_floor_add_one Y, hA₁]
  have hroot : Real.sqrt q≤Y := by
    apply Real.sqrt_le_sqrt
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact mul_le_mul_of_nonneg_right hqx hq₀
  have hsx : Real.sqrt (x*q) ≤ x := Real.sqrt_le_iff.mpr
    ⟨hx₀, by simpa only [sq] using mul_le_mul_of_nonneg_left hqx hx₀⟩
  have hAX : ((A*A : ℕ) : ℝ)≤x := by
    rw [Nat.cast_mul, ← sq]
    exact ((pow_le_pow_left₀ (Nat.cast_nonneg _) ha 2).trans_eq hYsq).trans hsx
  have hpower : Y^3=(x*q)^(3/4 : ℝ) := by
    dsimp only [Y]
    simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hX, ← Real.rpow_mul_natCast hX]
    norm_num
  refine ⟨A,hA,hAX,?_,?_⟩
  · rw [← Real.sqrt_mul hx₀, ← hYsq, ← hpower]
    calc
      _ ≤ Y^2*(Y+Y) := mul_le_mul_of_nonneg_left (add_le_add hroot ha) (sq_nonneg _)
      _ = _ := by ring
  · rw [← mul_div_assoc, div_le_iff₀ (zero_lt_one.trans_le hA₁), ← hpower]
    calc
      x*q = (Y^2)^2 := by rw [hYsq, Real.sq_sqrt hX]
      _ = Y^3*Y := by ring
      _ ≤ Y^3*(2*A) := mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = _ := by ring

end AnalyticNumberTheory.ExponentialSums
