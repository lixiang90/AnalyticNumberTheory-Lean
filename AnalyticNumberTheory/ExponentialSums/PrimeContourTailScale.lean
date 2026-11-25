import AnalyticNumberTheory.ExponentialSums.PrimeContourTailMean

/-! # Equal truncations on the absolute prime contour -/

noncomputable section
open Complex Real Finset
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.ExponentialSums

/-- With equal lower cutoffs the right-hand contour contributes at most
2x (q/A + 1+log x) (1+log x)³, including all characters modulo q. -/
theorem primeContourTail_balanced {q A : ℕ} [NeZero q] (hA : 1≤A) {x : ℝ} (hAx : (A : ℝ)≤x) :
    let L := 1+Real.log x
    (∑ χ : DirichletCharacter ℂ q, ‖logPerronIntegral (primeContourTailPart χ A A ⌊x⌋₊) 1 x‖) ≤
      2*x*((q : ℝ)/A+L)*L^3 := by
  intro L
  let X := ⌊x⌋₊
  let Y := X/A
  let E := (q : ℝ)/A+L
  let B := ((q : ℝ)/A+(1+Real.log Y))*(1+Real.log Y)^4
  let F := ((q : ℝ)/A+(1+Real.log X))*(Real.log X*(Real.log X+Real.log 4+8))
  have hA₁ : (1 : ℝ)≤A := by exact_mod_cast hA
  have hx := hA₁.trans hAx
  have hX : 1≤X := (Nat.one_le_floor_iff x).mpr hx
  have hAX : A≤X := (Nat.le_floor_iff (zero_le_one.trans hx)).mpr hAx
  have hY : 1≤Y := Nat.div_pos hAX hA
  have hYX : (Y : ℝ) ≤ X := by exact_mod_cast Nat.div_le_self X A
  have hxX : (X : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hy : Real.log Y ≤ Real.log x := Real.log_le_log (by exact_mod_cast hY) (hYX.trans hxX)
  have hxlog : Real.log X ≤ Real.log x := Real.log_le_log (by exact_mod_cast hX) hxX
  have hL : 1≤L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  have hE : 0≤E := by dsimp [E]; positivity
  have hB₀ : 0≤B := by dsimp [B]; positivity
  have hF₀ : 0≤F := by dsimp [F]; positivity [Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]
  have hδy : 1+Real.log Y ≤ L := add_le_add_right hy 1
  have hδx : 1+Real.log X ≤ L := add_le_add_right hxlog 1
  have hb : B ≤ E*L^4 := mul_le_mul (add_le_add_right hδy _) (pow_le_pow_left₀ (by positivity) hδy 4) (by positivity) hE
  have hf : F ≤ E*(16*L^2) := by
    apply mul_le_mul (add_le_add_right hδx _) _ (by positivity [Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]) hE
    have hfour : Real.log 4 ≤ 3 := by linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ)<4 by norm_num)]
    calc
      _ ≤ L*(16*L) := mul_le_mul (by linarith only [hδx]) (by linarith only [hL,hfour,hδx])
        (by positivity [Real.log_nonneg (show (1 : ℝ)≤4 by norm_num)]) hL₀
      _ = _ := by ring
  have hroot : Real.sqrt B*Real.sqrt F ≤ 4*E*L^3 := by
    rw [← Real.sqrt_mul hB₀]
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    exact (mul_le_mul hb hf hF₀ (by positivity)).trans_eq (by ring)
  have H := primeContourTail_integral_mean (q := q) hA hA hx
  change _ ≤ x*Real.sqrt B*Real.sqrt F/2 at H
  apply H.trans
  rw [mul_assoc x]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (zero_le_one.trans hx)) (by norm_num : (0 : ℝ)≤2)).trans_eq (by dsimp [E]; ring)

end AnalyticNumberTheory.ExponentialSums
