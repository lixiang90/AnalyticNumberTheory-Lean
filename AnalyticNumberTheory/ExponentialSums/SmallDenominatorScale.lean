import AnalyticNumberTheory.ExponentialSums.SmallDenominatorExpansion

/-! # The common scale on an exponential small-denominator arc -/

noncomputable section

open Real

namespace AnalyticNumberTheory.ExponentialSums

/-- The frequency and modulus factors in the small-denominator estimate.
The expression is finite at the center z = 0 of the arc. -/
def smallDenominatorPrimeScale (x : ℝ) (q : ℕ) (z : ℝ) : ℝ :=
  Real.log (Real.log (10*(q : ℝ)))/Real.sqrt q * (x/(1+x*|z|))

/-- A uniform positive lower bound for the double logarithm at all positive levels. -/
theorem half_le_loglog_modulus {q : ℕ} (hq : 0 < q) :
    1/2 ≤ Real.log (Real.log (10*(q : ℝ))) := by
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h : 2 ≤ Real.log (10*(q : ℝ)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith only [mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three.le, hq₁]
  exact (show 1/2 ≤ Real.log 2 by linarith only [Real.log_two_gt_d9]).trans
    (Real.log_le_log (by norm_num) h)

/-- At fixed modulus and frequency offset the major-arc scale increases with the endpoint. -/
theorem smallDenominatorPrimeScale_mono {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    {q : ℕ} (hq : 0 < q) (z : ℝ) :
    smallDenominatorPrimeScale y q z ≤ smallDenominatorPrimeScale x q z := by
  have hx := hy.trans hyx
  have hL := half_le_loglog_modulus hq
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith only [hL]) (Real.sqrt_nonneg _))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hyx]

/-- If q and x|z| are at most exp(η sqrt(log x)) and 4η ≤ b, the complete
character remainder is absorbed by the main-term scale, uniformly in y ≤ x. -/
theorem smallDenominator_error_absorption {x y η b z : ℝ} {q : ℕ} (hη : 0 ≤ η)
    (hb : 4*η ≤ b) (hx : 1 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) (hq₀ : 0 < q)
    (hq : (q : ℝ) ≤ Real.exp (η*Real.sqrt (Real.log x)))
    (hz : x*|z| ≤ Real.exp (η*Real.sqrt (Real.log x))) :
    q*x*Real.exp (-b*Real.sqrt (Real.log x))*(1+2*Real.pi*y*|z|) ≤
      (4*(1+2*Real.pi))*smallDenominatorPrimeScale x q z := by
  let u := Real.sqrt (Real.log x)
  let T := Real.exp (η*u)
  let F := 1+2*Real.pi*y*|z|
  let D := 1+x*|z|
  let L := Real.log (Real.log (10*(q : ℝ)))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hT : 1 ≤ T := Real.one_le_exp (mul_nonneg hη hu)
  have hT₀ := zero_lt_one.trans_le hT
  have hx₀ := zero_lt_one.trans_le hx
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq₀
  have hs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hq₁)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hqT : (q : ℝ)*Real.sqrt q ≤ T^2 := by
    rw [sq]
    exact mul_le_mul hq ((Real.sqrt_le_self_iff.mpr (Or.inr hq₁)).trans hq) hs.le hT₀.le
  have hDT : D ≤ 2*T := by dsimp only [D]; linarith only [hz, hT]
  have hFT : F ≤ (1+2*Real.pi)*T := by
    have h := (mul_le_mul_of_nonneg_right hyx (abs_nonneg z)).trans hz
    dsimp only [F]
    linarith only [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*Real.pi),hT]
  have hscaled : ((q : ℝ)*Real.sqrt q)*(D*F) ≤ 2*(1+2*Real.pi)*T^4 := by
    apply (mul_le_mul hqT (mul_le_mul hDT hFT hF (by positivity))
      (mul_nonneg hD.le hF) (sq_nonneg T)).trans_eq
    ring
  have hsave : T^4*Real.exp (-b*u) ≤ 1 := by
    dsimp only [T]
    rw [←Real.exp_nat_mul, ←Real.exp_add, Real.exp_le_one_iff]
    norm_num only [Nat.cast_ofNat]
    linarith only [mul_le_mul_of_nonneg_right hb hu]
  have hcost : ((q : ℝ)*Real.sqrt q)*(D*F)*Real.exp (-b*u) ≤ 2*(1+2*Real.pi) := by
    apply (mul_le_mul_of_nonneg_right hscaled (Real.exp_pos _).le).trans
    calc _ = (2*(1+2*Real.pi))*(T^4*Real.exp (-b*u)) := by ring
         _ ≤ _ := mul_le_of_le_one_right (by positivity) hsave
  have hL : 1/2 ≤ L := half_le_loglog_modulus hq₀
  change q*x*Real.exp (-b*u)*F ≤ (4*(1+2*Real.pi))*(L/Real.sqrt q*(x/D))
  rw [div_mul_div_comm, ← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hs hD)).mpr
  have hmain := mul_le_mul_of_nonneg_right (show 2 ≤ 4*L by linarith only [hL])
    (mul_nonneg hx₀.le (by positivity : 0 ≤ 1+2*Real.pi))
  nlinarith only [mul_le_mul_of_nonneg_left hcost hx₀.le,hmain]

end AnalyticNumberTheory.ExponentialSums
