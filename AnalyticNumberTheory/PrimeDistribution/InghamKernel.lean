import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A kernel estimate for zeros in unit height intervals

If at most `K` ordinates lie in each unit interval, the sum of the translated
weights `(1 + |t-γ|)⁻⁴` is at most `2π K`. Averaging the Cauchy kernel over
each unit interval handles ordinates arbitrarily close to an endpoint.
-/

open Real Complex Finset MeasureTheory
namespace AnalyticNumberTheory.PrimeDistribution

private theorem cauchyKernel_continuous (c : ℝ) : Continuous (fun u : ℝ => 1/(1+(u-c)^2)) :=
  continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2)) (fun u => by change 1+(u-c)^2 ≠ 0; positivity)

private theorem integral_cauchyKernel_le (a b c : ℝ) :
    (∫ u in a..b, 1/(1+(u-c)^2)) ≤ π := by
  rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => 1/(1+y^2)),
    integral_one_div_one_add_sq]
  linarith only [Real.arctan_lt_pi_div_two (b-c),Real.neg_pi_div_two_lt_arctan (a-c)]

private theorem inghamKernel_continuous (γ : ℝ) : Continuous (fun t : ℝ => 1/(1+|t-γ|)^4) :=
  continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 4) (fun t => by change (1+|t-γ|)^4 ≠ 0; positivity)

private theorem unitCell_inghamKernel_le {t γ u : ℝ} (h : |γ-u| ≤ 1) :
    1/(1+|t-γ|)^4 ≤ 2*(1/(1+(u-t)^2)) := by
  let r := |t-γ|
  have hr : 0 ≤ r := abs_nonneg _
  have hs : |u-t| ≤ r+1 := calc |u-t| = |t-u| := abs_sub_comm _ _
                                _ ≤ |t-γ|+|γ-u| := abs_sub_le _ _ _
                                _ ≤ r+1 := add_le_add le_rfl h
  have hs' := pow_le_pow_left₀ (abs_nonneg _) hs 2
  rw [sq_abs] at hs'
  have hR : (1:ℝ) ≤ 1+r := by linarith
  have hpow : (1+r)^2 ≤ (1+r)^4 := pow_le_pow_right₀ hR (by norm_num)
  have h1 : (1:ℝ) ≤ (1+r)^4 := one_le_pow₀ hR
  change 1/(1+r)^4 ≤ _
  rw [← mul_div_assoc,mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hs',hpow,h1]

/-- Unit-interval occupancy bounds the sum of all translated weights, uniformly in `t`. -/
theorem ingham_kernel_sum_le (S : Finset ℂ) {L : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < (L:ℝ))
    (hcount : ∀ j < L, ((S.filter (fun z => ⌊z.im⌋₊ = j)).card : ℝ) ≤ K) (t : ℝ) :
    ∑ z ∈ S, 1/(1+|t-z.im|)^4 ≤ 2*π*K := by
  classical
  let f (u : ℝ) := 1/(1+(u-t)^2)
  let J (j : ℕ) := ∫ u in (j:ℝ)..((j+1:ℕ):ℝ), f u
  have hf := cauchyKernel_continuous t
  have hJ (j : ℕ) : 0 ≤ J j := intervalIntegral.integral_nonneg (by exact_mod_cast Nat.le_succ j)
    (fun u _ => by dsimp [f]; positivity)
  have hcell (j : ℕ) (z : ℂ) (hz : z∈S) (hfloor : ⌊z.im⌋₊ = j) :
      1/(1+|t-z.im|)^4 ≤ 2*J j := by
    have hzj := Nat.floor_le (him z hz).1
    have hzj' := Nat.lt_floor_add_one z.im
    rw [hfloor] at hzj hzj'
    have hb : (j:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ j
    have h := intervalIntegral.integral_mono_on hb (intervalIntegrable_const (μ:=volume) (a:=(j:ℝ))
      (b:=((j+1:ℕ):ℝ)) (c:=1/(1+|t-z.im|)^4)) ((hf.const_mul 2).intervalIntegrable ..) (fun u hu =>
        unitCell_inghamKernel_le (by
          rw [abs_le]; push_cast at hu; constructor <;> linarith [hu.1,hu.2] : |z.im-u| ≤ 1))
    simpa only [intervalIntegral.integral_const,smul_eq_mul,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,
      one_mul,intervalIntegral.integral_const_mul,J,f] using h
  have hm : ∀ z ∈ S, ⌊z.im⌋₊ ∈ range L := fun z hz => mem_range.mpr ((Nat.floor_lt (him z hz).1).mpr (him z hz).2)
  rw [←sum_fiberwise_of_maps_to hm]
  calc
    _ ≤ ∑ j ∈ range L, K*(2*J j) := by
      apply sum_le_sum
      intro j hj
      calc _ ≤ ∑ _z ∈ S.filter (fun z => ⌊z.im⌋₊=j), 2*J j := by
                 apply sum_le_sum; intro z hz
                 exact hcell j z (mem_filter.mp hz).1 (mem_filter.mp hz).2
           _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hcount j (mem_range.mp hj)) (by positivity [hJ j])
    _ = (2*K)*∫ u in (0:ℝ)..L, f u := by
      simp_rw [show ∀ j : ℕ, K*(2*J j) = (2*K)*J j from fun j => by ring]
      rw [←mul_sum]
      congr 1
      simpa only [J,Nat.cast_zero] using (intervalIntegral.sum_integral_adjacent_intervals (μ:=volume)
        (a:=fun j : ℕ => (j:ℝ)) (n:=L) (f:=f) (fun j _ => hf.intervalIntegrable ..))
    _ ≤ _ := (mul_le_mul_of_nonneg_left (integral_cauchyKernel_le 0 L t) (by positivity : 0≤2*K)).trans_eq (by ring)

/-- The integral over any interval of the sum of the translated weights is at most `π` per ordinate. -/
theorem ingham_kernel_integral_le (S : Finset ℂ) {a b : ℝ} (hab : a≤b) :
    (∫ t in a..b, ∑ z ∈ S, 1/(1+|t-z.im|)^4) ≤ π*S.card := by
  rw [intervalIntegral.integral_finsetSum (fun z _ => (inghamKernel_continuous z.im).intervalIntegrable ..)]
  calc _ ≤ ∑ _z ∈ S, π := by
            apply sum_le_sum
            intro z _
            apply le_trans _ (integral_cauchyKernel_le a b z.im)
            apply intervalIntegral.integral_mono_on hab ((inghamKernel_continuous _).intervalIntegrable ..)
              ((cauchyKernel_continuous _).intervalIntegrable ..)
            intro t _
            apply one_div_le_one_div_of_le (by positivity)
            have hp : (1+|t-z.im|)^2 ≤ (1+|t-z.im|)^4 := pow_le_pow_right₀ (by linarith [abs_nonneg (t-z.im)]) (by norm_num)
            nlinarith only [sq_abs (t-z.im),abs_nonneg (t-z.im),hp]
       _ = _ := by rw [sum_const,nsmul_eq_mul,mul_comm]

end AnalyticNumberTheory.PrimeDistribution
