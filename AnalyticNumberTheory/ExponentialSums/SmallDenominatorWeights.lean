import AnalyticNumberTheory.ExponentialSums.SmallDenominatorPrimeSums
import AnalyticNumberTheory.ExponentialSums.PrimeWeightTransfer

/-! # Three prime weights near a rational frequency of small denominator -/

noncomputable section

open Real
open AnalyticNumberTheory.AdditiveNumberTheory AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.ExponentialSums

/-- The small-denominator scale dominates sqrt x times one logarithm.
This simultaneously controls the proper prime powers and small endpoints
when removing the logarithmic prime weight. -/
theorem sqrt_mul_log_le_smallDenominatorPrimeScale {x z η : ℝ} {q : ℕ}
    (hx : 1 ≤ x) (hη : 0 ≤ η) (hη₄ : η ≤ 1/4) (hq₀ : 0 < q)
    (hq : (q : ℝ) ≤ Real.exp (η*Real.sqrt (Real.log x)))
    (hz : x*|z| ≤ Real.exp (η*Real.sqrt (Real.log x))) :
    Real.sqrt x*(1+Real.log x) ≤ (20*Real.exp (1/4))*smallDenominatorPrimeScale x q z := by
  let u := Real.sqrt (Real.log x)
  let T := Real.exp (η*u)
  let R := x^(1/4:ℝ)
  let D := 1+x*|z|
  let L := Real.log (Real.log (10*(q : ℝ)))
  have hx₀ := zero_lt_one.trans_le hx
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu₂ : u^2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
  have hR : 1 ≤ R := Real.one_le_rpow hx (by norm_num)
  have hR₂ : R^2 = Real.sqrt x := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hx₀.le, Real.sqrt_eq_rpow]
    norm_num
  have hLx : 1+Real.log x ≤ 5*R := by
    have hh := Real.log_le_rpow_div hx₀.le (by norm_num : (0:ℝ) < 1/4)
    change Real.log x ≤ R/(1/4) at hh
    linarith only [hh,hR]
  have hT : 1 ≤ T := Real.one_le_exp (mul_nonneg hη hu)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq₀
  have hs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hq₁)
  have hT₂ : T^2 ≤ Real.exp (1/4)*R := by
    rw [show T^2 = Real.exp (η*u+η*u) by rw [Real.exp_add,sq],
      show R = Real.exp (Real.log x*(1/4)) from Real.rpow_def_of_pos hx₀ _, ←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hη₄ hu, sq_nonneg (u-1), hu₂]
  have hden : Real.sqrt q*D ≤ 2*Real.exp (1/4)*R := by
    calc _ ≤ T*(2*T) := mul_le_mul ((Real.sqrt_le_self_iff.mpr (Or.inr hq₁)).trans hq)
             (by dsimp only [D]; linarith only [hz,hT]) hD.le (zero_le_one.trans hT)
         _ = 2*T^2 := by ring
         _ ≤ _ := by linarith only [hT₂]
  have hL : 1/2 ≤ L := half_le_loglog_modulus hq₀
  change Real.sqrt x*(1+Real.log x) ≤ (20*Real.exp (1/4))*(L/Real.sqrt q*(x/D))
  rw [div_mul_div_comm, ←mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hs hD)).mpr
  calc _ ≤ (Real.sqrt x*(5*R))*(2*Real.exp (1/4)*R) := mul_le_mul
           (mul_le_mul_of_nonneg_left hLx (Real.sqrt_nonneg _)) hden
           (mul_nonneg hs.le hD.le) (by positivity)
       _ = (10*Real.exp (1/4))*(Real.sqrt x*R^2) := by ring
       _ = (10*Real.exp (1/4))*x := by rw [hR₂, Real.mul_self_sqrt hx₀.le]
       _ ≤ _ := by
         nlinarith only [mul_le_mul_of_nonneg_right hL (mul_nonneg (Real.exp_pos (1/4)).le hx₀.le)]

/-- All three classical prime sums near a reduced rational with small
denominator. The von Mangoldt and log-prime sums are bounded at every
intermediate endpoint. The unweighted prime sum saves one logarithm at x. -/
theorem prime_sums_small_denominator :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < C ∧
      ∀ {x : ℝ} {q : ℕ} {a : ℤ} {z : ℝ}, 2 ≤ x → 0 < q → a.natAbs.Coprime q →
        (q : ℝ) ≤ Real.exp (η*Real.sqrt (Real.log x)) →
        x*|z| ≤ Real.exp (η*Real.sqrt (Real.log x)) →
        (∀ {y : ℝ}, 1 ≤ y → y ≤ x →
          ‖primeExpSum y ((a : ℝ)/q+z)‖ ≤ C*smallDenominatorPrimeScale x q z ∧
          ‖logPrimeExpSum y ((a : ℝ)/q+z)‖ ≤ C*smallDenominatorPrimeScale x q z) ∧
        ‖unweightedPrimeExpSum x ((a : ℝ)/q+z)‖ ≤
          C*smallDenominatorPrimeScale x q z/(1+Real.log x) := by
  obtain ⟨η,A,hη,hη₄,hA,H⟩ := primeExpSum_small_denominator
  let D := 20*Real.exp (1/4)
  let B := (Real.log 4+4)*3
  let K := A+B*D
  let C := 2*D+12*K
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hAK : A ≤ K := le_add_of_nonneg_right (mul_nonneg hB.le hD.le)
  have hKC : K ≤ C := by dsimp only [C]; linarith only [hD,hK]
  have hC : 0 < C := hK.trans_le hKC
  refine ⟨η,C,hη,hη₄,hC,?_⟩
  intro x q a z hx hq ha hqx hz
  let V := smallDenominatorPrimeScale x q z
  let L := 1+Real.log x
  let α := (a : ℝ)/q+z
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hl : 1/2 ≤ Real.log x := by
    linarith only [Real.log_two_gt_d9,Real.log_le_log (by norm_num : (0:ℝ)<2) hx]
  have hL : 1 ≤ L := le_add_of_nonneg_right (Real.log_nonneg hx₁)
  have hL₀ := zero_lt_one.trans_le hL
  have hlog : 0 < Real.log x := by linarith only [hl]
  have hrootL : Real.sqrt x*L ≤ D*V :=
    sqrt_mul_log_le_smallDenominatorPrimeScale hx₁ hη.le hη₄ hq hqx hz
  have hroot : Real.sqrt x ≤ D*V :=
    (le_mul_of_one_le_right (Real.sqrt_nonneg x) hL).trans hrootL
  have hV : 0 ≤ V := nonneg_of_mul_nonneg_right ((Real.sqrt_nonneg x).trans hroot) hD
  have hθ {y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) : ‖logPrimeExpSum y α‖ ≤ K*V := by
    have he := (norm_primeExpSum_sub_logPrimeExpSum_le y α).trans
      ((le_abs_self _).trans (abs_psi_sub_theta_le_mul_sqrt y))
    have hr := (Real.sqrt_le_sqrt hyx).trans hroot
    have ht := norm_sub_le (primeExpSum y α) (primeExpSum y α-logPrimeExpSum y α)
    rw [sub_sub_cancel] at ht
    apply ht.trans ((add_le_add (H hx hq ha hqx hz hy hyx) he).trans ?_)
    change A*V+B*Real.sqrt y ≤ K*V
    dsimp only [K]
    nlinarith only [mul_le_mul_of_nonneg_left hr hB.le]
  refine ⟨fun {y} hy hyx => ⟨(H hx hq ha hqx hz hy hyx).trans
    (mul_le_mul_of_nonneg_right (hAK.trans hKC) hV), (hθ hy hyx).trans (mul_le_mul_of_nonneg_right hKC hV)⟩,?_⟩
  have hsum := norm_sum_primes_le_sqrt_add_of_log_bound hx (H := K*V)
    (f := fun p => AdditiveNumberTheory.e (α*p)) (fun _ => (AdditiveNumberTheory.norm_e _).le)
    (fun n hn hnx => by
      simpa only [logPrimeExpSum,Nat.floor_natCast] using hθ (y:=(n:ℝ))
        (by exact_mod_cast (show 1 ≤ n by omega)) hnx)
  change ‖unweightedPrimeExpSum x α‖ ≤ 2*Real.sqrt x+4*(K*V)/Real.log x at hsum
  apply hsum.trans
  apply (le_div_iff₀ hL₀).mpr
  have hratio : L/Real.log x ≤ 3 := (div_le_iff₀ hlog).mpr (by dsimp only [L]; linarith only [hl])
  calc (2*Real.sqrt x+4*(K*V)/Real.log x)*L =
         2*(Real.sqrt x*L)+4*(K*V)*(L/Real.log x) := by ring
       _ ≤ 2*(D*V)+4*(K*V)*3 := add_le_add
           (mul_le_mul_of_nonneg_left hrootL (by norm_num))
           (mul_le_mul_of_nonneg_left hratio (by positivity))
       _ = C*V := by dsimp only [C]; ring

end AnalyticNumberTheory.ExponentialSums
