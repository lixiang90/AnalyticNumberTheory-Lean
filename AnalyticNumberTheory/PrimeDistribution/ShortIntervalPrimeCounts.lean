import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Transfer from Chebyshev's ψ to primes in short intervals

When the length x^θ exceeds the square-root scale, the higher prime
powers make a lower-order contribution. The remaining logarithms lie
between the logarithms of the two endpoints.
-/
noncomputable section
open Finset Filter Real Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

private def intervalPrimeSet (x y : ℝ) := Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊x⌋₊

private theorem intervalPrimeSet_mem {x y : ℝ} (hx : 0≤x) (hxy : x≤y) {p : ℕ} (hp : p∈intervalPrimeSet x y) :
    p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤y := by
  obtain ⟨hy,hn⟩ := mem_sdiff.mp hp
  obtain ⟨hy,hp⟩ := Nat.mem_primesLE.mp hy
  exact ⟨hp,lt_of_not_ge (fun h => hn (Nat.mem_primesLE.mpr ⟨Nat.le_floor h,hp⟩)),
    (Nat.le_floor_iff (hx.trans hxy)).mp hy⟩

private theorem intervalPrimeSet_formulas {x y : ℝ} (hxy : x≤y) :
    Chebyshev.theta y-Chebyshev.theta x = ∑ p∈intervalPrimeSet x y,log p ∧
    primePi y-primePi x = ((intervalPrimeSet x y).card:ℝ) := by
  have hs : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans (Nat.floor_mono hxy),hp.2⟩
  constructor
  · rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE,←Finset.sum_sdiff_eq_sub hs]; rfl
  · rw [primePi_eq_card_primesLE,primePi_eq_card_primesLE,intervalPrimeSet,Finset.card_sdiff_of_subset hs,
      Nat.cast_sub (card_le_card hs)]

/-- Upper and lower logarithmic comparisons for the number of primes in
an interval with positive endpoints. -/
theorem theta_interval_primePi_comparison {x y : ℝ} (hx : 0<x) (hxy : x≤y) :
    (primePi y-primePi x)*log x ≤ Chebyshev.theta y-Chebyshev.theta x ∧
    Chebyshev.theta y-Chebyshev.theta x ≤ (primePi y-primePi x)*log y := by
  obtain ⟨hθ,hπ⟩ := intervalPrimeSet_formulas hxy
  rw [hθ,hπ,←nsmul_eq_mul,←sum_const,←nsmul_eq_mul,←sum_const]
  exact ⟨sum_le_sum (fun p hp => Real.log_le_log hx (intervalPrimeSet_mem hx.le hxy hp).2.1.le),
    sum_le_sum (fun p hp => Real.log_le_log (hx.trans (intervalPrimeSet_mem hx.le hxy hp).2.1)
      (intervalPrimeSet_mem hx.le hxy hp).2.2)⟩

/-- In power-length intervals above the square-root scale, replacing ψ
by θ incurs an error of smaller order than the interval length. -/
theorem shortInterval_theta_sub_psi_isLittleO {θ : ℝ} (hθ : 1/2<θ) (hθ' : θ≤1) :
    (fun x : ℝ => (Chebyshev.theta (x+x^θ)-Chebyshev.theta x)-
      (Chebyshev.psi (x+x^θ)-Chebyshev.psi x)) =o[atTop] fun x : ℝ => x^θ := by
  have hs : (fun x : ℝ => √x) =o[atTop] fun x : ℝ => x^θ := by
    apply isLittleO_of_tendsto' (by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact fun he => absurd he (Real.rpow_pos_of_pos hx θ).ne')
    apply (tendsto_rpow_neg_atTop (show 0<θ-1/2 by linarith)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub hx]; congr 1; ring
  let C := (log 4+4)*3
  have hC : 0≤C := by dsimp [C]; positivity
  apply IsBigO.trans_isLittleO _ hs
  apply IsBigO.of_bound (C*(√2+1))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx' : 0≤x := by linarith
  have hy := Real.rpow_le_rpow_of_exponent_le hx hθ'
  rw [Real.rpow_one] at hy
  have hroot : √(x+x^θ)≤√2*√x := by rw [←Real.sqrt_mul zero_le_two]; exact Real.sqrt_le_sqrt (by linarith)
  have hl := abs_psi_sub_theta_le_mul_sqrt (x+x^θ)
  have hr := abs_psi_sub_theta_le_mul_sqrt x
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  rw [show Chebyshev.theta (x+x^θ)-Chebyshev.theta x-(Chebyshev.psi (x+x^θ)-Chebyshev.psi x) =
    (Chebyshev.psi x-Chebyshev.theta x)-(Chebyshev.psi (x+x^θ)-Chebyshev.theta (x+x^θ)) by ring]
  apply (abs_sub _ _).trans
  change |Chebyshev.psi x-Chebyshev.theta x|+|Chebyshev.psi (x+x^θ)-Chebyshev.theta (x+x^θ)|≤_
  change _≤C*√(x+x^θ) at hl; change _≤C*√x at hr
  nlinarith only [hl,hr,mul_le_mul_of_nonneg_left hroot hC]

/-- A short-interval asymptotic for ψ implies the corresponding
short-interval asymptotic for θ. -/
theorem theta_shortInterval_of_psi_equivalent {θ : ℝ} (hθ : 1/2<θ) (hθ' : θ≤1)
    (hp : (fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ~[atTop] fun x : ℝ => x^θ) :
    (fun x : ℝ => Chebyshev.theta (x+x^θ)-Chebyshev.theta x) ~[atTop] fun x : ℝ => x^θ := by
  exact (hp.add_isLittleO (shortInterval_theta_sub_psi_isLittleO hθ hθ')).congr_left
    (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)

/-- An eventual lower bound for ψ in power-length intervals gives a
lower bound for θ with half the original constant. -/
theorem eventually_theta_interval_lower_of_psi {θ c : ℝ} (hθ : 1/2<θ) (hθ' : θ≤1) (hc : 0<c)
    (hp : ∀ᶠ x : ℝ in atTop, c*x^θ≤Chebyshev.psi (x+x^θ)-Chebyshev.psi x) :
    ∀ᶠ x : ℝ in atTop, (c/2)*x^θ≤Chebyshev.theta (x+x^θ)-Chebyshev.theta x := by
  filter_upwards [hp,(shortInterval_theta_sub_psi_isLittleO hθ hθ').bound (show 0<c/2 by positivity),
    eventually_gt_atTop (0:ℝ)] with x hpx h hx
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg hx.le θ)] at h
  linarith [(abs_le.mp h).1]

/-- Quantitative transfer from ψ to prime counting in power-length
intervals, with endpoints interpreted using natural floors. -/
theorem eventually_primePi_interval_lower_of_psi {θ c : ℝ} (hθ : 1/2<θ) (hθ' : θ≤1) (hc : 0<c)
    (hp : ∀ᶠ x : ℝ in atTop, c*x^θ≤Chebyshev.psi (x+x^θ)-Chebyshev.psi x) :
    ∀ᶠ x : ℝ in atTop, (c/4)*x^θ/log x ≤ primePi (x+x^θ)-primePi x := by
  filter_upwards [eventually_theta_interval_lower_of_psi hθ hθ' hc hp,eventually_ge_atTop (2:ℝ)] with x hx h2
  have hx' : 0<x := by linarith
  have hpow : 0≤x^θ := Real.rpow_nonneg hx'.le _
  have hxy : x≤x+x^θ := by linarith
  have he := (theta_interval_primePi_comparison hx' hxy).2
  have hπ : 0≤primePi (x+x^θ)-primePi x := by rw [(intervalPrimeSet_formulas hxy).2]; positivity
  have hu := Real.rpow_le_rpow_of_exponent_le (show 1≤x by linarith) hθ'
  rw [Real.rpow_one] at hu
  have hl := Real.log_le_log (hx'.trans_le hxy) (show x+x^θ≤2*x by linarith)
  rw [Real.log_mul (by norm_num) hx'.ne'] at hl
  have hlog := Real.log_le_log (show (0:ℝ)<2 by norm_num) h2
  rw [div_le_iff₀ (Real.log_pos (by linarith))]
  nlinarith only [hx,he,mul_le_mul_of_nonneg_left (show log (x+x^θ)≤2*log x by linarith) hπ]

/-- An eventual positive-proportion lower bound for the ψ increment gives
a prime in every sufficiently large power-length interval. -/
theorem eventually_exists_prime_interval_of_psi_lower {θ c : ℝ} (hθ : 1/2<θ) (hθ' : θ≤1) (hc : 0<c)
    (hp : ∀ᶠ x : ℝ in atTop, c*x^θ≤Chebyshev.psi (x+x^θ)-Chebyshev.psi x) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤x+x^θ := by
  filter_upwards [eventually_primePi_interval_lower_of_psi hθ hθ' hc hp,eventually_gt_atTop (1:ℝ)] with x hh hx
  have hxp : 0<x := zero_lt_one.trans hx
  have hxy : x≤x+x^θ := by exact le_add_of_nonneg_right (Real.rpow_nonneg hxp.le _)
  rw [(intervalPrimeSet_formulas hxy).2] at hh
  have hpos : 0<((intervalPrimeSet x (x+x^θ)).card:ℝ) := lt_of_lt_of_le (by positivity [Real.log_pos hx]) hh
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
  exact ⟨p,intervalPrimeSet_mem hxp.le hxy hp⟩

/-- A short-interval asymptotic for θ gives the prime-counting asymptotic
with main term equal to the interval length divided by log x. -/
theorem primePi_shortInterval_of_theta_equivalent {θ : ℝ} (hθ : θ≤1)
    (hp : (fun x : ℝ => Chebyshev.theta (x+x^θ)-Chebyshev.theta x) ~[atTop] fun x : ℝ => x^θ) :
    (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] fun x : ℝ => x^θ/log x := by
  let A (x : ℝ) := (Chebyshev.theta (x+x^θ)-Chebyshev.theta x)/x^θ
  let L (x : ℝ) := log (x+x^θ)/log x
  have hA : Tendsto A atTop (𝓝 1) := (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact (Real.rpow_pos_of_pos hx θ).ne')).mp hp
  have hL : Tendsto L atTop (𝓝 1) := by
    have hsmall := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (log 2)
    have hu : Tendsto (fun x : ℝ => 1+log 2*(log x)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hsmall
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      dsimp only [L]; rw [one_le_div (Real.log_pos hx)]
      exact Real.log_le_log (zero_lt_one.trans hx) (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _))
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
      dsimp only [L]; rw [div_le_iff₀ (Real.log_pos hx)]
      have hy := Real.rpow_le_rpow_of_exponent_le hx.le hθ
      rw [Real.rpow_one] at hy
      have hl := Real.log_le_log (show 0<x+x^θ by positivity [zero_lt_one.trans hx])
          (show x+x^θ≤2*x by linarith)
      rw [Real.log_mul (by norm_num) (zero_lt_one.trans hx).ne'] at hl
      rw [add_mul,one_mul,mul_assoc,inv_mul_cancel₀ (Real.log_pos hx).ne',mul_one]
      linarith
  apply isEquivalent_of_tendsto_one
  have hlow : Tendsto (A/L) atTop (𝓝 1) := by simpa using hA.div hL one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hA
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    let y := x+x^θ
    have hxp := zero_lt_one.trans hx
    have hxy : x≤y := le_add_of_nonneg_right (Real.rpow_nonneg hxp.le _)
    have hl : 0<log x := Real.log_pos hx
    have hl' : 0<log y := Real.log_pos (hx.trans_le hxy)
    have hp' := (div_le_iff₀ hl').mpr (theta_interval_primePi_comparison hxp hxy).2
    change ((Chebyshev.theta y-Chebyshev.theta x)/x^θ)/(log y/log x) ≤ (primePi y-primePi x)/(x^θ/log x)
    calc _ = ((Chebyshev.theta y-Chebyshev.theta x)/log y)*log x/x^θ := by
              simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
         _ ≤ (primePi y-primePi x)*log x/x^θ := by gcongr
         _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    let y := x+x^θ
    have hxp := zero_lt_one.trans hx
    have hxy : x≤y := le_add_of_nonneg_right (Real.rpow_nonneg hxp.le _)
    change (primePi y-primePi x)/(x^θ/log x) ≤ (Chebyshev.theta y-Chebyshev.theta x)/x^θ
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (theta_interval_primePi_comparison hxp hxy).1 (Real.rpow_nonneg hxp.le _)

end AnalyticNumberTheory.PrimeDistribution
