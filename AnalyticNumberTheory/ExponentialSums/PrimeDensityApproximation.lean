import AnalyticNumberTheory.ExponentialSums.PrimeSumsFromDensity
import AnalyticNumberTheory.ExponentialSums.PrimeDensityScale
import AnalyticNumberTheory.AdditiveNumberTheory.RationalRefinement

/-! # Zero-density estimates at real linear frequencies -/

noncomputable section

open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- A common bound on initial prime sums transports to a nearby frequency,
at a cost of at most `1+2πx|β|`, also for nonintegral endpoints. -/
theorem norm_primeExpSum_shift_of_bound {x D α : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (H : ∀ t ∈ Set.Icc 0 x, ‖primeExpSum t α‖ ≤ D) (β : ℝ) :
    ‖primeExpSum x (α+β)‖ ≤ D * (1 + 2 * Real.pi * x * |β|) := by
  let N := ⌊x⌋₊
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx
  have step (k : ℕ) (hk : k ∈ Icc 1 N) : ‖primeExpSum k α - (0 : ℂ)*k‖ ≤ D := by
    rw [zero_mul, sub_zero]
    exact H k ⟨Nat.cast_nonneg _, (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans hN⟩
  have h := norm_primeExpSum_shift_sub_main_le (α := α) (β := β) hD step
  have he (t : ℝ) : primeExpSum N t = primeExpSum x t := by simp only [primeExpSum, Nat.floor_natCast, N]
  rw [zero_mul, sub_zero, he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (by positivity)) (abs_nonneg β)) _) hD)

/-- The zero-density proof of the four-term linear prime exponential-sum
estimate near a reduced rational. All real endpoints between `0` and `x`
share the same majorant. -/
theorem primeExpSum_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x y : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 4 ≤ x → 0 ≤ y → y ≤ x →
      ‖primeExpSum y α‖ ≤ C * densityPrimeScale x q * (1 + Real.log x)^11 := by
  obtain ⟨C, hC, rational⟩ := primeExpSum_rational_zero_density
  let K := C * (1 + 4 * Real.pi)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨max 6 (3*K), (by norm_num : (0 : ℝ) < 6).trans_le (le_max_left ..), ?_⟩
  intro a q α x y hq ha hα hx hy hyx
  let L := 1 + Real.log x
  let V := densityPrimeScale x q
  let R (s : ℕ) := x / Real.sqrt s + x ^ (4/5 : ℝ) * (s : ℝ) ^ (1/10 : ℝ) + Real.sqrt (x*s)
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ := zero_lt_one.trans_le hq₁
  have hx₀ : 0 < x := by linarith
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ x)]
  have hR (s) : 0 ≤ R s := by dsimp only [R]; positivity
  have hV : 0 ≤ V := (Real.sqrt_nonneg _).trans (sqrt_mul_le_densityPrimeScale hx₀.le hq₀.le)
  have hlogpow := one_le_pow₀ hL (n := 11)
  change ‖primeExpSum y α‖ ≤ max 6 (3*K) * V * L^11
  by_cases hqx : (q : ℝ) ≤ x
  swap
  · have hsq : x ≤ Real.sqrt (x*q) := (Real.le_sqrt hx₀.le (mul_nonneg hx₀.le hq₀.le)).mpr
      (by nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hqx) hx₀.le])
    have hbound := hyx.trans (hsq.trans (sqrt_mul_le_densityPrimeScale hx₀.le hq₀.le))
    exact (norm_primeExpSum_le hy α).trans ((mul_le_mul (le_max_left ..) hbound hy
      (by positivity)).trans (le_mul_of_one_le_right (by positivity) hlogpow))
  have narrow {s : ℕ} [NeZero s] {b : ℤ} (hb : b.natAbs.Coprime s) (hsx : (s : ℝ) ≤ x)
      (hβ : x * |α - (b : ℝ)/s| ≤ 2) (hscale : R s ≤ 3*V) : ‖primeExpSum y α‖ ≤ max 6 (3*K) * V * L^11 := by
    let β := α - (b : ℝ)/s
    have hmain : 0 ≤ C * R s * L^11 := by positivity [hR s]
    have h := norm_primeExpSum_shift_of_bound (α := (b : ℝ)/s) hy hmain
      (fun t ht => rational hb hx hsx ht.1 (ht.2.trans hyx)) β
    rw [show (b : ℝ)/s + β = α by dsimp [β]; ring] at h
    have hβy : y * |β| ≤ 2 := (mul_le_mul_of_nonneg_right hyx (abs_nonneg β)).trans hβ
    have hfactor : 1 + 2 * Real.pi * y * |β| ≤ 1 + 4 * Real.pi := by
      nlinarith only [mul_le_mul_of_nonneg_left hβy Real.pi_pos.le]
    calc
      _ ≤ (C * R s * L^11) * (1 + 4 * Real.pi) := h.trans (mul_le_mul_of_nonneg_left hfactor hmain)
      _ = K * R s * L^11 := by dsimp only [K]; ring
      _ ≤ K * (3*V) * L^11 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hK.le) (by positivity)
      _ = (3*K) * V * L^11 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hV) (by positivity)
  have hextra := div_nonneg (Real.rpow_nonneg hx₀.le (9/10)) (Real.rpow_nonneg hq₀.le (1/10))
  by_cases hnear : x * |α - (a : ℝ)/q| ≤ 2
  · let _ : NeZero q := ⟨by omega⟩
    apply narrow ha hqx hnear
    have hRV : R q ≤ V := le_add_of_nonneg_right hextra
    linarith
  · obtain ⟨b, r, hr, hb, hrlo, hrhi, hrap⟩ := exists_narrow_rational_approximation hx₀ hq ha hα (lt_of_not_ge hnear)
    let _ : NeZero r := ⟨by omega⟩
    apply narrow hb (hrhi.trans (div_le_self hx₀.le hq₁)) hrap.le
    have hs := rational_density_scale_of_refinement hx₀ hq₀ hrlo.le ((le_div_iff₀ hq₀).mp hrhi)
    apply hs.trans
    change 3*x/Real.sqrt q + x^(9/10 : ℝ)/(q : ℝ)^(1/10 : ℝ) ≤ 3*densityPrimeScale x q
    unfold densityPrimeScale
    rw [mul_div_assoc]
    linarith only [hextra, Real.sqrt_nonneg (x*q),
      mul_nonneg (Real.rpow_nonneg hx₀.le (4/5)) (Real.rpow_nonneg hq₀.le (1/10))]

end AnalyticNumberTheory.ExponentialSums
