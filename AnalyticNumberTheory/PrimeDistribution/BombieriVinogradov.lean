import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovReduction
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovTypeI
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovTypeII

/-!
# Bombieri–Vinogradov

The conductor split combines Siegel–Walfisz for the small conductors with
Vaughan's identity and the multiplicative large sieve for the large conductors.
-/

noncomputable section

open Finset
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

private theorem largeConductor_psiChar_le {x Q R : ℝ} (hx : 2 ≤ x) (hQ : 1 ≤ Q) (hQx : Q ≤ x)
    (hR : 1 ≤ R) {U : ℕ} (hU : 1 ≤ U) :
    ∑ q ∈ Ioc ⌊R⌋₊ ⌊Q⌋₊, (q.totient : ℝ)⁻¹ *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), ‖psiChar x χ‖ ≤
      4 * Q^2 * (U:ℝ)^2 * Real.log x +
        4096 * (1+Real.log x)^7 * (x/R + Q*Real.sqrt x + x/Real.sqrt U) := by
  let T := vaughanTypeIICharacter ⌊x⌋₊ U
  let D := Ioc ⌊R⌋₊ ⌊Q⌋₊
  let P (q : ℕ) := (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive)
  have hX : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hQ' := (Nat.one_le_floor_iff _).mpr hQ
  have hR' := (Nat.one_le_floor_iff _).mpr hR
  have htri (q : ℕ) (χ : DirichletCharacter ℂ q) : ‖psiChar x χ‖ ≤ ‖psiChar x χ-T q χ‖ + ‖T q χ‖ :=
    by simpa only [sub_add_cancel] using norm_add_le (psiChar x χ-T q χ) (T q χ)
  have hs := calc
    (∑ q ∈ D, (q.totient:ℝ)⁻¹ * ∑ χ ∈ P q, ‖psiChar x χ‖) ≤
      ∑ q ∈ D, (q.totient:ℝ)⁻¹ * ∑ χ ∈ P q, (‖psiChar x χ-T q χ‖ + ‖T q χ‖) := by
        gcongr with q _ χ _
        exact htri q χ
    _ = (∑ q ∈ D, (q.totient:ℝ)⁻¹ * ∑ χ ∈ P q, ‖psiChar x χ-T q χ‖) +
        ∑ q ∈ D, (q.totient:ℝ)⁻¹ * ∑ χ ∈ P q, ‖T q χ‖ := by simp_rw [sum_add_distrib, mul_add, sum_add_distrib]
  have hi := sum_primitive_psiChar_sub_vaughanTypeII_le (Q:=⌊Q⌋₊) hR' hU hx
  have hii := sum_largeConductor_vaughanTypeII_le hX hU hQ' (by linarith : 0 < R)
  have hset : (Icc 2 ⌊Q⌋₊).filter (fun q : ℕ => R < (q:ℝ)) = D := by
    ext q
    simp only [D, mem_filter, mem_Icc, mem_Ioc, Nat.floor_lt (by linarith : 0 ≤ R)]
    constructor
    · rintro ⟨⟨_, hq⟩, hr⟩; exact ⟨hr,hq⟩
    · rintro ⟨hr,hq⟩
      have hqr : (1 : ℝ) < q := hR.trans_lt hr
      exact ⟨⟨by exact_mod_cast hqr, hq⟩, hr⟩
  rw [hset] at hii
  apply (hs.trans (add_le_add hi hii)).trans
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfq : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogq := Real.log_nonneg (by exact_mod_cast hQ' : (1:ℝ) ≤ ⌊Q⌋₊)
  have hlogX := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ) ≤ ⌊x⌋₊)
  have hLq : Real.log (⌊Q⌋₊:ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast hQ') (hfq.trans hQx)
  have hLX : Real.log (⌊x⌋₊:ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast hX) hfx
  rw [show 4096*(1+Real.log x)^7 = 4096*(1+Real.log x)*(1+Real.log x)^6 by ring]
  gcongr

private lemma absorb_vaughan {l x Q : ℝ} (hl : 1 ≤ l) (hx : 0 ≤ x) (hq : 0 ≤ Q)
    (k : ℕ) (U : ℕ) (hU : l^(k+8) ≤ Real.sqrt U) (hUb : (U : ℝ) ≤ 2*(l^(k+8))^2)
    (hQ : Q ≤ Real.sqrt x / (l^(k+8))^3) :
    4 * Q^2 * (U:ℝ)^2 * l +
      4096*(1+l)^7*(x/l^(k+8) + Q*Real.sqrt x + x/Real.sqrt U) ≤
      1572880 * x/l^k := by
  let r := l^(k+8)
  have hl0 : 0 < l := by linarith
  have hr : 1 ≤ r := one_le_pow₀ hl
  have hr0 : 0 < r := by linarith
  have hk : 0 < l^k := by positivity
  have hsr : 0 < Real.sqrt U := hr0.trans_le hU
  have hterm : Q * Real.sqrt x ≤ x / r := by
    calc
      _ ≤ (Real.sqrt x / r^3) * Real.sqrt x := mul_le_mul_of_nonneg_right hQ (Real.sqrt_nonneg x)
      _ = x / r^3 := by rw [div_mul_eq_mul_div, Real.mul_self_sqrt hx]
      _ ≤ _ := div_le_div_of_nonneg_left hx hr0 (by nlinarith [pow_le_pow_right₀ hr (by decide : 1 ≤ 3)])
  have hwide : x/Real.sqrt U ≤ x/r := div_le_div_of_nonneg_left hx hr0 hU
  have hpoly : l^7 * (x/r) ≤ x/l^k := by
    rw [← mul_div_assoc, div_le_div_iff₀ hr0 hk]
    dsimp only [r]
    rw [pow_add]
    have hs : l^7 ≤ l^8 := pow_le_pow_right₀ hl (by decide)
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hk.le) hx]
  have hlong : 4096*(1+l)^7*(x/r + Q*Real.sqrt x + x/Real.sqrt U) ≤ 1572864 * x/l^k := by
    calc
      _ ≤ 4096*(2*l)^7*(x/r + x/r + x/r) := by gcongr; linarith
      _ = 1572864 * (l^7*(x/r)) := by ring
      _ ≤ _ := by rw [mul_div_assoc]; gcongr
  have hsmall : 4*Q^2*(U:ℝ)^2*l ≤ 16*x/l^k := by
    calc
      _ ≤ 4*(Real.sqrt x/r^3)^2*(2*r^2)^2*l := by gcongr
      _ = 16*x*l/r^2 := by rw [div_pow, Real.sq_sqrt hx]; field_simp [hr0.ne']; ring
      _ ≤ _ := by
        rw [div_le_div_iff₀ (by positivity) hk]
        have hm : l * l^k ≤ r^2 := by
          calc
            _ = l^(k+1) := by ring
            _ ≤ r := pow_le_pow_right₀ hl (by omega)
            _ ≤ _ := by nlinarith
        nlinarith only [mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : 0 ≤ (16:ℝ)) hx)]
  change 4*Q^2*(U:ℝ)^2*l + 4096*(1+l)^7*(x/r + Q*Real.sqrt x + x/Real.sqrt U) ≤ _
  exact (add_le_add hsmall hlong).trans_eq (by ring)

/-- Logarithmic savings for the primitive-character mean up to the level of distribution. -/
theorem bombieriVinogradov_primitive_mean_large_x (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Real.log x → 1 ≤ Q →
      Q ≤ x^(1/2 : ℝ)/Real.log x^B →
      ∑ q ∈ Icc 2 ⌊Q⌋₊, (q.totient:ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), ‖psiChar x χ‖ ≤
        C*x/Real.log x^A := by
  let k := ⌈A⌉₊
  let e := k+8
  obtain ⟨C, hC, hsmall⟩ := sum_smallConductor_psiChar_le A (show 0 ≤ (e:ℝ) by positivity)
  refine ⟨(e*3:ℕ), by positivity, C+1572880, by positivity, ?_⟩
  intro x Q hx hl hq hQ
  let l := Real.log x
  let r := l^e
  let U := ⌈r^2⌉₊
  have hl0 : 0 < l := by change 1 ≤ l at hl; linarith
  have hr : 1 ≤ r := one_le_pow₀ hl
  have hr0 : 0 < r := by linarith
  have hU0 : r^2 ≤ (U:ℝ) := Nat.le_ceil _
  have hU1 : 1 ≤ U := by exact_mod_cast (show (1:ℝ) ≤ U by nlinarith)
  have hU2 : (U:ℝ) ≤ 2*r^2 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ r^2)
    change (U:ℝ) < r^2+1 at h
    nlinarith
  have hU : r ≤ Real.sqrt U := by
    calc r = Real.sqrt (r^2) := (Real.sqrt_sq hr0.le).symm
         _ ≤ _ := Real.sqrt_le_sqrt hU0
  have hQ' : Q ≤ Real.sqrt x/r^3 := by
    simpa only [Real.rpow_natCast, pow_mul, ← Real.sqrt_eq_rpow, r, l] using hQ
  have hQx : Q ≤ x := hQ'.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hr)).trans
    (Real.sqrt_le_self_iff.mpr (.inr (by linarith))))
  have hlarge := largeConductor_psiChar_le hx hq hQx hr hU1
  have hnum := absorb_vaughan hl (by linarith : 0 ≤ x) (by linarith : 0 ≤ Q) k U hU hU2 hQ'
  have hs := hsmall (Q:=Q) hx hl
  have he : Real.log x^(e:ℝ) = r := by rw [Real.rpow_natCast]
  rw [he] at hs
  let E (q : ℕ) := (q.totient:ℝ)⁻¹ * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
    (·.IsPrimitive), ‖psiChar x χ‖
  have hsplit : ∑ q ∈ Icc 2 ⌊Q⌋₊, E q =
      (∑ q ∈ Icc 2 ⌊min Q r⌋₊, E q) + ∑ q ∈ Ioc ⌊r⌋₊ ⌊Q⌋₊, E q := by
    have hh := sum_filter_add_sum_filter_not (Icc 2 ⌊Q⌋₊) (fun q => q ≤ ⌊r⌋₊) E
    have hfl : ⌊min Q r⌋₊ = min ⌊Q⌋₊ ⌊r⌋₊ := Nat.floor_mono.map_min
    have hfloor := (Nat.one_le_floor_iff _).mpr hr
    have h₁ : (Icc 2 ⌊Q⌋₊).filter (fun q => q ≤ ⌊r⌋₊) = Icc 2 ⌊min Q r⌋₊ := by
      ext q; simp only [mem_filter,mem_Icc,hfl,le_min_iff]; tauto
    have h₂ : (Icc 2 ⌊Q⌋₊).filter (fun q => ¬q ≤ ⌊r⌋₊) = Ioc ⌊r⌋₊ ⌊Q⌋₊ := by
      ext q; simp only [mem_filter,mem_Icc,mem_Ioc]; omega
    rwa [h₁,h₂,eq_comm] at hh
  change (∑ q ∈ Icc 2 ⌊Q⌋₊, E q) ≤ _
  rw [hsplit]
  apply (add_le_add hs (hlarge.trans hnum)).trans
  have hpow : l^A ≤ l^k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (Nat.le_ceil _)
  calc
    _ ≤ C*x/l^A + 1572880*x/l^A := by gcongr
    _ = _ := by ring

/-- The Bombieri–Vinogradov theorem for arithmetic progressions, uniformly
for every fixed endpoint `x ≥ 2` and `Q ≤ sqrt x / (log x)^B`. -/
theorem bombieriVinogradov : BombieriVinogradovStatement :=
  bombieriVinogradov_of_large_x_primitive_mean bombieriVinogradov_primitive_mean_large_x

/-- The corresponding unconditional average bound for the prime-weighted function `θ`. -/
theorem bombieriVinogradov_theta :
    ∀ A : ℝ, ∃ B C : ℝ, 0 < C ∧ ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maxThetaAPError x q ≤ C*x/Real.log x^A :=
  bombieriVinogradov_thetaAP bombieriVinogradov

end AnalyticNumberTheory.PrimeDistribution
