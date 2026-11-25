import AnalyticNumberTheory.SieveMethods.PrimePairSelberg
import AnalyticNumberTheory.SieveMethods.PrimePairMainTerm

/-!
# The coefficient eight in the prime-pair sieve

The finite Selberg error is accumulated over squarefree moduli up to the
square of the sieve limit. A saving of three logarithms absorbs this error
and the complementary primes at or below the sieve limit.
-/

noncomputable section
open Finset Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution

/-- The coefficient eight from a divisor-weighted progression error of order x/log³x. -/
theorem primePair_eight_of_error {B K : ℝ} (hB : 0≤B) (hK : 0<K)
    (hE : ∀ᶠ x : ℝ in atTop,
      ∑d∈(Icc 1 ⌊√x/(log x)^B⌋₊).filter Squarefree,(d.divisors.card:ℝ)^2*maximalPiAPError x d
        ≤ K*x/(log x)^3) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {h : ℤ}, Even h.natAbs → h.natAbs≠0 →
      (primePairCount x h:ℝ)≤8*primePairSingularFactor h.natAbs*(x/(log x)^2)*
        (1+C*(log (log x)/log x)) := by
  obtain ⟨A,hA,HA⟩ := primePair_selberg_mainTerm hB
  let b := (K+3)/(8*twinPrimeEulerConstant)
  have hC2 := twinPrimeEulerConstant_pos
  have hb : 0<b := div_pos (by linarith) (by positivity)
  refine ⟨A+b,by positivity,?_⟩
  have hs := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1/2)).bound zero_lt_one
  filter_upwards [HA,hE,hs,Real.tendsto_log_atTop.eventually_ge_atTop (exp 1),eventually_ge_atTop (2:ℝ)] with x hM hE hsmall hlog hx
  obtain ⟨hz,hzx,hzsq,hmain⟩ := hM
  intro h hh hh0
  let z := primePairSieveLimit B x
  let S := primePairSingularFactor h.natAbs
  let l := log x
  let m := log l
  have hx0 : 0<x := by linarith
  have hl : 0<l := Real.log_pos (by linarith)
  have hm : 1≤m := (Real.le_log_iff_exp_le hl).mpr hlog
  have hS : twinPrimeEulerConstant≤S := twinPrimeEulerConstant_le_primePairSingularFactor _
  have hsqrt : 1≤√x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogs : l^3≤√x := by
    change ‖(log x)^(3:ℝ)‖≤1*‖x^(1/2:ℝ)‖ at hsmall
    simpa only [Real.rpow_ofNat,←Real.sqrt_eq_rpow,Real.norm_of_nonneg (pow_nonneg hl.le 3),
      Real.norm_of_nonneg (Real.sqrt_nonneg x),one_mul,l] using hsmall
  have hcost : 2*z+1≤3*x/l^3 := by
    apply (le_div_iff₀ (pow_pos hl _)).mpr
    calc (2*z+1)*l^3 ≤ (3*√x)*√x := mul_le_mul (by linarith only [hzx,hsqrt]) hlogs (pow_nonneg hl.le 3) (by positivity)
         _ = 3*x := by nlinarith only [Real.sq_sqrt hx0.le]
  have h8 : K+3≤8*S*b*m := by
    have he : 8*twinPrimeEulerConstant*b=K+3 := by dsimp [b];field_simp
    calc _ = 8*twinPrimeEulerConstant*b := he.symm
         _ ≤ 8*S*b := by gcongr
         _ ≤ _ := le_mul_of_one_le_right (by positivity [hC2.trans_le hS]) hm
  have he : (K+3)*(x/l^3)≤(8*S*(x/l^2))*(b*(m/l)) := by
    convert mul_le_mul_of_nonneg_right h8 (div_nonneg hx0.le (pow_nonneg hl.le 3)) using 1 <;> ring
  have H := primePairCount_selberg hh hh0 hx (show 1≤z by linarith only [hz])
  rw [hzsq] at H
  calc (primePairCount x h:ℝ) ≤ 2*z+1+logIntegral x/primePairDenominator h.natAbs z+
        ∑d∈(Icc 1 ⌊√x/(log x)^B⌋₊).filter Squarefree,(d.divisors.card:ℝ)^2*maximalPiAPError x d := H
       _ ≤ 3*x/l^3 + (8*S*(x/l^2)*(1+A*(m/l))) + K*x/l^3 :=
         add_le_add (add_le_add hcost (hmain hh0)) hE
       _ = (8*S*(x/l^2)*(1+A*(m/l)))+(K+3)*(x/l^3) := by ring
       _ ≤ (8*S*(x/l^2)*(1+A*(m/l)))+(8*S*(x/l^2))*(b*(m/l)) := add_le_add le_rfl he
       _ = _ := by change _ = 8*S*(x/l^2)*(1+(A+b)*(m/l));ring

/-- Specialization of the shifted count to the usual twin-prime counting function. -/
theorem primePairCount_neg_two (x : ℝ) : (primePairCount x (-2):ℝ)=selbergTwinCount x := by
  have hshift (p : ℕ) : primeShift (-2) p=p+2 := by
    change ((p:ℤ)-(-2)).natAbs=_
    rw [show (p:ℤ)-(-2)=((p+2:ℕ):ℤ) by push_cast;ring]
    rfl
  simp [primePairCount,primeFinset,Nat.primesLE_eq_filter_Icc_one,filter_filter,hshift,selbergTwinCount]

/-- Specialization to the ordered binary Goldbach count. -/
theorem primePairCount_at_shift (N : ℕ) : primePairCount N N=goldbachRepCount N := by
  simp only [primePairCount,primeFinset,Nat.floor_natCast,Nat.primesLE_eq_filter_Icc_one,filter_filter,goldbachRepCount]
  congr 1
  ext p
  simp only [mem_filter,mem_Icc]
  by_cases hp : p≤N
  · have he : primeShift (N:ℤ) p=N-p := by
      change ((p:ℤ)-N).natAbs=_
      rw [show (p:ℤ)-N= -((N-p:ℕ):ℤ) by rw [Nat.cast_sub hp];ring,Int.natAbs_neg];rfl
    rw [he]
  · simp [hp]

end AnalyticNumberTheory.SieveMethods
