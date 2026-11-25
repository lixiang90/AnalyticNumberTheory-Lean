import AnalyticNumberTheory.SieveMethods.BrunTitchmarshFinite
import AnalyticNumberTheory.SieveMethods.BrunTitchmarshLargeRange
import AnalyticNumberTheory.SieveMethods.WeightedRoughSieve
import AnalyticNumberTheory.SieveMethods.SelbergEffectiveLower

/-! # The Brun–Titchmarsh theorem on every interval

The finite wheel covers the small interval-to-modulus ratios. The weighted
large sieve and its explicit denominator cover the remaining ratios.
-/
open Real Finset
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- Brun–Titchmarsh, uniformly for every modulus, residue, and real interval
(x, x+y] with x ≥ 0 and y > q. -/
theorem brun_titchmarsh_two {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hq : 1≤q) (hy : (q:ℝ)<y) :
    piAP (x+y) q a-piAP x q a ≤ 2*y/(q.totient*log (y/(q:ℝ))) := by
  let u := y/(q:ℝ)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hu : 1<u := (one_lt_div hq').2 hy
  by_cases hsmall : u≤20000
  · exact brun_titchmarsh_two_finite hx hq hu hsmall
  have hlarge : 16000≤u := by linarith
  let N := ⌈u⌉₊
  let z := (5/6:ℝ)*sqrt N
  have hlo : u≤(N:ℝ) := Nat.le_ceil _
  have hhi : (N:ℝ)≤u+1 := (Nat.ceil_lt_add_one (zero_lt_one.trans hu).le).le
  have hN := hlarge.trans hlo
  have hN₀ : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hroot : 120≤sqrt N := Real.le_sqrt_of_sq_le (by linarith only [hN])
  have hz : 100≤z := by dsimp [z]; linarith
  have hz' : 1≤z := by linarith
  have hl : 0<log z+31/100 := by linarith [Real.log_nonneg hz']
  have hcost : weightedHilbertConstant/π ≤ 36/25 := (div_le_iff₀ pi_pos).2
    (by linarith only [weightedHilbertConstant_lt,Real.pi_gt_d2])
  have hscale : weightedHilbertConstant/π*z^2≤(N:ℝ) := by
    apply (mul_le_mul_of_nonneg_right hcost (sq_nonneg z)).trans_eq
    dsimp only [z]
    rw [mul_pow,Real.sq_sqrt hN₀]
    ring
  have hd := selbergWeightedDenominator_ge_log hz
  rw [show (0.31:ℝ)=31/100 by norm_num] at hd
  have hblock := brun_titchmarsh_of_rough_block (a:=a) hx (hq'.trans hy) hq z ((N:ℝ)/(log z+31/100)) (by
    intro m T hT hr
    apply (le_div_iff₀ hl).2
    exact (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg T.card)).trans
      (card_rough_mul_weighted_denominator hz' hscale T hT
        (fun n hn p hp hpz => hr n hn p hp.one_lt hpz)))
  have hnum := brun_titchmarsh_large_range_numeric hlarge hlo hhi
  have H := hblock.trans (mul_le_mul_of_nonneg_left hnum hq'.le)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0<log u := Real.log_pos hu
  have he : (q:ℝ)*u=y := by dsimp [u]; field_simp
  apply (le_div_iff₀ (mul_pos hφ hlog)).mpr
  rw [←mul_assoc]
  apply (mul_le_mul_of_nonneg_right H hlog.le).trans_eq
  change (q:ℝ)*(2*u/log u)*log u=2*y
  field_simp [hlog.ne']
  linarith only [he]

/-- The interval prime-counting bound obtained at modulus one. -/
theorem brun_titchmarsh_primeCounting {x y : ℝ} (hx : 0≤x) (hy : 1<y) :
    (Nat.primeCounting ⌊x+y⌋₊:ℝ) - Nat.primeCounting ⌊x⌋₊ ≤ 2*y/log y := by
  have eqPi (t : ℝ) : piAP t 1 0=(Nat.primeCounting ⌊t⌋₊:ℝ) := by
    rw [←Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_Icc_one]
    simp [piAP,primeCountingAP,Nat.modEq_one]
  simpa only [eqPi,Nat.totient_one,Nat.cast_one,div_one,one_mul] using
    brun_titchmarsh_two (a:=0) hx (q:=1) (by decide) (by simpa using hy)

end AnalyticNumberTheory.SieveMethods
