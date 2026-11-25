import AnalyticNumberTheory.SieveMethods.SelbergWeightMeans
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A numerical lower bound for the Selberg denominator constant

The harmonic number H₃₁ bounds Euler's constant from below. The local
contributions from primes through 31 suffice for a positive second-order
saving over the Brun–Titchmarsh coefficient two.
-/

open Real Finset
namespace AnalyticNumberTheory.SieveMethods

private theorem log_lower_of_power {p k : ℕ} (hp : 0<p) (h : 2^k≤p^12) :
    (693:ℝ)*k/12000 ≤ log p := by
  have hh : (2:ℝ)^k≤(p:ℝ)^12 := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity : 0<(2:ℝ)^k) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (show 0≤Real.log 2-693/1000 by linarith [Real.log_two_gt_d9])]

/-- The harmonic sum through 31 gives a lower bound of 0.56 for Euler’s constant. -/
theorem euler_constant_gt_56 : 56/100 < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  rw [Real.eulerMascheroniSeq] at h
  norm_num only [Nat.cast_ofNat,show (31:ℝ)+1=2^5 by norm_num, Real.log_pow, Nat.cast_ofNat] at h
  norm_num [harmonic_succ,harmonic_zero] at h
  rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 800000 in
/-- The explicit Selberg denominator constant exceeds 1.28. -/
theorem selbergDenominatorConstant_gt : 128/100 < selbergDenominatorConstant := by
  let P : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,31}
  have hP : ∀p∈P, Nat.Prime p := by decide
  let e : P ↪ Nat.Primes := ⟨fun p => ⟨p.val,hP p.val p.prop⟩,fun _ _ h => Subtype.ext (congrArg (fun x : Nat.Primes => x.val) h)⟩
  let g (p : ℕ) := Real.log p/((p:ℝ)*(p-1))
  let f (p : Nat.Primes) := Real.log p.val/((p.val:ℝ)*(p.val-1))
  have hf : Summable f := by
    have h := hasSum_selbergNormalizedCoefficient_log.summable.neg
    simpa [f,neg_div] using h
  have hpos (p : Nat.Primes) : 0≤f p := by
    have hp : (1:ℝ)≤p.val := by exact_mod_cast p.prop.one_lt.le
    exact div_nonneg (log_nonneg hp) (mul_nonneg (by positivity) (by linarith))
  have hsum := hf.sum_le_tsum (Finset.univ.map e) (fun p _ => hpos p)
  rw [Finset.sum_map] at hsum
  change ∑p : P,g p ≤ ∑' p : Nat.Primes,f p at hsum
  rw [Finset.univ_eq_attach,Finset.sum_attach P g] at hsum
  have hfinite : (72:ℝ)/100<∑p∈P,g p := by
    dsimp only [P]
    simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton]
    dsimp [g]
    have h2 := log_lower_of_power (p:=2) (k:=12) (by norm_num) (by norm_num)
    have h3 := log_lower_of_power (p:=3) (k:=19) (by norm_num) (by norm_num)
    have h5 := log_lower_of_power (p:=5) (k:=27) (by norm_num) (by norm_num)
    have h7 := log_lower_of_power (p:=7) (k:=33) (by norm_num) (by norm_num)
    have h11 := log_lower_of_power (p:=11) (k:=41) (by norm_num) (by norm_num)
    have h13 := log_lower_of_power (p:=13) (k:=44) (by norm_num) (by norm_num)
    have h17 := log_lower_of_power (p:=17) (k:=49) (by norm_num) (by norm_num)
    have h19 := log_lower_of_power (p:=19) (k:=50) (by norm_num) (by norm_num)
    have h23 := log_lower_of_power (p:=23) (k:=54) (by norm_num) (by norm_num)
    have h29 := log_lower_of_power (p:=29) (k:=58) (by norm_num) (by norm_num)
    have h31 := log_lower_of_power (p:=31) (k:=59) (by norm_num) (by norm_num)
    norm_num only [Nat.cast_ofNat] at *
    linarith only [h2,h3,h5,h7,h11,h13,h17,h19,h23,h29,h31]
  change _<Real.eulerMascheroniConstant+∑' p : Nat.Primes,f p
  linarith [euler_constant_gt_56]

end AnalyticNumberTheory.SieveMethods
