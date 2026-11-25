import AnalyticNumberTheory.SieveMethods.BrunTitchmarshWheel
import AnalyticNumberTheory.SieveMethods.BrunTitchmarshFiniteRanges

/-! # The finite range of the Brun–Titchmarsh inequality

For 1 < y/q ≤ 20000 the sieve needs primes only up to 13. The wheel is
chosen as a function of the ratio y/q, independently of the starting
point, modulus and residue class.
-/
open Real Finset
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- The Brun–Titchmarsh bound with coefficient two for all real intervals
whose length is between one and 20000 times the modulus. -/
theorem brun_titchmarsh_two_finite {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hq : 1≤q)
    (hu : 1<y/(q:ℝ)) (hU : y/(q:ℝ)≤20000) :
    piAP (x+y) q a-piAP x q a ≤ 2*y/(q.totient*log (y/(q:ℝ))) := by
  let u := y/(q:ℝ)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hy : 0<y := (div_pos_iff_of_pos_right hq').mp (zero_lt_one.trans hu)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog : 0<log u := Real.log_pos hu
  have he : (q:ℝ)*u=y := by dsimp [u]; field_simp
  have H (z : ℝ) (d B : ℝ)
      (hd : (∏p∈primeFinset z,(1-(p:ℝ)⁻¹))=d)
      (hB : (2:ℝ)^(primeFinset z).card+(primeFinset z).card=B)
      (hbound : (d*u+B)*log u≤2*u) :
      piAP (x+y) q a-piAP x q a ≤ 2*y/(q.totient*log u) := by
    have T := brun_titchmarsh_wheel (a:=a) hx hy hq z
    rw [hd,add_assoc,hB] at T
    change _≤(q:ℝ)*(u*d+B) at T
    apply (le_div_iff₀ (mul_pos hφ hlog)).mpr
    have H₁ := mul_le_mul_of_nonneg_right T hlog.le
    have H₂ := mul_le_mul_of_nonneg_left hbound hq'.le
    linarith only [H₁,H₂,he]
  have P₀ : primeFinset 1=∅ := by unfold primeFinset; norm_num only [Nat.floor_ofNat,Nat.floor_one]; change Nat.primesLE 1=∅; decide
  have P₁ : primeFinset 2={2} := by unfold primeFinset; norm_num only [Nat.floor_ofNat,Nat.floor_one]; change Nat.primesLE 2={2}; decide
  have P₂ : primeFinset 3={2,3} := by unfold primeFinset; norm_num only [Nat.floor_ofNat,Nat.floor_one]; change Nat.primesLE 3={2,3}; decide
  have P₄ : primeFinset 7={2,3,5,7} := by unfold primeFinset; norm_num only [Nat.floor_ofNat,Nat.floor_one]; change Nat.primesLE 7={2,3,5,7}; decide
  have P₆ : primeFinset 13={2,3,5,7,11,13} := by unfold primeFinset; norm_num only [Nat.floor_ofNat,Nat.floor_one]; change Nat.primesLE 13={2,3,5,7,11,13}; decide
  rcases bt_finite_wheel_ranges hu hU with h|h|h|h|h
  · exact H 1 1 1 (by simp [P₀]) (by simp [P₀]) h
  · exact H 2 (1/2) 3 (by norm_num [P₁]) (by norm_num [P₁]) h
  · exact H 3 (1/3) 6 (by norm_num [P₂]) (by norm_num [P₂]) h
  · exact H 7 (8/35) 20 (by norm_num [P₄]) (by norm_num [P₄]) h
  · exact H 13 (192/1001) 70 (by norm_num [P₆]) (by norm_num [P₆]) h

end AnalyticNumberTheory.SieveMethods
