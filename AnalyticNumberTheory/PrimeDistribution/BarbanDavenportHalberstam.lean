import AnalyticNumberTheory.PrimeDistribution.VarianceConductorReduction
import AnalyticNumberTheory.PrimeDistribution.BarbanConductorMean
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovReduction

/-! # The Barban–Davenport–Halberstam theorem for primes in arithmetic progressions -/
noncomputable section
open Finset
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- The variance over one modulus written using its least nonnegative reduced residues. -/
theorem progressionVariance_eq_sum_coprime {q : ℕ} [NeZero q] (x m : ℝ) :
    progressionVariance x m q =
      ∑ a ∈ (range q).filter (fun a => a.Coprime q), (psiAP x q a - m / q.totient)^2 := by
  rw [progressionVariance, sum_filter]
  refine sum_bij (fun a _ => a.val) (fun a _ => mem_range.mpr (ZMod.val_lt a))
    (fun _ _ _ _ h => ZMod.val_injective q h) ?_ ?_
  · intro a ha
    exact ⟨(a : ZMod q), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp ha)⟩
  · intro a _
    have he : IsUnit a ↔ a.val.Coprime q := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime a.val q
    by_cases h : IsUnit a
    · simp only [if_pos h, if_pos (he.mp h)]
    · simp only [if_neg h, if_neg (fun hc => h (he.mpr hc))]

private theorem principal_square_bound (A : ℝ) :
    ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → x / Real.log x ^ A ≤ Q →
      |Chebyshev.psi x - x|^2 ≤ C * x * Q := by
  obtain ⟨C,hC,HC⟩ := abs_psi_sub_id_le_log_power A
  obtain ⟨D,hD,HD⟩ := abs_psi_sub_id_le_log_power 0
  refine ⟨C*D, by positivity, fun {x Q} hx hlow => ?_⟩
  have H := HD hx
  simp only [Real.rpow_zero, div_one] at H
  have H' : |Chebyshev.psi x - x| ≤ C*Q := (HC hx).trans
    ((by ring : C*x/Real.log x^A = C*(x/Real.log x^A)).le.trans
      (mul_le_mul_of_nonneg_left hlow hC.le))
  calc _ = |Chebyshev.psi x - x| * |Chebyshev.psi x - x| := sq _
       _ ≤ (D*x)*(C*Q) := mul_le_mul H H' (abs_nonneg _) (by positivity)
       _ = _ := by ring

/-- For every fixed positive A, the sum of squared errors in the reduced residue
classes of all moduli up to Q is O_A(x Q log x), for x/(log x)^A ≤ Q ≤ x.
The von Mangoldt weight includes prime powers, and the central term is x/φ(q). -/
theorem barban_davenport_halberstam (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → x / Real.log x ^ A ≤ Q → Q ≤ x →
      (∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
          (psiAP x q a - x / q.totient)^2) ≤ C * x * Q * Real.log x := by
  obtain ⟨D,hD,HD⟩ := barban_conductor_mean A hA
  obtain ⟨B,hB,HB⟩ := sum_inv_totient_le_mul_log
  obtain ⟨P,hP,HP⟩ := principal_square_bound A
  have h₂ : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨2*D + 4*B*P + 12/(Real.log 2)^2, by positivity, ?_⟩
  intro x Q hx hlow hu
  let ℓ := Real.log x
  let J := Icc 1 ⌊Q⌋₊
  have hx₀ : 0 < x := by linarith
  have hℓ : 0 < ℓ := Real.log_pos (by linarith)
  have hQ : 0 < Q := (div_pos hx₀ (Real.rpow_pos_of_pos hℓ _)).trans_le hlow
  have hfloor := Nat.floor_le hQ.le
  have hlog : Real.log ((⌊Q⌋₊:ℝ)+2) ≤ 2*ℓ := by
    have ht : (⌊Q⌋₊:ℝ)+2 ≤ x^2 := by nlinarith only [hfloor,hu,hx,sq_nonneg (x-2)]
    simpa only [Real.log_pow,Nat.cast_ofNat,ℓ] using Real.log_le_log (by positivity) ht
  have htot : (∑ q∈J,(q.totient:ℝ)⁻¹) ≤ 2*B*ℓ :=
    (HB _).trans ((mul_le_mul_of_nonneg_left hlog hB.le).trans_eq (by ring))
  have hcard : (J.card:ℝ) ≤ Q := by simpa [J,Nat.card_Icc] using hfloor
  have hlocal : ℓ^4 / (Real.log 2)^2 ≤ 6*x*ℓ / (Real.log 2)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have H := Real.pow_div_factorial_le_exp ℓ hℓ.le 3
    rw [show Real.exp ℓ=x from Real.exp_log hx₀] at H
    norm_num at H
    nlinarith only [mul_le_mul_of_nonneg_right H hℓ.le]
  let W (q : ℕ) := (q.totient:ℝ)⁻¹ * ∑ d∈q.divisors with 2≤d, primitivePsiEnergy x d
  have hq (q : ℕ) (hq : q∈J) :
      (∑ a∈(range q).filter (fun a => a.Coprime q), (psiAP x q a-x/q.totient)^2) ≤
      2*W q + (q.totient:ℝ)⁻¹ * (2*|Chebyshev.psi x-x|^2) + 2*(ℓ^4/(Real.log 2)^2) := by
    have hpos := (mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    rw [← progressionVariance_eq_sum_coprime]
    apply (progressionVariance_le_conductor_energy (by linarith : 1≤x)).trans
    have hql : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hpos)
    have hqx : (q:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (hfloor.trans hu)
    have hqlog : Real.log q ≤ ℓ := Real.log_le_log (by positivity) hqx
    have he := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hqlog h₂.le) hℓ.le
    have he' := pow_le_pow_left₀ (mul_nonneg (div_nonneg hql h₂.le) hℓ.le) he 2
    have hscale : (ℓ / Real.log 2 * ℓ)^2 = ℓ^4/(Real.log 2)^2 := by ring
    rw [hscale] at he'
    dsimp only [W,ℓ] at *
    linarith only [he']
  apply (sum_le_sum hq).trans
  simp only [sum_add_distrib,←mul_sum,←sum_mul,sum_const,nsmul_eq_mul]
  have hw : (∑q∈J,W q) ≤ D*x*Q*ℓ := HD hx hlow hu
  have hp := HP hx hlow
  have hmain := mul_le_mul htot (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2))
    (by positivity) (by positivity)
  have hrest := mul_le_mul hcard (mul_le_mul_of_nonneg_left hlocal (by norm_num : (0:ℝ)≤2))
    (by positivity) hQ.le
  change _ ≤ (2*D+4*B*P+12/(Real.log 2)^2)*x*Q*ℓ
  convert add_le_add (add_le_add (mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤2)) hmain) hrest using 1 <;> ring

end AnalyticNumberTheory.PrimeDistribution
