import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveDivisors
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveProgressions
import Mathlib.Analysis.PSeries

/-! # The mean Goldbach correction along shifted primes

Swapping the divisors of N − p with the prime sum produces a single
progression for each modulus. A fourth-root saving in the progression
bound makes the resulting series absolutely summable.
-/
noncomputable section
open Real Finset
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Uniform mean bound for the binary Goldbach sieve factor over shifted
primes N − p, for every real cutoff t ≥ max(2, √N). -/
theorem goldbachPrimeSieveFactor_average :
    ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ} {t : ℝ}, sqrt N≤t → 2≤t →
      (∑p∈(primeFinset t).filter (fun p => p<N), goldbachSieveFactor (N-p)) ≤ C*t/log t := by
  let w := fun d : ℕ => (d:ℝ)^(-(5/4:ℝ))
  have hs : Summable w := Real.summable_nat_rpow.mpr (by norm_num)
  have hw (d : ℕ) : 0≤w d := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let Z := ∑' d, w d
  have hZ : 0≤Z := tsum_nonneg hw
  refine ⟨48*(Z+1),by positivity,?_⟩
  intro N t htN ht
  let P := (primeFinset t).filter (fun p => p<N)
  let D := Icc 1 N
  let Cnt := fun d : ℕ => (P.filter (fun p => d∣N-p)).card
  have ht₀ : 0<t := by linarith
  have hh := Real.log_pos (show 1<t by linarith)
  have hNt : (N:ℝ)≤t^2 := by
    simpa only [Real.sq_sqrt (Nat.cast_nonneg N)] using pow_le_pow_left₀ (Real.sqrt_nonneg _) htN 2
  have hsum : (∑p∈P,∑d∈(N-p).divisors,(d:ℝ)⁻¹) = ∑d∈D,(Cnt d:ℝ)*(d:ℝ)⁻¹ := by
    calc _ = ∑p∈P,∑d∈D, if d∣N-p then (d:ℝ)⁻¹ else 0 := by
            apply sum_congr rfl;intro p hp
            have hpn := (mem_filter.mp hp).2
            have hpos : 0<N-p := Nat.sub_pos_of_lt hpn
            rw [←sum_filter]
            apply sum_congr _ (fun _ _ => rfl)
            ext d
            simp only [D,Nat.mem_divisors,mem_filter,mem_Icc]
            exact ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hpos,(Nat.le_of_dvd hpos h.1).trans (Nat.sub_le ..)⟩,h.1⟩,
              fun h => ⟨h.2,hpos.ne'⟩⟩
         _ = _ := by
            rw [sum_comm]; apply sum_congr rfl; intro d hd
            rw [←sum_filter,sum_const,nsmul_eq_mul]
  have hcount (d : ℕ) (hd : d∈D) : (Cnt d:ℝ) ≤ piAP t d N := by
    change ((P.filter (fun p => d∣N-p)).card:ℝ) ≤ ((primeCountingAP t d N:ℕ):ℝ)
    exact_mod_cast Finset.card_le_card (show P.filter (fun p => d∣N-p)⊆
      (Icc 1 ⌊t⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ N [MOD d]) by
        intro p hp
        obtain ⟨hp',hdp⟩ := mem_filter.mp hp
        obtain ⟨hp'',hpN⟩ := mem_filter.mp hp'
        obtain ⟨hpp,hpt⟩ := mem_primeFinset_iff.mp hp''
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.two_le.trans' (by decide),Nat.le_floor hpt⟩,
          hpp,(Nat.modEq_iff_dvd' hpN.le).2 hdp⟩)
  have hb (d : ℕ) (hd : d∈D) : (Cnt d:ℝ)*(d:ℝ)⁻¹ ≤ 16*t/log t*w d := by
    have hd₀ := (mem_Icc.mp hd).1
    have hd' : (0:ℝ)<d := by exact_mod_cast hd₀
    have hdN : (d:ℝ)≤N := by exact_mod_cast (mem_Icc.mp hd).2
    have H := (mul_le_mul_of_nonneg_right (hcount d hd) (Real.rpow_nonneg hd'.le (1/4:ℝ))).trans
      (goldbach_progression_quarter ht hd₀ (hdN.trans hNt) N)
    apply le_trans _ (mul_le_mul_of_nonneg_right H (hw d))
    apply le_of_eq
    rw [mul_assoc]
    congr 1
    rw [show w d=(d:ℝ)^(-(5/4:ℝ)) from rfl,←Real.rpow_add hd']
    norm_num [Real.rpow_neg_one]
  calc _ ≤ 3*∑p∈P,∑d∈(N-p).divisors,(d:ℝ)⁻¹ := by
          rw [mul_sum]; exact sum_le_sum (fun p hp => goldbachSieveFactor_le_divisor_sum (Nat.sub_pos_of_lt (mem_filter.mp hp).2))
       _ ≤ 3*(16*t/log t*∑d∈D,w d) := by
          rw [hsum]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [mul_sum]
          exact sum_le_sum hb
       _ ≤ 3*(16*t/log t*Z) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum D (fun d _ => hw d)) (by positivity)
       _ ≤ _ := by
          have h := mul_nonneg (by norm_num : (0:ℝ)≤48) (div_nonneg ht₀.le hh.le)
          apply (le_add_of_nonneg_right h).trans_eq
          ring

end AnalyticNumberTheory.AdditiveNumberTheory
