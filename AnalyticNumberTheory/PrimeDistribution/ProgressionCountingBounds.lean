import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovPrimeCounting

/-! # Elementary bounds for the maximal prime-counting error in progressions -/
noncomputable section
open Finset Real MeasureTheory
open scoped Interval
namespace AnalyticNumberTheory.PrimeDistribution

/-- A residue class of modulus `d` contributes at most `t/d+1` primes up to `t`. -/
theorem piAP_le_div_add_one {t : ℝ} (ht : 0≤t) {d : ℕ} (hd : 0<d) (a : ℕ) :
    piAP t d a ≤ t/d+1 := by
  let A := (Icc 1 ⌊t⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD d])
  have hi : Set.InjOn (fun n : ℕ => n/d) (↑A : Set ℕ) := by
    intro p hp q hq he
    change p/d=q/d at he
    have hp' : p%d=a%d := (mem_filter.mp hp).2.2
    have hq' : q%d=a%d := (mem_filter.mp hq).2.2
    exact (Nat.mod_add_div p d).symm.trans (by rw [hp',he,←hq',Nat.mod_add_div])
  have hsub : A.image (fun n : ℕ => n/d)⊆range (⌊t/d⌋₊+1) := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    apply mem_range.mpr
    rw [Nat.floor_div_natCast]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hn).1).2)
  have H := card_le_card hsub
  rw [card_image_of_injOn hi,card_range] at H
  have H' : (A.card:ℝ)≤(⌊t/d⌋₊:ℝ)+1 := by exact_mod_cast H
  change (A.card:ℝ)≤_
  linarith only [H',Nat.floor_le (div_nonneg ht (Nat.cast_nonneg d))]

/-- The endpoints in the maximal progression error have a common elementary bound. -/
theorem maximalPiAPError_le_div_totient {x : ℝ} (hx : 2 ≤ x) {d : ℕ}
    (hd : 1 ≤ d) (hdx : (d : ℝ) ≤ x) :
    maximalPiAPError x d ≤ (2 + (log 2)⁻¹) * x / d.totient := by
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hx₀ : 0 ≤ x := by linarith
  have hlog := log_pos (by norm_num : (1 : ℝ) < 2)
  unfold maximalPiAPError
  apply csSup_le
  · exact ⟨_, 2, ⟨le_rfl, hx⟩, 1, Nat.coprime_one_left _, rfl⟩
  rintro z ⟨y, hy, a, _, rfl⟩
  have hp : piAP y d a ≤ x / d.totient + 1 := (piAP_le_div_add_one (t := y) (by linarith [hy.1]) hd a).trans
    (add_le_add_left (div_le_div_of_nonneg_left hx₀ hφ hφd |>.trans'
      (div_le_div_of_nonneg_right hy.2 (Nat.cast_nonneg d))) 1)
  have hone : 1 ≤ x / d.totient := (one_le_div hφ).2 (hφd.trans hdx)
  have hLi : |logIntegral y| ≤ x * (log 2)⁻¹ := by
    unfold logIntegral
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := y)
      (f := fun t : ℝ => (log t)⁻¹) (C := (log 2)⁻¹) (by
        intro t ht
        rw [Set.uIoc_of_le hy.1] at ht
        have hl := log_le_log (by norm_num : (0:ℝ)<2) ht.1.le
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hlog.le.trans hl))]
        exact inv_anti₀ hlog hl)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.1)] at hh
    simpa only [mul_comm] using hh.trans
      (mul_le_mul_of_nonneg_left (by linarith [hy.2] : y-2 ≤ x) (inv_nonneg.mpr hlog.le))
  calc
    _ ≤ |piAP y d a| + |logIntegral y / d.totient| := abs_sub _ _
    _ ≤ (x/d.totient+1) + (x*(log 2)⁻¹)/d.totient := by
      rw [abs_of_nonneg (piAP_nonneg ..),abs_div,abs_of_pos hφ]
      exact add_le_add hp (div_le_div_of_nonneg_right hLi hφ.le)
    _ ≤ _ := by
      calc
        _ ≤ (x/d.totient+x/d.totient) + (x*(log 2)⁻¹)/d.totient := by linarith only [hone]
        _ = _ := by ring

/-- The maximal error is nonnegative on nonempty endpoint ranges. -/
theorem maximalPiAPError_nonneg {x : ℝ} (hx : 2 ≤ x) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ maximalPiAPError x d :=
  (abs_nonneg _).trans (abs_piAP_sub_le_maximalPiAPError ⟨le_rfl,hx⟩ hd (Nat.coprime_one_left _))

end AnalyticNumberTheory.PrimeDistribution
