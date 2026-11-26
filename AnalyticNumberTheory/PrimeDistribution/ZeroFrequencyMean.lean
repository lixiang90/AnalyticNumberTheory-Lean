import AnalyticNumberTheory.AnalyticTools.FrequencyKernelMean
import AnalyticNumberTheory.AnalyticTools.Summation.LogarithmicTailMoment
import AnalyticNumberTheory.PrimeDistribution.ZeroReciprocalTail

/-! # Uniform mean squares for zeta-zero exponential polynomials -/

noncomputable section

open Complex Real Finset Set MeasureTheory
open scoped Classical
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.PrimeDistribution

/-- The logarithmically weighted reciprocal-square moment is uniformly bounded
over finite sets of nontrivial zeros with their analytic multiplicities. -/
theorem log_weighted_zero_square_bound :
    ∃ B > 0, ∀ S : Finset ℂ, (∀ z ∈ S, z ∈ CriticalStripZeros) →
      (∑ z ∈ S,(zeroMultiplicity z : ℝ)*Real.log (|z.im|+2)/‖z‖^2) ≤ B := by
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_div_im_sq_tail_le
  let m (z : ℂ) : ℝ := zeroMultiplicity z
  let f (z : ℂ) := m z*Real.log (|z.im|+2)/‖z‖^2
  let b := ∑ z ∈ nontrivialZerosUpTo 2,f z
  have hf (z : ℂ) : 0 ≤ f z := div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by linarith [abs_nonneg z.im]))) (sq_nonneg _)
  have hb : 0 ≤ b := Finset.sum_nonneg fun z _ => hf z
  have hlog₂ := Real.log_pos one_lt_two
  have hlog₄ := Real.log_pos (by norm_num : (1:ℝ)<4)
  refine ⟨b+(K*((Real.log 2+1)/2)+Real.log 4*(K*(Real.log 2/2)))+1,by positivity,?_⟩
  intro S hS
  let H := S.filter (fun z => 2 ≤ |z.im|)
  let w (z : ℂ) := m z/z.im^2
  have hH (z : ℂ) (hz : z ∈ H) : z ∈ S ∧ 2 ≤ |z.im| := Finset.mem_filter.mp hz
  have hcount (u : ℝ) (hu : 2 ≤ u) : (∑ z ∈ H with u ≤ |z.im|,w z) ≤ K*(Real.log u/u) := by
    apply HK hu
    intro z hz
    obtain ⟨hi,hv⟩ := Finset.mem_filter.mp hz
    have hh := mem_criticalStripZeros.mp (hS z (hH z hi).1)
    exact ⟨hh.1,hh.2.1,hh.2.2,hv⟩
  have hlog := sum_log_ratio_of_tail_bound H (fun z : ℂ => |z.im|) w
    (fun z hz => (hH z hz).2) (fun z _ => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hcount
  have hbase := hcount 2 le_rfl
  rw [Finset.filter_eq_self.mpr (fun z hz => (hH z hz).2)] at hbase
  have hhi : (∑ z ∈ H,f z) ≤ K*((Real.log 2+1)/2)+Real.log 4*(K*(Real.log 2/2)) := by
    calc
      _ ≤ ∑ z ∈ H,(w z*Real.log (|z.im|/2)+Real.log 4*w z) := by
        apply sum_le_sum
        intro z hz
        have hh := (hH z hz).2
        have him : 0 < |z.im| := two_pos.trans_le hh
        have he : Real.log (|z.im|+2) ≤ Real.log (|z.im|/2)+Real.log 4 := by
          rw [←Real.log_mul (div_pos him two_pos).ne' (by norm_num)]
          exact Real.log_le_log (by positivity) (by linarith)
        have hs : z.im^2 ≤ ‖z‖^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2
        have hi : 0 < z.im^2 := (sq_abs z.im) ▸ sq_pos_of_pos him
        have h₀ : 0 ≤ Real.log (|z.im|+2) := Real.log_nonneg (by linarith)
        calc
          _ ≤ (m z*Real.log (|z.im|+2))/z.im^2 := div_le_div_of_nonneg_left
            (mul_nonneg (Nat.cast_nonneg _) h₀) hi hs
          _ ≤ m z*(Real.log (|z.im|/2)+Real.log 4)/z.im^2 := by
            gcongr
          _ = _ := by dsimp only [w]; ring
      _ ≤ _ := by
        rw [sum_add_distrib,←mul_sum]
        exact add_le_add hlog (mul_le_mul_of_nonneg_left hbase hlog₄.le)
  have hlow : S \ H ⊆ nontrivialZerosUpTo 2 := by
    intro z hz
    obtain ⟨hzS,hn⟩ := mem_sdiff.mp hz
    have hh := mem_criticalStripZeros.mp (hS z hzS)
    exact mem_nontrivialZerosUpTo.mpr ⟨hh.1,hh.2.1,hh.2.2,(lt_of_not_ge
      (fun hh => hn (Finset.mem_filter.mpr ⟨hzS,hh⟩))).le⟩
  have hlow' := sum_le_sum_of_subset_of_nonneg hlow (fun z _ _ => hf z)
  have heq := Finset.sum_sdiff (f := f) (show H ⊆ S from Finset.filter_subset ..)
  change (∑ z ∈ S,f z) ≤ _
  change (∑ z ∈ S \ H,f z) ≤ b at hlow'
  linarith

private theorem finite_zero_kernel_bound :
    ∃ C > 0, ∀ (S : Finset ℂ), (∀ z ∈ S,z ∈ CriticalStripZeros) → ∀ t : ℝ,
      (∑ z ∈ S, (zeroMultiplicity z:ℝ)/(1+(t-z.im)^2)) ≤ C*Real.log (|t|+2) := by
  obtain ⟨C,hC,HC⟩ := tsum_criticalStripZeros_inv_one_add_sq_le
  refine ⟨C,hC,?_⟩
  intro S hS t
  let Z := S.subtype (· ∈ CriticalStripZeros)
  have he : (∑ z ∈ Z, (zeroMultiplicity (z:ℂ):ℝ)/(1+(t-(z:ℂ).im)^2)) =
      ∑ z ∈ S,(zeroMultiplicity z:ℝ)/(1+(t-z.im)^2) := Finset.sum_subtype_of_mem (fun z : ℂ => (zeroMultiplicity z:ℝ)/(1+(t-z.im)^2)) hS
  rw [←he]
  apply ((summable_criticalStripZeros_inv_one_add_sq t).sum_le_tsum Z
    (fun z _ => div_nonneg (Nat.cast_nonneg _) (by positivity))).trans (HC t)

/-- The exponential sum with coefficients mρ/ρ has bounded mean square per
unit logarithmic length, uniformly over every finite set of nontrivial zeros. -/
theorem zeroFrequencyPolynomial_mean_square :
    ∃ D > 0, ∀ (S : Finset ℂ), (∀ z ∈ S,z ∈ CriticalStripZeros) → ∀ {L : ℝ}, 1 ≤ L →
      (∫ u in (0:ℝ)..L, ‖frequencyPolynomial S (fun z => (zeroMultiplicity z:ℂ)/z)
        Complex.im u‖^2) ≤ D*L := by
  obtain ⟨K,hK,HK⟩ := frequencyPolynomial_mean_square_kernel
  obtain ⟨B,hB,HB⟩ := log_weighted_zero_square_bound
  obtain ⟨C,hC,HC⟩ := finite_zero_kernel_bound
  refine ⟨K*(C*B),by positivity,?_⟩
  intro S hS L hL
  let m (z : ℂ) : ℝ := zeroMultiplicity z
  let b (z : ℂ) := ‖z‖⁻¹
  let k (z w : ℂ) := (1+(z.im-w.im)^2)⁻¹
  have hs (z w : ℂ) : k z w = k w z := by dsimp only [k]; rw [show w.im-z.im = -(z.im-w.im) by ring,even_two.neg_pow]
  have h := weighted_kernel_quadratic_le S m b k (fun _ _ => Nat.cast_nonneg _)
    (fun z _ w _ => inv_nonneg.mpr (by positivity)) (fun z _ w _ => hs z w)
  have hsum : (∑ z ∈ S, (m z*(b z)^2)*(∑ w ∈ S,m w*k z w)) ≤ C*B := by
    calc
      _ ≤ ∑ z ∈ S,(m z*(b z)^2)*(C*Real.log (|z.im|+2)) := by
        apply sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        exact HC S hS z.im
      _ = C*∑ z ∈ S,m z*Real.log (|z.im|+2)/‖z‖^2 := by
        rw [mul_sum]; apply sum_congr rfl; intro z _; dsimp only [b]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (HB S hS) hC.le
  have hcorr := h.trans hsum
  have he (z : ℂ) : ‖(zeroMultiplicity z:ℂ)/z‖ = m z*b z := by rw [norm_div,Complex.norm_natCast]; rfl
  have hp := HK S (fun z => (zeroMultiplicity z:ℂ)/z) Complex.im hL
  simp_rw [he,div_eq_mul_inv] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left hcorr (mul_nonneg hK.le (zero_le_one.trans hL))).trans_eq (by ring))

end AnalyticNumberTheory.PrimeDistribution
