import AnalyticNumberTheory.PrimeDistribution.ZeroSumHeightLimit
import AnalyticNumberTheory.RiemannZeta.ZeroCounting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Positive zero ordinates and the reciprocal-square tail -/

noncomputable section

open Finset Filter Complex Set MeasureTheory
open scoped Topology Classical
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Distinct nontrivial zeros of positive ordinate at most T. -/
def positiveZerosUpTo (T : ℝ) : Finset CriticalStripZeros :=
  (criticalStripZerosUpTo T).filter (fun z => 0 < (z:ℂ).im)

/-- The positive cutoff uses the inclusive upper endpoint of the counting function. -/
theorem mem_positiveZerosUpTo {T : ℝ} {z : CriticalStripZeros} :
    z ∈ positiveZerosUpTo T ↔ 0 < (z:ℂ).im ∧ (z:ℂ).im ≤ T := by
  simp only [positiveZerosUpTo,mem_filter,mem_criticalStripZerosUpTo]
  constructor
  · rintro ⟨h,hz⟩; exact ⟨hz,(le_abs_self _).trans h⟩
  · rintro ⟨h,hz⟩; exact ⟨by rwa [abs_of_pos h],h⟩

/-- Summing analytic multiplicities over the finite positive cutoff recovers N(T). -/
theorem sum_positiveZerosUpTo_multiplicity (T : ℝ) :
    (∑ z ∈ positiveZerosUpTo T, (zeroMultiplicity z : ℝ)) = (zeroCountUpTo T : ℝ) := by
  rw [zeroCountUpTo_eq_sum,Nat.cast_sum]
  refine sum_bij (fun z _ => (z:ℂ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro z hz
    obtain ⟨hp,hT⟩ := mem_positiveZerosUpTo.mp hz
    exact mem_filter.mpr ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr
      ⟨z.property,hp.le,hT⟩,hp⟩
  · intro z _ z' _ hz
    exact Subtype.ext hz
  · intro z hz
    obtain ⟨hm,hp⟩ := mem_filter.mp hz
    obtain ⟨hZ,_,hT⟩ := (criticalStripZeros_strip_finite 0 T).mem_toFinset.mp hm
    exact ⟨⟨z,hZ⟩,mem_positiveZerosUpTo.mpr ⟨hp,hT⟩,rfl⟩

/-- Reciprocal-square sum over positive ordinates strictly above a cutoff,
with each zero counted according to its analytic multiplicity. -/
def positiveZeroReciprocalSquareTail (T : ℝ) : ℝ :=
  ∑' z : CriticalStripZeros, if T < (z:ℂ).im then (zeroMultiplicity z : ℝ)/(z:ℂ).im^2 else 0

private lemma summable_positive_tail {T : ℝ} (hT : 1 ≤ T) :
    Summable (fun z : CriticalStripZeros => if T < (z:ℂ).im then
      (zeroMultiplicity z : ℝ)/(z:ℂ).im^2 else 0) := by
  have hs : Summable (fun z : CriticalStripZeros => (zeroMultiplicity z : ℝ)/(1+(z:ℂ).im^2)) := by
    simpa only [zero_sub,even_two.neg_pow,zeroMultiplicity] using summable_criticalStripZeros_inv_one_add_sq 0
  apply (hs.mul_left 2).of_norm_bounded
  intro z
  split_ifs with hz
  · have him : 1 ≤ (z:ℂ).im := hT.trans hz.le
    have hsq : 1 ≤ (z:ℂ).im^2 := one_le_pow₀ him
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_div_assoc',div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (zeroMultiplicity z))]
  · simp only [norm_zero]; positivity

private lemma kernel_integral {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun x : ℝ => x^(-3:ℝ)) (Ici u) ∧
    (∫ x in Ici u, x^(-3:ℝ)) = 1/(2*u^2) := by
  refine ⟨(integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hu),?_⟩
  rw [integral_Ici_eq_integral_Ioi,integral_Ioi_rpow_of_lt (by norm_num) hu]
  norm_num [Real.rpow_neg hu.le]
  ring

private lemma positive_tail_integrand_sum {T u : ℝ} (hT : 0 < T) (hu : T < u) :
    (∑' z : CriticalStripZeros, if T < (z:ℂ).im then
      (Ici (z:ℂ).im).indicator (fun x : ℝ => (zeroMultiplicity z : ℝ) * 2 * x^(-3:ℝ)) u
      else 0) =
    2*((zeroCountUpTo u : ℝ)-(zeroCountUpTo T : ℝ))*u^(-3:ℝ) := by
  let S := positiveZerosUpTo u \ positiveZerosUpTo T
  have hmem (z : CriticalStripZeros) : z ∈ S ↔ T < (z:ℂ).im ∧ (z:ℂ).im ≤ u := by
    simp only [S,Finset.mem_sdiff,mem_positiveZerosUpTo]
    constructor
    · rintro ⟨⟨hp,hmax⟩,hn⟩
      exact ⟨lt_of_not_ge (fun h => hn ⟨hp,h⟩),hmax⟩
    · rintro ⟨hl,hr⟩
      exact ⟨⟨hT.trans hl,hr⟩,fun h => hl.not_ge h.2⟩
  have hsub : positiveZerosUpTo T ⊆ positiveZerosUpTo u := fun z hz => by
    obtain ⟨hp,ht⟩ := mem_positiveZerosUpTo.mp hz
    exact mem_positiveZerosUpTo.mpr ⟨hp,ht.trans hu.le⟩
  have hsum : (∑ z ∈ S,(zeroMultiplicity z:ℝ)) =
      (zeroCountUpTo u:ℝ) - (zeroCountUpTo T:ℝ) := by
    rw [← sum_positiveZerosUpTo_multiplicity, ← sum_positiveZerosUpTo_multiplicity]
    exact eq_sub_of_add_eq (sum_sdiff hsub)
  rw [tsum_eq_sum (s := S) (fun z hz => by
    rw [hmem] at hz
    by_cases hh : T < (z:ℂ).im
    · simp [hh,Set.indicator_of_notMem (show u ∉ Ici (z:ℂ).im from fun h => hz ⟨hh,h⟩)]
    · simp [hh]), ← hsum]
  rw [mul_comm (2:ℝ),Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl
  intro z hz
  obtain ⟨ht,hu⟩ := (hmem z).mp hz
  simp [ht,Set.indicator_of_mem (show u ∈ Ici (z:ℂ).im from hu)]

/-- Partial summation over positive zero ordinates gives an exact integral of N(u)−N(T).
The formula also holds when T itself is a zero ordinate. -/
theorem positiveZeroReciprocalSquareTail_eq_integral {T : ℝ} (hT : 1 ≤ T) :
    positiveZeroReciprocalSquareTail T =
      ∫ u in Ioi T, 2*((zeroCountUpTo u : ℝ)-(zeroCountUpTo T : ℝ))*u^(-3:ℝ) := by
  let : Countable CriticalStripZeros := Set.countable_univ_iff.mp <|
    (Set.countable_iUnion (fun n : ℕ => (criticalStripZerosUpTo n).countable_toSet)).mono (by
      intro z _
      obtain ⟨n,hn⟩ := exists_nat_ge |(z:ℂ).im|
      exact mem_iUnion.mpr ⟨n,mem_criticalStripZerosUpTo.mpr hn⟩)
  let F (z : CriticalStripZeros) (u : ℝ) := if T < (z:ℂ).im then
    (Ici (z:ℂ).im).indicator (fun x : ℝ => (zeroMultiplicity z : ℝ)*2*x^(-3:ℝ)) u else 0
  have hT0 := zero_lt_one.trans_le hT
  have hi (z : CriticalStripZeros) : Integrable (F z) := by
    by_cases hz : T < (z:ℂ).im
    · simpa only [F,ite_eq_left hz] using
        (integrable_indicator_iff measurableSet_Ici).mpr
          ((kernel_integral (hT0.trans hz)).1.const_mul ((zeroMultiplicity z:ℝ)*2))
    · simp [F,hz]
  have hrow (z : CriticalStripZeros) : (∫ u, F z u) =
      if T < (z:ℂ).im then (zeroMultiplicity z:ℝ)/(z:ℂ).im^2 else 0 := by
    by_cases hz : T < (z:ℂ).im
    · simp only [F,ite_eq_left hz,integral_indicator measurableSet_Ici,integral_const_mul,
        (kernel_integral (hT0.trans hz)).2]
      ring
    · simp [F,hz]
  have hn (z : CriticalStripZeros) (u : ℝ) : 0 ≤ F z u := by
    by_cases hz : T < (z:ℂ).im
    · dsimp only [F]; rw [ite_eq_left hz]
      by_cases hu : u ∈ Ici (z:ℂ).im
      · rw [Set.indicator_of_mem hu]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg ((hT0.trans hz).le.trans hu) _)
      · rw [Set.indicator_of_notMem hu]
    · simp [F,hz]
  have hf := integral_tsum_of_summable_integral_norm hi (by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _ _),hrow] using summable_positive_tail hT)
  simp_rw [hrow] at hf
  rw [positiveZeroReciprocalSquareTail,hf,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : T < u
  · rw [Set.indicator_of_mem (show u ∈ Ioi T from hu)]
    exact positive_tail_integrand_sum hT0 hu
  rw [Set.indicator_of_notMem (show u ∉ Ioi T from hu)]
  calc
    _ = ∑' _ : CriticalStripZeros, (0:ℝ) := by
      apply tsum_congr
      intro z
      by_cases hz : T < (z:ℂ).im
      · simp [F,hz,Set.indicator_of_notMem (show u ∉ Ici (z:ℂ).im from fun h => hu (hz.trans_le h))]
      · simp [F,hz]
    _ = _ := tsum_zero

/-- Including the lower endpoint changes the tail by the multiplicity at exactly T
divided by T². This correction is uniformly at most a constant times log(T)/T². -/
theorem positiveZeroReciprocalSquareTail_endpoint_error :
    ∃ C > 0, ∀ {T : ℝ}, 2 ≤ T →
      let inclusive := ∑' z : CriticalStripZeros, if T ≤ (z:ℂ).im then
        (zeroMultiplicity z : ℝ)/(z:ℂ).im^2 else 0
      0 ≤ inclusive - positiveZeroReciprocalSquareTail T ∧
        inclusive - positiveZeroReciprocalSquareTail T ≤ C*Real.log T/T^2 := by
  obtain ⟨C,hC,HC⟩ := zeroCountUpTo_sub_le_log
  refine ⟨2*C,by positivity,?_⟩
  intro T hT inclusive
  have hT0 : 0 < T := by linarith
  let S := (positiveZerosUpTo T).filter (fun z : CriticalStripZeros => (z:ℂ).im = T)
  have hmem (z : CriticalStripZeros) : z ∈ S ↔ (z:ℂ).im = T := by
    simp only [S,Finset.mem_filter,mem_positiveZerosUpTo]
    constructor
    · exact And.right
    · intro he; simp [he,hT0]
  let b (z : CriticalStripZeros) := if z ∈ S then (zeroMultiplicity z : ℝ)/T^2 else 0
  have hb : Summable b := summable_of_ne_finset_zero (s := S) (fun z hz => by simp [b,hz])
  have hrow : inclusive = positiveZeroReciprocalSquareTail T + ∑' z, b z := by
    rw [positiveZeroReciprocalSquareTail, ← Summable.tsum_add (summable_positive_tail (by linarith : 1 ≤ T)) hb]
    apply tsum_congr
    intro z
    rcases lt_trichotomy (z:ℂ).im T with h|h|h
    · simp [b,hmem,h.ne,h.not_gt,h.not_ge]
    · simp [b,hmem,h]
    · simp [b,hmem,h.ne',h,h.le]
  have hmass : ∑' z, b z = (∑ z ∈ S,(zeroMultiplicity z:ℝ))/T^2 := by
    rw [tsum_eq_sum (s := S) (fun z hz => by simp [b,hz]),Finset.sum_div]
    exact sum_congr rfl fun z hz => by simp [b,hz]
  rw [hrow,add_sub_cancel_left,hmass]
  refine ⟨by positivity,?_⟩
  have hsub : positiveZerosUpTo (T-1) ⊆ positiveZerosUpTo T := fun z hz => by
    obtain ⟨hp,ht⟩ := mem_positiveZerosUpTo.mp hz
    exact mem_positiveZerosUpTo.mpr ⟨hp,by linarith⟩
  have hs : S ⊆ positiveZerosUpTo T \ positiveZerosUpTo (T-1) := by
    intro z hz
    have he := (hmem z).mp hz
    apply Finset.mem_sdiff.mpr
    simp [mem_positiveZerosUpTo,he,hT0]
  have hmass' : (∑ z ∈ S,(zeroMultiplicity z:ℝ)) ≤
      (zeroCountUpTo T:ℝ) - (zeroCountUpTo (T-1):ℝ) := by
    apply (sum_le_sum_of_subset_of_nonneg hs (fun z _ _ => Nat.cast_nonneg _)).trans_eq
    rw [←sum_positiveZerosUpTo_multiplicity,←sum_positiveZerosUpTo_multiplicity]
    exact eq_sub_of_add_eq (sum_sdiff hsub)
  have hH := HC (T-1)
  rw [sub_add_cancel,Nat.cast_sub (zeroCountUpTo_mono (by linarith)),abs_of_nonneg (by linarith)] at hH
  have hlog : Real.log (T-1+2) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by linarith) (by nlinarith [mul_nonneg (by linarith : 0 ≤ T-2) hT0.le])
      _ = _ := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply hmass'.trans (hH.trans _)
  nlinarith [mul_le_mul_of_nonneg_left hlog hC.le]

end AnalyticNumberTheory.PrimeDistribution
