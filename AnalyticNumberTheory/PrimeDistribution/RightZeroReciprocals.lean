import AnalyticNumberTheory.AnalyticTools.LogPowerBounds
import AnalyticNumberTheory.AnalyticTools.Summation.ReciprocalHeights
import AnalyticNumberTheory.PrimeDistribution.InghamDensity
import AnalyticNumberTheory.PrimeDistribution.ZeroSumHeightLimit

/-! # Convergence of the reciprocal zero sum to the right of the critical line -/

noncomputable section

open Complex Finset Set
open scoped Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The multiplicity of any finite collection of right-hand zeros of either sign
is bounded by twice the positive-height density count at the same cutoff. -/
theorem sum_right_zeroMultiplicity_le_twice_positive (S : Finset ℂ) {σ T : ℝ} (hσ : 0 < σ)
    (hS : ∀ z ∈ S, z ∈ CriticalStripZeros ∧ σ ≤ z.re ∧ |z.im| ≤ T) :
    (∑ z ∈ S, (zeroMultiplicity z : ℝ)) ≤ 2*∑ z ∈ zeroDensityFinset σ T, (zeroMultiplicity z : ℝ) := by
  let P := zeroDensityFinset σ T
  let m (z : ℂ) : ℝ := zeroMultiplicity z
  have hsub : S ⊆ P ∪ P.image star := by
    intro z hz
    obtain ⟨hstrip, hre, ht⟩ := hS z hz
    obtain ⟨hζ, h₀, h₁⟩ := mem_criticalStripZeros.mp hstrip
    have hsym := mem_zeroDensityFinsetSymmetric.mpr ⟨hζ, h₀, h₁, ht⟩
    rcases mem_union.mp hsym with hpos | hneg
    · obtain ⟨_, _, _, hi, hi'⟩ := mem_zeroDensityFinset.mp hpos
      exact mem_union_left _ (mem_zeroDensityFinset.mpr ⟨hζ, hre, h₁, hi, hi'⟩)
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hneg
      obtain ⟨hvζ, _, hv₁, hvi, hvi'⟩ := mem_zeroDensityFinset.mp hv
      exact mem_union_right _ (mem_image.mpr ⟨v, mem_zeroDensityFinset.mpr ⟨hvζ,
        by simpa using hre, hv₁, hvi, hvi'⟩, rfl⟩)
  have hdis : Disjoint P (P.image star) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rcases mem_image.mp hz' with ⟨v, hv, rfl⟩
    have hpos := (mem_zeroDensityFinset.mp hz).2.2.2.1
    have hvpos := (mem_zeroDensityFinset.mp hv).2.2.2.1
    change 0 < -v.im at hpos
    linarith
  have hsum : (∑ z ∈ P.image star, m z) = ∑ z ∈ P, m z := by
    rw [Finset.sum_image (fun a _ b _ hab => star_injective hab)]
    apply sum_congr rfl
    intro z hz
    obtain ⟨_, hre, hre', _, _⟩ := mem_zeroDensityFinset.mp hz
    exact congrArg (fun n : ℕ => (n : ℝ)) (analyticOrderNatAt_riemannZeta_star (hσ.trans_le hre) hre')
  apply (sum_le_sum_of_subset_of_nonneg (f := m) hsub (fun _ _ _ => Nat.cast_nonneg _)).trans_eq
  rw [sum_union hdis, hsum, two_mul]

/-- For a fixed σ greater than one half, every finite subset of zeros with real
part at least σ has uniformly bounded sum of multiplicity divided by |ρ|. -/
theorem sum_zeroMultiplicity_div_norm_right_le {σ : ℝ} (hσ : 1/2 < σ) :
    ∃ C > 0, ∀ S : Finset ℂ, (∀ z ∈ S, z ∈ CriticalStripZeros ∧ σ ≤ z.re) →
      (∑ z ∈ S, (zeroMultiplicity z : ℝ)/‖z‖) ≤ C := by
  let a := min σ (3/4)
  have ha : 1/2 < a := lt_min hσ (by norm_num)
  have ha₁ : a ≤ 1 := (min_le_right ..).trans (by norm_num)
  have has : a ≤ σ := min_le_left ..
  let e := inghamExponent a
  have he : e < 1 := (div_lt_one (by linarith : 0 < 2-a)).mpr (by linarith)
  let δ := (1-e)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let β := e+δ
  have hβ : β < 1 := by dsimp only [β, δ]; linarith
  obtain ⟨B, hB, HB⟩ := ingham_zeroDensity_with_multiplicity_log_eight
  let A := 2*B*(8/δ)^8
  have hA : 0 < A := by dsimp only [A]; positivity
  have hr : (2 : ℝ)^β/2 < 1 := (div_lt_one two_pos).mpr
    (by simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hβ)
  refine ⟨3*(A*2^β/(1-2^β/2)), by positivity [sub_pos.mpr hr], ?_⟩
  intro S hS
  let v (z : ℂ) := |z.im|
  let m (z : ℂ) : ℝ := zeroMultiplicity z
  let T := ∑ z ∈ S, v z
  have hv (z : ℂ) (hz : z ∈ S) : 0 ≤ v z ∧ v z ≤ T :=
    ⟨abs_nonneg _, single_le_sum (f := v) (fun _ _ => abs_nonneg _) hz⟩
  have hcount (u : ℝ) (hu : 2 ≤ u) : (∑ z ∈ S with v z ≤ u, m z) ≤ A*u^β := by
    have hu₁ := one_le_two.trans hu
    have hu₀ := zero_lt_one.trans_le hu₁
    have hh := sum_right_zeroMultiplicity_le_twice_positive (S.filter (fun z => v z ≤ u))
      (show 0 < a by linarith) (fun z hz => by
        obtain ⟨h₁, h₂⟩ := mem_filter.mp hz
        exact ⟨(hS z h₁).1, has.trans (hS z h₁).2, h₂⟩)
    have hc := HB a ⟨ha.le, ha₁⟩ u hu
    have hlog := log_pow_le_rpow_mul_const 8 hδ hu₁
    change (Real.log u)^8 ≤ (8/δ)^8*u^δ at hlog
    apply hh.trans ((mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)).trans ?_)
    calc
      2*(B*u^e*(Real.log u)^8) ≤ 2*(B*u^e*((8/δ)^8*u^δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity)) (by norm_num)
      _ = A*(u^e*u^δ) := by dsimp only [A]; ring
      _ = A*u^β := by rw [← Real.rpow_add hu₀]
  have hrec := reciprocal_height_sum_le_of_sublinear S v m hA.le hβ hv (fun _ _ => Nat.cast_nonneg _) hcount
  calc
    _ ≤ ∑ z ∈ S, 3*(m z/(1+v z)) := by
      apply sum_le_sum
      intro z hz
      have hre := (hS z hz).2.trans (Complex.re_le_norm z)
      have hn : 0 < ‖z‖ := by linarith
      have hi : v z ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hden : 1+v z ≤ 3*‖z‖ := by linarith
      change m z/‖z‖ ≤ _
      rw [← mul_div_assoc, div_le_div_iff₀ hn (by linarith [(hv z hz).1] : 0 < 1+v z)]
      linarith only [mul_le_mul_of_nonneg_left hden (show 0 ≤ m z from Nat.cast_nonneg _)]
    _ = 3*(∑ z ∈ S, m z/(1+v z)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by norm_num)

/-- The reciprocal absolute values of all nontrivial zeros in any closed
half-plane strictly to the right of the critical line are summable with multiplicity. -/
theorem summable_zeroMultiplicity_div_norm_right {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun z : {z : ℂ // z ∈ CriticalStripZeros ∧ σ ≤ z.re} =>
      (zeroMultiplicity z : ℝ)/‖(z : ℂ)‖) := by
  obtain ⟨C, _, H⟩ := sum_zeroMultiplicity_div_norm_right_le hσ
  apply summable_of_sum_le (c := C) (fun _ => by positivity)
  intro S
  let i : {z : ℂ // z ∈ CriticalStripZeros ∧ σ ≤ z.re} ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have h := H (S.map i) (fun z hz => by
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hz
    exact v.property)
  simpa only [Finset.sum_map, i, Function.Embedding.coeFn_mk] using h

end AnalyticNumberTheory.PrimeDistribution
