import AnalyticNumberTheory.PrimeDistribution.InghamKernel
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicWindowMeans
import AnalyticNumberTheory.AnalyticTools.FamilyIntegralMoments

/-! # Weighted mean values for the zero detectors in a character family -/
noncomputable section
open Finset Real Complex MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.PrimeDistribution

/-- Sum of the positive translates of the sixth-order decay factor. -/
def detectorWeight (S : Finset ℂ) (t : ℝ) : ℝ := ∑ z∈S,1/(1+|t-z.im|)^6

theorem continuous_detectorWeight (S : Finset ℂ) : Continuous (detectorWeight S) := by
  unfold detectorWeight
  apply continuous_finsetSum
  intro z _
  exact continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 6)
    (fun t => by change (1+|t-z.im|)^6≠0;positivity)

theorem detectorWeight_nonneg (S : Finset ℂ) (t : ℝ) : 0≤detectorWeight S t :=
  sum_nonneg (fun z _ => by positivity)

/-- The integral of the weight counts at most π per sample. -/
theorem integral_detectorWeight_le (S : Finset ℂ) {a b : ℝ} (hab : a≤b) :
    (∫ t in a..b,detectorWeight S t) ≤ π*S.card := by
  apply le_trans _ (ingham_kernel_integral_le S hab)
  have hc : Continuous fun t : ℝ => ∑ z∈S,1/(1+|t-z.im|)^4 := by
    apply continuous_finsetSum;intro z _
    exact continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 4)
      (fun t => by change (1+|t-z.im|)^4≠0;positivity)
  apply intervalIntegral.integral_mono_on hab ((continuous_detectorWeight S).intervalIntegrable ..)
    (hc.intervalIntegrable ..)
  intro t _
  exact sum_le_sum (fun z _ => one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀
    (by linarith [abs_nonneg (t-z.im)] : 1≤1+|t-z.im|) (by decide : 4≤6)))

/-- Two powers of kernel decay remain after bounding the local density of zeros. -/
theorem detectorWeight_dyadic_le (S : Finset ℂ) {L : ℕ} (hL : 1≤L) {K : ℝ} (hK : 0≤K)
    (him : ∀ z∈S,0≤z.im ∧ z.im<L)
    (hc : ∀ j<L,((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) (j : ℕ) (t : ℝ)
    (ht : j=0 ∨ (2:ℝ)^j*L≤|t|) :
    detectorWeight S t ≤ 2*π*K/(2:ℝ)^(2*j) := by
  have hpeak := ingham_kernel_sum_le S hK him hc t
  have hP : 0 < (2:ℝ)^(2*j) := by positivity
  apply (le_div_iff₀ hP).2
  unfold detectorWeight
  rw [sum_mul]
  apply le_trans _ hpeak
  apply sum_le_sum;intro z hz
  have h1 : 1≤1+|t-z.im| := by linarith [abs_nonneg (t-z.im)]
  have hj : (2:ℝ)^j≤1+|t-z.im| := by
    rcases ht with rfl|h
    · simpa only [pow_zero] using h1
    · have hl : (1:ℝ)≤L := by exact_mod_cast hL
      have hp : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
      have hh := abs_sub_le t z.im 0
      simp only [sub_zero,abs_of_nonneg (him z hz).1] at hh
      nlinarith only [h,hh,(him z hz).2.le,mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hl)]
  rw [one_div_mul_eq_div,div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hj 2)
    (show 0≤(1+|t-z.im|)^4 by positivity)
  rw [Nat.mul_comm 2 j,pow_mul];nlinarith only [hpow]

/-- A uniform dyadic moment bound for a finite family controls the sum
of its weighted moments, independently of the outer integration window. -/
theorem family_detector_moment (k : ℕ) : ∃ C : ℝ,0<C ∧
    ∀ {ι : Type*} (F : Finset ι) (S : ι → Finset ℂ) {L : ℕ} {K B : ℝ}, 1≤L → 0≤K → 0≤B →
    (∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L) →
    (∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) →
    ∀ f : ι → ℝ → ℝ, (∀ i∈F,Continuous (f i)) → (∀ i∈F,∀ t,0≤f i t) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,f i t) ≤ B*2^j*((j:ℝ)+1)^k) →
    ∀ n : ℕ, (∑ i∈F,∫ t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*f i t) ≤ C*K*B := by
  obtain ⟨D,hD,H⟩ := localized_dyadic_mean k
  refine ⟨D*(2*π),by positivity,?_⟩
  intro ι F S L K B hL hK hB him hc f hf hf₀ hm n
  let g (t : ℝ) := ∑ i∈F,detectorWeight (S i) t*f i t
  let a (t : ℝ) := ∑ i∈F,f i t
  have hg (i) (hi : i∈F) := (continuous_detectorWeight (S i)).mul (hf i hi)
  have hdom (j : ℕ) (t : ℝ) (ht : j=0 ∨ 2^j*L≤|t|) : g t≤(2*π*K/(2:ℝ)^(2*j))*a t := by
    dsimp only [g,a];rw [mul_sum]
    exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right
      (detectorWeight_dyadic_le (S i) hL hK (him i hi) (hc i hi) j t ht) (hf₀ i hi t))
  have hs := H (L:=(L:ℝ)) (A:=2*π*K) (B:=B) (f:=a) (g:=g) (Nat.cast_nonneg _) (by positivity) hB
    (continuous_finsetSum _ hf) (continuous_finsetSum _ hg) (fun t => sum_nonneg (fun i hi => hf₀ i hi t))
    (fun t => by simpa using hdom 0 t (Or.inl rfl))
    (fun j t ht => (hdom j t (Or.inr ht)).trans (by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun i hi => hf₀ i hi t))
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [show 0≤2*π*K by positivity]))
    (fun j => by simpa only [a,intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable ..)] using hm j) n
  change (∑ i∈F,∫ t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*f i t)≤_
  rw [←intervalIntegral.integral_finsetSum (f:=fun i t => detectorWeight (S i) t*f i t) (fun i hi => (hg i hi).intervalIntegrable ..)]
  exact hs.trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
