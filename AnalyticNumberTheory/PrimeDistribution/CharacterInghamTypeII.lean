import AnalyticNumberTheory.PrimeDistribution.FamilyDetectorMoments

/-! # The integral alternative of Ingham's detector for a finite character family -/
noncomputable section
open Finset Real Complex Filter MeasureTheory
open AnalyticNumberTheory.AnalyticTools
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

private def cellKernel (z : ℂ) (t : ℝ) : ℝ := 1/(1+|t-z.im|)^6
private lemma continuous_cellKernel (z : ℂ) : Continuous (cellKernel z) :=
  continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 6)
    (fun t => by change (1+|t-z.im|)^6≠0;positivity)

/-- A cubic counting inequality for large integral detectors. The two moment
inputs include the actual sample weights, so they can exploit sparse samples. -/
theorem count_from_weighted_detector_moments {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ)
    {L : ℕ} (hL : 1≤L) {V B₄ B₂ : ℝ} (hV : 0≤V) (hB₄ : 0≤B₄) (hB₂ : 0≤B₂)
    (f g : ι → ℝ → ℝ) (hf : ∀ i∈F,Continuous (f i)) (hg : ∀ i∈F,Continuous (g i))
    (hm₄ : ∀ n : ℕ,(∑ i∈F,∫ t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*(f i t)^4)≤B₄)
    (hm₂ : ∀ n : ℕ,(∑ i∈F,∫ t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*(g i t)^2)≤B₂)
    (hdet : ∀ i∈F,∀ z∈S i,∀ᶠ R : ℝ in atTop,V≤∫ t in -R..R,1/(1+|t-z.im|)^6*f i t*g i t) :
    (∑ i∈F,((S i).card:ℝ))^3*V^4≤π*B₄*B₂^2 := by
  let M := ∑ i∈F,((S i).card:ℝ)
  have hM : 0≤M := sum_nonneg fun i _ => Nat.cast_nonneg _
  have he : ∀ᶠ R : ℝ in atTop, ∀ i∈F,∀ z∈S i,V≤∫ t in -R..R,cellKernel z t*f i t*g i t :=
    F.eventually_all.mpr (fun i hi => (S i).eventually_all.mpr (hdet i hi))
  have hL₀ : 0<(L:ℝ) := by exact_mod_cast hL
  have ht : Tendsto (fun n : ℕ => (2:ℝ)^n*L) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hL₀
  obtain ⟨n,hn⟩ := (ht.eventually he).exists
  let R := (2:ℝ)^n*L
  have hR : -R≤R := neg_le_self (by dsimp [R];positivity)
  let W (i : ι) := detectorWeight (S i)
  have hmass : (∑ i∈F,∫ t in -R..R,W i t) ≤ π*M := by
    dsimp only [M];rw [mul_sum]
    exact sum_le_sum (fun i _ => integral_detectorWeight_le _ hR)
  have hlarge : M*V ≤ ∑ i∈F,∫ t in -R..R,W i t*f i t*g i t := by
    dsimp only [M];rw [sum_mul]
    apply sum_le_sum;intro i hi
    calc ((S i).card:ℝ)*V = ∑ _z∈S i,V := by simp
         _ ≤ ∑ z∈S i,∫ t in -R..R,cellKernel z t*f i t*g i t := sum_le_sum (hn i hi)
         _ = _ := by
           rw [←intervalIntegral.integral_finsetSum (f:=fun z t => cellKernel z t*f i t*g i t)
             (fun z _ => (((continuous_cellKernel z).mul (hf i hi)).mul (hg i hi)).intervalIntegrable ..)]
           apply intervalIntegral.integral_congr;intro t _
           dsimp only [W,detectorWeight,cellKernel];rw [sum_mul,sum_mul]
  have hbig := (pow_le_pow_left₀ (mul_nonneg hM hV) hlarge 4).trans
    (family_weighted_interval_fourth_second F hR (fun i _ => continuous_detectorWeight (S i))
      hf hg (fun i _ => detectorWeight_nonneg (S i)))
  have h0 (p : ι → ℝ → ℝ) (hp : ∀ i t,0≤p i t) :
      0≤∑ i∈F,∫ t in -R..R,W i t*p i t := sum_nonneg fun i _ =>
    intervalIntegral.integral_nonneg hR (fun t _ => mul_nonneg (detectorWeight_nonneg _ _) (hp i t))
  have hh := hbig.trans (mul_le_mul (mul_le_mul hmass (hm₄ n)
    (h0 (fun i t => (f i t)^4) (fun _ _ => by positivity)) (mul_nonneg pi_pos.le hM))
    (pow_le_pow_left₀ (h0 (fun i t => (g i t)^2) (fun _ _ => sq_nonneg _)) (hm₂ n) 2)
    (sq_nonneg _) (mul_nonneg (mul_nonneg pi_pos.le hM) hB₄))
  change M^3*V^4≤_
  rcases hM.eq_or_lt with hm|hm
  · simp only [←hm,zero_pow (by decide : 3≠0),zero_mul];positivity
  · apply le_of_mul_le_mul_left (a:=M) _ hm
    convert hh using 1 <;> ring

set_option maxHeartbeats 600000 in
/-- Family form of Ingham's cubic large-values bound. The moments are taken
over symmetric windows with no restriction linking height and modulus. -/
theorem character_ingham_typeII_count : ∃ C : ℝ,0<C ∧
    ∀ {ι : Type*} (F : Finset ι) (S : ι → Finset ℂ) {L : ℕ} {K B₄ B₂ V : ℝ},
    1≤L → 0≤K → 0≤B₄ → 0≤B₂ → 0≤V →
    (∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L) →
    (∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) →
    ∀ f g : ι → ℝ → ℝ, (∀ i∈F,Continuous (f i)) → (∀ i∈F,Continuous (g i)) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,(f i t)^4) ≤ B₄*2^j*((j:ℝ)+1)^4) →
    (∀ j : ℕ, (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,(g i t)^2) ≤ B₂*2^j*((j:ℝ)+1)) →
    (∀ i∈F,∀ z∈S i, ∀ᶠ R : ℝ in atTop, V ≤ ∫ t in -R..R,1/(1+|t-z.im|)^6*f i t*g i t) →
    (∑ i∈F,((S i).card:ℝ))^3*V^4 ≤ C*K^3*B₄*B₂^2 := by
  obtain ⟨C₄,hC₄,H₄⟩ := family_detector_moment 4
  obtain ⟨C₂,hC₂,H₂⟩ := family_detector_moment 1
  refine ⟨π*C₄*C₂^2,by positivity,?_⟩
  intro ι F S L K B₄ B₂ V hL hK hB₄ hB₂ hV him hc f g hf hg hm₄ hm₂ hdet
  have h := count_from_weighted_detector_moments F S hL hV
    (by positivity : 0≤C₄*K*B₄) (by positivity : 0≤C₂*K*B₂) f g hf hg
    (H₄ F S hL hK hB₄ him hc (fun i t => (f i t)^4)
      (fun i hi => (hf i hi).pow 4) (fun _ _ _ => by positivity) hm₄)
    (H₂ F S hL hK hB₂ him hc (fun i t => (g i t)^2)
      (fun i hi => (hg i hi).pow 2) (fun _ _ _ => by positivity) (by simpa only [pow_one] using hm₂)) hdet
  exact h.trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
