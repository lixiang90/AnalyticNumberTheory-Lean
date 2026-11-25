import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeII

/-! # Translating sparse samples under a positive detector kernel -/
noncomputable section
open Finset Real Complex MeasureTheory Filter
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

private def kernel (v : ℝ) : ℝ := 1/(1+|v|)^6
private lemma continuous_kernel : Continuous kernel :=
  continuous_const.div ((continuous_const.add continuous_abs).pow 6)
    (fun v => by change (1+|v|)^6≠0;positivity)
private lemma kernel_nonneg (v : ℝ) : 0≤kernel v := by dsimp [kernel];positivity

/-- A uniform bound on the translated discrete second moment gives a mean
against the detector weights on any symmetric window. -/
theorem sparse_detector_second_mean {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ)
    {L R B : ℝ} (hL : 0≤L) (hR : 0≤R) (hB : 0≤B)
    (him : ∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im≤L) (g : ι→ℝ→ℝ)
    (hg : ∀ i∈F,Continuous (g i))
    (hd : ∀ v : ℝ, (∑ i∈F,∑ z∈S i,(g i (v+z.im))^2)≤B) :
    (∑ i∈F,∫ t in -R..R,detectorWeight (S i) t*(g i t)^2)≤π*B := by
  let U := R+L
  have hu : 0≤U := add_nonneg hR hL
  let f (i : ι) (z : ℂ) (v : ℝ) := kernel v*(g i (v+z.im))^2
  have hf (i) (hi : i∈F) (z : ℂ) : Continuous (f i z) :=
    continuous_kernel.mul (((hg i hi).comp (continuous_id.add continuous_const)).pow 2)
  have he (i) (hi : i∈F) (z : ℂ) (hz : z∈S i) :
      (∫ t in -R..R,kernel (t-z.im)*(g i t)^2) ≤ ∫ v in -U..U,f i z v := by
    have htr := intervalIntegral.integral_comp_sub_right (a:=-R) (b:=R) (f i z) z.im
    simp only [f,sub_add_cancel] at htr
    apply htr.le.trans
    apply intervalIntegral.integral_mono_interval (by dsimp [U];linarith [(him i hi z hz).2])
      (by linarith) (by dsimp [U];linarith [(him i hi z hz).1])
    · exact Eventually.of_forall (fun v => mul_nonneg (kernel_nonneg v) (sq_nonneg _))
    · exact (hf i hi z).intervalIntegrable ..
  have hr (i) (hi : i∈F) :
      (∫ t in -R..R,detectorWeight (S i) t*(g i t)^2)≤∫ v in -U..U,∑ z∈S i,f i z v := by
    have hfi (z : ℂ) : Continuous (fun t : ℝ => kernel (t-z.im)*(g i t)^2) :=
      (continuous_kernel.comp (continuous_id.sub continuous_const)).mul ((hg i hi).pow 2)
    calc _ = ∫ t in -R..R,∑ z∈S i,kernel (t-z.im)*(g i t)^2 := by
               apply intervalIntegral.integral_congr;intro t _;exact sum_mul ..
         _ = _ := intervalIntegral.integral_finsetSum (fun z _ => (hfi z).intervalIntegrable ..)
         _ ≤ ∑ z∈S i,∫ v in -U..U,f i z v := sum_le_sum (he i hi)
         _ = _ := (intervalIntegral.integral_finsetSum (fun z _ => (hf i hi z).intervalIntegrable ..)).symm
  have hc (i) (hi : i∈F) := continuous_finsetSum (S i) (fun z _ => hf i hi z)
  apply (sum_le_sum hr).trans
  rw [←intervalIntegral.integral_finsetSum (fun i hi => (hc i hi).intervalIntegrable ..)]
  have hker : (∫ v in -U..U,kernel v)≤π := by
    simpa [detectorWeight,kernel] using integral_detectorWeight_le ({0}:Finset ℂ) (neg_le_self hu)
  calc _ ≤ ∫ v in -U..U,kernel v*B := by
             apply intervalIntegral.integral_mono_on (neg_le_self hu) ((continuous_finsetSum F hc).intervalIntegrable ..)
               ((continuous_kernel.mul_const B).intervalIntegrable ..)
             intro t _;dsimp only [f];simp only [←mul_sum]
             exact mul_le_mul_of_nonneg_left (hd t) (kernel_nonneg t)
       _ = (∫ v in -U..U,kernel v)*B := intervalIntegral.integral_mul_const ..
       _ ≤ _ := mul_le_mul_of_nonneg_right hker hB

/-- Cubic count using an ordinary fourth mean and a discrete second mean at
each translate of the sample set. Only the fourth mean pays for local density. -/
theorem sparse_integral_detector_count : ∃ C : ℝ,0<C ∧
    ∀ {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ) {L : ℕ} {K B₄ B₂ V : ℝ},
    1≤L → 0≤K → 0≤B₄ → 0≤B₂ → 0≤V →
    (∀ i∈F,∀ z∈S i,0≤z.im ∧ z.im<L) →
    (∀ i∈F,∀ j<L,(((S i).filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K) →
    ∀ f g : ι→ℝ→ℝ,(∀ i∈F,Continuous (f i)) → (∀ i∈F,Continuous (g i)) →
    (∀ j : ℕ,(∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,(f i t)^4)≤B₄*2^j*((j:ℝ)+1)^4) →
    (∀ v : ℝ,(∑ i∈F,∑ z∈S i,(g i (v+z.im))^2)≤B₂) →
    (∀ i∈F,∀ z∈S i,∀ᶠ R : ℝ in atTop,V≤∫ t in -R..R,1/(1+|t-z.im|)^6*f i t*g i t) →
    (∑ i∈F,((S i).card:ℝ))^3*V^4≤C*K*B₄*B₂^2 := by
  obtain ⟨D,hD,HD⟩ := family_detector_moment 4
  refine ⟨π^3*D,by positivity,?_⟩
  intro ι F S L K B₄ B₂ V hL hK hB₄ hB₂ hV him hc f g hf hg hm hs hdet
  have h := count_from_weighted_detector_moments F S hL hV
    (by positivity : 0≤D*K*B₄) (mul_nonneg pi_pos.le hB₂) f g hf hg
    (HD F S hL hK hB₄ him hc (fun i t => (f i t)^4) (fun i hi => (hf i hi).pow 4)
      (fun _ _ _ => by positivity) hm)
    (fun n => sparse_detector_second_mean F S (L:=(L:ℝ)) (R:=2^n*(L:ℝ))
      (Nat.cast_nonneg _) (by positivity) hB₂
      (fun i hi z hz => ⟨(him i hi z hz).1,(him i hi z hz).2.le⟩) g hg hs) hdet
  exact h.trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
