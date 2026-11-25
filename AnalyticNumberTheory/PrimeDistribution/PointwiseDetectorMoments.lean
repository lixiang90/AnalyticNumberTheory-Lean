import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeII
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Critical-line pointwise estimates in the character zero detector

A bound of conductor power a at most one quarter absorbs a shift from
the zero height at a cost of half a power. The remaining four powers of
the detector kernel have total mass at most π for each sample.
-/
open Real Complex Finset Set Filter MeasureTheory
namespace AnalyticNumberTheory.PrimeDistribution

private theorem log_factor_quarter {b : ℝ} (hb : 0≤b) :
    ∃D : ℝ,0<D ∧ ∀{w : ℝ},1≤w → (1+Real.log w)^b≤D*w^(1/4:ℝ) := by
  let η := 1/(4*(1+b))
  have hη : 0<η := by dsimp [η];positivity
  have he : η*b≤1/4 := by
    dsimp only [η];rw [one_div_mul_eq_div,div_le_div_iff₀ (by positivity) (by norm_num)];linarith
  refine ⟨(1+1/η)^b,by positivity,?_⟩
  intro w hw
  have hw' := zero_lt_one.trans_le hw
  have hl := Real.log_le_rpow_div hw'.le hη
  have h1 := Real.one_le_rpow hw hη.le
  have hu : 1+Real.log w≤(1+1/η)*w^η := by
    rw [add_mul,one_mul,one_div_mul_eq_div];linarith only [hl,h1]
  apply (Real.rpow_le_rpow (by linarith [Real.log_nonneg hw] : 0≤1+Real.log w) hu hb).trans
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hw'.le _),←Real.rpow_mul hw'.le]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw he) (by positivity)

/-- Uniform translation of a hybrid conductor-height growth bound, with a square
root of the relative height as the only additional factor. -/
theorem translated_conductor_growth {a b : ℝ} (ha : a∈Icc (0:ℝ) (1/4)) (hb : 0≤b) :
    ∃D : ℝ,0<D ∧ ∀{P H w : ℝ},1≤P → 1≤H → 1≤w → P≤H*w →
      P^a*(1+Real.log P)^b ≤ D*(H^a*(1+Real.log H)^b)*Real.sqrt w := by
  obtain ⟨D,hD,HD⟩ := log_factor_quarter hb
  refine ⟨D,hD,?_⟩
  intro P H w hP hH hw h
  have hH' := zero_lt_one.trans_le hH
  have hw' := zero_lt_one.trans_le hw
  have hP' := zero_lt_one.trans_le hP
  have hlog := Real.log_le_log hP' h
  rw [Real.log_mul hH'.ne' hw'.ne'] at hlog
  have hlog' : 1+Real.log P≤(1+Real.log H)*(1+Real.log w) := by
    nlinarith only [hlog,mul_nonneg (Real.log_nonneg hH) (Real.log_nonneg hw)]
  have hpow := Real.rpow_le_rpow (by linarith [Real.log_nonneg hP] : 0≤1+Real.log P) hlog' hb
  have hHlog : 0≤1+Real.log H := by linarith [Real.log_nonneg hH]
  have hwlog : 0≤1+Real.log w := by linarith [Real.log_nonneg hw]
  rw [Real.mul_rpow hHlog hwlog] at hpow
  have ha' := Real.rpow_le_rpow hP'.le h ha.1
  rw [Real.mul_rpow hH'.le hw'.le] at ha'
  apply (mul_le_mul ha' (hpow.trans (mul_le_mul_of_nonneg_left (HD hw) (by positivity)))
    (by have := Real.log_nonneg hP;positivity) (by positivity)).trans
  rw [show H^a*w^a*((1+Real.log H)^b*(D*w^(1/4:ℝ)))=
    D*(H^a*(1+Real.log H)^b)*(w^a*w^(1/4:ℝ)) by ring,←Real.rpow_add hw',Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw (by linarith [ha.2])) (by positivity)

/-- The sample-weighted fourth moment on any finite window, from a pointwise
bound translated separately from each zero height. -/
theorem detector_fourth_moment_of_pointwise (S : Finset ℂ) {f : ℝ→ℝ} (hf : Continuous f)
    (hf₀ : ∀t,0≤f t) {A : ℝ} (hA : 0≤A)
    (h : ∀z∈S,∀t : ℝ,f t≤A*Real.sqrt (1+|t-z.im|)) {l r : ℝ} (hlr : l≤r) :
    ∫ t in l..r,detectorWeight S t*(f t)^4 ≤ A^4*(π*S.card) := by
  let g (z : ℂ) (t : ℝ) := 1/(1+|t-z.im|)^4
  have hc (z : ℂ) : Continuous (g z) := continuous_const.div
    ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 4) (fun t => by
    change (1+|t-z.im|)^4≠0;positivity)
  let G (t:ℝ) := ∑z∈S,g z t
  have hG : Continuous G := continuous_finsetSum _ (fun z _ => hc z)
  calc _ ≤ ∫ t in l..r,A^4*G t := by
          apply intervalIntegral.integral_mono_on hlr (((continuous_detectorWeight S).mul (hf.pow 4)).intervalIntegrable ..)
            ((hG.const_mul _).intervalIntegrable ..)
          intro t _
          change detectorWeight S t * (f t)^4≤A^4*G t
          simp only [detectorWeight,G,sum_mul,mul_sum]
          apply sum_le_sum;intro z hz
          let w := 1+|t-z.im|
          have hw : 0<w := by dsimp [w];positivity
          have hpow := pow_le_pow_left₀ (hf₀ t) (h z hz t) 4
          rw [mul_pow,show Real.sqrt (1+|t-z.im|)^4=w^2 by
            change Real.sqrt w ^ (2*2)=w^2;rw [pow_mul,Real.sq_sqrt hw.le]] at hpow
          change 1/w^6*(f t)^4≤A^4*(1/w^4)
          apply (mul_le_mul_of_nonneg_left hpow (by positivity : 0≤1/w^6)).trans_eq
          change 1/w^6*(A^4*w^2)=A^4*(1/w^4)
          field_simp
       _ ≤ _ := by rw [intervalIntegral.integral_const_mul];exact mul_le_mul_of_nonneg_left (ingham_kernel_integral_le S hlr) (by positivity)

/-- A second moment for the Möbius polynomial suffices when the critical L-value
is pointwise bounded by A times the square root of the distance weight. -/
theorem count_from_pointwise_detector {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ)
    {L : ℕ} (hL : 1≤L) {A B V : ℝ} (hA : 0≤A) (hB : 0≤B) (hV : 0≤V)
    (f g : ι→ℝ→ℝ) (hf : ∀i∈F,Continuous (f i)) (hf₀ : ∀i∈F,∀t,0≤f i t)
    (hg : ∀i∈F,Continuous (g i)) (h : ∀i∈F,∀z∈S i,∀t,f i t≤A*Real.sqrt (1+|t-z.im|))
    (hm : ∀n : ℕ,(∑i∈F,∫ t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*(g i t)^2)≤B)
    (hdet : ∀i∈F,∀z∈S i,∀ᶠ R : ℝ in atTop,V≤∫ t in -R..R,1/(1+|t-z.im|)^6*f i t*g i t) :
    (∑i∈F,((S i).card:ℝ))*V^2≤π*A^2*B := by
  let R := ∑i∈F,((S i).card:ℝ)
  have hR : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hfour (n : ℕ) : (∑i∈F,∫t in -(2^n*(L:ℝ))..2^n*L,detectorWeight (S i) t*(f i t)^4)≤A^4*π*R := by
    dsimp [R];rw [mul_sum]
    apply sum_le_sum;intro i hi
    exact (detector_fourth_moment_of_pointwise (S i) (hf i hi) (hf₀ i hi) hA (h i hi)
      (by linarith [show 0≤(2:ℝ)^n*(L:ℝ) by positivity])).trans_eq (by ring)
  have hc := count_from_weighted_detector_moments F S hL hV (by positivity : 0≤A^4*π*R) hB f g hf hg hfour hm hdet
  change R^3*V^4≤_ at hc
  change R*V^2≤_
  rcases hR.eq_or_lt with hR|hR
  · rw [←hR];simp;positivity
  · have he : (R*V^2)^2≤(π*A^2*B)^2 := by
      apply le_of_mul_le_mul_left (a:=R) _ hR
      convert hc using 1 <;> ring
    exact (sq_le_sq₀ (mul_nonneg hR.le (sq_nonneg V)) (mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg A)) hB)).mp he

end AnalyticNumberTheory.PrimeDistribution
