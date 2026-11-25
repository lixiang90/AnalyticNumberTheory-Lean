import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectedSquare
import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectionBlock
import AnalyticNumberTheory.RiemannZeta.CriticalCorrectedBlock
import AnalyticNumberTheory.RiemannZeta.HurwitzWaveComparison

/-!
# The corrected Hurwitz square mean between consecutive cutoffs

The direct and reciprocal polynomials change length at two interlaced
sequences of heights. Splitting the integer saddle block at its shifted
cutoff gives a sum of two uniformly bounded discrepancies.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped Interval ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem partial_block_mean : ∃ C : ℝ,0<C ∧ ∀ {a b c : ℝ} {j m N : ℕ},
    a∈Ioc (0:ℝ) 1 → 2≤j → j+1≤N → b≤c → hardyCutoff j≤b → c≤hardyCutoff (j+1) →
    (∀t∈Icc b c,hardySaddleRoot t∈Icc ((m:ℝ)+a) ((m:ℝ)+a+1)) →
    (∀t∈Ioo b c,hardySaddleRoot t<(m:ℝ)+a+1) →
    |∫t in b..c,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-
      ‖hurwitzWaveSum a N t‖^2|≤
      C*((Real.sqrt a)⁻¹+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n) := by
  obtain ⟨D,hD,H⟩ := hurwitz_corrected_square_error
  obtain ⟨E,hE,J⟩ := hurwitz_correction_polynomial_block
  refine ⟨24*D+2*E,by positivity,?_⟩
  intro a b c j m N ha hj hN hbc hb hc hs hs'
  let u : ℝ := (m:ℝ)+a
  let f := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-‖hurwitzWaveSum a N t‖^2
  let g := fun t => hurwitzCorrectionAmplitude j u (hardySaddleRoot t)
  let w := fun t => conj (hurwitzWaveSum a N t)*g t
  let A := (Real.sqrt a)⁻¹
  let S := ∑n∈Finset.Icc 1 N,criticalCosineGap j n
  have hp := (hardyCutoff_pos (by omega : 0<j)).trans_le hb
  have hjp : 0<(j:ℝ) := Nat.cast_pos.mpr (by omega)
  have hmin : 8*Real.pi≤b := by
    have hsq : (4:ℝ)≤(j:ℝ)^2 := by nlinarith only [show (2:ℝ)≤j by exact_mod_cast hj,sq_nonneg ((j:ℝ)-2)]
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤2*Real.pi)
    dsimp [hardyCutoff] at hb;linarith only [h,hb]
  have hx (t : ℝ) (ht : t∈Icc b c) := hardySaddleRoot_mem
    (show t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨hb.trans ht.1,ht.2.trans hc⟩)
  have hu : |(j:ℝ)-u|≤1 := by
    obtain ⟨v,z⟩ := hx b ⟨le_rfl,hbc⟩
    obtain ⟨l,r⟩ := hs b ⟨le_rfl,hbc⟩
    dsimp [u];rw [abs_le];constructor <;>linarith
  have harg (t : ℝ) (ht : t∈Icc b c) : 2*hardySaddleRoot t-u-j∈Icc (0:ℝ) 2 := by
    obtain ⟨v,z⟩ := hx t ht;obtain ⟨l,r⟩ := hs t ht;dsimp [u];constructor <;>linarith
  have hf : IntervalIntegrable f volume b c := (((continuous_hurwitz_critical_line a).norm.pow 2).intervalIntegrable ..).sub
    (hurwitzWaveSum_sq_intervalIntegrable a N b c)
  have hG : ContinuousOn g (uIcc b c) := by
    rw [uIcc_of_le hbc];intro t ht
    have ht' := hp.trans_le ht.1
    have hroot := hardySaddleRoot_pos ht'
    have hh := (differentiableOn_hurwitzCorrectionAmplitude (j:ℝ) u _ hroot).differentiableAt (isOpen_Ioi.mem_nhds hroot)
    exact (hh.continuousAt.comp (f:=hardySaddleRoot) (hardySaddleRoot_hasDerivAt ht').continuousAt).continuousWithinAt
  have hw : IntervalIntegrable w volume b c := by
    apply IntervalIntegrable.mul_continuousOn _ hG
    simp only [hurwitzWaveSum,map_sum]
    apply intervalIntegrable_iff.mpr
    apply integrable_finsetSum;intro i _
    have he (t : ℝ) : conj (enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t)=
        enteredWave (hurwitzWaveEntry a i) (fun t=>conj (hurwitzWave a i t)) t := by
      change conj (if _ then _ else _)=if _ then _ else _;split_ifs <;>simp
    simp_rw [he]
    exact (enteredWave_intervalIntegrable _ (Complex.continuous_conj.comp (continuous_hurwitzWave a i)) b c).def'
  have hwR : IntervalIntegrable (fun t => (w t).re) volume b c := intervalIntegrable_iff.mpr hw.def'.re
  have herror := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a:=b) (b:=c) (C:=D*(A+1)/j)
    (f:=fun t=>f t-2*(w t).re) (by
      filter_upwards [volume.ae_ne c] with t hne ht
      rw [uIoc_of_le hbc] at ht
      have htoo : t∈Ioo b c := ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
      have htcc : t∈Icc b c := ⟨ht.1.le,ht.2⟩
      have hJ := hardyCutoffIndex_on_block (show t∈Ico (hardyCutoff j) (hardyCutoff (j+1)) from
        ⟨hb.trans ht.1.le,htoo.2.trans_le hc⟩)
      change ⌊hardySaddleRoot t⌋₊=j at hJ
      have hM : ⌊hardySaddleRoot t-a⌋₊=m := (Nat.floor_eq_iff (by linarith [(hs t htcc).1,Nat.cast_nonneg (α:=ℝ) m])).mpr
        ⟨by linarith [(hs t htcc).1],by linarith [hs' t htoo]⟩
      have h := H ha (hmin.trans ht.1.le) (N:=N) (by rwa [hJ])
      dsimp only at h;rw [hJ,hM] at h
      rw [Real.norm_eq_abs]
      exact h.trans (div_le_div_of_nonneg_left (by positivity) hjp (hx t htcc).1))
  have hRe : (∫t in b..c,(w t).re)=(∫t in b..c,w t).re := intervalIntegral.intervalIntegral_re hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hbc),intervalIntegral.integral_sub hf (hwR.const_mul 2),
    intervalIntegral.integral_const_mul,hRe] at herror
  have hL : c-b≤24*(j:ℝ) := (sub_le_sub hc hb).trans (hardyCutoff_step_length (by omega))
  have hR := herror.trans (mul_le_mul_of_nonneg_left hL (by dsimp [A];positivity))
  rw [show D*(A+1)/(j:ℝ)*(24*(j:ℝ))=24*D*(A+1) by field_simp] at hR
  have hW := J N ha hj hbc hb hc hu harg
  change ‖∫t in b..c,w t‖≤E*(A+2+S) at hW
  have hS : 0≤S := sum_nonneg fun n _ => by unfold criticalCosineGap;split_ifs <;>positivity
  have hsum := abs_add_le ((∫t in b..c,f t)-2*(∫t in b..c,w t).re) (2*(∫t in b..c,w t).re)
  rw [sub_add_cancel,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hsum
  change |∫t in b..c,f t|≤(24*D+2*E)*(A+2+S)
  linarith only [hsum,hR,Complex.abs_re_le_norm (∫t in b..c,w t),hW,mul_nonneg hD.le hS,hD.le]

/-- One full or clipped integer saddle block, split internally at the
shifted cutoff. The polynomial length can be larger than the active set. -/
theorem hurwitz_corrected_block_mean : ∃ C : ℝ,0<C ∧ ∀ {a c : ℝ} {j N : ℕ},
    a∈Ioc (0:ℝ) 1 → 2≤j → j+1≤N → c∈Icc (hardyCutoff j) (hardyCutoff (j+1)) →
    |∫t in (hardyCutoff j)..c,‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-
      ‖hurwitzWaveSum a N t‖^2|≤
      C*((Real.sqrt a)⁻¹+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n) := by
  obtain ⟨C,hC,H⟩ := partial_block_mean
  refine ⟨2*C,by positivity,?_⟩
  intro a c j N ha hj hN hc
  let b := hardyCutoff j
  let d := 2*Real.pi*((j:ℝ)+a)^2
  let z := min d c
  let f := fun t : ℝ => ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖^2-‖hurwitzWaveSum a N t‖^2
  let E := C*((Real.sqrt a)⁻¹+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n)
  have hjr : (2:ℝ)≤j := by exact_mod_cast hj
  have hj₁ : 1≤j := by omega
  have hp : 0<b := hardyCutoff_pos hj₁
  have hπ : 0<2*Real.pi := by positivity
  have hq : 0<(j:ℝ)+a := by linarith [ha.1]
  have hb : b≤d := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [ha.1] : (j:ℝ)≤(j:ℝ)+a) 2) hπ.le
  have hbz : b≤z := le_min hb hc.1
  have hzc : z≤c := min_le_right ..
  have hzd : z≤d := min_le_left ..
  have hmem {t : ℝ} (hb' : b≤t) (hc' : t≤c) := hardySaddleRoot_mem
    (show t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨hb',hc'.trans hc.2⟩)
  have hroot_le {t : ℝ} (ht : t≤d) : hardySaddleRoot t≤(j:ℝ)+a := by
    apply Real.sqrt_le_iff.mpr ⟨hq.le,(div_le_iff₀ hπ).mpr ?_⟩
    dsimp [d] at ht;linarith only [ht]
  have hroot_lt {t : ℝ} (ht : t<d) : hardySaddleRoot t<(j:ℝ)+a := by
    apply (Real.sqrt_lt' hq).mpr;apply (div_lt_iff₀ hπ).mpr
    dsimp [d] at ht;linarith only [ht]
  have hroot_ge {t : ℝ} (ht : d≤t) : (j:ℝ)+a≤hardySaddleRoot t := by
    apply Real.le_sqrt_of_sq_le;apply (le_div_iff₀ hπ).mpr
    dsimp [d] at ht;linarith only [ht]
  have hjsub : ((j-1:ℕ):ℝ)=(j:ℝ)-1 := by rw [Nat.cast_sub hj₁];norm_num
  have h₁ : |∫t in b..z,f t|≤E := H (m:=j-1) ha hj hN hbz le_rfl (hzc.trans hc.2)
    (fun t ht => by obtain ⟨l,r⟩ := hmem ht.1 (ht.2.trans hzc);rw [hjsub];constructor <;>linarith [ha.2,hroot_le (ht.2.trans hzd)])
    (fun t ht => by rw [hjsub];linarith only [hroot_lt (ht.2.trans_le hzd)])
  have h₂ : |∫t in z..c,f t|≤E := by
    by_cases hdc : d≤c
    · have hz : z=d := min_eq_left hdc
      apply H (m:=j) ha hj hN hzc hbz hc.2
      · intro t ht;obtain ⟨l,r⟩ := hmem (hbz.trans ht.1) ht.2
        exact ⟨hroot_ge (hz ▸ ht.1),by linarith [ha.1]⟩
      · intro t ht;obtain ⟨l,r⟩ := hmem (hbz.trans ht.1.le) ht.2.le
        linarith [ha.1]
    · rw [show z=c from min_eq_right (le_of_not_ge hdc),intervalIntegral.integral_same,abs_zero]
      have hgap (n : ℕ) : 0≤criticalCosineGap j n := by unfold criticalCosineGap;split_ifs <;>positivity
      dsimp [E];positivity [sum_nonneg (s:=Finset.Icc 1 N) (fun n _ => hgap n)]
  have hi (x y : ℝ) : IntervalIntegrable f volume x y := (((continuous_hurwitz_critical_line a).norm.pow 2).intervalIntegrable ..).sub
      (hurwitzWaveSum_sq_intervalIntegrable a N x y)
  change |∫t in b..c,f t|≤_
  rw [←intervalIntegral.integral_add_adjacent_intervals (hi b z) (hi z c)]
  have h := (abs_add_le ..).trans (add_le_add h₁ h₂)
  dsimp [E] at h;linarith only [h]

end AnalyticNumberTheory.RiemannZeta
