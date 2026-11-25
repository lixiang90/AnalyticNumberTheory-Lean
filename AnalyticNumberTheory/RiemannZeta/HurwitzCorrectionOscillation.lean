import AnalyticNumberTheory.AnalyticTools.ComplexAmplitude
import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectionAmplitude
import AnalyticNumberTheory.RiemannZeta.HurwitzUniformWavePairs
import AnalyticNumberTheory.RiemannZeta.CriticalCorrectionOscillation

/-!
# Oscillation of the Hurwitz first correction against a single wave

Partial integrals of a real-frequency Hardy wave have reciprocal
logarithmic decay beyond the frequency's entry. The rotated correction
has uniformly bounded variation on a pair of cutoff intervals.
-/
noncomputable section
open Real Complex Finset MeasureTheory Set
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

private theorem norm_integral_hardy_real_frequency {r j a b : ℝ} (hr : 0<r) (hrj : r<j)
    (ha : 2*Real.pi*j^2≤a) (hab : a≤b) :
    ‖∫t in a..b,Complex.exp (((hardyPhase t-t*Real.log r:ℝ):ℂ)*I)‖≤4/(Real.log j-Real.log r) := by
  let L := fun t : ℝ => (Real.log t-Real.log (2*Real.pi))/2-Real.log r
  have hj := hr.trans hrj
  have hp : 0<a := (show 0<2*Real.pi*j^2 by positivity).trans_le ha
  have h₁ (t : ℝ) (ht : 0<t) : HasDerivAt (fun t => hardyPhase t-t*Real.log r) (L t) t := by
    have H := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
      ((hasDerivAt_id t).const_mul (Real.log (2*Real.pi)+1))
    convert (((H.div_const 2).sub_const (Real.pi/8)).sub ((hasDerivAt_id t).mul_const (Real.log r))) using 1
    · rfl
    · dsimp [L];field_simp;ring
  have h₂ (t : ℝ) (ht : 0<t) : HasDerivAt L (1/(2*t)) t := by
    convert (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2*Real.pi))).div_const 2).sub_const (Real.log r) using 1 <;>ring
  apply vanDerCorput_integral_first_deriv (F':=L) (F'':=fun t : ℝ => 1/(2*t)) hab
    (sub_pos.mpr (Real.log_lt_log hr hrj)) (fun t ht=>h₁ t (hp.trans_le ht.1)) (fun t ht=>h₂ t (hp.trans_le ht.1))
    (continuousOn_const.div (continuousOn_const.mul continuousOn_id) (fun t ht=>mul_ne_zero (by norm_num : (2:ℝ)≠0) (hp.trans_le ht.1).ne'))
    (Or.inl (fun t ht => by positivity [hp.trans_le ht.1]))
  intro t ht
  have hl := Real.log_le_log (by positivity : 0<2*Real.pi*j^2) (ha.trans ht.1)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hl
  apply le_trans _ (le_abs_self _)
  dsimp [L];push_cast at hl;linarith

/-- The complete wave includes its constant reciprocal Fourier phase and its
inverse-square-root coefficient. -/
theorem norm_integral_hurwitzWave_later {a j b c : ℝ} (i : Bool×ℕ)
    (hr : 0<hurwitzWaveFrequency a i) (hrj : hurwitzWaveFrequency a i<j)
    (hb : 2*Real.pi*j^2≤b) (hbc : b≤c) :
    let r := hurwitzWaveFrequency a i
    ‖∫t in b..c,conj (hurwitzWave a i t)‖≤(Real.sqrt r)⁻¹*(4/(Real.log j-Real.log r)) := by
  intro r
  rw [intervalIntegral.intervalIntegral_conj,Complex.norm_conj]
  let f := fun t : ℝ => Complex.exp (((hardyPhase t-t*Real.log r:ℝ):ℂ)*I)
  have H := norm_integral_hardy_real_frequency hr hrj hb hbc
  change ‖∫t in b..c,f t‖≤_ at H
  let w : ℂ := ((Real.sqrt r)⁻¹:ℝ)
  have hw : ‖w‖=(Real.sqrt r)⁻¹ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  obtain ⟨e,m⟩ := i
  cases e
  · have he (t : ℝ) : hurwitzWave a (false,m) t=w*f t := rfl
    simp_rw [he];rw [intervalIntegral.integral_const_mul,norm_mul,hw]
    exact mul_le_mul_of_nonneg_left H (by positivity)
  · let U := Complex.exp (((-2*Real.pi*r*a:ℝ):ℂ)*I)
    have he (t : ℝ) : hurwitzWave a (true,m) t=(w*U)*conj (f t) := by
      change w*Complex.exp (((-(hardyPhase t-t*Real.log r)-2*Real.pi*r*a:ℝ):ℂ)*I)=_
      dsimp only [f,U]
      rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_assoc w,←Complex.exp_add]
      congr 2;push_cast;ring
    simp_rw [he];rw [intervalIntegral.integral_const_mul,norm_mul,norm_mul,hw,
      show ‖U‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one,intervalIntegral.intervalIntegral_conj,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left H (by positivity)

/-- Against an earlier frequency, integration by parts retains its full
logarithmic separation from the saddle. The interval may be clipped at
either end inside one common cutoff block. -/
theorem hurwitz_correction_wave_nonstationary : ∃ C : ℝ,0<C ∧ ∀ {a u b c : ℝ} {j : ℕ} (i : Bool×ℕ),
    a∈Ioc (0:ℝ) 1 → 1≤j → hurwitzWaveFrequency a i<j → b≤c →
    hardyCutoff j≤b → c≤hardyCutoff (j+1) → |(j:ℝ)-u|≤1 →
    (∀t∈Icc b c,2*hardySaddleRoot t-u-j∈Icc (0:ℝ) 2) →
    let r := hurwitzWaveFrequency a i
    ‖∫t in b..c,conj (hurwitzWave a i t)*hurwitzCorrectionAmplitude j u (hardySaddleRoot t)‖ ≤
        C*(j:ℝ)^(-(1/2:ℝ))*(Real.sqrt r)⁻¹/(Real.log j-Real.log r) := by
  obtain ⟨C,hC,H⟩ := hurwitzCorrectionAmplitude_height_bounds
  refine ⟨100*C,by positivity,?_⟩
  intro a u b c j i ha hj hrj hbc hb hc hju harg r
  have hj' : (1:ℝ)≤j := by exact_mod_cast hj
  have hjp : 0<(j:ℝ) := by linarith
  let g := fun t => hurwitzCorrectionAmplitude j u (hardySaddleRoot t)
  have hp : 0<b := (hardyCutoff_pos hj).trans_le hb
  have hbx {t : ℝ} (ht : t∈Icc b c) : (j:ℝ)≤hardySaddleRoot t :=
    (hardySaddleRoot_mem (show t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨hb.trans ht.1,ht.2.trans hc⟩)).1
  have hdiff (t : ℝ) (ht : t∈Icc b c) : DifferentiableAt ℝ g t := by
    have hx := hardySaddleRoot_pos (hp.trans_le ht.1)
    have hh := (differentiableOn_hurwitzCorrectionAmplitude (j:ℝ) u _ hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact hh.comp t (hardySaddleRoot_hasDerivAt (hp.trans_le ht.1)).differentiableAt
  have hweight (t : ℝ) (ht : t∈Icc b c) :
      ‖g t‖≤C*(j:ℝ)^(-(1/2:ℝ)) ∧ ‖deriv g t‖≤C*(j:ℝ)^(-(3/2:ℝ)) := by
    obtain ⟨h,h'⟩ := H (hp.trans_le ht.1) (hj'.trans (hbx ht)) hju (harg t ht)
    constructor
    · exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hjp (hbx ht) (by norm_num)) hC.le)
    · exact h'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hjp (hbx ht) (by norm_num)) hC.le)
  have H' := norm_integral_mul_of_partial_integrals (g:=g) hbc (Complex.continuous_conj.comp (continuous_hurwitzWave a i)) hdiff
    (fun t ht => norm_integral_hurwitzWave_later i (hurwitzWaveFrequency_pos ha.1 i) hrj hb ht.1)
    (hweight c ⟨hbc,le_rfl⟩).1 (fun t ht => (hweight t ht).2)
  have hlen : c-b≤24*(j:ℝ) := (sub_le_sub hc hb).trans (hardyCutoff_step_length hj)
  have hscale : (j:ℝ)^(-(3/2:ℝ))=(j:ℝ)^(-(1/2:ℝ))/(j:ℝ) := by rw [←Real.rpow_sub_one hjp.ne'];norm_num
  have Hlen := mul_le_mul_of_nonneg_right hlen (show 0≤C*(j:ℝ)^(-(3/2:ℝ)) by positivity)
  rw [hscale,show 24*(j:ℝ)*(C*((j:ℝ)^(-(1/2:ℝ))/j))=24*C*(j:ℝ)^(-(1/2:ℝ)) by field_simp,←hscale] at Hlen
  have hgap : 0<Real.log j-Real.log r := sub_pos.mpr (Real.log_lt_log (hurwitzWaveFrequency_pos ha.1 i) hrj)
  apply H'.trans
  apply (mul_le_mul_of_nonneg_left (show C*(j:ℝ)^(-(1/2:ℝ))+(c-b)*(C*(j:ℝ)^(-(3/2:ℝ)))≤25*C*(j:ℝ)^(-(1/2:ℝ)) by linarith only [Hlen])
    (show 0≤(Real.sqrt r)⁻¹*(4/(Real.log j-Real.log r)) by positivity)).trans_eq
  ring

end AnalyticNumberTheory.RiemannZeta
