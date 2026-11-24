import AnalyticNumberTheory.DirichletLFunctions.TuranPrimeWindow
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-!
# Turán prime detection for the Riemann zeta function

For ordinates of absolute value at least three the local disk avoids the pole, while the
prime polynomial is the one attached to the primitive character of modulus one.
-/

noncomputable section
open Complex Metric Finset
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

private theorem zeta_upper_half_strip :
    ∃ C > 0, ∀ {z : ℂ}, 0≤z.re → 2≤|z.im| → ‖riemannZeta z‖ ≤ C*(|z.im|+2) := by
  obtain ⟨P,hP,HP⟩ := norm_riemannZeta_critical_strip_le (ε:=1/2) (by norm_num)
  obtain ⟨R,hR,HR⟩ := norm_riemannZeta_re_ge_one_le
  refine ⟨max P R,hP.trans_le (le_max_left ..),?_⟩
  intro z hz ht
  by_cases hs : z.re ≤ 1
  · have h := HP (σ:=z.re) (t:=z.im) ⟨hz,hs⟩ (by linarith)
    rw [re_add_im] at h
    apply h.trans
    apply mul_le_mul (le_max_left ..) _ (by positivity) (hP.le.trans (le_max_left ..))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤|z.im|+2)
      (show (1-z.re)/2+1/2 ≤ 1 by linarith)
  · have h := HR (σ:=z.re) (t:=z.im) (le_of_not_ge hs) ht
    rw [re_add_im] at h
    apply h.trans
    exact mul_le_mul (le_max_right ..) (by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < |z.im|+2)])
      (Real.log_nonneg (by linarith)) (hP.le.trans (le_max_left ..))

/-- The local zero count and the finite prime detector around `1+η+it`,
with absolute constants and both choices uniform for `|t|≥3`. -/
theorem zeta_turan_local_estimates :
    ∃ C > 0, ∃ K > 0, ∀ {t η Y : ℝ}, 3≤|t| → |t|+2≤Y →
    0<η → η≤1/1024 → 1≤η*Real.log Y →
    let c := ((1+η:ℝ):ℂ)+(t:ℂ)*I
    (∀ S : Finset ℂ, (∀ z ∈ S, riemannZeta z=0 ∧ ‖c-z‖≤2*η) →
      (∑ z ∈ S,(analyticOrderNatAt riemannZeta z:ℝ)) ≤ K*(1+η*Real.log Y)) ∧
    (∀ {ρ : ℂ}, riemannZeta ρ=0 → ‖c-ρ‖≤2*η → ∀ {X U : ℝ} {M : ℕ}, 1≤X → X≤U →
      C*(1+η*Real.log Y)≤M → 1024*(η*Real.log X)≤M → 128*(M:ℝ)≤η*Real.log U →
      ∃ m ∈ Icc M (2*M), (1/128:ℝ)^(2*M+1)≤
        ‖∑ p ∈ turanPrimes X U,turanMangoldtTerm (1:DirichletCharacter ℂ 1) η t m p‖) := by
  obtain ⟨P,hP,HP⟩ := zeta_upper_half_strip
  obtain ⟨B,hB,HB⟩ := norm_logDeriv_LFunction_re_gt_one_le
  obtain ⟨D,hD,HD⟩ := turan_prime_detector_of_large_derivative
  let F := 4*(P+1)
  let E := 352*(Real.log F+2)
  have hF : 1≤F := by dsimp [F]; linarith
  have hFp : 0<F := by linarith
  have hlogF := Real.log_nonneg hF
  have hE : 0<E := by dsimp only [E]; positivity
  let K := 2+B+E
  have hK : 0<K := by dsimp only [K]; positivity
  refine ⟨max D (16*256^2*K),hD.trans_le (le_max_left ..),4*K,by positivity,?_⟩
  intro t η Y ht hY hη hη' hg
  let c := ((1+η:ℝ):ℂ)+(t:ℂ)*I
  have hcr : c.re=1+η := by simp [c]
  have hci : c.im=t := by simp [c]
  have hYp : 0<Y := by linarith
  have hlog := Real.log_nonneg (by linarith : 1≤Y)
  have hlog1 : 1≤Real.log Y := hg.trans (mul_le_of_le_one_left hlog (by linarith))
  have hcf : 1<c.re := by linarith
  have hnorm := HB (1:DirichletCharacter ℂ 1) c hcf (by linarith)
  rw [DirichletCharacter.LFunction_modOne_eq,hcr,add_sub_cancel_left] at hnorm
  have hinv := norm_inv_LFunction_le_one_add_inv (1:DirichletCharacter ℂ 1) hcf
  rw [DirichletCharacter.LFunction_modOne_eq,hcr,add_sub_cancel_left] at hinv
  have hre (w : ℂ) (hw : w∈closedBall c (3/4)) : 0≤w.re ∧ 2≤|w.im| ∧ |w.im|+2≤2*Y := by
    have hdw : ‖w-c‖≤3/4 := by simpa only [mem_closedBall,Complex.dist_eq] using hw
    have hr := abs_le.mp ((Complex.abs_re_le_norm (w-c)).trans hdw)
    have hi := (Complex.abs_im_le_norm (w-c)).trans hdw
    rw [sub_re,hcr] at hr
    rw [sub_im,hci] at hi
    have hab := abs_sub_abs_le_abs_sub w.im t
    have hba := abs_sub_abs_le_abs_sub t w.im
    rw [abs_sub_comm t w.im] at hba
    exact ⟨by linarith,by linarith,by linarith⟩
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall c (3/4)) := by
    have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
    apply (hdiff.analyticOnNhd isOpen_compl_singleton).mono
    intro w hw he; have hi := (hre w hw).2.1; rw [Set.mem_singleton_iff.mp he,one_im,abs_zero] at hi; norm_num at hi
  have hG : 0<F*Y^2 := by positivity
  have hDG : 352*Real.log (F*Y^2) ≤ E*Real.log Y := by
    rw [Real.log_mul hFp.ne' (by positivity),Real.log_pow]
    dsimp only [E]; norm_num only [Nat.cast_ofNat]
    nlinarith only [le_mul_of_one_le_right hlogF hlog1]
  have hbound (w : ℂ) (hw : w∈sphere c (3/4)) : ‖riemannZeta w / riemannZeta c‖ ≤ F*Y^2 := by
    obtain ⟨hwr,hwi,hwY⟩ := hre w (sphere_subset_closedBall hw)
    rw [div_eq_mul_inv,norm_mul]
    have hwz := HP hwr hwi
    have hrec : 1/η ≤ Real.log Y := (div_le_iff₀ hη).mpr (by linarith only [hg])
    have hrec' := hinv.trans (by linarith [Real.log_le_sub_one_of_pos hYp] : 1+1/η≤Y)
    apply (mul_le_mul (hwz.trans (mul_le_mul_of_nonneg_left hwY hP.le)) hrec' (norm_nonneg _) (by positivity)).trans
    dsimp only [F]; nlinarith [mul_nonneg hP.le (sq_nonneg Y),sq_nonneg Y]
  have hcancel : η*(1/η)=1 := by field_simp
  have hbudget : η*(1/η+B+E*Real.log Y)+1 ≤ K*(1+η*Real.log Y) := by
    dsimp only [K]
    have hηB := mul_le_mul_of_nonneg_right (by linarith : η≤1) hB.le
    nlinarith only [hcancel,hηB,mul_nonneg (by linarith : 0≤2+B) (mul_nonneg hη.le hlog),hE.le]
  constructor
  · intro S hS
    have hh := local_logDeriv_zero_count hη (by linarith) hcr hf (fun z h => riemannZeta_ne_zero_of_one_le_re h)
      hG hbound hDG hnorm S hS
    linarith only [hh,hbudget]
  · intro ρ hz hd X U M hX hU hM hlow hhigh
    have hD' := (mul_le_mul (le_max_left D (16*256^2*K)) (by linarith : 1≤1+η*Real.log Y)
      zero_le_one (hD.le.trans (le_max_left ..))).trans hM
    apply HD (1:DirichletCharacter ℂ 1) hη hη' hX hU (by simpa only [mul_one] using hD') hlow hhigh
    rw [DirichletCharacter.LFunction_modOne_eq]
    apply local_logDeriv_turan_detector hη hη' hcr hf (fun z h => riemannZeta_ne_zero_of_one_le_re h)
      hG hbound (show 0≤E*Real.log Y by positivity) hDG hnorm hz hd
    calc
      _ ≤ 16*256^2*(K*(1+η*Real.log Y)) := by gcongr
      _ = (16*256^2*K)*(1+η*Real.log Y) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right (le_max_right ..) (by linarith)).trans hM

end AnalyticNumberTheory.RiemannZeta
