import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# Horizontal argument variation of Dirichlet L-functions

Jensen's formula counts the zeros near `2+it`. Removing them and bounding the
remaining logarithmic derivative controls the horizontal change of argument
uniformly, even when the ordinate is arbitrarily close to a zero.
-/

open Complex Real Filter MeasureTheory Set Metric
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.DirichletLFunctions

/-- The horizontal variation of the uncompleted L-function on the right half
of the critical strip is logarithmic in `q|t|`, provided the path misses zeros. -/
theorem integral_im_logDeriv_LFunction_horizontal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ t : ℝ, 2 ≤ |t| → (∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t) →
      |∫ x in (1/2:ℝ)..2, (logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ)+t*I)).im| ≤
        C * Real.log ((q:ℝ)*|t|) := by
  let d := Real.log ((7/4:ℝ)/(13/8))
  let K := 2*((13/8:ℝ)+3/2)/((13/8:ℝ)-3/2)^2
  let A := Real.log 1000 / Real.log 2 + 2
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; norm_num
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(3/2:ℝ)*(K*(A + A/d*Real.log 26)) + Real.pi*(A/d), by positivity, ?_⟩
  intro q _ χ hχ t ht hno
  let X := (q:ℝ)*|t|
  let z₀ := (2:ℂ)+(t:ℂ)*I
  let f := DirichletCharacter.LFunction χ
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hX : 2 ≤ X := ht.trans (le_mul_of_one_le_left (abs_nonneg _) hq)
  have hX0 : 0 < X := by linarith
  have han : AnalyticOnNhd ℂ f (closedBall z₀ (7/4)) :=
    ((differentiable_LFunction_of_ne_one hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hne : f z₀ ≠ 0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [z₀])
  have hinv : ‖f z₀‖⁻¹ ≤ 2 := norm_LFunction_inv_le_of_two_le_re χ (by simp [z₀])
  have hpoly (w : ℂ) (hw : w ∈ closedBall z₀ (7/4)) : ‖f w‖ ≤ 500*X^2 := by
    have hw' : ‖w-z₀‖ ≤ 7/4 := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hre : |w.re-2| ≤ 7/4 := by simpa [z₀] using (Complex.abs_re_le_norm (w-z₀)).trans hw'
    have him : |w.im-t| ≤ 7/4 := by simpa [z₀] using (Complex.abs_im_le_norm (w-z₀)).trans hw'
    have him' : |w.im|+2 ≤ 3*|t| := by linarith [abs_sub_abs_le_abs_sub w.im t]
    by_cases h : w.re ≤ 2
    · have hb := norm_LFunction_strip_poly_le hχ (by linarith [(abs_le.mp hre).1] : -(1/2:ℝ) ≤ w.re) h
      calc
        _ ≤ ((q:ℝ)+48*(q:ℝ)^2)*(|w.im|+2)^2 := hb
        _ ≤ (49*(q:ℝ)^2)*(3*|t|)^2 := by gcongr; nlinarith
        _ ≤ _ := by dsimp [X]; nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (sq_nonneg |t|)]
    · exact (norm_LFunction_le_two_of_two_le_re χ (not_le.mp h).le).trans (by nlinarith)
  have hratio (w : ℂ) (hw : w ∈ closedBall z₀ (7/4)) : ‖f w / f z₀‖ ≤ 1000*X^2 := by
    rw [norm_div,div_eq_mul_inv]
    calc _ ≤ (500*X^2)*2 := mul_le_mul (hpoly w hw) hinv (by positivity) (by positivity)
         _ = _ := by ring
  have hlog : Real.log (1000*X^2) ≤ A*Real.log X := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hX
    have h2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1000 : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num)
    have he : Real.log 1000 ≤ (Real.log 1000/Real.log 2)*Real.log X := by
      calc _ = (Real.log 1000/Real.log 2)*Real.log 2 := (div_mul_cancel₀ _ h2p.ne').symm
           _ ≤ _ := mul_le_mul_of_nonneg_left h2 (div_nonneg h1000 h2p.le)
    dsimp [A]
    linarith
  have hcnt : (zeroCount f z₀ (13/8):ℝ) ≤ (A/d)*Real.log X := by
    have hj := zeroCount_le_sub_log_div_log (f := f) (r := (13/8:ℝ)) (R := (7/4:ℝ))
      (by norm_num) (by norm_num) (show 0 < 500*X^2 by positivity) han hne (fun w hw => hpoly w (sphere_subset_closedBall hw))
    apply hj.trans
    change _ / d ≤ _
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    apply le_trans _ hlog
    rw [← Real.log_div (by positivity) (norm_pos_iff.mpr hne).ne']
    apply Real.log_le_log (by positivity)
    rw [div_eq_mul_inv]
    calc _ ≤ (500*X^2)*2 := mul_le_mul_of_nonneg_left hinv (by positivity)
         _ = _ := by ring
  have hmiss (ρ : ℂ) (hρ : ρ ∈ closedBall z₀ (13/8)) (hz : f ρ = 0) : t-ρ.im ≠ 0 := by
    have hr : |ρ.re-2| ≤ 13/8 := by
      have hh : ‖ρ-z₀‖ ≤ 13/8 := by simpa [mem_closedBall,dist_eq_norm] using hρ
      simpa [z₀] using (Complex.abs_re_le_norm (ρ-z₀)).trans hh
    have hr1 : ρ.re < 1 := by by_contra! h; exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hz
    exact sub_ne_zero.mpr (hno ρ ⟨by linarith [(abs_le.mp hr).1],hr1,hz⟩).symm
  have H := AnalyticNumberTheory.RiemannZeta.horizontalArgumentIntegral_le_of_disk_bound f t (1000*X^2) ((A/d)*Real.log X)
    (by nlinarith : 1 ≤ 1000*X^2) han hne hratio hcnt hmiss
  change |∫ x in (1/2:ℝ)..2, (deriv f ((x:ℂ)+t*I)/f ((x:ℂ)+t*I)).im| ≤ _
  apply H.trans
  change 3/2*(K*_) + _ ≤ _ * Real.log X
  calc
    _ ≤ 3/2*(K*(A*Real.log X + A/d*Real.log X*Real.log 26)) + Real.pi*(A/d*Real.log X) := by gcongr
    _ = _ := by ring

private theorem complex_logDeriv_continuousOn_path {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p : ℝ → ℂ} (hp : Continuous p) {U : Set ℝ} (hn : ∀ x ∈ U, f (p x) ≠ 0) :
    ContinuousOn (fun x => logDeriv f (p x)) U :=
  ((hf.contDiff (n := 1)).continuous_deriv le_rfl).comp hp |>.continuousOn |>.div
    (hf.continuous.comp hp).continuousOn hn

private theorem abs_im_digamma_horizontal_le {a t : ℝ} (ha : a ∈ Icc (0:ℝ) 2) (ht : 1 ≤ |t|) :
    |(AnalyticTools.Gamma.digamma ((a:ℂ)+t*I)).im| ≤ Real.pi +
      (1/2 + (1 + 8 * ((max |(0:ℝ)| |(2:ℝ)|)^2+1)^(3/2:ℝ))/12) := by
  let M : ℝ := 1/2 + (1 + 8 * ((max |(0:ℝ)| |(2:ℝ)|)^2+1)^(3/2:ℝ))/12
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let w := (a:ℂ)+t*I
  have h := norm_digamma_sub_log_strip_le ha ht
  have him : |(AnalyticTools.Gamma.digamma w - Complex.log w).im| ≤ M := (Complex.abs_im_le_norm _).trans
    (h.trans (div_le_self hM ht))
  have hlog : |(Complex.log w).im| ≤ Real.pi := by rw [Complex.log_im]; exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le,Complex.arg_le_pi w⟩
  have he : (AnalyticTools.Gamma.digamma w).im = (Complex.log w).im + (AnalyticTools.Gamma.digamma w - Complex.log w).im := by simp
  calc
    _ = |(Complex.log w).im + (AnalyticTools.Gamma.digamma w - Complex.log w).im| := congrArg abs he
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlog him)

/-- The completed L-function has the same logarithmic horizontal-variation
bound. Stirling's formula gives a bounded imaginary part for its digamma term. -/
theorem integral_im_logDeriv_completedLFunction_horizontal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ.IsPrimitive → 2 ≤ q →
      ∀ t : ℝ, 2 ≤ |t| → (∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ t) →
      |∫ x in (1/2:ℝ)..2, (logDeriv (DirichletCharacter.completedLFunction χ) ((x:ℂ)+t*I)).im| ≤
        C * Real.log ((q:ℝ)*|t|) := by
  obtain ⟨C,hC,h⟩ := integral_im_logDeriv_LFunction_horizontal_le
  let D := Real.pi + (1/2 + (1 + 8 * ((max |(0:ℝ)| |(2:ℝ)|)^2+1)^(3/2:ℝ))/12)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C + 2*D/Real.log 2, by positivity, ?_⟩
  intro q _ χ hχ hq t ht hno
  let f := DirichletCharacter.LFunction χ
  let F := DirichletCharacter.completedLFunction χ
  let p (x : ℝ) := (x:ℂ)+t*I
  have hχn := isPrimitive_ne_one hχ hq
  have hp : Continuous p := Complex.continuous_ofReal.add continuous_const
  have hr (x : ℝ) : (p x).re = x := by simp [p]
  have hi (x : ℝ) : (p x).im = t := by simp [p]
  have hfn (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) 2) : f (p x) ≠ 0 := by
    by_cases hh : 1 ≤ x
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχn) ((hr x).symm ▸ hh)
    · intro hz
      exact hno (p x) ⟨(hr x).symm ▸ (by linarith [hx.1]),(hr x).symm ▸ not_le.mp hh,hz⟩ (hi x)
  have hFn (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) 2) : F (p x) ≠ 0 :=
    fun hz => hno (p x) ((completedLFunction_eq_zero_iff_criticalStrip hχ hq (p x)).mp hz) (hi x)
  have hint {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hne : ∀ x ∈ Icc (1/2:ℝ) 2, g (p x) ≠ 0) :
      IntervalIntegrable (fun x => (logDeriv g (p x)).im) volume (1/2:ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact Complex.continuous_im.comp_continuousOn (complex_logDeriv_continuousOn_path hg hp hne)
  have hf_int := hint (differentiable_LFunction_of_ne_one hχn) hfn
  have hF_int := hint (differentiable_completedLFunction_of_ne_one hχn) hFn
  have herr (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) 2) :
      |(logDeriv F (p x)).im - (logDeriv f (p x)).im| ≤ D := by
    have hx0 : 0 < (p x).re := (hr x).symm ▸ (by linarith [hx.1])
    rw [logDeriv_completedLFunction_eq_add_gammaFactor_eq χ hq (Or.inl hχn) (hfn x hx) (gammaFactor_ne_zero_of_re_pos χ hx0)]
    let a : ℝ := (x + parityExp χ)/2
    have ha : a ∈ Icc (0:ℝ) 2 := by
      dsimp [a]
      have hh : (parityExp χ : ℝ) ≤ 1 := by exact_mod_cast parityExp_le_one χ
      constructor <;> linarith [hx.1,hx.2, Nat.cast_nonneg (α := ℝ) (parityExp χ)]
    have hh := abs_im_digamma_horizontal_le ha (show 1 ≤ |t/2| by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
    have he : (p x+(parityExp χ:ℂ))/2 = (a:ℂ)+(t/2:ℝ)*I := by dsimp [a,p]; push_cast; ring
    rw [he]
    change |(AnalyticTools.Gamma.digamma ((a:ℂ)+(t/2:ℝ)*I)).im| ≤ D at hh
    change |(logDeriv f (p x) + _).im - (logDeriv f (p x)).im| ≤ D
    simpa [Complex.add_im,Complex.mul_im, abs_mul] using (show (1/2:ℝ)*|(AnalyticTools.Gamma.digamma ((a:ℂ)+(t/2:ℝ)*I)).im| ≤ D by linarith)
  have hdiff := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x => (logDeriv F (p x)).im - (logDeriv f (p x)).im)
    (a := (1/2:ℝ)) (b := 2) (C := D) fun x hx => herr x (by rw [← Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]; exact Set.uIoc_subset_uIcc hx)
  rw [Real.norm_eq_abs, intervalIntegral.integral_sub hF_int hf_int] at hdiff
  norm_num at hdiff
  have hmain := h hχn t ht hno
  have hlog : Real.log 2 ≤ Real.log ((q:ℝ)*|t|) := Real.log_le_log (by norm_num)
    (ht.trans (le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast NeZero.pos q)))
  have hcomp : 2*D ≤ (2*D/Real.log 2)*Real.log ((q:ℝ)*|t|) := by
    simpa [hlog2.ne'] using mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2*D/Real.log 2)
  change |∫ x in (1/2:ℝ)..2, (logDeriv F (p x)).im| ≤ _
  have htri := abs_sub_abs_le_abs_sub (∫ x in (1/2:ℝ)..2, (logDeriv F (p x)).im) (∫ x in (1/2:ℝ)..2, (logDeriv f (p x)).im)
  change |∫ x in (1/2:ℝ)..2, (logDeriv f (p x)).im| ≤ _ at hmain
  rw [add_mul]
  linarith

end AnalyticNumberTheory.DirichletLFunctions
