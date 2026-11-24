import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# The zero-counting rectangle for primitive Dirichlet L-functions

The logarithmic derivative on the reflected edge contains the conductor term
`-log q`. The argument principle counts precisely the open critical-strip
zeros, including real zeros with multiplicity.
-/

open Complex Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Logarithmic differentiation of the primitive functional equation. -/
theorem logDeriv_completedLFunction_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {s : ℂ}
    (hs : DirichletCharacter.completedLFunction (star χ) s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) (1-s) =
      -(Real.log (q:ℝ):ℂ) - logDeriv (DirichletCharacter.completedLFunction (star χ)) s := by
  let F := DirichletCharacter.completedLFunction χ
  let G := DirichletCharacter.completedLFunction (star χ)
  let P (w : ℂ) := (q:ℂ)^(w-1/2) * DirichletCharacter.rootNumber χ
  have hq0 : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hP : P s ≠ 0 := mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hq0))
    (DirichletCharacter.rootNumber_ne_zero hχ)
  have he : F ∘ (fun w : ℂ => 1-w) = P*G := funext (completedLFunction_one_sub_primitive hχ)
  have hF : Differentiable ℂ F := differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one hχ hq)
  have hG : Differentiable ℂ G := differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one (isPrimitive_star hχ) hq)
  have hPd : HasDerivAt P (P s * Complex.log (q:ℂ)) s := by
    have hp := (((hasDerivAt_id s).sub_const (1/2:ℂ)).const_cpow (c := (q:ℂ)) (Or.inl hq0)).mul_const
      (DirichletCharacter.rootNumber χ)
    exact hp.congr_deriv (by dsimp [P]; ring)
  have H := congrArg (fun f => logDeriv f s) he
  change logDeriv (F ∘ (fun w : ℂ => 1-w)) s = logDeriv (P*G) s at H
  have hminus : HasDerivAt (fun w : ℂ => 1-w) (-1) s := (hasDerivAt_id s).const_sub (1:ℂ)
  rw [logDeriv_comp (hF _) hminus.differentiableAt, hminus.deriv,
    logDeriv_mul s hP hs hPd.differentiableAt (hG _)] at H
  have hlog : logDeriv P s = (Real.log (q:ℝ):ℂ) := by
    rw [logDeriv_apply, hPd.deriv, mul_div_cancel_left₀ _ hP]
    exact (Complex.ofReal_log (by positivity)).symm
  rw [hlog] at H
  change logDeriv F (1-s) = _ - logDeriv G s
  linear_combination -H

private theorem contour_logDeriv_int {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p : ℝ → ℂ} (hp : Continuous p) {a b : ℝ} (hn : ∀ x ∈ uIcc a b, f (p x) ≠ 0) :
    IntervalIntegrable (fun x => logDeriv f (p x)) volume a b := by
  exact ((((hf.contDiff (n := 1)).continuous_deriv le_rfl).comp hp).continuousOn.div
    (hf.continuous.comp hp).continuousOn hn).intervalIntegrable

/-- The exact rectangular argument-principle identity, expressed in terms of
the imaginary horizontal and real vertical logarithmic derivative integrals. -/
theorem zeroCountL_rectangle {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {T : ℝ} (hT : 0 < T)
    (hno : ∀ ρ ∈ CriticalStripZerosL χ, ρ.im ≠ T ∧ ρ.im ≠ -T) :
    let F := DirichletCharacter.completedLFunction χ
    let H (t : ℝ) := ∫ x in (-1:ℝ)..2, (logDeriv F ((x:ℂ)+t*I)).im
    let V (x : ℝ) := ∫ t in (-T)..T, (logDeriv F ((x:ℂ)+t*I)).re
    2*Real.pi*(zeroCountL χ T : ℝ) = H (-T) - H T + V 2 - V (-1) := by
  let F := DirichletCharacter.completedLFunction χ
  let Z := criticalStripZeroFinset χ (-T) T
  have hF := differentiable_completedLFunction_of_ne_one (isPrimitive_ne_one hχ hq)
  have hint (ρ : ℂ) (hρ : ρ ∈ Z) : ρ.re ∈ Ioo (-1:ℝ) 2 ∧ ρ.im ∈ Ioo (-T) T := by
    obtain ⟨h0,h1,hlo,hhi,hz⟩ := (mem_criticalStripZeroFinset χ).mp hρ
    have hh := hno ρ ⟨h0,h1,hz⟩
    exact ⟨⟨by linarith,by linarith⟩,lt_of_le_of_ne hlo hh.2.symm,lt_of_le_of_ne hhi hh.1⟩
  have hall (w : ℂ) (hw : w ∈ Icc (-1:ℝ) 2 ×ℂ Icc (-T) T) (hz : F w = 0) : w ∈ Z := by
    obtain ⟨h0,h1,hl⟩ := (completedLFunction_eq_zero_iff_criticalStrip hχ hq _).mp hz
    exact (mem_criticalStripZeroFinset χ).mpr ⟨h0,h1,hw.2.1,hw.2.2,hl⟩
  have hr := AnalyticNumberTheory.RiemannZeta.argument_principle_rect_entire hF (by norm_num : (-1:ℝ)<2)
    (by linarith : -T < T) Z hint hall
  have hcount : (∑ ρ ∈ Z, (analyticOrderNatAt F ρ:ℂ)) = (zeroCountL χ T : ℂ) := by
    unfold zeroCountL
    push_cast
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [← analyticOrderNatAt_LFunction_eq_completedLFunction χ ((mem_criticalStripZeroFinset χ).mp hρ).1
      (Or.inl (isPrimitive_ne_one hχ hq))]
  change _ = (2*Real.pi*I)*(∑ ρ ∈ Z, (analyticOrderNatAt F ρ:ℂ)) at hr
  rw [hcount] at hr
  have h := congrArg Complex.im hr
  have H (t : ℝ) (ht : t = T ∨ t = -T) :
      (∫ x in (-1:ℝ)..2, logDeriv F ((x:ℂ)+t*I)).im = ∫ x in (-1:ℝ)..2, (logDeriv F ((x:ℂ)+t*I)).im := by
    have hh := contour_logDeriv_int (f := F) hF (p := fun x : ℝ => (x:ℂ)+t*I) (Complex.continuous_ofReal.add continuous_const)
      (a := -1) (b := 2) (fun x _ hf => by
        have hh := hno _ ((completedLFunction_eq_zero_iff_criticalStrip hχ hq _).mp hf)
        simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at hh
        rcases ht with he|he <;> tauto)
    exact (Complex.imCLM.intervalIntegral_comp_comm hh).symm
  have V (a : ℝ) (ha : a = 2 ∨ a = -1) :
      (∫ t in (-T)..T, logDeriv F ((a:ℂ)+t*I)).re = ∫ t in (-T)..T, (logDeriv F ((a:ℂ)+t*I)).re := by
    have hh := contour_logDeriv_int (f := F) hF (p := fun t : ℝ => (a:ℂ)+t*I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) (a := -T) (b := T)
      (fun t _ hf => by
        obtain ⟨h0,h1,_⟩ := (completedLFunction_eq_zero_iff_criticalStrip hχ hq _).mp hf
        simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero] at h0 h1
        rcases ha with he|he <;> linarith)
    exact (Complex.reCLM.intervalIntegral_comp_comm hh).symm
  simp only [Complex.add_im,Complex.sub_im,Complex.I_mul_im] at h
  have hR : ((2*(Real.pi:ℂ)*I)*(zeroCountL χ T:ℂ)).im = 2*Real.pi*(zeroCountL χ T:ℝ) := by simp [Complex.mul_im,Complex.mul_re]
  rw [hR] at h
  dsimp only
  calc
    _ = _ := h.symm
    _ = _ := by
      change (∫ x in (-1:ℝ)..2, logDeriv F ((x:ℂ)+(-T:ℝ)*I)).im -
        (∫ x in (-1:ℝ)..2, logDeriv F ((x:ℂ)+T*I)).im +
        (∫ t in (-T)..T, logDeriv F (((2:ℝ):ℂ)+t*I)).re -
        (∫ t in (-T)..T, logDeriv F (((-1:ℝ):ℂ)+t*I)).re = _
      rw [H (-T) (Or.inr rfl),H T (Or.inl rfl),V 2 (Or.inl rfl),V (-1) (Or.inr rfl)]

end AnalyticNumberTheory.DirichletLFunctions
