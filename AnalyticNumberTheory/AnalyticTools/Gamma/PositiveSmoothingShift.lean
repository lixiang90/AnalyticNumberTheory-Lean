import AnalyticNumberTheory.AnalyticTools.Gamma.SmoothingKernel
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalResidue

/-!
# Positive Mellin lines crossing a simple pole

The two lines have positive real parts, so the only residue comes from
the Dirichlet-series factor. The kernel is Γ(w) X^w on both lines.
-/
open Real Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.AnalyticTools

/-- Move a gamma-smoothed integral past a simple pole at p on the positive strip.
R is the analytic extension of (w−p)F(w). -/
theorem gammaSmoothingIntegral_positive_residue {F R : ℂ→ℂ} {l r X : ℝ} {p : ℂ}
    (hl : 0<l) (ha : l<p.re) (hb : p.re<r) (hX : 0<X)
    (hR : ∀w : ℂ,w.re∈Icc l r → AnalyticAt ℂ R w)
    (he : ∀w : ℂ,w.re∈Icc l r → w≠p → R w=(w-p)*F w)
    {B : ℝ} (hB : 0≤B) {m : ℕ} (hg : ∀w : ℂ,w.re∈Icc l r → ‖R w‖≤B*(1+|w.im|)^m) :
    gammaSmoothingIntegral F X r-gammaSmoothingIntegral F X l=
      R p*Complex.Gamma p*(X:ℂ)^p := by
  let G (w:ℂ) := R w*Complex.Gamma w*(X:ℂ)^w
  have hlr := ha.le.trans hb.le
  have hG (w:ℂ) (hw:w.re∈Icc l r) : AnalyticAt ℂ G w := by
    have hpos := hl.trans_le hw.1
    have hΓ : AnalyticAt ℂ Complex.Gamma w := by
      apply (analyticAt_iff_eventually_differentiableAt).mpr
      filter_upwards [(isOpen_lt (f:=fun _ : ℂ => (0:ℝ)) continuous_const Complex.continuous_re).mem_nhds hpos] with v hv
      apply Complex.differentiableAt_Gamma
      intro k he; rw [he] at hv; simp at hv; linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hpow : AnalyticAt ℂ (fun v : ℂ => (X:ℂ)^v) w :=
      (show Differentiable ℂ (fun v : ℂ => (X:ℂ)^v) from
        differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).analyticAt w
    exact ((hR w hw).mul hΓ).mul hpow
  obtain ⟨C,hC,HC⟩ := norm_Gamma_positive_strip_weight hl hlr (m+2)
  let D := max (X^l) (X^r)
  have hd : 0≤D := (Real.rpow_nonneg hX.le _).trans (le_max_left ..)
  have hh (x : ℝ) (hx : x∈Icc l r) (t : ℝ) : ‖G ((x:ℂ)+t*I)‖≤B*C*D/(1+t^2) := by
    let w : ℂ := (x:ℂ)+t*I
    have hre : w.re=x := by simp [w]
    have him : w.im=t := by simp [w]
    have hpow : ‖(X:ℂ)^w‖≤D := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX,hre]
      rcases le_total 1 X with h|h
      · exact (Real.rpow_le_rpow_of_exponent_le h hx.2).trans (le_max_right ..)
      · exact (Real.rpow_le_rpow_of_exponent_ge hX h hx.1).trans (le_max_left ..)
    have h := hg w (hre ▸ hx)
    have hg' := HC w (hre ▸ hx)
    rw [him] at h hg'
    have ht : 1+t^2≤(1+|t|)^2 := by nlinarith only [sq_abs t,abs_nonneg t]
    change ‖R w*Complex.Gamma w*(X:ℂ)^w‖≤_
    rw [norm_mul,norm_mul,le_div_iff₀ (by positivity)]
    calc _ ≤ (B*(1+|t|)^m)*‖Complex.Gamma w‖*D*(1+|t|)^2 := by gcongr
         _ = B*((1+|t|)^(m+2)*‖Complex.Gamma w‖)*D := by rw [pow_add];ring
         _ ≤ _ := by gcongr
  have H := integral_verticalLine_sub_residue (F:=G) (p:=p) 0 ha hb hG (by positivity : 0≤B*C*D) hh
  simp only [Nat.zero_add,pow_one,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one] at H
  have heq (x:ℝ) (hx : x∈Icc l r) (hne : x≠p.re) (t:ℝ) :
      G ((x:ℂ)+t*I)/((x:ℂ)+t*I-p)=F ((x:ℂ)+t*I)*Complex.Gamma ((x:ℂ)+t*I)*(X:ℂ)^((x:ℂ)+t*I) := by
    let w : ℂ := (x:ℂ)+t*I
    have hw : w.re=x := by simp [w]
    have hn : w≠p := fun h => hne (hw ▸ congrArg Complex.re h)
    change (R w*Complex.Gamma w*(X:ℂ)^w)/(w-p)=F w*Complex.Gamma w*(X:ℂ)^w
    rw [he w (hw ▸ hx) hn];field_simp [sub_ne_zero.mpr hn]
  simp_rw [heq r ⟨hlr,le_rfl⟩ hb.ne',heq l ⟨le_rfl,hlr⟩ ha.ne] at H
  unfold gammaSmoothingIntegral
  rw [←mul_sub,H]
  dsimp only [G]
  field_simp [Real.pi_ne_zero]

end AnalyticNumberTheory.AnalyticTools
