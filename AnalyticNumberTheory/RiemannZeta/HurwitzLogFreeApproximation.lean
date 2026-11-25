import AnalyticNumberTheory.RiemannZeta.HurwitzSharpWindowCancellation
import AnalyticNumberTheory.RiemannZeta.RiemannSharpApproximation

/-!
# Log-free sharp approximate functional equations

For 2≤x≤y and 2πxy=|t|, the direct and reciprocal Hurwitz polynomials
have error O(x^{-σ}), including σ=0 and σ=1. Taking equal cutoffs at
σ=1/2 yields the classical Riemann–Siegel error of order |t|^{-1/4}
before the first transition correction.
-/
noncomputable section
open Real Complex Finset Set Filter
open scoped ComplexConjugate
namespace AnalyticNumberTheory.RiemannZeta

private theorem sharp_interior {a x y : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x) (hxy' : x≤y)
    {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖≤604*x^(-s.re) := by
  have H (v : ℂ) (hv : 0<v.re) (hv' : v.re<1) (ht : v.im=2*Real.pi*x*y) :
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) v-hurwitzDirectSum a x v-hurwitzDualSum a y v‖≤604*x^(-v.re) := by
    apply (hurwitzZeta_sharp_afe_of_window ha hx (hx.trans hxy') hv hv' ht
      (hurwitz_frequency_window_uniform (a:=a) hx hxy' hv hv' ht)
      (hurwitz_frequency_boundary_uniform a x (by linarith) v _)).trans_eq
    ring
  rcases le_total 0 s.im with ht|ht
  · exact H s hσ hσ' ((abs_of_nonneg ht).symm.trans hxy)
  · have hs : s≠1 := fun he => by simp [he] at hσ'
    have h := H (conj s) hσ hσ' (by simpa [abs_of_nonpos ht] using hxy)
    rw [hurwitzZeta_conj_in_strip ha (by linarith) hs,hurwitzDirectSum_conj ha.1,hurwitzDualSum_conj,
      ←map_sub,←map_sub,Complex.norm_conj] at h
    exact h

/-- Uniform log-free sharp Hurwitz approximation throughout the full
closed strip, for either sign of the height and every real shift 0<a≤1. -/
theorem hurwitzZeta_logFree_sharp_afe {a x y : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x) (hxy' : x≤y)
    {s : ℂ} (hσ : s.re∈Icc (0:ℝ) 1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖≤604*x^(-s.re) := by
  have hx' : 0<x := by linarith
  have hy' := hx'.trans_le hxy'
  have ht : s.im≠0 := abs_pos.mp (hxy ▸ by positivity)
  let v (σ : ℝ) : ℂ := (σ:ℂ)+s.im*I
  have hv : Continuous v := by dsimp [v];fun_prop
  have hvi (σ : ℝ) : (v σ).im=s.im := by simp [v]
  have hvr (σ : ℝ) : (v σ).re=σ := by simp [v]
  have hζ : Continuous (fun σ => HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (v σ)) := by
    apply continuous_iff_continuousAt.mpr
    intro σ
    apply (HurwitzZeta.differentiableAt_hurwitzZeta _ ?_).continuousAt.comp hv.continuousAt
    intro he;have h := congrArg Complex.im he;rw [hvi,one_im] at h;exact ht h
  have hg : Continuous (fun σ => Complex.Gamma (1-v σ)) := by
    apply continuous_iff_continuousAt.mpr
    intro σ
    apply (Complex.continuousAt_Gamma _ ?_).comp (continuous_const.sub hv).continuousAt
    intro n hn
    have h := congrArg Complex.im hn
    simp [hvi] at h
    exact ht h
  have hD : Continuous (fun σ => hurwitzDirectSum a x (v σ)) := by
    unfold hurwitzDirectSum
    apply continuous_finsetSum
    intro n hn
    apply (continuous_const_cpow' ?_).comp hv.neg
    exact_mod_cast (show (n:ℝ)+a≠0 by linarith [ha.1,Nat.cast_nonneg (α:=ℝ) n])
  have hU : Continuous (fun σ => hurwitzDualSum a y (v σ)) := by
    unfold hurwitzDualSum
    apply continuous_finsetSum
    intro m hm
    have hm' (ω : ℝ) (hw : ω≠0) : Continuous (fun σ => hurwitzDualMode (v σ) ω) :=
      ((continuous_const_cpow' (hurwitzFrequency_ne hw)).comp (hv.sub continuous_const)).mul hg
    apply (continuous_const.mul (hm' _ (hurwitzOmega_pos m).ne')).add
    exact continuous_const.mul (hm' _ (neg_ne_zero.mpr (hurwitzOmega_pos m).ne'))
  have hc := isClosed_le (g:=fun σ : ℝ => 604*x^(-σ)) ((hζ.sub hD).sub hU).norm
    (continuous_const.mul ((continuous_const_rpow hx'.ne').comp continuous_neg))
  have H : closure (Ioo (0:ℝ) 1) ⊆ {σ : ℝ | ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (v σ)-
      hurwitzDirectSum a x (v σ)-hurwitzDualSum a y (v σ)‖ ≤ 604*x^(-σ)} := by
    apply closure_minimal _ hc
    intro σ hσ
    change ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (v σ)-hurwitzDirectSum a x (v σ)-hurwitzDualSum a y (v σ)‖≤604*x^(-σ)
    simpa only [hvr] using sharp_interior (s:=v σ) ha hx hxy' ((hvr σ).symm ▸ hσ.1) ((hvr σ).symm ▸ hσ.2)
      ((congrArg abs (hvi σ)).trans hxy)
  rw [closure_Ioo (by norm_num : (0:ℝ)≠1)] at H
  simpa only [v,Complex.re_add_im,mem_setOf_eq] using H hσ

/-- Ordinary zeta at the actual zero circle shift, with no logarithm in
the error term and with explicit direct and reciprocal cutoffs. -/
theorem riemannZeta_logFree_sharp_afe {x y : ℝ} (hx : 2≤x) (hxy' : x≤y) {s : ℂ}
    (hσ : s.re∈Icc (0:ℝ) 1) (hxy : |s.im|=2*Real.pi*x*y) :
    ‖riemannZeta s-(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s))-
      riemannDualGamma s*(∑ m∈range ⌊y⌋₊,((m:ℂ)+1)^(s-1))‖ ≤604*x^(-s.re) := by
  have H := hurwitzZeta_logFree_sharp_afe (a:=1) (by constructor <;>norm_num) hx hxy' hσ hxy
  rw [AddCircle.coe_period,HurwitzZeta.hurwitzZeta_zero,hurwitzDirectSum_one s (by linarith),hurwitzDualSum_one] at H
  exact H

/-- The balanced sharp Riemann–Siegel approximation on the critical line. -/
theorem riemannSiegel_sharp_error {t : ℝ} (ht : 8*Real.pi≤|t|) :
    let x := Real.sqrt (|t|/(2*Real.pi))
    let s := (1/2:ℂ)+(t:ℂ)*I
    ‖riemannZeta s-(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s))-
      riemannDualGamma s*(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(s-1))‖ ≤
      604*(2*Real.pi)^(1/4:ℝ)*|t|^(-(1/4:ℝ)) := by
  intro x s
  have hπ : 0<2*Real.pi := by positivity
  have hp : 0 < |t| := lt_of_lt_of_le (by positivity) ht
  have hxt : x^2=|t|/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have hx : 2≤x := by
    have h : (4:ℝ)≤|t|/(2*Real.pi) := (le_div_iff₀ hπ).mpr (by linarith)
    nlinarith [Real.sqrt_nonneg (|t|/(2*Real.pi))]
  have H := riemannZeta_logFree_sharp_afe (s:=s) hx (le_refl x) (by dsimp [s];norm_num)
    (by simp only [s,add_im,div_ofNat_im,one_im,zero_div,ofReal_im,mul_I_im,ofReal_re,zero_add]
        calc |t| = (2*Real.pi)*(x^2) := by rw [hxt];field_simp
             _ = _ := by ring)
  apply H.trans_eq
  rw [show s.re=1/2 by simp [s]]
  dsimp only [x]
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (div_nonneg hp.le hπ.le),show (1/2:ℝ)*(-(1/2))= -(1/4) by norm_num,
    Real.div_rpow hp.le hπ.le,Real.rpow_neg hπ.le,div_inv_eq_mul]
  ring

end AnalyticNumberTheory.RiemannZeta
