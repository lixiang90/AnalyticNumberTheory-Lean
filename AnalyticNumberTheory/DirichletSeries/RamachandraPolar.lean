import AnalyticNumberTheory.DirichletSeries.Ramachandra
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalResidue
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic

/-!
# Polar terms in Ramachandra's functional equation

An isolated pole of order at most `k+1` contributes the `k`-th Taylor
coefficient of the pole-cleared function multiplied by the Gamma kernel.
The abscissa of the pole lies between zero and the original right contour.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletSeries

/-- The residue of the Gamma kernel times a function with numerator `G` and
denominator `(w-p)^(k+1)`. The pole location is measured relative to the center. -/
noncomputable def gammaSmoothingResidue (G : ℂ → ℂ) (X : ℝ) (p : ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k (fun w : ℂ => G w*Complex.Gamma w*(X:ℂ)^w) p/(k.factorial:ℂ)

@[simp] theorem gammaSmoothingResidue_simple (G : ℂ → ℂ) (X : ℝ) (p : ℂ) :
    gammaSmoothingResidue G X p 0 = G p*Complex.Gamma p*(X:ℂ)^p := by
  simp [gammaSmoothingResidue]

private theorem growth_left_of_pole {G H : ℂ → ℂ} {p : ℂ} {l r c : ℝ} {k : ℕ}
    (hc : c<p.re) (hcr : c≤r) (hg : PolynomialGrowthOnStrip G l r)
    (hrep : ∀ w : ℂ, w≠p → H w=G w/(w-p)^(k+1)) :
    PolynomialGrowthOnStrip H l c := by
  obtain ⟨A,hA,m,hB⟩ := hg.bound
  have hi (z : ℂ) (hz : z.re∈Icc l c) : z.re∈Icc l r := ⟨hz.1,hz.2.trans hcr⟩
  have hn (z : ℂ) (hz : z.re∈Icc l c) : z≠p := by
    rintro rfl; exact (not_le_of_gt hc) hz.2
  refine ⟨?_, A/(p.re-c)^(k+1),by positivity,m,?_⟩
  · intro z hz
    have han : AnalyticAt ℂ (fun w => G w/(w-p)^(k+1)) z :=
      (hg.analytic _ (hi z hz)).div ((analyticAt_id.sub analyticAt_const).pow _) (pow_ne_zero _ (sub_ne_zero.mpr (hn z hz)))
    apply han.congr
    filter_upwards [eventually_ne_nhds (hn z hz)] with w hw
    exact (hrep w hw).symm
  · intro z hz
    have hd : p.re-c ≤ ‖z-p‖ := by
      calc _ ≤ -(z-p).re := by simp; linarith [hz.2]
           _ ≤ _ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    rw [hrep z (hn z hz),norm_div,norm_pow]
    apply (div_le_div₀ (by positivity) (hB z (hi z hz)) (pow_pos (sub_pos.mpr hc) _)
      (pow_le_pow_left₀ (sub_nonneg.mpr hc.le) hd _)).trans_eq
    ring

/-- Moving the Gamma smoothing contour past its own pole at zero and a
finite-order pole of the original function. -/
theorem gammaSmoothingIntegral_sub_residue {G H : ℂ → ℂ} {p : ℂ} {l r X : ℝ} (k : ℕ)
    (hl : -1<l) (hl0 : l<0) (hp : 0<p.re) (hpr : p.re<r) (hX : 0<X)
    (hg : PolynomialGrowthOnStrip G l r)
    (hrep : ∀ w : ℂ, w≠p → H w=G w/(w-p)^(k+1)) :
    gammaSmoothingIntegral H X r - gammaSmoothingIntegral H X l =
      H 0+gammaSmoothingResidue G X p k := by
  let c := p.re/2
  have hc : 0<c := by dsimp [c]; positivity
  have hcp : c<p.re := by dsimp [c]; linarith
  have hcr := (hcp.trans hpr).le
  have hcL := growth_left_of_pole hcp hcr hg hrep
  obtain ⟨A,hA,m,hB⟩ := hcL.bound
  have h₁ := gammaSmoothingIntegral_sub hl hl0 hc hX m hA hcL.analytic hB
  obtain ⟨B,hB0,n,hgB⟩ := hg.bound
  obtain ⟨D,hD,hdec⟩ := gamma_smoothing_bound hl (by linarith : l≤r) hX n hB0 hgB
  let J (w : ℂ) := G w*Complex.Gamma w*(X:ℂ)^w
  have hi (z : ℂ) (hz : z.re∈Icc c r) : z.re∈Icc l r := ⟨by linarith [hz.1],hz.2⟩
  have hJ (z : ℂ) (hz : z.re∈Icc c r) : AnalyticAt ℂ J z := by
    have hga := Gamma.analyticOnNhd_gamma z (Gamma.mem_nonPoleSet_of_re_pos (hc.trans_le hz.1))
    have hpow : AnalyticAt ℂ (fun w : ℂ => (X:ℂ)^w) z :=
      (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).analyticAt z
    exact ((hg.analytic z (hi z hz)).mul hga).mul hpow
  have hJd (x : ℝ) (hx : x∈Icc c r) (t : ℝ) :
      ‖J ((x:ℂ)+t*I)‖ ≤ (D/c)/(1+t^2) := by
    let w : ℂ := x+t*I
    have hw : c≤‖w‖ := hx.1.trans (by simpa [w] using Complex.re_le_norm w)
    have hn : w≠0 := norm_pos_iff.mp (hc.trans_le hw)
    have he : J w=(G w*Complex.Gamma (w+1)*(X:ℂ)^w)/w := by
      rw [Complex.Gamma_add_one _ hn]; dsimp [J]; field_simp [hn]
    change ‖J w‖≤_
    rw [he,norm_div]
    exact (div_le_div₀ (by positivity) (hdec x ⟨by linarith [hx.1],hx.2⟩ t) hc hw).trans_eq (by ring)
  have h₂ := integral_verticalLine_sub_residue k hcp hpr hJ (div_nonneg hD hc.le) hJd
  have he (u : ℝ) (hu : u≠p.re) : gammaSmoothingIntegral H X u =
      (2*(π:ℂ))⁻¹*(∫ t : ℝ, J ((u:ℂ)+t*I)/((u:ℂ)+t*I-p)^(k+1)) := by
    unfold gammaSmoothingIntegral; congr 1
    apply integral_congr_ae; filter_upwards with t
    have hn : (u:ℂ)+t*I≠p := fun h => hu (by simpa using congrArg Complex.re h)
    rw [hrep _ hn]; dsimp [J]; ring
  have hs : gammaSmoothingIntegral H X r-gammaSmoothingIntegral H X c =
      gammaSmoothingResidue G X p k := by
    rw [he r hpr.ne',he c hcp.ne,← mul_sub,h₂]
    dsimp [gammaSmoothingResidue,J]
    field_simp [Real.pi_ne_zero]
  linear_combination hs + h₁

/-- Ramachandra's smoothed functional equation with its exact polar contribution.
For a simple pole the subtracted term is `G p * Γ(p) * X^p`. -/
theorem ramachandra_smoothed_functional_equation_with_pole {a b : ℕ → ℂ} {F ψ G : ℂ → ℂ}
    (s : ℂ) (N k : ℕ) {p : ℂ} {l r d X : ℝ} (hl : -1<l) (hl0 : l<0) (hp : 0<p.re)
    (hpr : p.re<r) (hd : 0<d) (hX : 0<X)
    (hF : ∀ t : ℝ, LSeriesHasSum a (s+((r:ℂ)+t*I)) (F (s+((r:ℂ)+t*I))))
    (hFE : ∀ t : ℝ, let z := s+((l:ℂ)+t*I)
      ∃ S : ℂ, LSeriesHasSum b (1-z) S ∧ F z=ψ z*S)
    (hg : PolynomialGrowthOnStrip G l r)
    (hrep : ∀ w : ℂ, w≠p → F (s+w)=G w/(w-p)^(k+1))
    (hψ : PolynomialGrowthOnStrip (fun w => ψ (s+w)) l d) :
    F s = (∑' n : ℕ, LSeries.term a s n*(Real.exp (-(n:ℝ)/X):ℂ)) +
      ψ s*dirichletPartialSum b (1-s) N -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletTail b (1-(s+w)) N) X l -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletPartialSum b (1-(s+w)) N) X d -
      gammaSmoothingResidue G X p k :=
  ramachandra_split_of_shift s _ N hl hl0 (hp.trans hpr) hd hX hF hFE hψ
    (growth_left_of_pole (hl0.trans hp) (hl0.trans (hp.trans hpr)).le hg hrep)
    (by simpa only [add_zero] using gammaSmoothingIntegral_sub_residue k hl hl0 hp hpr hX hg hrep)

end AnalyticNumberTheory.DirichletSeries
