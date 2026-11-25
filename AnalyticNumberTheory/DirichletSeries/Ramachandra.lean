import AnalyticNumberTheory.DirichletSeries.ExponentialSmoothing

/-!
# Ramachandra's exponentially smoothed functional equation

The first contour shift picks up the value of the original function. On
the new line the functional equation gives a convergent dual series. Its
finite initial segment can be moved back to a positive line, giving the
dual Dirichlet polynomial and two explicit remainder integrals.
-/

open Complex Real Set MeasureTheory Filter
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletSeries

/-- Holomorphy and uniform polynomial growth on a closed vertical strip. -/
structure PolynomialGrowthOnStrip (H : ℂ → ℂ) (l r : ℝ) : Prop where
  analytic : ∀ z : ℂ, z.re∈Icc l r → AnalyticAt ℂ H z
  bound : ∃ A : ℝ, 0≤A ∧ ∃ m : ℕ, ∀ z : ℂ, z.re∈Icc l r → ‖H z‖≤A*(1+|z.im|)^m

theorem PolynomialGrowthOnStrip.mul {H G : ℂ → ℂ} {l r : ℝ}
    (h : PolynomialGrowthOnStrip H l r) (g : PolynomialGrowthOnStrip G l r) :
    PolynomialGrowthOnStrip (fun w => H w*G w) l r := by
  obtain ⟨A,hA,m,hm⟩ := h.bound
  obtain ⟨B,hB,n,hn⟩ := g.bound
  refine ⟨fun z hz => (h.analytic z hz).mul (g.analytic z hz),A*B,mul_nonneg hA hB,m+n,?_⟩
  intro z hz
  rw [norm_mul,pow_add]
  calc _ ≤ (A*(1+|z.im|)^m)*(B*(1+|z.im|)^n) :=
             mul_le_mul (hm z hz) (hn z hz) (norm_nonneg _) (by positivity)
       _ = _ := by ring

private theorem dualPolynomial_growth (b : ℕ → ℂ) (s : ℂ) (N : ℕ) (l r : ℝ) :
    PolynomialGrowthOnStrip (fun w => dirichletPartialSum b (1-(s+w)) N) l r := by
  refine ⟨fun z _ => ((dirichletPartialSum_differentiable b N).analyticAt _).comp
    (analyticAt_const.sub (analyticAt_const.add analyticAt_id)),?_,?_,0,?_⟩
  · exact ∑ n ∈ Finset.Icc 1 N, ‖LSeries.term b ((1-s.re-r:ℝ):ℂ) n‖
  · positivity
  · intro z hz
    rw [pow_zero,mul_one]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ =>
      LSeries.norm_term_le_of_re_le_re b (by simp; linarith [hz.2]) n))

private theorem integrable_on_left {H : ℂ → ℂ} {l r X : ℝ} (hl : -1<l) (hl0 : l<0)
    (hlr : l≤r) (hX : 0<X) (hH : PolynomialGrowthOnStrip H l r) :
    Integrable (fun t : ℝ => let w : ℂ := l+t*I; H w*Complex.Gamma w*(X:ℂ)^w) := by
  let w (t : ℝ) : ℂ := l+t*I
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hz (t : ℝ) : (w t).re∈Icc l r := by simp [w,hlr]
  have hnorm (t : ℝ) : -l≤‖w t‖ := by simpa [w,abs_of_neg hl0] using Complex.abs_re_le_norm (w t)
  have hn (t : ℝ) : w t≠0 := norm_pos_iff.mp ((neg_pos.mpr hl0).trans_le (hnorm t))
  have hHc : Continuous (fun t => H (w t)) := continuous_iff_continuousAt.mpr
    (fun t => (hH.analytic _ (hz t)).continuousAt.comp hw.continuousAt)
  have hGc : Continuous (fun t => Complex.Gamma (w t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g:=Complex.Gamma) _ hw.continuousAt
    apply DifferentiableAt.continuousAt (𝕜:=ℂ)
    apply Complex.differentiableAt_Gamma
    intro n he
    have hr := congrArg Complex.re he
    simp [w] at hr
    cases n with
    | zero => simp at hr; linarith
    | succ n => push_cast at hr; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : Continuous (fun t => (X:ℂ)^(w t)) :=
    (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp hw
  obtain ⟨A,hA,m,hb⟩ := hH.bound
  obtain ⟨D,hD,hd⟩ := gamma_smoothing_bound hl hlr hX m hA hb
  apply (integrable_inv_one_add_sq.const_mul (D/(-l))).mono' ((hHc.mul hGc).mul hp).aestronglyMeasurable
  filter_upwards with t
  have he : H (w t)*Complex.Gamma (w t)*(X:ℂ)^w t =
      (H (w t)*Complex.Gamma (w t+1)*(X:ℂ)^w t)/(w t) := by
    rw [Complex.Gamma_add_one _ (hn t)]; field_simp [hn t]
  change ‖H (w t)*Complex.Gamma (w t)*(X:ℂ)^w t‖ ≤ _
  rw [he,norm_div]
  exact (div_le_div₀ (by positivity) (hd l ⟨le_rfl,hlr⟩ t) (neg_pos.mpr hl0) (hnorm t)).trans_eq (by ring)

/-- The dual Dirichlet series restricted to indices strictly above the truncation. -/
noncomputable def dirichletTail (b : ℕ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  ∑' n : ℕ, LSeries.term b z (n+(N+1))

theorem dirichletPartialSum_add_tail {b : ℕ → ℂ} {z v : ℂ} (N : ℕ) (h : LSeriesHasSum b z v) :
    dirichletPartialSum b z N + dirichletTail b z N = v := by
  have he : dirichletPartialSum b z N = ∑ n ∈ Finset.range (N+1), LSeries.term b z n := by
    apply Finset.sum_subset
    · intro n hn; simp only [Finset.mem_Icc] at hn; simpa using hn.2
    · intro n hn hn'
      have hnN : n≤N := by simpa using hn
      obtain rfl : n=0 := by by_contra hc; exact hn' (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hc,hnN⟩)
      simp
  rw [he,dirichletTail,h.summable.sum_add_tsum_nat_add (N+1),h.tsum_eq]

/-- Assemble the two-contour formula from the first displacement and its crossed residues. -/
theorem ramachandra_split_of_shift {a b : ℕ → ℂ} {F ψ : ℂ → ℂ} (s R : ℂ)
    (N : ℕ) {l r d X : ℝ} (hl : -1<l) (hl0 : l<0) (hr : 0<r) (hd : 0<d) (hX : 0<X)
    (hF : ∀ t : ℝ, LSeriesHasSum a (s+((r:ℂ)+t*I)) (F (s+((r:ℂ)+t*I))))
    (hFE : ∀ t : ℝ, let z := s+((l:ℂ)+t*I)
      ∃ G : ℂ, LSeriesHasSum b (1-z) G ∧ F z=ψ z*G)
    (hψ : PolynomialGrowthOnStrip (fun w => ψ (s+w)) l d)
    (hleft : PolynomialGrowthOnStrip (fun w => F (s+w)) l l)
    (hshift : gammaSmoothingIntegral (fun w => F (s+w)) X r -
      gammaSmoothingIntegral (fun w => F (s+w)) X l = F s + R) :
    F s = (∑' n : ℕ, LSeries.term a s n*(Real.exp (-(n:ℝ)/X):ℂ)) +
      ψ s*dirichletPartialSum b (1-s) N -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletTail b (1-(s+w)) N) X l -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletPartialSum b (1-(s+w)) N) X d - R := by
  let P (w : ℂ) := ψ (s+w)*dirichletPartialSum b (1-(s+w)) N
  let E (w : ℂ) := ψ (s+w)*dirichletTail b (1-(s+w)) N
  have hP : PolynomialGrowthOnStrip P l d := hψ.mul (dualPolynomial_growth b s N l d)
  obtain ⟨A,hA,m,hm⟩ := hP.bound
  have hdual := gammaSmoothingIntegral_sub hl hl0 hd hX m hA hP.analytic hm
  have hEs (t : ℝ) : E ((l:ℂ)+t*I) = F (s+((l:ℂ)+t*I))-P ((l:ℂ)+t*I) := by
    obtain ⟨G,hG,he⟩ := hFE t
    rw [he,← dirichletPartialSum_add_tail N hG]
    dsimp [E,P]; ring
  have hleftEq : gammaSmoothingIntegral E X l = gammaSmoothingIntegral (fun w => F (s+w)) X l -
      gammaSmoothingIntegral P X l := by
    have hi := integrable_on_left hl hl0 le_rfl hX hleft
    have hj := integrable_on_left hl hl0 (by linarith : l≤d) hX hP
    unfold gammaSmoothingIntegral
    simp_rw [hEs,sub_mul]
    rw [integral_sub hi hj,mul_sub]
  rw [(hasSum_exponentiallySmoothed s hr hX hF).tsum_eq]
  change F s = _ + ψ s*dirichletPartialSum b (1-s) N - gammaSmoothingIntegral E X l -
    gammaSmoothingIntegral P X d - R
  have he : P 0=ψ s*dirichletPartialSum b (1-s) N := by simp [P]
  rw [he] at hdual
  linear_combination -hshift + hleftEq + hdual

/-- Ramachandra's two-contour identity for a pole-free strip. The original and dual
right-hand contours and the truncation of the dual sum may all be chosen independently. -/
theorem ramachandra_smoothed_functional_equation {a b : ℕ → ℂ} {F ψ : ℂ → ℂ} (s : ℂ)
    (N : ℕ) {l r d X : ℝ} (hl : -1<l) (hl0 : l<0) (hr : 0<r) (hd : 0<d) (hX : 0<X)
    (hF : ∀ t : ℝ, LSeriesHasSum a (s+((r:ℂ)+t*I)) (F (s+((r:ℂ)+t*I))))
    (hFE : ∀ t : ℝ, let z := s+((l:ℂ)+t*I)
      ∃ G : ℂ, LSeriesHasSum b (1-z) G ∧ F z=ψ z*G)
    (hFstrip : PolynomialGrowthOnStrip (fun w => F (s+w)) l r)
    (hψ : PolynomialGrowthOnStrip (fun w => ψ (s+w)) l d) :
    F s = (∑' n : ℕ, LSeries.term a s n*(Real.exp (-(n:ℝ)/X):ℂ)) +
      ψ s*dirichletPartialSum b (1-s) N -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletTail b (1-(s+w)) N) X l -
      gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletPartialSum b (1-(s+w)) N) X d := by
  obtain ⟨A,hA,m,hm⟩ := hFstrip.bound
  have hi (z : ℂ) (hz : z.re∈Icc l l) : z.re∈Icc l r := ⟨hz.1,by linarith [hz.2]⟩
  have hleft : PolynomialGrowthOnStrip (fun w => F (s+w)) l l :=
    ⟨fun z hz => hFstrip.analytic z (hi z hz),A,hA,m,fun z hz => hm z (hi z hz)⟩
  simpa using ramachandra_split_of_shift s 0 N hl hl0 hr hd hX hF hFE hψ hleft
    (by simpa using gammaSmoothingIntegral_sub hl hl0 hr hX m hA hFstrip.analytic hm)

end AnalyticNumberTheory.DirichletSeries
