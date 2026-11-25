import AnalyticNumberTheory.DirichletSeries.FrequencyAbel
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The half-plane of convergence of a general Dirichlet series -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℂ}

/-- Ordered convergence at even one point bounds the partial sums there at
every frequency cutoff. -/
theorem ConvergesAt.exists_bound {s₀ : ℂ} (h : F.ConvergesAt a s₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖F.summatory a s₀ u‖ ≤ C := by
  obtain ⟨C,hC⟩ := h.tendsto.norm.bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun u => (hC ⟨F.count u,rfl⟩).trans (le_max_left _ _)⟩

theorem ConvergesAt.of_re_lt {s₀ s : ℂ} (h : F.ConvergesAt a s₀) (hs : s₀.re < s.re) :
    F.ConvergesAt a s := by
  obtain ⟨C,_,hC⟩ := h.exists_bound
  have H := F.tendsto_partialSum_integral a (α := 0) (s₀ := s₀)
    (fun u _ => by simpa using hC u) (z := s-s₀) (by simpa using sub_pos.mpr hs)
  exact ⟨_, by simpa only [add_sub_cancel] using H⟩

theorem abscissa_le_re {s : ℂ} (h : F.ConvergesAt a s) : F.abscissa a ≤ (s.re : EReal) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx => ?_
  have H : F.ConvergesAt a (x : ℂ) := h.of_re_lt (by simpa using EReal.coe_lt_coe_iff.mp hx)
  exact sInf_le ⟨x,H,rfl⟩

theorem exists_real_of_abscissa_lt {t : ℝ} (h : F.abscissa a < (t : EReal)) :
    ∃ σ : ℝ, F.ConvergesAt a σ ∧ σ < t := by
  rw [abscissa, sInf_lt_iff] at h
  obtain ⟨_,⟨σ,hσ,rfl⟩,hlt⟩ := h
  exact ⟨σ,hσ,EReal.coe_lt_coe_iff.mp hlt⟩

theorem convergesAt_of_abscissa_lt {s : ℂ} (h : F.abscissa a < (s.re : EReal)) :
    F.ConvergesAt a s := by
  obtain ⟨σ,hσ,hs⟩ := exists_real_of_abscissa_lt h
  exact hσ.of_re_lt hs

/-- Uniform convergence in frequency strips that may widen exponentially
toward the right. Write `d = Re (s - s₀) - α`. The hypotheses bound the
displacement by `K d exp(H d)` and keep `d` at least `δ > 0`. -/
theorem tendstoUniformlyOn_of_summatory_bound {s₀ : ℂ} {α C δ H K : ℝ} {S : Set ℂ}
    (hC : 0 ≤ C) (h : ∀ u, F 0 ≤ u → ‖F.summatory a s₀ u‖ ≤ C * Real.exp (α*u))
    (hδ : 0 < δ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hS : ∀ s ∈ S, let d := (s-s₀).re-α
      δ ≤ d ∧ ‖s-s₀‖ ≤ K * d * Real.exp (H*d)) :
    TendstoUniformlyOn (fun N s => F.partialSum a s N) (F.sum a) atTop S := by
  have he : Tendsto (fun n => C*(1+K)*Real.exp (-δ * (F n-H))) atTop (𝓝 0) := by
    have hF : Tendsto (fun n => F n-H) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-H) F.tendsto_atTop
    simpa using (Real.tendsto_exp_atBot.comp (hF.const_mul_atTop_of_neg (neg_lt_zero.mpr hδ))).const_mul (C*(1+K))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((F.tendsto_atTop.eventually_ge_atTop H).and (he.eventually (gt_mem_nhds hε)))
  refine eventually_atTop.mpr ⟨N+1, ?_⟩
  rintro (_|n) hn s hs
  · omega
  have hn' : N ≤ n := by omega
  obtain ⟨hFn,hεn⟩ := hN n hn'
  let z := s-s₀
  let d := z.re-α
  obtain ⟨hd,hz⟩ := hS s hs
  have hd' : 0 < d := hδ.trans_le hd
  have hzdiv : ‖z‖/d ≤ K * Real.exp (H*d) := (div_le_iff₀ hd').mpr (by
    calc
      ‖z‖ ≤ K*d*Real.exp (H*d) := hz
      _ = _ := by ring)
  have h₁ : 1 ≤ Real.exp (H*d) := Real.one_le_exp (mul_nonneg hH hd'.le)
  have hbound := F.norm_partialSum_sub_sum_le a h (z := z) (sub_pos.mp hd') n
  have heq : s₀+z = s := add_sub_cancel _ _
  rw [dist_comm, dist_eq_norm, ← heq]
  apply hbound.trans_lt
  apply lt_of_le_of_lt _ hεn
  calc
    C * (1 + ‖z‖ / d) * Real.exp (-d * F n) ≤ C * ((1+K)*Real.exp (H*d)) * Real.exp (-d*F n) := by
      gcongr
      nlinarith only [h₁,hzdiv]
    _ = C*(1+K)*Real.exp (-d*(F n-H)) := by
      rw [← mul_assoc C, mul_assoc (C*(1+K)), ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by gcongr

private lemma isOpen_halfPlane (F : DirichletFrequency) (a : ℕ → ℂ) :
    IsOpen {s : ℂ | F.abscissa a < (s.re : EReal)} :=
  isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)

/-- The series converges locally uniformly on its full open half-plane of
ordered convergence, even where its terms need not be absolutely summable. -/
theorem tendstoLocallyUniformlyOn_partialSum (F : DirichletFrequency) (a : ℕ → ℂ) :
    TendstoLocallyUniformlyOn (fun N s => F.partialSum a s N) (F.sum a) atTop
      {s : ℂ | F.abscissa a < (s.re : EReal)} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_halfPlane F a)]
  intro S hsub hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨σ,hσ,hlt⟩ := exists_real_of_abscissa_lt (hsub hp)
  obtain ⟨C,hC,hbound⟩ := hσ.exists_bound
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn
    ((continuous_id.sub continuous_const).continuousOn : ContinuousOn (fun s : ℂ => s-(σ : ℂ)) S)
  let δ := p.re-σ
  have hδ : 0 < δ := sub_pos.mpr hlt
  have hM₀ := (norm_nonneg _).trans (hM p hp)
  apply tendstoUniformlyOn_of_summatory_bound (s₀ := (σ : ℂ)) (α := 0) hC
    (fun u _ => by simpa using hbound u) hδ (H := 0) le_rfl (K := M/δ) (div_nonneg hM₀ hδ.le)
  intro s hs
  simp only [sub_re, ofReal_re, sub_zero, zero_mul, Real.exp_zero, mul_one]
  have hds : δ ≤ s.re-σ := sub_le_sub_right (hmin hs) _
  refine ⟨hds,(hM s hs).trans ?_⟩
  calc
    M = (M/δ)*δ := (div_mul_cancel₀ M hδ.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hds (div_nonneg hM₀ hδ.le)

/-- Holomorphy on the open half-plane of convergence for every frequency. -/
theorem analyticOnNhd_sum (F : DirichletFrequency) (a : ℕ → ℂ) :
    AnalyticOnNhd ℂ (F.sum a) {s : ℂ | F.abscissa a < (s.re : EReal)} := by
  have hd (N : ℕ) : Differentiable ℂ (fun s => F.partialSum a s N) := by
    unfold partialSum
    fun_prop
  exact ((F.tendstoLocallyUniformlyOn_partialSum a).differentiableOn
    (.of_forall fun N => (hd N).differentiableOn) (isOpen_halfPlane F a)).analyticOnNhd (isOpen_halfPlane F a)

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
