import AnalyticNumberTheory.DirichletSeries.FrequencySpectrum

/-! # Uniqueness for different Dirichlet exponent sequences -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

private lemma zero_of_scaled_polynomial {ι : Type*} {l : Filter ι} [l.NeBot] {t : ι → ℝ}
    (ht : Tendsto t l atTop) (S : Finset ℝ) (c : ℝ → ℂ)
    (h : ∀ v ∈ S, Tendsto (fun k => ∑ r ∈ S, c r * (Real.exp ((v-r)*t k) : ℂ)) l (𝓝 0)) :
    ∀ v ∈ S, c v = 0 := by
  classical
  intro v hv
  by_contra hcv
  let D := S.filter (fun r => c r ≠ 0)
  have hne : D.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hcv⟩⟩
  let w := D.min' hne
  have hwD : w ∈ D := Finset.min'_mem D hne
  obtain ⟨hw, hcw⟩ := Finset.mem_filter.mp hwD
  have hlim (r : ℝ) (hr : r ∈ S) :
      Tendsto (fun k => c r * (Real.exp ((w-r)*t k) : ℂ)) l (𝓝 (if r = w then c w else 0)) := by
    rcases lt_trichotomy r w with hlt | he | hgt
    · have hz : c r = 0 := by
        by_contra hr0
        exact hlt.not_ge (Finset.min'_le D r (Finset.mem_filter.mpr ⟨hr, hr0⟩))
      simp [hz, hlt.ne]
    · subst r
      simp
    · have H := Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (sub_neg.mpr hgt))
      simpa [hgt.ne', Function.comp_def] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp H).const_mul (c r)
  have H : Tendsto (fun k => ∑ r ∈ S, c r * (Real.exp ((w-r)*t k) : ℂ)) l (𝓝 (c w)) := by
    simpa [hw] using tendsto_finsetSum S hlim
  exact hcw (tendsto_nhds_unique H (h w hw))

private lemma scaled_summatory (F : DirichletFrequency) (a : ℕ → ℂ) {S : Finset ℝ} {u : ℝ}
    (hs : F.exponentsThrough u ⊆ S) (hu : ∀ v ∈ S, v ≤ u) (w t : ℝ) :
    Complex.exp ((t : ℂ) * w) * F.summatory a t u =
      ∑ r ∈ S, F.coefficientAt a r * (Real.exp ((w-r)*t) : ℂ) := by
  rw [F.summatory_eq_sum_coefficientAt a hs hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_left_comm, ← Complex.exp_add, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- Two general Dirichlet series with possibly different frequencies that
agree along real arguments tending to infinity have the same coefficient at
every real exponent. A point of ordered convergence for each series suffices.
Zero coefficients and inserted or omitted zero terms are allowed. -/
theorem coefficientAt_eq_of_sum_eq {F G : DirichletFrequency} {a b : ℕ → ℂ} {σ τ : ℝ}
    (ha : F.ConvergesAt a (σ : ℂ)) (hb : G.ConvergesAt b (τ : ℂ))
    {ι : Type*} {l : Filter ι} [l.NeBot] {t : ι → ℝ} (ht : Tendsto t l atTop)
    (he : ∀ᶠ k in l, F.sum a (t k) = G.sum b (t k)) :
    F.coefficientAt a = G.coefficientAt b := by
  classical
  funext u
  let S := F.exponentsThrough u ∪ G.exponentsThrough u
  have hF : F.exponentsThrough u ⊆ S := Finset.subset_union_left
  have hG : G.exponentsThrough u ⊆ S := Finset.subset_union_right
  have hu (v : ℝ) (hv : v ∈ S) : v ≤ u :=
    (Finset.mem_union.mp hv).elim (fun h => (F.mem_exponentsThrough.mp h).1)
      (fun h => (G.mem_exponentsThrough.mp h).1)
  by_cases hmem : u ∈ S
  · let c (v : ℝ) := F.coefficientAt a v - G.coefficientAt b v
    have H (w : ℝ) (hw : w ∈ S) :
        Tendsto (fun k => ∑ r ∈ S, c r * (Real.exp ((w-r)*t k) : ℂ)) l (𝓝 0) := by
      have hR := (hb.tendsto_scaled_cutoff_remainder (hu w hw)).comp ht
      have hL := (ha.tendsto_scaled_cutoff_remainder (hu w hw)).comp ht
      have hsub := hR.sub hL
      rw [sub_zero] at hsub
      apply hsub.congr'
      filter_upwards [he] with k hk
      have hterm (r : ℝ) : c r * (Real.exp ((w-r)*t k) : ℂ) =
          F.coefficientAt a r * (Real.exp ((w-r)*t k) : ℂ) -
          G.coefficientAt b r * (Real.exp ((w-r)*t k) : ℂ) := sub_mul _ _ _
      simp only [Function.comp_apply, hterm, Finset.sum_sub_distrib,
        ← scaled_summatory F a hF hu w (t k), ← scaled_summatory G b hG hu w (t k)]
      rw [hk]
      ring
    exact sub_eq_zero.mp (zero_of_scaled_polynomial ht S c H u hmem)
  · rw [F.coefficientAt_of_notMem_range a (fun h => hmem (hF (F.mem_exponentsThrough.mpr ⟨le_rfl, h⟩))),
      G.coefficientAt_of_notMem_range b (fun h => hmem (hG (G.mem_exponentsThrough.mpr ⟨le_rfl, h⟩)))]

/-- If both series list only nonzero coefficients, agreement along a real
sequence tending to infinity recovers their increasing exponent sequences as
well as every coefficient. -/
theorem exponents_and_coefficients_eq_of_nonzero {F G : DirichletFrequency} {a b : ℕ → ℂ}
    {σ τ : ℝ} (ha : F.ConvergesAt a (σ : ℂ)) (hb : G.ConvergesAt b (τ : ℂ))
    (ha0 : ∀ n, a n ≠ 0) (hb0 : ∀ n, b n ≠ 0) {ι : Type*} {l : Filter ι} [l.NeBot] {t : ι → ℝ}
    (ht : Tendsto t l atTop) (he : ∀ᶠ k in l, F.sum a (t k) = G.sum b (t k)) :
    F.exponent = G.exponent ∧ a = b := by
  have hc := coefficientAt_eq_of_sum_eq ha hb ht he
  have hrange : Set.range F.exponent = Set.range G.exponent := by
    ext u
    constructor
    · rintro ⟨n, rfl⟩
      by_contra hn
      exact ha0 n (by simpa only [F.coefficientAt_exponent, G.coefficientAt_of_notMem_range b hn]
        using congrFun hc (F n))
    · rintro ⟨n, rfl⟩
      by_contra hn
      exact hb0 n (by simpa only [G.coefficientAt_exponent, F.coefficientAt_of_notMem_range a hn]
        using congrFun hc.symm (G n))
  have hfreq := (F.strictMono.range_inj_of_wellFoundedLT G.strictMono).mp hrange
  refine ⟨hfreq, funext fun n => ?_⟩
  calc
    a n = F.coefficientAt a (F n) := (F.coefficientAt_exponent a n).symm
    _ = G.coefficientAt b (G n) := by rw [hc, congrFun hfreq n]
    _ = b n := G.coefficientAt_exponent b n

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
