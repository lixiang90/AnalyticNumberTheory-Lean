import AnalyticNumberTheory.AdditiveNumberTheory.WaringUniformDensities

/-!
# A uniform lower bound on the Waring major arcs

For a fixed positive fraction of the main scale, both singular factors stay
away from zero. This estimate permits a varying target after subtracting the
powers coming from shorter ranges.
-/

open Finset MeasureTheory Filter Real
open scoped Topology

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- The major-arc integral at the fixed dissection with denominator cutoff `P^(1/10)`. -/
noncomputable def waringMajorContribution (k s P n : ℕ) : ℂ :=
  majorArcIntegralFixed (fun α => waringSum k P α ^ s * e (-α * n))
    ((P:ℝ)^(1/10:ℝ)) ((P:ℝ)^((k:ℝ)-1/10))

/-- The normalized major-arc contribution has a uniform singular-factor approximation,
for every varying target and every sequence of cutoff lengths tending to infinity. -/
theorem tendsto_waringMajorContribution_sub_singularFactors {k s : ℕ} (hk : 2≤k) (hs : 2*k<s)
    {ι : Type*} {l : Filter ι} (P n : ι → ℕ) (hP : Tendsto P l atTop) :
    Tendsto (fun i => waringMajorContribution k s (P i) (n i)/(P i:ℂ)^(s-k) -
      waringSingularSeries k s (n i)*waringSingularIntegral s k ((n i:ℝ)/(P i:ℝ)^k)) l (𝓝 0) := by
  let A (i : ι) := (P i:ℝ)^(1/10:ℝ)
  let t (i : ι) := (n i:ℝ)/(P i:ℝ)^k
  let M (i : ι) := (∑ q ∈ Icc 1 ⌊A i⌋₊, waringSingularTerm k s (n i) q) *
    ∫ γ in (-(A i))..(A i), waringOscillatoryIntegral k γ ^ s * e (-γ * t i)
  let K := 2*(s:ℝ)*2^(s-1)*(3+4*Real.pi)
  have hp : Tendsto (fun i => (P i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hP
  have hA : Tendsto A l atTop := (tendsto_rpow_atTop (by norm_num)).comp hp
  have hmain : Tendsto (fun i => waringMajorContribution k s (P i) (n i)/(P i:ℂ)^(s-k)-M i) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hv := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hp).const_mul K
    apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ (by simpa using hv)
    filter_upwards [hP.eventually_ge_atTop 3] with i hi
    have hp2 : (2:ℝ)<P i := by exact_mod_cast (by omega : 2<P i)
    have hp0 : (0:ℝ)<P i := by linarith
    have hpc : (P i:ℂ)≠0 := by exact_mod_cast hp0.ne'
    obtain ⟨h₁,h₂,h₃⟩ := waringArcParameters hp2 hk
    have h := norm_waringMajorArc_sub_truncated_le (n:=n i) (by omega : k≤s) (by omega : 0<P i) h₁ h₂
    rw [h₃] at h
    have hraw := h.trans (waringMajorError_le hp2 hk (by omega : 0<s))
    rw [show waringMajorContribution k s (P i) (n i)/(P i:ℂ)^(s-k)-M i =
      (waringMajorContribution k s (P i) (n i)-(P i:ℂ)^(s-k)*M i)/(P i:ℂ)^(s-k) by field_simp,
      norm_div, norm_pow, Complex.norm_natCast, div_le_iff₀ (pow_pos hp0 _)]
    apply hraw.trans_eq
    change K * _ = K * _ * _
    conv_rhs =>
      rw [mul_assoc, ← Real.rpow_natCast (P i:ℝ) (s-k), ← Real.rpow_add hp0, Nat.cast_sub (by omega : k≤s)]
    congr 2
    ring
  have hf := tendsto_waringTruncated_sub_singularFactors (by omega : 0<k) hs A t n hA
  simpa only [M,t,sub_add_sub_cancel,add_zero] using hmain.add hf

/-- Every shifted target in `[P^k/4,P^k]` gives a positive major-arc contribution
of order `P^(s-k)` when the number of full-length variables is at least `4k`. -/
theorem eventually_waringMajorContribution_re_ge {k s : ℕ} (hk : 2≤k) (hs : 4*k≤s) :
    ∃ c>(0:ℝ), ∀ᶠ P : ℕ in atTop, ∀ n : ℕ, (P:ℝ)^k/4≤n → (n:ℝ)≤(P:ℝ)^k →
      c*(P:ℝ)^(s-k) ≤ (waringMajorContribution k s P n).re := by
  have hk0 : 0<k := by omega
  have hks : k<s := by omega
  have hkr : (0:ℝ)<k := by exact_mod_cast hk0
  let r := (s:ℝ)/k-1
  let G := Gamma (1/(k:ℝ)+1)^s / Gamma ((s:ℝ)/k)
  have hr : 0≤r := by
    have H : (1:ℝ)≤(s:ℝ)/k := (le_div_iff₀ hkr).mpr (by simpa using (show (k:ℝ)≤s by exact_mod_cast hks.le))
    dsimp [r]; linarith
  have hG : 0<G := by
    apply div_pos (pow_pos (Gamma_pos_of_pos (by positivity)) _)
    apply Gamma_pos_of_pos
    exact div_pos (by exact_mod_cast (by omega : 0<s)) hkr
  obtain ⟨b,hb,hS⟩ := exists_pos_le_waringSingularSeries_re_of_four_mul hk0 hs
  let c := b*G*(1/4:ℝ)^r/2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  let l := comap (Prod.fst : ℕ×ℕ→ℕ) atTop
  have h := tendsto_waringMajorContribution_sub_singularFactors hk (by omega : 2*k<s)
    (l:=l) Prod.fst Prod.snd tendsto_comap
  have H := (Metric.tendsto_nhds.mp h) c hc
  filter_upwards [eventually_comap.mp H,eventually_ge_atTop 1] with P hP hP1 n hn hn'
  have hp : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  let t := (n:ℝ)/(P:ℝ)^k
  have ht : 1/4≤t := (le_div_iff₀ (pow_pos hp _)).mpr (by linarith)
  have ht1 : t≤1 := (div_le_iff₀ (pow_pos hp _)).mpr (by simpa using hn')
  have hJ : waringSingularIntegral s k t = ((G*t^r:ℝ):ℂ) := by
    rcases ht1.eq_or_lt with he|he
    · rw [he,waringSingularIntegral_one hk0 hks,Real.one_rpow,mul_one]
    · exact waringSingularIntegral_eq_density hk0 hks (by linarith) he
  have hE := hP (P,n) rfl
  change dist (waringMajorContribution k s P n/(P:ℂ)^(s-k)-waringSingularSeries k s n*waringSingularIntegral s k t) 0<c at hE
  rw [dist_zero_right,hJ] at hE
  have hneg := (abs_le.mp (Complex.abs_re_le_norm (waringMajorContribution k s P n/(P:ℂ)^(s-k)-waringSingularSeries k s n*((G*t^r:ℝ):ℂ)))).1
  rw [Complex.sub_re,Complex.re_mul_ofReal] at hneg
  have hlower : 2*c≤(waringSingularSeries k s n).re*(G*t^r) := by
    dsimp only [c]
    rw [show 2*(b*G*(1/4:ℝ)^r/2)=b*(G*(1/4:ℝ)^r) by ring]
    exact mul_le_mul (hS n) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) ht hr) hG.le) (by positivity) (hb.le.trans (hS n))
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow,Complex.div_ofReal_re] at hneg
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow] at hE
  apply (le_div_iff₀ (pow_pos hp _)).mp
  linarith

end AnalyticNumberTheory.AdditiveNumberTheory
