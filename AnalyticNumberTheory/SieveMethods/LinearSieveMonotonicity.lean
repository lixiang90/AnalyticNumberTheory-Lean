import AnalyticNumberTheory.SieveMethods.BuchstabNormalization

/-!
# Monotonicity of the linear sieve functions

The first point of failure of the upper derivative inequality would force
the upper function to be decreasing, hence the lower function increasing,
all the way up to that point. Their strictly positive Dickman gap excludes
the failure. Together with the common limit this gives a factorial error.
-/
noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- Derivative of either unweighted sieve function past the initial interval. -/
theorem hasDerivAt_linearSieveFunction (b : Bool) {t : ℝ} (ht : 2<t) :
    HasDerivAt (linearSieveFunction b) ((linearSieveFunction (!b) (t-1)-linearSieveFunction b t)/t) t := by
  have ht' : t≠0 := by linarith
  have hh := (hasDerivAt_mul_linearSieveFunction b ht).div (hasDerivAt_id' t) ht'
  have he : linearSieveFunction b =ᶠ[𝓝 t] fun x => (x*linearSieveFunction b x)/x := by
    filter_upwards [eventually_ne_nhds ht'] with x hx using (mul_div_cancel_left₀ _ hx).symm
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hh using 1
  field_simp [ht'] <;> ring

private theorem upper_deriv_initial {t : ℝ} (ht : 1<t) (ht' : t<3) :
    deriv linearSieveUpper t<0 := by
  have he : linearSieveUpper =ᶠ[𝓝 t] (fun x : ℝ => 2*exp eulerMascheroniConstant/x) := by
    filter_upwards [eventually_gt_nhds ht,eventually_lt_nhds ht'] with x h₁ h₂
    exact linearSieveUpper_eq_of_le_three ⟨h₁.le,h₂.le⟩
  rw [he.deriv_eq]
  have hh := (hasDerivAt_const t (2*exp eulerMascheroniConstant)).div (hasDerivAt_id' t) (by linarith)
  dsimp only [Pi.div_def] at hh
  rw [hh.deriv]; simp only [zero_mul,zero_sub,mul_one]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (sq_pos_of_pos (by linarith))

private theorem gap_pos {u : ℝ} (hu : 1≤u) : linearSieveLower u<linearSieveUpper u := by
  apply sub_pos.mp
  exact (linearSieve_gap_le_factorial 0 (by simpa using hu)).1

private theorem upper_deriv_of_comparison {t : ℝ} (h₁ : 1<t)
    (h : 2≤t → linearSieveLower (t-1)<linearSieveUpper t) : deriv linearSieveUpper t<0 := by
  by_cases ht : t≤2
  · exact upper_deriv_initial h₁ (by linarith)
  have ht' := not_le.mp ht
  change deriv (linearSieveFunction true) t<0
  rw [(hasDerivAt_linearSieveFunction true ht').deriv]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (h ht'.le)) (by linarith)

private theorem upper_comparison {x : ℝ} (hx : 2≤x) :
    linearSieveLower (x-1)<linearSieveUpper x := by
  let H (t : ℝ) := linearSieveLower (max 1 (t-1))-linearSieveUpper (max 1 t)
  have hc (b : Bool) : Continuous (fun t : ℝ => linearSieveFunction b (max 1 t)) :=
    (continuousOn_linearSieveFunction b).comp_continuous (continuous_const.max continuous_id)
      (fun t => mem_Ici.mpr (le_max_left ..))
  have hcH : Continuous H := ((hc false).comp (continuous_id.sub continuous_const)).sub (hc true)
  have he (t : ℝ) (ht : 2≤t) : H t=linearSieveLower (t-1)-linearSieveUpper t := by
    simp only [H,max_eq_right (by linarith : 1≤t-1),max_eq_right (by linarith : 1≤t)]
  let S := Ici 2 ∩ H ⁻¹' Ici 0
  by_contra! hfail
  have hxS : x∈S := ⟨hx,by change 0≤H x; rw [he x hx]; linarith⟩
  have hmin := (isClosed_Ici.inter (isClosed_Ici.preimage hcH)).isLeast_csInf
    (show S.Nonempty from ⟨x,hxS⟩) (show BddBelow S from ⟨2,fun t ht => ht.1⟩)
  let m := sInf S
  have hm : 2≤m := hmin.1.1
  have hbad : linearSieveUpper m≤linearSieveLower (m-1) := by
    have h : 0≤H m := hmin.1.2
    rwa [he m hm,sub_nonneg] at h
  have hpre (t : ℝ) (ht : 2≤t) (htm : t<m) : linearSieveLower (t-1)<linearSieveUpper t := by
    by_contra! hh
    apply (not_le.mpr htm) (hmin.2 ⟨ht,by change 0≤H t; rw [he t ht]; linarith⟩)
  have hupper : AntitoneOn linearSieveUpper (Icc 1 m) := by
    apply StrictAntiOn.antitoneOn
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) ((continuousOn_linearSieveFunction true).mono Icc_subset_Ici_self)
    rw [interior_Icc]
    exact fun t ht => upper_deriv_of_comparison ht.1 (fun h => hpre _ h ht.2)
  have hlower : MonotoneOn linearSieveLower (Icc 2 m) := by
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Icc ..) ((continuousOn_linearSieveFunction false).mono
      (fun t (ht : t∈Icc (2:ℝ) m) => show 1≤t by linarith [ht.1]))
    rw [interior_Icc]
    intro t ht
    have hF := hupper (show t-1∈Icc 1 m from ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      (show t∈Icc 1 m from ⟨by linarith [ht.1],ht.2.le⟩) (by linarith)
    change 0<deriv (linearSieveFunction false) t
    rw [(hasDerivAt_linearSieveFunction false ht.1).deriv]
    exact div_pos (sub_pos.mpr ((gap_pos (by linarith [ht.1] : 1≤t)).trans_le hF)) (by linarith [ht.1])
  have hl : linearSieveLower (m-1)≤linearSieveLower m := by
    by_cases h : 2≤m-1
    · exact hlower ⟨h,by linarith⟩ ⟨hm,le_rfl⟩ (by linarith)
    · rw [(linearSieve_initial (show m-1∈Icc 1 2 from ⟨by linarith,(not_le.mp h).le⟩)).2]
      exact linearSieveFunction_nonneg false (by linarith)
  exact (not_lt.mpr (hbad.trans hl)) (gap_pos (by linarith : 1≤m))

/-- F decreases strictly on the full sieve domain. -/
theorem strictAntiOn_linearSieveUpper : StrictAntiOn linearSieveUpper (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuousOn_linearSieveFunction true)
  rw [interior_Ici]; exact fun t ht => upper_deriv_of_comparison ht upper_comparison

/-- f increases strictly after its initial zero interval. -/
theorem strictMonoOn_linearSieveLower : StrictMonoOn linearSieveLower (Ici 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) ((continuousOn_linearSieveFunction false).mono
    (Ici_subset_Ici.mpr (by norm_num)))
  rw [interior_Ici]; intro t ht
  change 0<deriv (linearSieveFunction false) t
  rw [(hasDerivAt_linearSieveFunction false ht).deriv]
  apply div_pos _ (by change 2<t at ht; linarith)
  apply sub_pos.mpr
  apply (gap_pos (by change 2<t at ht; linarith : 1≤t)).trans
  exact strictAntiOn_linearSieveUpper (show 1≤t-1 by change 2<t at ht; linarith)
    (show 1≤t by change 2<t at ht; linarith) (by linarith)

/-- At finite sieve parameter the functions strictly bracket one. -/
theorem linearSieve_bracket_one {u : ℝ} (hu : 1≤u) :
    linearSieveLower u<1 ∧ 1<linearSieveUpper u := by
  have hlo (t : ℝ) (ht : 2≤t) : linearSieveLower t≤1 :=
    ge_of_tendsto tendsto_linearSieve.2 ((eventually_ge_atTop t).mono
      (fun v hv => strictMonoOn_linearSieveLower.monotoneOn ht (ht.trans hv) hv))
  have hup (t : ℝ) (ht : 1≤t) : 1≤linearSieveUpper t :=
    le_of_tendsto tendsto_linearSieve.1 ((eventually_ge_atTop t).mono
      (fun v hv => strictAntiOn_linearSieveUpper.antitoneOn ht (ht.trans hv) hv))
  constructor
  · by_cases h : 2≤u
    · exact (strictMonoOn_linearSieveLower h (show 2≤u+1 by linarith) (by linarith)).trans_le (hlo _ (by linarith))
    · rw [(linearSieve_initial ⟨hu,(not_le.mp h).le⟩).2]; norm_num
  · exact (hup (u+1) (by linarith)).trans_lt (strictAntiOn_linearSieveUpper hu
      (show 1≤u+1 by linarith) (by linarith))

/-- The individual errors of both sieve functions are factorially small. -/
theorem linearSieve_factorial_error (b : Bool) (n : ℕ) {u : ℝ} (hu : n+1≤u) :
    |linearSieveFunction b u-1|≤2*exp eulerMascheroniConstant/((n.factorial:ℝ)*u) := by
  obtain ⟨hf,hF⟩ := linearSieve_bracket_one (by linarith [Nat.cast_nonneg (α:=ℝ) n] : 1≤u)
  have h := (linearSieve_gap_le_factorial n hu).2
  cases b
  · change |linearSieveLower u-1|≤_
    rw [abs_of_neg (sub_neg.mpr hf)]; linarith
  · change |linearSieveUpper u-1|≤_
    rw [abs_of_pos (sub_pos.mpr hF)]; linarith

end AnalyticNumberTheory.SieveMethods
