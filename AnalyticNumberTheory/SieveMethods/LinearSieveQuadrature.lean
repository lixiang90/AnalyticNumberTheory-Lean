import AnalyticNumberTheory.SieveMethods.LinearSieveMonotonicity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Comparing the linear sieve prime sum with its continuous model

A discrepancy estimate for intervals controls integration against bounded
monotone sieve functions. The bound only involves the height of the test
function, even when the parameter interval is very long.
-/
noncomputable section
open Set MeasureTheory Real Finset Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open Classical

private theorem superlevel_interval {f : ℝ → ℝ} (hf : Continuous f) {a b t : ℝ}
    (hm : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    let S := {x | t≤f x} ∩ Icc a b
    S=∅ ∨ ∃ l r : ℝ, a≤l ∧ l≤r ∧ r≤b ∧ S=Icc l r := by
  let S := {x | t≤f x} ∩ Icc a b
  by_cases he : S.Nonempty
  · have hc : IsClosed S := (isClosed_le continuous_const hf).inter isClosed_Icc
    have hmin := hc.isLeast_csInf he (show BddBelow S from ⟨a,fun x hx => hx.2.1⟩)
    have hmax := hc.isGreatest_csSup he (show BddAbove S from ⟨b,fun x hx => hx.2.2⟩)
    refine Or.inr ⟨sInf S,sSup S,hmin.1.2.1,hmin.2 hmax.1,hmax.1.2.2,?_⟩
    apply Set.Subset.antisymm
    · intro x hx; exact ⟨hmin.2 hx,hmax.2 hx⟩
    intro x hx
    have hx' : x∈Icc a b := ⟨hmin.1.2.1.trans hx.1,hx.2.trans hmax.1.2.2⟩
    refine ⟨?_,hx'⟩
    rcases hm with hd | hd
    · exact (show t≤f (sInf S) from hmin.1.1).trans (hd hmin.1.2 hx' hx.1)
    · exact (show t≤f (sSup S) from hmax.1.1).trans (hd hx' hmax.1.2 hx.2)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp he)

private theorem layer_integral (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    {f : ℝ → ℝ} (hf : Continuous f) {a b M : ℝ} (h : ∀x∈Icc a b, f x∈Icc 0 M) :
    (∫x in Icc a b,f x ∂μ) = ∫t in Ioc 0 M, μ.real ({x | t≤f x} ∩ Icc a b) := by
  have hint := hf.continuousOn.integrableOn_compact (μ:=μ) (isCompact_Icc : IsCompact (Icc a b))
  rw [hint.integral_eq_integral_Ioc_meas_le (M:=M) _ _]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht; exact measureReal_restrict_apply (isClosed_le continuous_const hf).measurableSet
  · filter_upwards [ae_restrict_mem (μ:=μ) measurableSet_Icc] with x hx using (h x hx).1
  · filter_upwards [ae_restrict_mem (μ:=μ) measurableSet_Icc] with x hx using (h x hx).2

private theorem layer_integrable (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (f : ℝ → ℝ) (a b M : ℝ) : IntegrableOn (fun t => μ.real ({x | t≤f x} ∩ Icc a b)) (Ioc 0 M) := by
  have hm : Antitone (fun t : ℝ => μ.real ({x | t≤f x} ∩ Icc a b)) := by
    intro s t hst; refine measureReal_mono ?_ ?_
    · intro x hx; exact ⟨hst.trans hx.1,hx.2⟩
    · exact ne_top_of_le_ne_top isCompact_Icc.measure_lt_top.ne (measure_mono inter_subset_right)
  exact ((hm.antitoneOn (Icc 0 M)).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- A monotone test of height M transfers an interval discrepancy D into
an integration error at most MD. Closed intervals allow atoms at either end. -/
theorem monotone_quadrature_one_sided (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    {a b c L A M : ℝ} (hL : 0≤L) (hA : 0≤A) (hM : 0≤M) (f : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀x∈Icc a b,f x∈Icc 0 M)
    (hm : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hd : ∀ l r : ℝ, a≤l → l≤r → r≤b → μ.real (Icc l r)-c*(r-l)∈Set.Icc (-L) A) :
    (∫x in Icc a b,f x ∂μ)-c*(∫x in Icc a b,f x)∈Set.Icc (-(L*M)) (A*M) := by
  let F (t : ℝ) := μ.real ({x | t≤f x} ∩ Icc a b)-c*volume.real ({x | t≤f x} ∩ Icc a b)
  have hI : IntegrableOn F (Ioc 0 M) := (layer_integrable μ f a b M).sub ((layer_integrable volume f a b M).const_mul c)
  have hFin : volume (Ioc 0 M)<⊤ := measure_Ioc_lt_top
  have ht (t : ℝ) : F t ∈ Set.Icc (-L) A := by
    dsimp [F]
    rcases superlevel_interval (t:=t) hf hm with he | ⟨l,r,hl,hlr,hr,he⟩
    · simp [he,hL,hA]
    · rw [he,Real.volume_real_Icc_of_le hlr]; exact hd l r hl hlr hr
  rw [layer_integral μ hf hF,layer_integral volume hf hF,←integral_const_mul,
    ←integral_sub (layer_integrable μ f a b M) ((layer_integrable volume f a b M).const_mul c)]
  have h₁ := setIntegral_mono_on (integrableOn_const hFin.ne : IntegrableOn (fun _ : ℝ => -L) (Ioc 0 M)) hI
    measurableSet_Ioc (fun t _ => (ht t).1)
  have h₂ := setIntegral_mono_on hI (integrableOn_const hFin.ne : IntegrableOn (fun _ : ℝ => A) (Ioc 0 M))
    measurableSet_Ioc (fun t _ => (ht t).2)
  simpa only [F,setIntegral_const,Real.volume_real_Ioc_of_le hM,sub_zero,smul_eq_mul,Set.mem_Icc,mul_neg,mul_comm M,neg_mul] using And.intro h₁ h₂

/-- A monotone test of height M transfers an interval discrepancy D into
an integration error at most MD. Closed intervals allow atoms at either end. -/
theorem monotone_quadrature_of_interval_discrepancy (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    {a b c D M : ℝ} (hD : 0≤D) (hM : 0≤M) (f : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀x∈Icc a b,f x∈Icc 0 M)
    (hm : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hd : ∀ l r : ℝ, a≤l → l≤r → r≤b → |μ.real (Icc l r)-c*(r-l)|≤D) :
    |(∫x in Icc a b,f x ∂μ)-c*(∫x in Icc a b,f x)|≤D*M := by
  exact abs_le.mpr (monotone_quadrature_one_sided μ hD hD hM f hf hF hm
    (fun l r hl hlr hr => abs_le.mp (hd l r hl hlr hr)))

/-- Finite atomic version of the quadrature estimate. -/
theorem finite_monotone_quadrature_one_sided {ι : Type*} (S : Finset ι) (x m : ι → ℝ)
    {a b c L A M : ℝ} (hL : 0≤L) (hA : 0≤A) (hM : 0≤M) (hm : ∀i∈S,0≤m i) (hx : ∀i∈S,x i∈Icc a b)
    (f : ℝ → ℝ) (hf : Continuous f) (hF : ∀t∈Icc a b,f t∈Icc 0 M)
    (hmono : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hd : ∀ l r : ℝ, a≤l → l≤r → r≤b →
      (∑ i∈S.filter (fun i => x i∈Icc l r), m i)-c*(r-l)∈Set.Icc (-L) A) :
    (∑ i∈S,m i*f (x i))-c*(∫t in Icc a b,f t)∈Set.Icc (-(L*M)) (A*M) := by
  let ν := fun i => (m i).toNNReal • Measure.dirac (x i)
  let μ := ∑i∈S,ν i
  haveI (i : ι) : IsFiniteMeasure (ν i) := by dsimp [ν]; infer_instance
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hs (l r : ℝ) : μ.real (Icc l r)=∑i∈S.filter (fun i => x i∈Icc l r),m i := by
    rw [Finset.sum_filter]
    dsimp only [μ]
    clear hd hx
    induction S using Finset.induction_on with
    | empty => simp [measureReal_def]
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,measureReal_add_apply]
      have hν : (ν i).real (Icc l r)=(if x i∈Icc l r then m i else 0) := by
        simp only [ν,measureReal_nnreal_smul_apply,Real.coe_toNNReal _ (hm i (by simp)),
          Measure.dirac_real_apply,indicator_apply,Pi.one_apply]
        split_ifs <;> simp
      rw [hν]; congr 1
      exact ih (fun j hj => hm _ (by simp [hj])) (by infer_instance)
  have hsum : (∫ t in Icc a b,f t ∂μ)=∑i∈S,m i*f (x i) := by
    rw [←integral_indicator measurableSet_Icc]
    change (∫t,(Icc a b).indicator f t ∂(∑i∈S,ν i))=_
    rw [integral_finsetSum_measure (fun i hi => (integrable_dirac (by simp)).smul_measure_nnreal)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ν,integral_smul_nnreal_measure,integral_dirac,indicator_of_mem (hx i hi),
      NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal _ (hm i hi)]
  rw [←hsum]
  exact monotone_quadrature_one_sided μ hL hA hM f hf hF hmono
    (fun l r hl hlr hr => (hs l r).symm ▸ hd l r hl hlr hr)


/-- Finite atomic version of the quadrature estimate. -/
theorem finite_monotone_quadrature {ι : Type*} (S : Finset ι) (x m : ι → ℝ)
    {a b c D M : ℝ} (hD : 0≤D) (hM : 0≤M) (hm : ∀i∈S,0≤m i) (hx : ∀i∈S,x i∈Icc a b)
    (f : ℝ → ℝ) (hf : Continuous f) (hF : ∀t∈Icc a b,f t∈Icc 0 M)
    (hmono : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hd : ∀ l r : ℝ, a≤l → l≤r → r≤b →
      |(∑ i∈S.filter (fun i => x i∈Icc l r), m i)-c*(r-l)|≤D) :
    |(∑ i∈S,m i*f (x i))-c*(∫t in Icc a b,f t)|≤D*M := by
  exact abs_le.mpr (finite_monotone_quadrature_one_sided S x m hD hD hM hm hx f hf hF hmono
    (fun l r hl hlr hr => abs_le.mp (hd l r hl hlr hr)))

/-- A bound for cumulative mass up to each parameter gives an interval
discrepancy with twice the error, including intervals consisting of one atom. -/
theorem finite_interval_discrepancy_of_cumulative {ι : Type*} (S : Finset ι) (x m : ι → ℝ)
    {a b c D : ℝ} (hD : 0≤D) (hx : ∀i∈S,a≤x i)
    (h : ∀t∈Icc a b,|(∑i∈S.filter (fun i => x i≤t),m i)-c*(t-a)|≤D)
    {l r : ℝ} (hl : a≤l) (hlr : l≤r) (hr : r≤b) :
    |(∑i∈S.filter (fun i => x i∈Icc l r),m i)-c*(r-l)|≤2*D := by
  let Z := ∑i∈S.filter (fun i => x i<l),m i
  have hz : |Z-c*(l-a)|≤D := by
    rcases hl.eq_or_lt with he | hlt
    · subst l
      have hnil : S.filter (fun i => x i<a)=∅ := Finset.filter_eq_empty_iff.mpr (fun i hi => not_lt.mpr (hx i hi))
      simpa [Z,hnil] using hD
    · have he : ∀ᶠ t in 𝓝[<] l,∀i∈S, (x i≤t ↔ x i<l) := by
        apply (eventually_all_finset S).mpr
        intro i hi
        by_cases hxi : x i<l
        · filter_upwards [(eventually_gt_nhds hxi).filter_mono nhdsWithin_le_nhds] with t ht
          exact iff_of_true ht.le hxi
        · filter_upwards [self_mem_nhdsWithin] with t (ht : t<l)
          exact iff_of_false (fun hh => hxi (hh.trans_lt ht)) hxi
      have hc : Continuous (fun t => |Z-c*(t-a)|) := by fun_prop
      apply le_of_tendsto (hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:=Iio l)))
      filter_upwards [he,(eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht ha (htl : t<l)
      have hset : S.filter (fun i => x i≤t)=S.filter (fun i => x i<l) := Finset.filter_congr (fun i hi => ht i hi)
      simpa only [Z,←hset] using h t ⟨ha.le,htl.le.trans (hlr.trans hr)⟩
  have hsum : (∑i∈S.filter (fun i => x i≤r),m i)=Z+∑i∈S.filter (fun i => x i∈Icc l r),m i := by
    dsimp [Z]; simp only [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h₁ : x i<l
    · simp [h₁,h₁.le.trans hlr,Set.mem_Icc,not_le.mpr h₁]
    · simp [h₁,not_lt.mp h₁,Set.mem_Icc]
  have hh := h r ⟨hl.trans hlr,hr⟩
  rw [hsum] at hh
  rw [abs_le] at hz hh ⊢
  constructor <;> linarith only [hz.1,hz.2,hh.1,hh.2]

end AnalyticNumberTheory.SieveMethods
