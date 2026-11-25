import AnalyticNumberTheory.SieveMethods.DickmanFunction

/-!
# Buchstab's function

The normalized sum of the two linear sieve functions satisfies Buchstab's
delay equation. Its values on each unit interval are weighted averages of
the preceding values; this gives convergence at infinity.
-/
noncomputable section
open Filter Set MeasureTheory Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

private def c : ℝ := 2*exp eulerMascheroniConstant
private theorem c_pos : 0<c := by unfold c; positivity

/-- Buchstab's function on [1,∞), extended by the constant 1 on the left. -/
def buchstab (u : ℝ) : ℝ := (linearSieveUpper (max 1 u)+linearSieveLower (max 1 u))/c

theorem continuous_buchstab : Continuous buchstab := by
  have H (b : Bool) : Continuous (fun u : ℝ => linearSieveFunction b (max 1 u)) :=
    (continuousOn_linearSieveFunction b).comp_continuous (continuous_const.max continuous_id) (fun u => mem_Ici.mpr (le_max_left ..))
  exact ((H true).add (H false)).div_const c

theorem linearSieve_sum_eq_buchstab {u : ℝ} (hu : 1≤u) :
    linearSieveUpper u+linearSieveLower u=2*exp eulerMascheroniConstant*buchstab u := by
  change linearSieveUpper u+linearSieveLower u=c*buchstab u
  rw [buchstab,max_eq_right hu]; field_simp [c_pos.ne']

theorem buchstab_initial {u : ℝ} (hu : u∈Icc 1 2) : buchstab u=u⁻¹ := by
  obtain ⟨hF,hf⟩ := linearSieve_initial hu
  rw [buchstab,max_eq_right hu.1,hF,hf,add_zero]; unfold c
  field_simp [show u≠0 by linarith [hu.1]]

theorem buchstab_integral {u : ℝ} (hu : 2≤u) :
    u*buchstab u=1+∫v in (2:ℝ)..u,buchstab (v-1) := by
  have hF := linearSieve_integral true hu
  have hf := linearSieve_integral false hu
  simp only [Bool.false_eq_true,Bool.not_true,Bool.not_false,ite_true,ite_false,zero_add] at hF hf
  have hplus (b : Bool) : IntervalIntegrable (fun v : ℝ => linearSieveFunction b (v-1)) volume 2 u := by
    apply ContinuousOn.intervalIntegrable_of_Icc hu
    exact (continuousOn_linearSieveFunction b).comp (continuous_id.sub continuous_const).continuousOn
      (fun v hv => by change 1≤v-1; linarith [hv.1])
  have hint : c*(∫v in (2:ℝ)..u,buchstab (v-1))=
      (∫v in (2:ℝ)..u,linearSieveFunction false (v-1))+
      (∫v in (2:ℝ)..u,linearSieveFunction true (v-1)) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_add (hplus false) (hplus true)]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hu] at hv
    exact (linearSieve_sum_eq_buchstab (by linarith [hv.1] : 1≤v-1)).symm.trans (add_comm ..)
  have he := linearSieve_sum_eq_buchstab (by linarith : 1≤u)
  apply (mul_left_cancel₀ c_pos.ne')
  change linearSieveFunction true u+linearSieveFunction false u=c*buchstab u at he
  change u*linearSieveFunction true u=c+_ at hF
  linear_combination (norm:=ring_nf) u*he.symm+hF+hf-hint

/-- Integral form of the Buchstab equation starting at an arbitrary a≥2. -/
theorem buchstab_integral_from {a x : ℝ} (ha : 2≤a) (hx : a≤x) :
    x*buchstab x=a*buchstab a+∫v in a..x,buchstab (v-1) := by
  have hc : Continuous (fun v : ℝ => buchstab (v-1)) := continuous_buchstab.comp (continuous_id.sub continuous_const)
  rw [buchstab_integral (ha.trans hx),buchstab_integral ha]
  linarith only [intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 2 a) (hc.intervalIntegrable a x)]

/-- A closed interval containing the values on [a−1,a] also contains every
later value. This is the maximum principle for the Buchstab equation. -/
theorem buchstab_stays_in_interval {a l r : ℝ} (ha : 2≤a)
    (h : ∀ t∈Icc (a-1) a,buchstab t∈Icc l r) {x : ℝ} (hx : a-1≤x) :
    buchstab x∈Icc l r := by
  have hc : Continuous (fun v : ℝ => buchstab (v-1)) := continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hs (n : ℕ) : ∀ t : ℝ, a-1≤t → t≤a+n → buchstab t∈Icc l r := by
    induction n with
    | zero => intro t ht ht'; exact h t ⟨ht,by simpa using ht'⟩
    | succ n ih =>
      intro t ht ht'; push_cast at ht'
      by_cases hle : t≤a+n
      · exact ih t ht hle
      have hat := (not_le.mp hle).le
      let b := a+(n:ℝ)
      have hb : 2≤b := by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) n]
      have hm := ih b (by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) n]) le_rfl
      have hset (v : ℝ) (hv : v∈Icc b t) : buchstab (v-1)∈Icc l r :=
        ih _ (by dsimp [b] at hv; linarith [hv.1,Nat.cast_nonneg (α:=ℝ) n]) (by linarith [hv.2])
      have hl := intervalIntegral.integral_mono_on (a:=b) (b:=t) (μ:=volume) hat
        (intervalIntegrable_const (c:=l)) (hc.intervalIntegrable _ _) (fun v hv => (hset v hv).1)
      have hr := intervalIntegral.integral_mono_on (a:=b) (b:=t) (μ:=volume) hat (hc.intervalIntegrable _ _)
        (intervalIntegrable_const (c:=r)) (fun v hv => (hset v hv).2)
      rw [intervalIntegral.integral_const,smul_eq_mul] at hl hr
      have he := buchstab_integral_from hb hat
      have h₁ := mul_le_mul_of_nonneg_left hm.1 (show 0≤b by linarith)
      have h₂ := mul_le_mul_of_nonneg_left hm.2 (show 0≤b by linarith)
      have htpos : 0<t := by linarith
      exact ⟨le_of_mul_le_mul_left (a:=t) (by nlinarith only [hl,h₁,he]) htpos,
        le_of_mul_le_mul_left (a:=t) (by nlinarith only [hr,h₂,he]) htpos⟩
  exact hs ⌈x-a⌉₊ x hx (by linarith [Nat.le_ceil (x-a)])

theorem buchstab_mem_Icc {u : ℝ} (hu : 1≤u) : buchstab u∈Icc (1/2:ℝ) 1 := by
  apply buchstab_stays_in_interval (a:=2) le_rfl _ (by linarith)
  intro t ht
  have h₁ : 1≤t := by linarith [ht.1]
  rw [buchstab_initial ⟨h₁,ht.2⟩]; constructor
  · simpa only [one_div] using one_div_le_one_div_of_le (by linarith : (0:ℝ)<t) ht.2
  · simpa only [inv_one] using inv_anti₀ zero_lt_one h₁


private theorem buchstab_local_oscillation {a x : ℝ} (ha : 2≤a) (hx : x∈Icc a (a+1)) :
    |buchstab x-buchstab a|≤a⁻¹ := by
  have hc : Continuous (fun v : ℝ => buchstab (v-1)) := continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hi : x*(buchstab x-buchstab a)=∫v in a..x,(buchstab (v-1)-buchstab a) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable a x) (intervalIntegrable_const ..),
      intervalIntegral.integral_const,smul_eq_mul]
    linarith only [buchstab_integral_from ha hx.1]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=x) (C:=1)
    (f:=fun v : ℝ => buchstab (v-1)-buchstab a) (fun v hv => by
      rw [uIoc_of_le hx.1] at hv
      have h₁ := buchstab_mem_Icc (u:=v-1) (by linarith [hv.1])
      have h₂ := buchstab_mem_Icc (u:=a) (by linarith)
      rw [Real.norm_eq_abs,abs_le]; constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2])
  rw [←hi,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by linarith [hx.1] : 0≤x),
    abs_of_nonneg (sub_nonneg.mpr hx.1),one_mul] at hh
  rw [←one_div,le_div_iff₀ (by linarith : 0<a)]
  nlinarith only [hh,hx.2,mul_le_mul_of_nonneg_right hx.1 (abs_nonneg (buchstab x-buchstab a))]

/-- All values after a≥2 remain within 1/a of the value at a. -/
theorem buchstab_oscillation {a x : ℝ} (ha : 2≤a) (hx : a≤x) :
    |buchstab x-buchstab a|≤a⁻¹ := by
  have h := buchstab_stays_in_interval (a:=a+1) (l:=buchstab a-a⁻¹) (r:=buchstab a+a⁻¹)
    (by linarith) (fun t ht => by
      have hloc := abs_le.mp (buchstab_local_oscillation ha (show t∈Icc a (a+1) from ⟨by linarith [ht.1],ht.2⟩))
      exact ⟨by linarith [hloc.1],by linarith [hloc.2]⟩) (x:=x) (by linarith)
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

/-- Existence of the Buchstab limit, directly from the delay equation. -/
theorem buchstab_exists_limit : ∃ L : ℝ, Tendsto buchstab atTop (𝓝 L) := by
  apply cauchy_iff_exists_le_nhds.mp
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  refine ⟨max 2 (2/ε),?_⟩
  intro x hx
  rw [Real.dist_eq]
  apply (buchstab_oscillation (le_max_left ..) hx).trans_lt
  have hh : 0<max 2 (2/ε) := lt_of_lt_of_le (by norm_num) (le_max_left ..)
  rw [←one_div,div_lt_iff₀ hh]
  have h := mul_le_mul_of_nonneg_left (le_max_right 2 (2/ε)) hε.le
  rw [show ε*(2/ε)=2 by field_simp] at h
  linarith


/-- Differential form of the Buchstab delay equation. -/
theorem hasDerivAt_mul_buchstab {u : ℝ} (hu : 2<u) :
    HasDerivAt (fun t => t*buchstab t) (buchstab (u-1)) u := by
  have hc : Continuous (fun v : ℝ => buchstab (v-1)) := continuous_buchstab.comp (continuous_id.sub continuous_const)
  exact ((hc.integral_hasStrictDerivAt 2 u).hasDerivAt.const_add 1).congr_of_eventuallyEq
    ((eventually_gt_nhds hu).mono (fun v hv => buchstab_integral hv.le))

end AnalyticNumberTheory.SieveMethods
