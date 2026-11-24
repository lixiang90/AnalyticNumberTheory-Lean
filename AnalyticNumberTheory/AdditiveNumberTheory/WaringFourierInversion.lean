import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularIntegral
import AnalyticNumberTheory.AdditiveNumberTheory.WaringVolume
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier inversion for the Waring singular integral

The distribution of the sum of powers on the unit cube has Fourier transform
given by a power of the one-variable oscillatory integral. Below level one,
its distribution function is the volume of the Waring region.
-/

namespace AnalyticNumberTheory.AdditiveNumberTheory

open MeasureTheory Set Real Filter
open scoped Topology FourierTransform InnerProductSpace ENNReal

/-- Distribution of `∑ xᵢᵏ` for Lebesgue measure on the unit cube. -/
noncomputable def waringDistribution (s k : ℕ) : Measure ℝ :=
  Measure.map (fun x : Fin s → ℝ => ∑ i, x i ^ k)
    ((volume : Measure (Fin s → ℝ)).restrict (univ.pi fun _ => Icc 0 1))

instance (s k : ℕ) : IsFiniteMeasure (waringDistribution s k) := by
  have : IsFiniteMeasure ((volume : Measure (Fin s → ℝ)).restrict (univ.pi fun _ => Icc 0 1)) := by
    apply isFiniteMeasure_restrict.mpr
    rw [volume_pi_pi]
    simp
  unfold waringDistribution
  infer_instance

/-- The Fourier character factors over the independent coordinates of the unit cube. -/
theorem integral_e_waringDistribution (s k : ℕ) (β : ℝ) :
    (∫ u : ℝ, e (β * u) ∂waringDistribution s k) = waringOscillatoryIntegral k β ^ s := by
  unfold waringDistribution
  rw [integral_map (f := fun u : ℝ => e (β * u))
    (show Measurable (fun x : Fin s → ℝ => ∑ i, x i ^ k) by fun_prop).aemeasurable
    (show Continuous (fun u : ℝ => e (β * u)) from continuous_e.comp (by fun_prop)).aestronglyMeasurable]
  simp_rw [Finset.mul_sum, e_sum]
  change (∫ x : Fin s → ℝ, ∏ i, e (β * x i ^ k) ∂(Measure.pi (fun _ : Fin s => (volume : Measure ℝ))).restrict _) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (fun (_ : Fin s) (x : ℝ) => e (β * x ^ k))]
  simp [integral_Icc_eq_integral_Ioc, waringOscillatoryIntegral, intervalIntegral.integral_of_le zero_le_one]

/-- At levels at most one, nonnegative coordinates with sum of powers at most
the level already lie in the unit cube. -/
theorem waringDistribution_Iic {k : ℕ} (hk : 0 < k) (s : ℕ) {t : ℝ} (ht : t ≤ 1) :
    waringDistribution s k (Iic t) = volume (waringRegion s k t) := by
  rw [waringDistribution, Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (by exact (by fun_prop : Measurable (fun x : Fin s → ℝ => ∑ i, x i ^ k)) measurableSet_Iic)]
  congr 1
  ext x
  change ((∑ i, x i ^ k ≤ t) ∧ x ∈ univ.pi (fun _ => Icc 0 1)) ↔ _
  simp only [Set.mem_univ_pi, Set.mem_Icc, waringRegion, Set.mem_ofPred_eq]
  constructor
  · exact fun h => ⟨fun i => (h.2 i).1, h.1⟩
  · rintro ⟨hx, hsum⟩
    refine ⟨hsum, fun i => ⟨hx i, ?_⟩⟩
    by_contra! hgt
    have hpow : 1 < x i ^ k := one_lt_pow₀ hgt hk.ne'
    have hle := Finset.single_le_sum (f := fun j => x j ^ k) (fun j _ => pow_nonneg (hx j) k) (Finset.mem_univ i)
    linarith

private noncomputable def window (h : ℝ) : ℝ → ℂ := (Ico 0 h).indicator (fun _ => 1)

private theorem stronglyMeasurable_window (h : ℝ) : StronglyMeasurable (window h) :=
  stronglyMeasurable_const.indicator measurableSet_Ico

private theorem integrable_window (h : ℝ) : Integrable (window h) :=
  (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (hs := measure_Ico_lt_top.ne))

private noncomputable def boxAverage (μ : Measure ℝ) (h t : ℝ) : ℂ :=
  ∫ u : ℝ, window h (t - u) ∂μ

private theorem boxAverage_eq_measure (μ : Measure ℝ) (h t : ℝ) :
    boxAverage μ h t = (μ.real (Ioc (t-h) t) : ℂ) := by
  have heq : (fun u : ℝ => window h (t-u)) = (Ioc (t-h) t).indicator (fun _ => (1 : ℂ)) := by
    ext u
    simp only [window, Set.indicator_apply, mem_Ioc, mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [boxAverage, heq, integral_indicator_const _ measurableSet_Ioc, Complex.real_smul, mul_one]

private theorem boxAverage_waring_eq {k : ℕ} (hk : 0 < k) (s : ℕ) {h t : ℝ} (hh : 0 ≤ h) (ht : t ≤ 1) :
    boxAverage (waringDistribution s k) h t =
      ((waringVolume s k t - waringVolume s k (t-h) : ℝ) : ℂ) := by
  rw [boxAverage_eq_measure, ← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr (sub_le_self _ hh)) measurableSet_Iic]
  simp only [measureReal_def, waringDistribution_Iic hk s ht,
    waringDistribution_Iic hk s ((sub_le_self _ hh).trans ht), waringVolume]

private theorem fourierInv_eq_e (f : ℝ → ℂ) (β : ℝ) :
    𝓕⁻ f β = ∫ x : ℝ, e (β*x) * f x := by
  rw [Real.fourierInv_eq']
  congr 1
  funext x
  simp only [smul_eq_mul, e, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat]

private theorem fourier_eq_e (f : ℝ → ℂ) (β : ℝ) :
    𝓕 f β = ∫ x : ℝ, e (-β*x) * f x := by
  rw [Real.fourier_eq']
  congr 1
  funext x
  simp only [smul_eq_mul, e, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring_nf

private theorem integrable_window_pair (μ : Measure ℝ) [IsFiniteMeasure μ] (h : ℝ) :
    Integrable (fun p : ℝ × ℝ => window h (p.1-p.2)) (volume.prod μ) := by
  apply (integrable_prod_iff' ((stronglyMeasurable_window h).comp_measurable (by fun_prop)).aestronglyMeasurable).mpr
  refine ⟨.of_forall fun u => (integrable_window h).comp_sub_right u, ?_⟩
  change Integrable (fun u : ℝ => ∫ x : ℝ, ‖window h (x-u)‖) μ
  simp_rw [show ∀ u : ℝ, (∫ x : ℝ, ‖window h (x-u)‖) = ∫ x : ℝ, ‖window h x‖ from
    fun u => integral_sub_right_eq_self (μ := volume) (fun x => ‖window h x‖) u]
  exact integrable_const _

private theorem integrable_boxAverage (μ : Measure ℝ) [IsFiniteMeasure μ] (h : ℝ) : Integrable (boxAverage μ h) :=
  (integrable_window_pair μ h).integral_prod_left

private theorem fourierInv_boxAverage (μ : Measure ℝ) [IsFiniteMeasure μ] (h β : ℝ) :
    𝓕⁻ (boxAverage μ h) β = (∫ u : ℝ, e (β * u) ∂μ) * 𝓕⁻ (window h) β := by
  rw [fourierInv_eq_e, fourierInv_eq_e]
  have hh : Continuous (fun p : ℝ × ℝ => e (β*p.1)) := continuous_e.comp (by fun_prop)
  have hpair : Integrable (fun p : ℝ × ℝ => e (β*p.1) * window h (p.1-p.2)) (volume.prod μ) := by
    apply (integrable_window_pair μ h).norm.mono' (hh.stronglyMeasurable.mul
      ((stronglyMeasurable_window h).comp_measurable (by fun_prop))).aestronglyMeasurable
    exact .of_forall fun p => by simp [norm_e]
  have hinner (x : ℝ) : e (β*x) * boxAverage μ h x = ∫ u : ℝ, e (β*x) * window h (x-u) ∂μ :=
    (integral_const_mul _ _).symm
  simp_rw [hinner]
  rw [integral_integral_swap (f := fun x u : ℝ => e (β*x) * window h (x-u)) hpair]
  rw [← integral_mul_const]
  refine integral_congr_ae (.of_forall fun u => ?_)
  dsimp only
  rw [← integral_const_mul, ← integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => e (β*u) * (e (β*x) * window h x)) u]
  refine integral_congr_ae (.of_forall fun x => ?_)
  dsimp only
  rw [← mul_assoc, ← e_add]
  ring_nf

private theorem norm_fourierInv_window_le (h β : ℝ) : ‖𝓕⁻ (window h) β‖ ≤ ∫ x : ℝ, ‖window h x‖ := by
  rw [fourierInv_eq_e]
  simpa [norm_e] using norm_integral_le_integral_norm (fun x : ℝ => e (β*x) * window h x)

private theorem integrable_fourier_boxAverage {k s : ℕ} (hk : 0 < k) (hks : k < s) (h : ℝ) :
    Integrable (𝓕 (boxAverage (waringDistribution s k) h)) := by
  let f := boxAverage (waringDistribution s k) h
  have hbound (β : ℝ) : ‖𝓕 f β‖ ≤ ‖waringOscillatoryIntegral k (-β) ^ s‖ * ∫ x : ℝ, ‖window h x‖ := by
    have heq : 𝓕 f β = 𝓕⁻ f (-β) := by rw [fourier_eq_e, fourierInv_eq_e]
    rw [heq, fourierInv_boxAverage, integral_e_waringDistribution, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_fourierInv_window_le _ _) (norm_nonneg _)
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (integrable_boxAverage _ _)
  exact (((integrable_waringOscillatoryIntegral_pow hk hks).comp_neg.norm).mul_const _).mono'
    hcont.aestronglyMeasurable (.of_forall hbound)

private theorem window_factor (β a b : ℝ) (hab : a ≤ b) :
    e (-b*β) * 𝓕⁻ (window (b-a)) β = ∫ t in a..b, e (-β*t) := by
  rw [fourierInv_eq_e]
  have hfun : (fun x : ℝ => e (β*x) * window (b-a) x) = (Ico 0 (b-a)).indicator (fun x => e (β*x)) := by
    funext x
    by_cases hx : x ∈ Ico 0 (b-a) <;> simp [window, hx]
  rw [hfun, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (sub_nonneg.mpr hab), ← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in (0 : ℝ)..(b-a), e (-β*(b-x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [← e_add]
      congr 1
      ring
    _ = _ := by
      simpa using intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := b-a) (fun t : ℝ => e (-β*t)) b

theorem continuous_waringSingularIntegral {s k : ℕ} (hk : 0 < k) (hks : k < s) : Continuous (waringSingularIntegral s k) := by
  have h : waringSingularIntegral s k = 𝓕 (fun β : ℝ => waringOscillatoryIntegral k β ^ s) := by
    funext t
    rw [waringSingularIntegral, fourier_eq_e]
    refine integral_congr_ae (.of_forall fun β => ?_)
    simp [mul_comm]
  rw [h]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (integrable_waringOscillatoryIntegral_pow hk hks)

private theorem intervalIntegral_waringSingularIntegral {s k : ℕ} (hk : 0 < k) (hks : k < s) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, waringSingularIntegral s k t) =
      ∫ β : ℝ, waringOscillatoryIntegral k β ^ s * ∫ t in a..b, e (-β*t) := by
  let ν := (volume : Measure ℝ).restrict (Ioc a b)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hpair : Integrable (fun p : ℝ × ℝ => waringOscillatoryIntegral k p.2 ^ s * e (-p.2*p.1)) (ν.prod volume) := by
    have hm := ((stronglyMeasurable_waringOscillatoryIntegral k).pow s).comp_measurable
      (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
    have he : Continuous (fun p : ℝ × ℝ => e (-p.2*p.1)) := continuous_e.comp (by fun_prop)
    apply ((integrable_waringOscillatoryIntegral_pow hk hks).norm.comp_snd ν).mono'
      (hm.mul he.stronglyMeasurable).aestronglyMeasurable
    exact .of_forall fun p => by simp [norm_e]
  simp only [waringSingularIntegral, intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap (f := fun t β : ℝ => waringOscillatoryIntegral k β ^ s * e (-β*t)) hpair]
  simp_rw [integral_const_mul]
  rfl

/-- On subintervals strictly below one the inverse Fourier density integrates
to the volume difference of the power ball. -/
theorem integral_waringSingularIntegral_eq_volume_sub {s k : ℕ} (hk : 0 < k) (hks : k < s)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ y in a..b, waringSingularIntegral s k y) = ((waringVolume s k b - waringVolume s k a : ℝ) : ℂ) := by
  let μ := waringDistribution s k
  let f := boxAverage μ (b-a)
  have hba : b - (b-a) = a := by ring
  have hc : ContinuousAt f b := by
    have h1 := (hasDerivAt_waringVolume (hk.trans hks) hk (ha.trans_le hab)).continuousAt
    have h2 : ContinuousAt (fun x : ℝ => waringVolume s k (x - (b-a))) b :=
      (hasDerivAt_waringVolume (hk.trans hks) hk (show 0 < b-(b-a) by linarith)).continuousAt.comp (f := fun x : ℝ => x-(b-a))
        (by fun_prop)
    apply (Complex.continuous_ofReal.continuousAt.comp (h1.sub h2)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hb] with x hx using boxAverage_waring_eq hk s (sub_nonneg.mpr hab) hx.le
  have hinv := (integrable_boxAverage μ (b-a)).fourier_fourierInv_eq (integrable_fourier_boxAverage hk hks _) hc
  change 𝓕 (𝓕⁻ f) b = f b at hinv
  rw [fourier_eq_e] at hinv
  calc
    _ = ∫ β : ℝ, waringOscillatoryIntegral k β ^ s * ∫ y in a..b, e (-β*y) :=
      intervalIntegral_waringSingularIntegral hk hks hab
    _ = ∫ β : ℝ, e (-b*β) * 𝓕⁻ f β := by
      refine integral_congr_ae (.of_forall fun β => ?_)
      dsimp only [f, μ]
      rw [← window_factor β a b hab, fourierInv_boxAverage, integral_e_waringDistribution]
      ring
    _ = f b := hinv
    _ = _ := by simpa [f, μ, hba] using boxAverage_waring_eq hk s (h := b-a) (sub_nonneg.mpr hab) hb.le

/-- The inverse Fourier integral equals the derivative of the geometric
volume at each interior level of the unit interval. -/
theorem waringSingularIntegral_eq_density {s k : ℕ} (hk : 0 < k) (hks : k < s)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    waringSingularIntegral s k t =
      (((Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k)) * t ^ ((s : ℝ) / k - 1) : ℝ) : ℂ) := by
  let a := t/2
  have ha : 0 < a := half_pos ht
  have hat : a < t := half_lt_self ht
  have hc := continuous_waringSingularIntegral hk hks
  have hJ := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hV := ((hasDerivAt_waringVolume (hk.trans hks) hk ht).sub_const (waringVolume s k a)).ofReal_comp
  exact hJ.unique (hV.congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds hat, gt_mem_nhds ht1] with x hx hx1
    exact integral_waringSingularIntegral_eq_volume_sub hk hks ha hx.le hx1))

/-- **Waring's singular integral at one**. Absolute convergence holds for
`s > k`. Its value is the positive-orthant density `Γ(1+1/k)^s / Γ(s/k)`. -/
theorem waringSingularIntegral_one {s k : ℕ} (hk : 0 < k) (hks : k < s) :
    waringSingularIntegral s k 1 = ((Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k) : ℝ) : ℂ) := by
  let C := Gamma (1 / (k : ℝ) + 1) ^ s / Gamma ((s : ℝ) / k)
  let D := fun t : ℝ => ((C * t ^ ((s : ℝ)/k-1) : ℝ) : ℂ)
  have hD : ContinuousAt D 1 := Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_const.mul (Real.continuousAt_rpow_const 1 ((s : ℝ)/k-1) (Or.inl one_ne_zero)))
  have heq : waringSingularIntegral s k =ᶠ[𝓝[<] (1 : ℝ)] D := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (lt_mem_nhds zero_lt_one)] with t ht1 ht
    exact waringSingularIntegral_eq_density hk hks ht ht1
  have h := tendsto_nhds_unique (continuous_waringSingularIntegral hk hks).continuousAt.continuousWithinAt.tendsto
    (hD.continuousWithinAt.tendsto.congr' heq.symm)
  simpa [D,C] using h

/-- The same integrable majorant bounds the singular integral at every real target. -/
theorem norm_waringSingularIntegral_le (s k : ℕ) (t : ℝ) :
    ‖waringSingularIntegral s k t‖ ≤ ∫ β : ℝ, ‖waringOscillatoryIntegral k β ^ s‖ := by
  simpa [waringSingularIntegral, norm_mul, norm_e] using
    norm_integral_le_integral_norm (fun β : ℝ => waringOscillatoryIntegral k β ^ s * e (-β*t))

/-- The error after truncating at frequencies of magnitude at most `R` admits
a bound independent of the target `t`. -/
theorem norm_waringSingularIntegral_sub_truncation_le {s k : ℕ} (hk : 0 < k) (hks : k < s)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ‖waringSingularIntegral s k t -
        ∫ β in -R..R, waringOscillatoryIntegral k β ^ s * e (-β*t)‖ ≤
      ∫ β in (Ioc (-R) R)ᶜ, ‖waringOscillatoryIntegral k β ^ s‖ := by
  rw [waringSingularIntegral, intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    ← setIntegral_compl measurableSet_Ioc (integrable_waringSingularIntegrand hk hks t)]
  simpa [norm_mul, norm_e] using norm_integral_le_integral_norm
    (μ := volume.restrict (Ioc (-R) R)ᶜ) (fun β : ℝ => waringOscillatoryIntegral k β ^ s * e (-β*t))

/-- The uniform majorant for the truncation error tends to zero. -/
theorem tendsto_waringSingularIntegral_tail {s k : ℕ} (hk : 0 < k) (hks : k < s) :
    Tendsto (fun R : ℝ => ∫ β in (Ioc (-R) R)ᶜ, ‖waringOscillatoryIntegral k β ^ s‖) atTop (𝓝 0) := by
  have h := (integrable_waringOscillatoryIntegral_pow hk hks).norm
  have hi := intervalIntegral_tendsto_integral h tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have hz := hi.const_sub (∫ β : ℝ, ‖waringOscillatoryIntegral k β ^ s‖)
  rw [sub_self] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  dsimp only [id_eq]
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), setIntegral_compl measurableSet_Ioc h]

end AnalyticNumberTheory.AdditiveNumberTheory
