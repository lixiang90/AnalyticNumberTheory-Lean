import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# A mixed weak-type bound for a fourth-moment pairing

A weak distribution bound with powers two and six controls the conjugate
four-thirds norm even when neither tail estimate alone is available.
-/
noncomputable section
open Set Filter MeasureTheory Real
namespace AnalyticNumberTheory.AnalyticTools

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

private theorem normalized_moment {g : α → ℝ} (hg : AEMeasurable g μ)
    (hg0 : ∀ x, 0≤g x) {r : ℝ} (hr : 0≤r) (hm : μ.real univ≤r)
    (hd : ∀ v≥1, μ.real {x | v<g x}≤2*r/v^2) :
    Integrable (fun x => g x^(4/3:ℝ)) μ ∧ (∫ x, g x^(4/3:ℝ) ∂μ)≤5*r := by
  let H (x : α) := g x^(4/3:ℝ)
  have hH0 : ∀ x, 0≤H x := fun x => Real.rpow_nonneg (hg0 x) _
  have hH : AEMeasurable H μ := hg.pow_const _
  have htail (t : ℝ) (ht : 1<t) :
      μ {x | t<H x}≤ENNReal.ofReal (2*r*t^(-(3/2):ℝ)) := by
    have ht0 : 0<t := by linarith
    have hv : 1≤t^(3/4:ℝ) := Real.one_le_rpow ht.le (by norm_num)
    have hinc : {x | t<H x}⊆{x | t^(3/4:ℝ)<g x} := by
      intro x hx
      change t < (g x)^(4/3:ℝ) at hx
      change t^(3/4:ℝ)<g x
      calc _ < ((g x)^(4/3:ℝ))^(3/4:ℝ) := Real.rpow_lt_rpow ht0.le hx (by norm_num)
           _ = _ := by rw [←Real.rpow_mul (hg0 x)]; norm_num
    rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    change μ.real _≤_
    apply (measureReal_mono hinc).trans ((hd _ hv).trans_eq ?_)
    rw [←Real.rpow_mul_natCast ht0.le,Real.rpow_neg ht0.le]
    norm_num; ring
  have hu : Ioi (0:ℝ)=Ioc 0 1 ∪ Ioi 1 := by ext t; simp
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := Set.disjoint_left.mpr (fun _ h₁ h₂ => not_lt_of_ge h₁.2 h₂)
  have hi := (integrableOn_Ioi_rpow_of_lt (a:=(-(3/2):ℝ)) (by norm_num) zero_lt_one).const_mul (2*r)
  have hreal : (∫ t : ℝ in Ioi 1, 2*r*t^(-(3/2):ℝ))=4*r := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num; ring
  have htailI : (∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (2*r*t^(-(3/2):ℝ)))=ENNReal.ofReal (4*r) := by
    rw [←hreal,ofReal_integral_eq_lintegral_ofReal hi]
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [show 1<t from ht]) _)
  have hl : (∫⁻ x,ENNReal.ofReal (H x) ∂μ)≤ENNReal.ofReal (5*r) := by
    rw [lintegral_eq_lintegral_meas_lt μ (.of_forall hH0) hH,hu,lintegral_union measurableSet_Ioi hdisj]
    calc _ ≤ (∫⁻ _t : ℝ in Ioc 0 1,ENNReal.ofReal r)+(∫⁻ t : ℝ in Ioi 1,ENNReal.ofReal (2*r*t^(-(3/2):ℝ))) := by
            apply add_le_add
            · apply lintegral_mono; intro t
              change μ _≤ENNReal.ofReal r
              rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
              exact ENNReal.ofReal_le_ofReal ((measureReal_mono (subset_univ _)).trans hm)
            · exact setLIntegral_mono' measurableSet_Ioi htail
         _ = _ := by rw [htailI,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
                     simp only [sub_zero,ENNReal.ofReal_one,mul_one]
                     rw [←ENNReal.ofReal_add hr (show 0≤4*r by positivity)]
                     congr 1; ring
  have hint : Integrable H μ := ⟨hH.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (.of_forall hH0)).mpr
    (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint (.of_forall hH0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤5*r)).mp hl



/-- A mixed weak bound with powers two and six implies strong four-thirds
integrability and an explicit estimate on the four-thirds norm. Here r
can be any positive upper bound for the total mass. -/
theorem mixed_weak_four_thirds {g : α → ℝ} (hg : AEMeasurable g μ) (hg0 : ∀ x, 0≤g x)
    {B C r : ℝ} (hB : 0<B) (hC : 0≤C) (hr : 0<r) (hm : μ.real univ≤r)
    (hd : ∀ v>0, μ.real {x | v<g x}≤B/v^2+C/v^6) :
    Integrable (fun x => g x^(4/3:ℝ)) μ ∧
      (∫ x, g x^(4/3:ℝ) ∂μ)^(3/4:ℝ)≤(5:ℝ)^(3/4:ℝ)*
        (B^(1/2:ℝ)*r^(1/4:ℝ)+C^(1/6:ℝ)*r^(7/12:ℝ)) := by
  let a := (B/r)^(1/2:ℝ)+(C/r)^(1/6:ℝ)
  have ha : 0<a := by dsimp [a]; positivity
  let G (x : α) := g x/a
  have hG0 (x : α) : 0≤G x := div_nonneg (hg0 x) ha.le
  have hG : AEMeasurable G μ := hg.div_const _
  have hba : B≤r*a^2 := by
    have hle : (B/r)^(1/2:ℝ)≤a := le_add_of_nonneg_right (by positivity)
    have hle' := pow_le_pow_left₀ (Real.rpow_nonneg (div_nonneg hB.le hr.le) _) hle 2
    rw [←Real.rpow_mul_natCast (div_nonneg hB.le hr.le)] at hle'
    norm_num at hle'; exact (div_le_iff₀ hr).mp hle' |>.trans_eq (by ring)
  have hca : C≤r*a^6 := by
    have hle : (C/r)^(1/6:ℝ)≤a := le_add_of_nonneg_left (by positivity)
    have hle' := pow_le_pow_left₀ (Real.rpow_nonneg (div_nonneg hC hr.le) _) hle 6
    rw [←Real.rpow_mul_natCast (div_nonneg hC hr.le)] at hle'
    norm_num at hle'; exact (div_le_iff₀ hr).mp hle' |>.trans_eq (by ring)
  have htail (v : ℝ) (hv : 1≤v) : μ.real {x | v<G x}≤2*r/v^2 := by
    have hv0 : 0<v := by linarith
    have he : {x | v<G x}={x | a*v<g x} := by
      ext x; change v<g x/a ↔ _; rw [lt_div_iff₀ ha,mul_comm v]
      rfl
    rw [he]
    apply (hd _ (mul_pos ha hv0)).trans
    calc _ ≤ (r*a^2)/(a*v)^2+(r*a^6)/(a*v)^6 := by gcongr
         _ = r/v^2+r/v^6 := by field_simp
         _ ≤ r/v^2+r/v^2 := add_le_add le_rfl (div_le_div_of_nonneg_left hr.le (pow_pos hv0 2) (pow_le_pow_right₀ hv (show 2≤6 by decide)))
         _ = _ := by ring
  obtain ⟨hint,hbound⟩ := normalized_moment hG hG0 hr.le hm htail
  have he (x : α) : g x^(4/3:ℝ)=a^(4/3:ℝ)*G x^(4/3:ℝ) := by
    rw [←Real.mul_rpow ha.le (hG0 x)]
    congr 1; dsimp [G]; field_simp
  constructor
  · simp_rw [he]; exact hint.const_mul _
  simp_rw [he]; rw [integral_const_mul]
  have h0 : 0≤∫ x,G x^(4/3:ℝ) ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (hG0 x) _)
  rw [Real.mul_rpow (Real.rpow_nonneg ha.le _) h0,←Real.rpow_mul ha.le,
    show (4/3:ℝ)*(3/4)=1 by norm_num,Real.rpow_one]
  calc _ ≤ a*(5*r)^(3/4:ℝ) := by gcongr <;> norm_num
       _ = _ := by
         dsimp [a]
         rw [Real.mul_rpow (by norm_num) hr.le,Real.div_rpow hB.le hr.le,Real.div_rpow hC hr.le]
         have hb : r^(3/4:ℝ)/r^(1/2:ℝ)=r^(1/4:ℝ) := by rw [←Real.rpow_sub hr]; norm_num
         have hc : r^(3/4:ℝ)/r^(1/6:ℝ)=r^(7/12:ℝ) := by rw [←Real.rpow_sub hr]; norm_num
         rw [←hb,←hc]; ring

/-- Hölder pairing of a fourth moment with a mixed weak distribution. -/
theorem mixed_weak_holder {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ x, 0≤f x) (hg0 : ∀ x, 0≤g x) (hfi : Integrable (fun x => (f x)^4) μ)
    {B C r : ℝ} (hB : 0<B) (hC : 0≤C) (hr : 0<r) (hm : μ.real univ≤r)
    (hd : ∀ v>0, μ.real {x | v<g x}≤B/v^2+C/v^6) :
    (∫ x, f x*g x ∂μ) ≤ (∫ x,(f x)^4 ∂μ)^(1/4:ℝ)*
      ((5:ℝ)^(3/4:ℝ)*(B^(1/2:ℝ)*r^(1/4:ℝ)+C^(1/6:ℝ)*r^(7/12:ℝ))) := by
  obtain ⟨hgi,hmom⟩ := mixed_weak_four_thirds hg hg0 hB hC hr hm hd
  have hfg : Real.HolderConjugate 4 (4/3) := by rw [Real.holderConjugate_iff]; norm_num
  have hf' : MemLp f (ENNReal.ofReal 4) μ := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable (by norm_num) (by simp)).mp
    simp only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4),Real.norm_of_nonneg (hf0 _),Real.rpow_ofNat]
    exact hfi
  have hg' : MemLp g (ENNReal.ofReal (4/3:ℝ)) μ := by
    apply (integrable_norm_rpow_iff hg.aestronglyMeasurable (by norm_num) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4/3),Real.norm_of_nonneg (hg0 _)] using hgi
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hfg (.of_forall hf0) (.of_forall hg0) hf' hg'
  rw [show (1/(4/3):ℝ)=3/4 by norm_num] at h
  simp only [Real.rpow_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_left hmom (Real.rpow_nonneg (integral_nonneg (fun x => pow_nonneg (hf0 x) 4)) _))

end AnalyticNumberTheory.AnalyticTools
