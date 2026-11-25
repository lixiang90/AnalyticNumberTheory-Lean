import AnalyticNumberTheory.PrimeDistribution.InghamTypeII
import AnalyticNumberTheory.AnalyticTools.MixedWeakMoments
import AnalyticNumberTheory.PrimeDistribution.HuxleyMomentBalance
import AnalyticNumberTheory.RiemannZeta.RieszDetectorKernel

/-!
# Weak moment estimates on a finite family of zero detectors

Restrict the translated kernel sum to the common height window, and use
it as the density of a finite measure. The peak and the mass give distinct
powers of the occupancy and of the number of detected zeros.
-/
noncomputable section
open Complex Real Filter Finset MeasureTheory
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.PrimeDistribution

theorem huxley_weighted_detector {T : ℕ} {S : Finset ℂ} {A B C r V F : ℝ}
    (hA : 0<A) (hB : 0<B) (hC : 0≤C) (hr : 0<r)
    (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im ≤ 2*T) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0≤f t) (hg0 : ∀ t, 0≤g t)
    (hdet : ∀ z ∈ S, V ≤ ∫ v in -(4*(T:ℝ))..4*T, (1/(1+|v|)^4)*(f (z.im+v)*g (z.im+v)))
    (hpeak : ∀ t, (∑ z∈S,1/(1+|t-z.im|)^4)≤A)
    (hmass : (∫ t in -(6*(T:ℝ))..6*T, ∑ z∈S,1/(1+|t-z.im|)^4)≤r)
    (hfour : (∫ t in -(6*(T:ℝ))..6*T,(f t)^4)≤F)
    (htail : ∀ v>0,(volume.restrict (Set.Ioc (-(6*(T:ℝ))) (6*T))).real {t | v<g t}≤B/v^2+C/v^6) :
    (S.card:ℝ)*V≤(A*F)^(1/4:ℝ)*((5:ℝ)^(3/4:ℝ)*
      ((A*B)^(1/2:ℝ)*r^(1/4:ℝ)+(A*C)^(1/6:ℝ)*r^(7/12:ℝ))) := by
  let b := 6*(T:ℝ)
  have hb : -b≤b := by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) T]
  let ν := (volume:Measure ℝ).restrict (Set.Ioc (-b) b)
  let _ : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioc (-b) b)))
  let w (t : ℝ) := ∑ z∈S,1/(1+|t-z.im|)^4
  have hw : Continuous w := by
    apply continuous_finsetSum; intro z _
    exact continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 4)
      (fun t => by change (1+|t-z.im|)^4≠0; positivity)
  have hw0 (t : ℝ) : 0≤w t := sum_nonneg (fun _ _ => by positivity)
  let W := fun t => ENNReal.ofReal (w t)
  let νw := ν.withDensity W
  have hwm : Measurable W := hw.measurable.ennreal_ofReal
  have hwt : ∀ᵐ t ∂ν, W t<⊤ := .of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hdom : νw≤ENNReal.ofReal A • ν := by
    rw [←withDensity_const]
    exact withDensity_mono (.of_forall (fun t => ENNReal.ofReal_le_ofReal (hpeak t)))
  have hfinite (E : Set ℝ) : (ENNReal.ofReal A • ν) E≠⊤ := by
    rw [smul_apply,smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  let _ : IsFiniteMeasure νw := ⟨(hdom Set.univ).trans_lt ((hfinite _).lt_top)⟩
  have hreal (E : Set ℝ) : νw.real E≤A*ν.real E := by
    have he := ENNReal.toReal_mono (hfinite E) (hdom E)
    simpa only [measureReal_def,smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hA.le] using he
  have heq (G : ℝ → ℝ) : (∫ t,G t ∂νw)=∫ t in -b..b,w t*G t := by
    rw [intervalIntegral.integral_of_le hb]
    simpa only [νw,W,smul_eq_mul,ENNReal.toReal_ofReal (hw0 _)] using
      (integral_withDensity_eq_integral_toReal_smul hwm hwt G)
  have hm : νw.real Set.univ≤r := by
    have he := heq (fun _ => (1:ℝ))
    simp only [integral_const,smul_eq_mul,mul_one] at he
    exact he.le.trans hmass
  have hfi : Integrable (fun t => f t^4) νw := by
    apply (integrable_withDensity_iff_integrable_smul' hwm hwt).mpr
    simp only [W,ENNReal.toReal_ofReal (hw0 _),smul_eq_mul]
    change IntegrableOn (fun t => w t*(f t)^4) (Set.Ioc (-b) b) volume
    have hc : Continuous (fun t => w t*(f t)^4) := hw.mul (hf.pow 4)
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htail' (v : ℝ) (hv : 0<v) : νw.real {t | v<g t}≤(A*B)/v^2+(A*C)/v^6 :=
    (hreal _).trans ((mul_le_mul_of_nonneg_left (htail v hv) hA.le).trans_eq (by ring))
  have hh := mixed_weak_holder hf.measurable.aemeasurable hg.measurable.aemeasurable hf0 hg0 hfi
    (mul_pos hA hB) (mul_nonneg hA.le hC) hr hm htail'
  have hF : (∫ t,f t^4 ∂νw)≤A*F := by
    rw [heq]
    calc _ ≤ ∫ t in -b..b,A*f t^4 := intervalIntegral.integral_mono_on hb
                  ((hw.mul (hf.pow 4)).intervalIntegrable ..) ((continuous_const.mul (hf.pow 4)).intervalIntegrable ..)
                  (fun t _ => mul_le_mul_of_nonneg_right (hpeak t) (pow_nonneg (hf0 t) 4))
         _ ≤ _ := by rw [intervalIntegral.integral_const_mul]; exact mul_le_mul_of_nonneg_left hfour hA.le
  have hd := ingham_sum_translated_detectors_le him hf hg hf0 hg0 hdet
  have he := heq (fun t => f t*g t)
  simp only [←mul_assoc] at he
  change _≤∫ t in -b..b,w t*f t*g t at hd
  exact (hd.trans_eq he.symm).trans (hh.trans (by gcongr <;> norm_num))



/-- Huxley's integral alternative. A distribution estimate for the Möbius
polynomial on the critical line bounds the number of detected ordinates.
The multiplicative constant depends only on the occupancy and distribution
constants, uniformly in the mollifier length, height, and detection level. -/
theorem huxley_typeII_count {K D : ℝ} (hK : 0<K) (hD : 0<D) :
    ∃ C>0, ∀ {T X : ℕ} {S : Finset ℂ} {V : ℝ}, 1≤T → 1≤X → 0<V →
    (∀ z∈S,0≤z.im ∧ z.im≤2*T) →
    (∀ j<2*T+1,((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ)≤K*(1+Real.log T)) →
    (∀ z∈S, V≤∫ v in -(4*(T:ℝ))..4*T,(1/(1+|v|)^4)*
        (‖riemannZeta ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖*
         ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+((z.im+v:ℝ):ℂ)*I)‖)) →
    (∀ v>0,(volume.restrict (Set.Ioc (-(6*(T:ℝ))) (6*T))).real
        {t : ℝ | v<‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖}≤
        D*X*(1+Real.log T)^3/v^2+D*T*X*(1+Real.log T)^7/v^6) →
    (S.card:ℝ)≤C*(1+Real.log T)^10*
        ((T:ℝ)^(1/3:ℝ)*(X:ℝ)^(2/3:ℝ)*V^(-(4/3):ℝ)+
         T*(X:ℝ)^(2/5:ℝ)*V^(-(12/5):ℝ)) := by
  obtain ⟨Z,hZ,hfour⟩ := ingham_zeta_fourth_mean
  let P := 2*π*K
  have hP : 0<P := by dsimp [P]; positivity
  obtain ⟨A,hA,hshape⟩ := huxley_weak_moment_shape hP hZ hD
  refine ⟨1+(2*A)^(4/3:ℝ)+(2*A)^(12/5:ℝ),by positivity,?_⟩
  intro T X S V hT hX hV him hcrowd hdet htail
  let L := 1+Real.log T
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg (show (1:ℝ)≤T by exact_mod_cast hT)]
  have hL0 : 0<L := by linarith
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  have hX' : (0:ℝ)<X := by exact_mod_cast hX
  by_cases hs : S.Nonempty
  · have hR : 0<(S.card:ℝ) := by exact_mod_cast card_pos.mpr hs
    let f (t : ℝ) := ‖riemannZeta ((1/2:ℂ)+t*I)‖
    let g (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖
    have hf : Continuous f := RiemannZeta.continuous_riemannZeta_half.norm
    have hg : Continuous g := by
      apply Continuous.norm
      apply (RiemannZeta.differentiable_rieszMobiusPolynomial X).continuous.comp
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hpeak (t : ℝ) : (∑ z∈S,1/(1+|t-z.im|)^4)≤P*L := by
      have hht : ∀ z∈S,0≤z.im ∧ z.im<(2*T+1:ℕ) := by
        intro z hz; obtain ⟨h₀,h₂⟩ := him z hz; exact ⟨h₀,by push_cast; linarith⟩
      exact (ingham_kernel_sum_le S (show 0≤K*L by positivity) hht hcrowd t).trans_eq (by dsimp only [P]; ring)
    have hbound := huxley_weighted_detector (show 0<P*L by positivity) (show 0<D*X*L^3 by positivity)
      (show 0≤D*T*X*L^7 by positivity) (show 0<π*(S.card:ℝ) by positivity) him hf hg
      (fun t => norm_nonneg _) (fun t => norm_nonneg _) hdet hpeak
      (ingham_kernel_integral_le S (by linarith : -(6*(T:ℝ))≤6*T)) (hfour T hT) htail
    exact huxley_weak_count_balance hR hV hA.le hL hT'.le hX'.le (hbound.trans (hshape hL hT'.le hX'.le hR.le))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [card_empty,Nat.cast_zero]; positivity

end AnalyticNumberTheory.PrimeDistribution
