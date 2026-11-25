import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.WeightedArgumentPrinciple
import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaContours
import AnalyticNumberTheory.PrimeDistribution.PrimitiveConductorBlockSums

/-!
# The zero contribution to a primitive character Perron contour

The completed function has only critical-strip zeros. Its functional
equation pairs the regularized weights even when a zero lies near the origin.
-/

noncomputable section

open Complex Set Finset
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- The finite contour integral is exactly the signed sum of the enclosed
residues, including possible real zeros. -/
theorem completed_perron_boundary_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x c T : ℝ} (hx : 1≤x) (hc : 1<c) (hT : 0<T)
    (hn : ∀ z : ℂ, -(1/2:ℝ)≤z.re → z.re≤c → |z.im|=T → DirichletCharacter.completedLFunction χ z≠0) :
    rectangleBoundary (fun z => perronDifferenceWeight x z*logDeriv (DirichletCharacter.completedLFunction χ) z)
      ⟨-(1/2),-T⟩ ⟨c,T⟩ = 2*Real.pi*I*∑ z∈criticalStripZeroFinset χ (-T) T,
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z:ℂ)*perronDifferenceWeight x z := by
  let Z := criticalStripZeroFinset χ (-T) T
  let F := DirichletCharacter.completedLFunction χ
  have hχn := isPrimitive_ne_one hχ hq
  have hi (z : ℂ) (hz : z∈Z) : z.re∈Ioo (-(1/2:ℝ)) c ∧ z.im∈Ioo (-T) T := by
    obtain ⟨hl,hu,ht,ht',hf⟩ := (mem_criticalStripZeroFinset χ).mp hz
    have hf' := (completedLFunction_eq_zero_iff_criticalStrip hχ hq z).mpr ⟨hl,hu,hf⟩
    have hne : |z.im|≠T := fun he => hn z (by linarith) (by linarith) he hf'
    refine ⟨⟨by linarith,by linarith⟩,lt_of_le_of_ne ht (fun h => ?_),lt_of_le_of_ne ht' (fun h => ?_)⟩
    · exact hne (by rw [←h,abs_neg,abs_of_pos hT])
    · exact hne (by rw [h,abs_of_pos hT])
  have ha (z : ℂ) (hz : z∈Icc (-(1/2:ℝ)) c ×ℂ Icc (-T) T) (h : F z=0) : z∈Z := by
    obtain ⟨hl,hu,hf⟩ := (completedLFunction_eq_zero_iff_criticalStrip hχ hq z).mp h
    exact (mem_criticalStripZeroFinset χ).mpr ⟨hl,hu,hz.2.1,hz.2.2,hf⟩
  have hr := weighted_argument_principle_rect_entire (differentiable_completedLFunction_of_ne_one hχn)
    (differentiable_perronDifferenceWeight x) (by linarith : -(1/2:ℝ)<c) (by linarith : -T<T) Z hi ha
  exact hr

theorem completed_perron_boundary_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x c T : ℝ} (hx : 1≤x) (hc : 1<c) (hT : 0<T)
    (hn : ∀ z : ℂ, -(1/2:ℝ)≤z.re → z.re≤c → |z.im|=T → DirichletCharacter.completedLFunction χ z≠0) :
    ‖rectangleBoundary (fun z => perronDifferenceWeight x z*logDeriv (DirichletCharacter.completedLFunction χ) z)
        ⟨-(1/2),-T⟩ ⟨c,T⟩‖ ≤
      64*Real.pi*characterZeroWeight χ T (fun z => x^z.re/(1+|z.im|)) := by
  let Z := criticalStripZeroFinset χ (-T) T
  let F := DirichletCharacter.completedLFunction χ
  have hχn := isPrimitive_ne_one hχ hq
  have hr := completed_perron_boundary_eq hχ hq hx hc hT hn
  rw [hr,norm_mul,norm_mul,norm_mul,norm_I,mul_one,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hs : ‖∑z∈Z,(analyticOrderNatAt F z:ℂ)*perronDifferenceWeight x z‖ ≤
      32*characterZeroWeight χ T (fun z => x^z.re/(1+|z.im|)) := by
    apply (norm_sum_le _ _).trans
    have ho : ∀ z∈Z, analyticOrderNatAt F z=analyticOrderNatAt χ.LFunction z := by
      intro z hz
      exact (analyticOrderNatAt_LFunction_eq_completedLFunction χ ((mem_criticalStripZeroFinset χ).mp hz).1 (.inl hχn)).symm
    have he : ∑z∈Z,‖(analyticOrderNatAt F z:ℂ)*perronDifferenceWeight x z‖ =
        ∑z∈Z,(analyticOrderNatAt χ.LFunction z:ℝ)*‖perronDifferenceWeight x z‖ := by
      apply sum_congr rfl; intro z hz; rw [norm_mul,Complex.norm_natCast,ho z hz]
    rw [he]
    simpa [Z,characterZeroWeight,characterStripZeros,characterZeroMultiplicity,NeZero.ne q] using
      sum_norm_perronDifferenceWeight_le hχ hq hx (-T) T
  calc
    _ ≤ (2*Real.pi)*(32*characterZeroWeight χ T (fun z => x^z.re/(1+|z.im|))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem completed_perron_shift_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x c T B M : ℝ} (hx : 1≤x) (hc : 1<c) (hc' : c≤3/2)
    (hT : 0<T) (hB : 0≤B) (hM : 0≤M)
    (hv : ∀ t∈Icc (-T) T, ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1/2:ℂ)+t*I)‖≤B)
    (hh : ∀ z : ℂ, -(1/2:ℝ)≤z.re → z.re≤c → |z.im|=T →
      DirichletCharacter.completedLFunction χ z≠0 ∧ ‖logDeriv (DirichletCharacter.completedLFunction χ) z‖≤M) :
    ‖perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T‖≤
      64*Real.pi*characterZeroWeight χ T (fun z => x^z.re/(1+|z.im|))+
      12*B*Real.log (1+T)+4*((x^c+1)/T)*M := by
  let G := logDeriv (DirichletCharacter.completedLFunction χ)
  let W := fun s => perronDifferenceWeight x s*G s
  have hxp : 0<x := by linarith
  have hres := completed_perron_boundary_bound hχ hq hx hc hT (fun z hl hu ht => (hh z hl hu ht).1)
  have h := norm_perronVertical_of_boundary (F:=W) (a:= -(1/2:ℝ)) (b:=c) (T:=T) rfl
  have hleft := norm_perronVertical_weight (F:=G) hxp hT.le (σ:= -(1/2:ℝ)) (by norm_num) hB
    (fun t ht => by simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,neg_div] using hv t ht)
  have hH (t : ℝ) (ht : |t|=T) := norm_perronHorizontal_weight (F:=G) (a:= -(1/2:ℝ)) (b:=c) hx
    (by linarith) (t:=t) (by intro h; rw [h,abs_zero] at ht; linarith) hM
    (fun u hu => (hh _ (by simpa using hu.1) (by simpa using hu.2) (by simpa using ht)).2)
  have ht := hH T (abs_of_pos hT)
  have hb := hH (-T) (by rw [abs_neg,abs_of_pos hT])
  rw [abs_of_pos hT] at ht
  rw [abs_neg,abs_of_pos hT] at hb
  have he : x^(-(1/2:ℝ))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hl := Real.log_nonneg (by linarith : 1≤1+T)
  have H₁ := mul_le_mul_of_nonneg_right (show x^(-(1/2:ℝ))+1≤2 by linarith) (mul_nonneg hB hl)
  have H₂ := mul_le_mul_of_nonneg_right (show c- -(1/2:ℝ)≤2 by linarith) (show 0≤(x^c+1)/T*M by positivity)
  apply h.trans
  change ‖rectangleBoundary W _ _‖+‖perronVertical W (-(1/2:ℝ)) T‖+
    ‖perronHorizontal W (-(1/2:ℝ)) c T‖+‖perronHorizontal W (-(1/2:ℝ)) c (-T)‖≤_
  change ‖rectangleBoundary W _ _‖≤_ at hres
  change ‖perronVertical W _ T‖≤_ at hleft
  change ‖perronHorizontal W _ c T‖≤_ at ht
  change ‖perronHorizontal W _ c (-T)‖≤_ at hb
  linarith

end AnalyticNumberTheory.PrimeDistribution
