import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronCorrection
import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronResidues
import AnalyticNumberTheory.PrimeDistribution.SignedPerronWeights

/-!
# Signed residue contributions on the Perron contour

The factor `2πi` in the argument principle cancels against the Perron
normalization and the differential on the vertical side.
-/

noncomputable section
open Complex Set Finset
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

private theorem norm_perronVertical_sub_of_boundary {F : ℂ→ℂ} {a b T : ℝ} {p : ℂ}
    (h : rectangleBoundary F ⟨a,-T⟩ ⟨b,T⟩=I*p) :
    ‖perronVertical F b T-p‖≤‖perronVertical F a T‖+‖perronHorizontal F a b T‖+
      ‖perronHorizontal F a b (-T)‖ := by
  change perronHorizontal F a b (-T)-perronHorizontal F a b T+
    I*perronVertical F b T-I*perronVertical F a T=I*p at h
  have he : I*(perronVertical F b T-p)=I*perronVertical F a T+
      perronHorizontal F a b T-perronHorizontal F a b (-T) := by linear_combination h
  have H := congrArg norm he
  simp only [norm_mul,Complex.norm_I,one_mul] at H
  rw [H]
  have h₁ := norm_sub_le (I*perronVertical F a T+perronHorizontal F a b T) (perronHorizontal F a b (-T))
  have h₂ := norm_add_le (I*perronVertical F a T) (perronHorizontal F a b T)
  rw [norm_mul,Complex.norm_I,one_mul] at h₂
  linarith only [h₁,h₂]

/-- The three non-Perron edges control the difference of the right integral
and the signed residue sum. -/
theorem completed_perron_signed_shift_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x c T B M : ℝ} (hx : 1≤x) (hc : 1<c) (hc' : c≤3/2)
    (hT : 0<T) (hB : 0≤B) (hM : 0≤M)
    (hv : ∀ t∈Icc (-T) T, ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1/2:ℂ)+t*I)‖≤B)
    (hh : ∀ z : ℂ, -(1/2:ℝ)≤z.re → z.re≤c → |z.im|=T →
      DirichletCharacter.completedLFunction χ z≠0 ∧ ‖logDeriv (DirichletCharacter.completedLFunction χ) z‖≤M) :
    ‖perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T-
      (2*Real.pi:ℂ)*characterPerronZeroSum χ x T‖ ≤
      12*B*Real.log (1+T)+4*((x^c+1)/T)*M := by
  let G := logDeriv (DirichletCharacter.completedLFunction χ)
  let F := fun s => perronDifferenceWeight x s*G s
  have he := completed_perron_boundary_eq hχ hq hx hc hT (fun z hl hu ht => (hh z hl hu ht).1)
  have hz : (∑z∈criticalStripZeroFinset χ (-T) T, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z:ℂ)*
      perronDifferenceWeight x z)=characterPerronZeroSum χ x T := by
    simp only [characterPerronZeroSum,characterStripZeros,characterZeroMultiplicity,dite_eq_left (NeZero.ne q)]
    apply sum_congr rfl
    intro z hm
    rw [analyticOrderNatAt_LFunction_eq_completedLFunction χ ((mem_criticalStripZeroFinset χ).mp hm).1 (.inl (isPrimitive_ne_one hχ hq))]
  rw [hz] at he
  have H : rectangleBoundary F ⟨-(1/2),-T⟩ ⟨c,T⟩ = I*((2*Real.pi:ℂ)*characterPerronZeroSum χ x T) :=
    he.trans (by ring)
  apply (norm_perronVertical_sub_of_boundary H).trans
  have hxp : 0<x := by linarith
  have hleft := norm_perronVertical_weight (F:=G) hxp hT.le (σ:= -(1/2:ℝ)) (by norm_num) hB
    (fun t ht => by simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,neg_div] using hv t ht)
  have hH (t : ℝ) (ht : |t|=T) := norm_perronHorizontal_weight (F:=G) (a:= -(1/2:ℝ)) (b:=c) hx
    (by linarith) (t:=t) (by intro h; rw [h,abs_zero] at ht; linarith) hM
    (fun u hu => (hh _ (by simpa using hu.1) (by simpa using hu.2) (by simpa using ht)).2)
  have ht := hH T (abs_of_pos hT)
  have hb := hH (-T) (by rw [abs_neg,abs_of_pos hT])
  rw [abs_of_pos hT] at ht
  rw [abs_neg,abs_of_pos hT] at hb
  have hr : x^(-(1/2:ℝ))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hl := Real.log_nonneg (by linarith : 1≤1+T)
  have H₁ := mul_le_mul_of_nonneg_right (show x^(-(1/2:ℝ))+1≤2 by linarith) (mul_nonneg hB hl)
  have H₂ := mul_le_mul_of_nonneg_right (show c- -(1/2:ℝ)≤2 by linarith) (show 0≤(x^c+1)/T*M by positivity)
  change ‖perronVertical F _ T‖≤_ at hleft
  change ‖perronHorizontal F _ c T‖≤_ at ht
  change ‖perronHorizontal F _ c (-T)‖≤_ at hb
  linarith only [hleft,ht,hb,H₁,H₂]

/-- Norm comparison retaining an arbitrary prescribed complex main term. -/
theorem norm_twistedPerron_add_le_completed_and_corrections {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hq : 2≤q) {x c T : ℝ} (hx : 0<x) (hc : 1<c) (p : ℂ) :
    ‖dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T+p‖ ≤
      ‖perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T-
        (2*Real.pi:ℂ)*p‖+
      ‖perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T‖+
      ‖perronVertical (fun s => logDeriv χ.LFunction s/s) c T‖ := by
  let J := perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T
  let K := perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T
  let U := perronVertical (fun s => logDeriv χ.LFunction s/s) c T
  let v : ℂ := 2*Real.pi
  have hn : v≠0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hv : ‖-(1/v)‖≤1 := by
    dsimp [v]
    rw [norm_neg,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  rw [twistedPerron_completion_identity hχ hq hx hc]
  change ‖-(1/v)*(J-K+U)+p‖≤‖J-v*p‖+‖K‖+‖U‖
  rw [show -(1/v)*(J-K+U)+p= -(1/v)*((J-v*p)-K+U) by field_simp; ring,norm_mul]
  calc
    _ ≤ ‖(J-v*p)-K+U‖ := (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := (norm_add_le _ _).trans (by linarith only [norm_sub_le (J-v*p) K])

end AnalyticNumberTheory.PrimeDistribution
