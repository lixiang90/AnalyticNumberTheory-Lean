import AnalyticNumberTheory.RiemannZeta.HurwitzFourierExpansion

/-!
# Conjugation of sharp Hurwitz polynomials and gamma factors

Real shifts give a Schwarz reflection identity. The two Fourier frequencies
are interchanged under conjugation, including their translation factors.
-/
noncomputable section
open Real Complex Filter Set Finset MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem positive_cpow_conj {u : ℝ} (hu : 0≤u) (k : ℂ) :
    (u:ℂ)^(conj k)=conj ((u:ℂ)^k) := by
  simpa using Complex.cpow_conj (u:ℂ) k (by rw [Complex.arg_ofReal_of_nonneg hu]; exact Real.pi_ne_zero.symm)

theorem hurwitzDirectSum_conj {a : ℝ} (ha : 0<a) (x : ℝ) (s : ℂ) :
    hurwitzDirectSum a x (conj s)=conj (hurwitzDirectSum a x s) := by
  simp only [hurwitzDirectSum,map_sum]
  apply sum_congr rfl
  intro n hn
  rw [←Complex.ofReal_natCast,←Complex.ofReal_add,←map_neg,positive_cpow_conj (by positivity)]

theorem hurwitzZeta_conj_in_strip {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) {s : ℂ}
    (hσ : -1<s.re) (hs : s≠1) :
    HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (conj s)=conj (HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s) := by
  have hs' : conj s ≠ 1 := by
    intro h; apply hs; simpa using congrArg conj h
  rw [hurwitzZeta_eq_real_cutoff ha (le_refl a) (by simpa using hσ) hs',
      hurwitzZeta_eq_real_cutoff ha (le_refl a) hσ hs,hurwitzDirectSum_conj ha.1]
  simp only [sub_self,map_sub,map_add,map_mul,map_div,map_one,Complex.conj_ofReal,map_ofNat]
  have hint : (∫ u in Ioi (0:ℝ),(bernoulliKernel 2 u:ℂ)*((u+a:ℝ):ℂ)^(-conj s-2)) =
      conj (∫ u in Ioi (0:ℝ),(bernoulliKernel 2 u:ℂ)*((u+a:ℝ):ℂ)^(-s-2)) := by
    rw [←integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have he : -conj s-2=conj (-s-2) := by simp [Complex.conj_ofNat]
    rw [he,positive_cpow_conj (u:=u+a) (by linarith [mem_Ioi.mp hu,ha.1])]
    simp
  rw [hint,map_div₀]
  have hp (k : ℂ) := positive_cpow_conj ha.1.le k
  have hp₁ := hp (1-s)
  have hp₂ := hp (-s-1)
  have hp₃ := hp (-s)
  simp only [map_sub,map_one,map_neg] at hp₁ hp₂ hp₃ ⊢
  rw [hp₁,hp₂,hp₃]

theorem hurwitzShift_conj (a ω : ℝ) : hurwitzShift a (-ω)=conj (hurwitzShift a ω) := by
  rw [hurwitzShift,hurwitzShift,←Complex.exp_conj]; congr 1
  simp <;> ring

theorem hurwitzDualMode_conj (s : ℂ) {ω : ℝ} (hw : ω≠0) :
    hurwitzDualMode (conj s) (-ω)=conj (hurwitzDualMode s ω) := by
  have hz : hurwitzFrequency (-ω) = conj (hurwitzFrequency ω) := by simp [hurwitzFrequency]
  have harg : (hurwitzFrequency (-ω)).arg ≠ Real.pi := by
    intro he
    have him := (Complex.arg_eq_pi_iff.mp he).2
    simp [hurwitzFrequency] at him
    exact hw him
  rw [hurwitzDualMode,hurwitzDualMode,hz,show conj s-1=conj (s-1) by simp,
    show 1-conj s=conj (1-s) by simp,Complex.Gamma_conj,map_mul]
  congr 1
  rw [←hz,Complex.cpow_conj _ _ harg,hz,conj_conj]

end AnalyticNumberTheory.RiemannZeta
