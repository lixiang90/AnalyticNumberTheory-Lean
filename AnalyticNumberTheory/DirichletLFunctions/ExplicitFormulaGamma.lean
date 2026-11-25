import AnalyticNumberTheory.DirichletLFunctions.RectangularCount
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Archimedean terms on the explicit-formula contour

The logarithmic derivative of the gamma factor grows logarithmically on the
right half of the contour. Reflection then gives the same bound on the left
vertical side for the completed L-function.
-/

noncomputable section

open Complex Set
open AnalyticNumberTheory.AnalyticTools.Gamma

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Logarithmic derivative of the archimedean factor, on the positive half-plane. -/
def characterGammaLogCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(1/2:ℂ)*(Real.log Real.pi:ℂ)+(1/2:ℂ)*AnalyticTools.Gamma.digamma ((s+(parityExp χ:ℂ))/2)

theorem differentiableAt_characterGammaLogCorrection {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0<s.re) : DifferentiableAt ℂ (characterGammaLogCorrection χ) s := by
  have hn : ∀ n : ℕ,(s+(parityExp χ:ℂ))/2≠-(n:ℂ) := by
    intro n h
    have hh := congrArg Complex.re h
    simp at hh
    linarith [Nat.cast_nonneg (α:=ℝ) (parityExp χ),Nat.cast_nonneg (α:=ℝ) n]
  have hh := (differentiableAt_digamma hn).comp s
    (((differentiableAt_id (𝕜:=ℂ)).add_const (parityExp χ:ℂ)).div_const 2)
  exact (differentiableAt_const _).add (hh.const_mul _)

private theorem norm_digamma_positive_strip :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, 1/4≤z.re → z.re≤2 →
      ‖AnalyticTools.Gamma.digamma z‖ ≤ C*(1+Real.log (|z.im|+2)) := by
  let K := Icc (1/4:ℝ) 2 ×ℂ Icc (-2:ℝ) 2
  have hc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hd : ContinuousOn AnalyticTools.Gamma.digamma K := by
    intro z hz
    apply (differentiableAt_digamma _).continuousAt.continuousWithinAt
    intro n hn
    have hh := congrArg Complex.re hn
    simp at hh
    linarith [hz.1.1,Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuousOn hd
  let B := Real.log (1+(max |(1/4:ℝ)| |(2:ℝ)|)^2)/2+Real.pi+
    (1/2+(1+8*((max |(1/4:ℝ)| |(2:ℝ)|)^2+1)^(3/2:ℝ))/12)
  let C := |M|+|B|+1
  have hC : 1≤C := by dsimp [C]; linarith [abs_nonneg M,abs_nonneg B]
  refine ⟨C,by linarith,fun z hl hu => ?_⟩
  have hlog : 0≤Real.log (|z.im|+2) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  by_cases h : 2≤|z.im|
  · have hh := norm_digamma_strip_le (σ₁:=1/4) (σ₂:=2) (σ:=z.re) (t:=z.im) ⟨hl,hu⟩ h
    rw [Complex.re_add_im] at hh
    have h₁ : ‖AnalyticTools.Gamma.digamma z‖≤Real.log |z.im|+B := by dsimp [B]; linarith
    have h₂ := Real.log_le_log (by linarith : 0 < abs z.im) (by linarith : |z.im|≤|z.im|+2)
    have h₃ := mul_le_mul_of_nonneg_right hC hlog
    dsimp [C] at *
    nlinarith [le_abs_self B,abs_nonneg M]
  · have hm := hM z (show z∈K from ⟨⟨hl,hu⟩,abs_le.mp (le_of_lt (lt_of_not_ge h))⟩)
    apply hm.trans
    have h₁ : M≤C := by dsimp [C]; linarith [le_abs_self M,abs_nonneg B]
    exact h₁.trans (le_mul_of_one_le_right (by linarith) (by linarith))

/-- Uniformity in both parities and all heights, including `t=0`. -/
theorem norm_characterGammaLogCorrection_le :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      1/2≤s.re → s.re≤3/2 →
      ‖characterGammaLogCorrection χ s‖ ≤ C*(1+Real.log (|s.im|+2)) := by
  obtain ⟨D,hD,HD⟩ := norm_digamma_positive_strip
  let K := |Real.log Real.pi|+D+1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,fun {q} _ χ {s} hl hu => ?_⟩
  let z := (s+(parityExp χ:ℂ))/2
  have hr : z.re=(s.re+(parityExp χ:ℝ))/2 := by simp [z]
  have hi : z.im=s.im/2 := by simp [z]
  have he : (parityExp χ:ℝ)≤1 := by exact_mod_cast parityExp_le_one χ
  have hz := HD z (by rw [hr]; linarith [Nat.cast_nonneg (α:=ℝ) (parityExp χ)]) (by rw [hr]; linarith)
  have hlog : 0≤Real.log (|s.im|+2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hlog' : Real.log (|z.im|+2)≤Real.log (|s.im|+2) := by
    apply Real.log_le_log (by positivity)
    rw [hi,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg s.im]
  have h := norm_add_le (-(1/2:ℂ)*(Real.log Real.pi:ℂ)) ((1/2:ℂ)*AnalyticTools.Gamma.digamma z)
  rw [norm_mul,norm_mul,norm_neg,norm_div,norm_one,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs] at h
  change ‖-(1/2:ℂ)*(Real.log Real.pi:ℂ)+(1/2:ℂ)*AnalyticTools.Gamma.digamma z‖ ≤ _
  apply h.trans
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_left hlog' hD.le,mul_nonneg (abs_nonneg (Real.log Real.pi)) hlog,
    abs_nonneg (Real.log Real.pi),norm_nonneg (AnalyticTools.Gamma.digamma z)]

/-- Reflection places the fixed left edge at absolute convergence. -/
theorem norm_completed_logDeriv_left_edge :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsPrimitive → 2≤q → ∀ t : ℝ,
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1/2:ℂ)+t*I)‖ ≤
        C*(1+Real.log ((q:ℝ)*(|t|+2))) := by
  obtain ⟨D,hD,HD⟩ := norm_characterGammaLogCorrection_le
  obtain ⟨B,hB,HB⟩ := norm_logDeriv_LFunction_re_gt_one_le
  refine ⟨4+B+D,by positivity,fun {q} _ {χ} hχ hq t => ?_⟩
  let z := (3/2:ℂ)-(t:ℂ)*I
  have hr : z.re=3/2 := by norm_num [z]
  have hi : z.im= -t := by simp [z]
  have hχ' := isPrimitive_ne_one (isPrimitive_star hχ) hq
  have hn : (star χ).LFunction z≠0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inl hχ') (by rw [hr]; norm_num)
  have hnc : DirichletCharacter.completedLFunction (star χ) z≠0 := by
    intro h
    obtain ⟨_,h',_⟩ := (completedLFunction_eq_zero_iff_criticalStrip (isPrimitive_star hχ) hq z).mp h
    linarith
  have hR := logDeriv_completedLFunction_reflect hχ hq hnc
  rw [show 1-z=(-1/2:ℂ)+t*I by dsimp [z]; ring] at hR
  have hsplit := logDeriv_completedLFunction_eq_add_gammaFactor_eq (star χ) hq (.inl hχ') hn
    (gammaFactor_ne_zero_of_re_pos _ (by rw [hr]; norm_num))
  change _ = logDeriv (star χ).LFunction z+characterGammaLogCorrection (star χ) z at hsplit
  have hγ := HD (star χ) (s:=z) (by rw [hr]; norm_num) (by rw [hr])
  rw [hi,abs_neg] at hγ
  have hL := HB (star χ) z (by rw [hr]; norm_num) (by rw [hr]; norm_num)
  rw [hr] at hL
  norm_num at hL
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hlq := Real.log_nonneg hq1
  have hlt : 0≤Real.log (|t|+2) := Real.log_nonneg (by linarith [abs_nonneg t])
  rw [hR,hsplit]
  have hh := norm_sub_le (-(Real.log (q:ℝ):ℂ))
    (logDeriv (star χ).LFunction z+characterGammaLogCorrection (star χ) z)
  rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlq] at hh
  apply hh.trans
  rw [Real.log_mul (by positivity) (by positivity)]
  nlinarith [norm_add_le (logDeriv (star χ).LFunction z) (characterGammaLogCorrection (star χ) z),
    mul_nonneg hB.le hlq,mul_nonneg hB.le hlt,mul_nonneg hD.le hlq]

end AnalyticNumberTheory.DirichletLFunctions
