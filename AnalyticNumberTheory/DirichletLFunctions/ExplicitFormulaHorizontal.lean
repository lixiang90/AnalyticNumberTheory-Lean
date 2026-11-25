import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaHeights
import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaGamma

/-!
# Good horizontal sides for the completed character L-function

The right-hand segment is controlled by the local partial fractions and the
left-hand segment by the primitive functional equation.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace AnalyticNumberTheory.DirichletLFunctions

/-- Both sides at heights `±T` of the full rectangle have logarithmic derivative
of order at most the square of the logarithm of the analytic conductor. -/
theorem exists_completed_horizontal_logDeriv_bound :
    ∃ E : ℝ, 0<E ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
    χ.IsPrimitive → 2≤q → ∀ {A : ℝ}, 4≤A →
    ∃ T ∈ Set.Icc (A+1/4) (A+3/4), ∀ s : ℂ, -(1/2:ℝ)≤s.re → s.re≤3/2 → |s.im|=T →
      DirichletCharacter.completedLFunction χ s ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
        E*(1+Real.log ((q:ℝ)*(A+3)))^2 := by
  obtain ⟨G,hG,HG⟩ := norm_characterGammaLogCorrection_le
  let D := 4*(2*jensenUnitZeroDensityConst+1)
  have hD : 0<D := by dsimp [D]; positivity [jensenUnitZeroDensityConst_pos]
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K := 10304+14/Real.log 2*D+G
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K+1,by positivity,fun {q} _ {χ} hχ hq {A} hA => ?_⟩
  have hχn := isPrimitive_ne_one hχ hq
  obtain ⟨T,hT,H⟩ := exists_LFunction_good_height hχn (by linarith : 0≤A)
  let L := 1+Real.log ((q:ℝ)*(A+3))
  let δ := 1/(D*L)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hq0 : (0:ℝ)<q := by linarith
  have hL : 1≤L := by
    dsimp [L]
    exact le_add_of_nonneg_right (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 (by linarith)))
  have hLp : 0<L := by linarith
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hlogT : 1+Real.log (T+2)≤L := by
    dsimp [L]
    apply add_le_add_right
    exact Real.log_le_log (by linarith [hT.1]) ((show T+2≤A+3 by linarith [hT.2]).trans
      (le_mul_of_one_le_left (by linarith) hq1))
  have hlogQ : Real.log ((q:ℝ)*(T+2))≤L := by
    have h := Real.log_le_log (show 0<(q:ℝ)*(T+2) from mul_pos hq0 (by linarith [hT.1]))
      (mul_le_mul_of_nonneg_left (by linarith [hT.2] : T+2≤A+3) hq0.le)
    dsimp [L]; linarith
  have hright {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive)
      (Hψ : ∀ z : ℂ, 0<z.re → z.re<1 → ψ.LFunction z=0 → δ≤abs (T-|z.im|))
      {s : ℂ} (hlo : 1/2≤s.re) (hhi : s.re≤3/2) (ht : |s.im|=T) :
      DirichletCharacter.completedLFunction ψ s≠0 ∧
        ‖logDeriv (DirichletCharacter.completedLFunction ψ) s‖≤K*L^2 := by
    have hψn := isPrimitive_ne_one hψ hq
    obtain ⟨hn,hb⟩ := norm_logDeriv_on_separated_horizontal hψn (δ:=δ) (σ:=s.re) (t:=s.im)
      hδ (by linarith) hhi (fun z hl hu hz => (Hψ z hl hu hz).trans (by
        rw [←ht]
        exact abs_abs_sub_abs_le_abs_sub ..))
    rw [Complex.re_add_im] at hn hb
    rw [ht] at hb
    have Hs := logDeriv_completedLFunction_eq_add_gammaFactor_eq ψ hq (.inl hψn) hn
      (gammaFactor_ne_zero_of_re_pos ψ (by linarith))
    change _ = logDeriv ψ.LFunction s+characterGammaLogCorrection ψ s at Hs
    have hγ := HG ψ hlo hhi
    rw [ht] at hγ
    have hc : 14/(Real.log 2*δ)=14/Real.log 2*D*L := by dsimp [δ]; field_simp
    rw [hc] at hb
    refine ⟨fun h => hn ((completedLFunction_eq_zero_iff_criticalStrip hψ hq s).mp h).2.2,?_⟩
    rw [Hs]
    apply (norm_add_le _ _).trans
    have hA₁ := mul_le_mul_of_nonneg_left hlogQ (show 0≤10304+14/Real.log 2*D*L by positivity)
    have hA₂ := mul_le_mul_of_nonneg_left hlogT hG.le
    have hpow : L≤L^2 := by nlinarith [mul_nonneg hLp.le (sub_nonneg.mpr hL)]
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hpow hG.le]
  have Hstar : ∀ z : ℂ, 0<z.re → z.re<1 → (star χ).LFunction z=0 → δ≤abs (T-|z.im|) := by
    intro z hl hu hz
    have he := LFunction_star_conj hχn (conj z)
    rw [Complex.conj_conj,hz] at he
    have hz' := (map_eq_zero (starRingEnd ℂ)).mp he.symm
    simpa [δ,D,L] using H (conj z) (by simpa using hl) (by simpa using hu) hz'
  refine ⟨T,hT,fun s hlo hhi ht => ?_⟩
  change _ ∧ _≤(K+1)*L^2
  by_cases hr : 1/2≤s.re
  · obtain ⟨hn,hs⟩ := hright hχ H hr hhi ht
    exact ⟨hn,hs.trans (by nlinarith [sq_nonneg L])⟩
  · have hsr : (1-s).re=1-s.re := by simp
    have hsi : |(1-s).im|=T := by simpa using ht
    obtain ⟨hn,hs⟩ := hright (isPrimitive_star hχ) Hstar (s:=1-s)
      (by rw [hsr]; linarith) (by rw [hsr]; linarith) hsi
    have he := logDeriv_completedLFunction_reflect hχ hq hn
    rw [sub_sub_cancel] at he
    have hnc : DirichletCharacter.completedLFunction χ s≠0 := by
      rw [←sub_sub_cancel (1:ℂ) s,completedLFunction_one_sub_primitive hχ (1-s)]
      exact mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
        (DirichletCharacter.rootNumber_ne_zero hχ)) hn
    have hlq := Real.log_nonneg hq1
    have hqL : Real.log (q:ℝ)≤L := by
      dsimp [L]; rw [Real.log_mul hq0.ne' (by linarith)]
      linarith [Real.log_nonneg (by linarith : 1≤A+3)]
    have hh := norm_sub_le (-(Real.log (q:ℝ):ℂ)) (logDeriv (DirichletCharacter.completedLFunction (star χ)) (1-s))
    rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlq] at hh
    refine ⟨hnc,?_⟩
    rw [he]
    nlinarith [mul_nonneg hLp.le (sub_nonneg.mpr hL)]

end AnalyticNumberTheory.DirichletLFunctions
