import AnalyticNumberTheory.PrimeDistribution.SignedCharacterCutoff
import AnalyticNumberTheory.PrimeDistribution.CharacterTruncatedExplicitFormula

/-! # A signed explicit formula for every nonprincipal Dirichlet character -/
noncomputable section
open Complex Finset
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Induction preserves the complex regularized zero sum, with its multiplicities. -/
theorem characterPerronZeroSum_changeLevel {d q : ℕ} [NeZero d] [NeZero q] (hdq : d∣q)
    (χ : DirichletCharacter ℂ d) (x T : ℝ) :
    characterPerronZeroSum (χ.changeLevel hdq) x T = characterPerronZeroSum χ x T := by
  simp only [characterPerronZeroSum,characterStripZeros,characterZeroMultiplicity,
    dite_eq_left (NeZero.ne q),dite_eq_left (NeZero.ne d),criticalStripZeroFinset_changeLevel]
  apply sum_congr rfl
  intro z hz
  obtain ⟨hl,hu,_,_,_⟩ := (mem_criticalStripZeroFinset χ).mp hz
  rw [(LFunction_changeLevel_strip_zero_order hdq χ hl hu).2]

/-- The complex sum of (y^ρ−1)/ρ at height √x approximates the negative of
ψ(y,χ). The absolute remainder bound is uniform in q and in 1 ≤ y ≤ x. -/
theorem nonprincipal_psi_signed_explicit_formula :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ≠1 →
      ∀ {x y : ℝ}, 4≤x → 1≤y → y≤x →
        ‖psiChar y χ + characterPerronZeroSum χ y (Real.sqrt x)‖ ≤
          C*Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2 := by
  obtain ⟨B,hB,H⟩ := primitive_signed_explicit_of_perron primitiveSignedPerronContourBound
  have hl₂ : 0<Real.log 2 := Real.log_pos one_lt_two
  refine ⟨B+1/Real.log 2,by positivity,fun {q} _ {χ} hn {x y} hx hy hyx => ?_⟩
  have hd := three_le_conductor_of_ne_one hn
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := H hx hy hyx (show 2≤χ.conductor by omega) χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hid := characterPerronZeroSum_changeLevel χ.conductor_dvd_level χ.primitiveCharacter y (Real.sqrt x)
  rw [χ.changeLevel_primitiveCharacter] at hid
  let L := 1+Real.log ((q:ℝ)*x)
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hx₁ : 1≤x := by linarith
  have hl : 1≤L := le_add_of_nonneg_right (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hx₁))
  have hd₁ : (1:ℝ)≤χ.conductor := by exact_mod_cast (show 1≤χ.conductor by omega)
  have hdq : (χ.conductor:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hl' : 1+Real.log ((χ.conductor:ℝ)*x)≤L := by
    dsimp only [L];gcongr
  have hp' : ‖psiChar y χ.primitiveCharacter + characterPerronZeroSum χ y (Real.sqrt x)‖ ≤ B*Real.sqrt x*L^2 := by
    rw [hid];apply hp.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one
      (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd₁ hx₁))) hl' _) (by positivity)
  have hlog : L=1+Real.log q+Real.log x := by
    dsimp only [L];rw [Real.log_mul (by linarith) (by linarith)];ring
  have hprod : Real.log q*Real.log y ≤ L^2 := by
    rw [sq];apply mul_le_mul _ _ (Real.log_nonneg hy) (by linarith)
    · linarith only [hlog,Real.log_nonneg hx₁]
    · linarith only [hlog,Real.log_nonneg hq,Real.log_le_log (by linarith : 0<y) hyx]
  have he : ‖psiChar y χ-psiChar y χ.primitiveCharacter‖ ≤ (1/Real.log 2)*Real.sqrt x*L^2 := by
    apply (norm_psiChar_sub_primitive_le hy (NeZero.pos q) χ).trans
    have HH := mul_le_mul_of_nonneg_left (hprod.trans
      (le_mul_of_one_le_left (sq_nonneg L) (Real.one_le_sqrt.mpr hx₁))) (by positivity : 0≤1/Real.log 2)
    convert HH using 1 <;> ring
  have hu := norm_add_le (psiChar y χ-psiChar y χ.primitiveCharacter)
    (psiChar y χ.primitiveCharacter+characterPerronZeroSum χ y (Real.sqrt x))
  rw [show (psiChar y χ-psiChar y χ.primitiveCharacter)+(psiChar y χ.primitiveCharacter+characterPerronZeroSum χ y (Real.sqrt x)) = psiChar y χ+characterPerronZeroSum χ y (Real.sqrt x) by abel] at hu
  change _≤(B+1/Real.log 2)*Real.sqrt x*L^2
  linarith only [hu,he,hp']

end AnalyticNumberTheory.PrimeDistribution