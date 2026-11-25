import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronExplicit
import AnalyticNumberTheory.PrimeDistribution.PrimitivePsiExplicitReduction
import AnalyticNumberTheory.DirichletLFunctions.ConductorZeros
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik

/-!
# The truncated explicit inequality for character sums

For every nonprincipal character the zero sum is cut at height `√x`; the
same error term controls all real endpoints from zero to `x`. Both the
height and the implied constant are uniform in the modulus.
-/

noncomputable section

open Complex Finset
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- The primitive explicit inequality used in conductor averages. -/
theorem primitivePsiExplicitBound : PrimitivePsiExplicitBound :=
  primitivePsiExplicitBound_of_perron primitivePerronContourBound

/-- The primitive inequality with no upper restriction on the modulus. -/
theorem primitive_psi_explicit_all_moduli :
    ∃ C : ℝ, 0<C ∧ ∀ {x y : ℝ} {q : ℕ}, 4≤x → 0≤y → y≤x → 2≤q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ‖psiChar y χ‖≤C*(Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2+
          characterZeroWeight χ (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))) :=
  primitive_psi_explicit_all_moduli_of_perron primitivePerronContourBound

/-- Induction of a character preserves all weighted critical-strip sums. -/
theorem characterZeroWeight_changeLevel {q d : ℕ} [NeZero q] [NeZero d] (hdq : d∣q)
    (χ : DirichletCharacter ℂ d) (T : ℝ) (w : ℂ→ℝ) :
    characterZeroWeight (χ.changeLevel hdq) T w=characterZeroWeight χ T w := by
  simp only [characterZeroWeight,characterStripZeros,characterZeroMultiplicity,
    dite_eq_left (NeZero.ne q),dite_eq_left (NeZero.ne d),criticalStripZeroFinset_changeLevel]
  apply sum_congr rfl
  intro z hz
  obtain ⟨hl,hu,_,_,_⟩ := (mem_criticalStripZeroFinset χ).mp hz
  rw [(LFunction_changeLevel_strip_zero_order hdq χ hl hu).2]

/-- Uniform truncated explicit inequality for all nonprincipal characters.
The zero ordinates run through both signs and are counted with analytic
multiplicity. The common endpoint `x` may exceed the summation limit `y`. -/
theorem nonprincipal_psi_truncated_explicit_bound :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ≠1 →
      ∀ {x y : ℝ}, 4≤x → 0≤y → y≤x →
        ‖psiChar y χ‖≤C*(Real.sqrt x*(1+Real.log ((q:ℝ)*x))^2+
          characterZeroWeight χ (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))) := by
  obtain ⟨B,hB,H⟩ := primitive_psi_explicit_all_moduli
  have hl₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B+1/Real.log 2,by positivity,fun {q} _ {χ} hn {x y} hx hy hyx => ?_⟩
  let L := 1+Real.log ((q:ℝ)*x)
  let Z := characterZeroWeight χ (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))
  have hZ : 0≤Z := by
    dsimp [Z,characterZeroWeight]
    exact sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hqr : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hq₀ : (0:ℝ)<q := by linarith
  have hx₁ : 1≤x := by linarith
  have hx₀ : 0<x := by linarith
  have hlq := Real.log_nonneg hqr
  have hlx := Real.log_nonneg hx₁
  have hL : L=1+Real.log (q:ℝ)+Real.log x := by dsimp [L]; rw [Real.log_mul hq₀.ne' hx₀.ne']; ring
  have hL₁ : 1≤L := by linarith
  change ‖psiChar y χ‖≤(B+1/Real.log 2)*(Real.sqrt x*L^2+Z)
  by_cases hy₁ : 1≤y
  swap
  · have hfloor : ⌊y⌋₊=0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hy₁)
    simp only [psiChar,hfloor,Finset.Icc_eq_empty_of_lt (by decide : 0<1),sum_empty,norm_zero]
    positivity
  have hd := three_le_conductor_of_ne_one hn
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := H hx hy hyx (show 2≤χ.conductor by omega) χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hzc := characterZeroWeight_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))
  rw [χ.changeLevel_primitiveCharacter] at hzc
  rw [←hzc] at hp
  have hd₁ : (1:ℝ)≤χ.conductor := by exact_mod_cast (show 1≤χ.conductor by omega)
  have hdq : (χ.conductor:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hpow : (1+Real.log ((χ.conductor:ℝ)*x))^2≤L^2 := by
    apply pow_le_pow_left₀
    · exact add_nonneg zero_le_one (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hd₁ hx₁))
    · dsimp [L]; gcongr
  have hp' : ‖psiChar y χ.primitiveCharacter‖≤B*(Real.sqrt x*L^2+Z) := by
    apply hp.trans
    dsimp [Z]; gcongr
  have hdiff := norm_psiChar_sub_primitive_le hy₁ (NeZero.pos q) χ
  have hylog := Real.log_le_log (by linarith : 0<y) hyx
  have he : Real.log q*Real.log y≤L^2 := by
    have h₁ : Real.log q≤L := by linarith
    have h₂ : Real.log y≤L := by linarith
    simpa [sq] using mul_le_mul h₁ h₂ (Real.log_nonneg hy₁) (by linarith : 0≤L)
  have hD : (Real.log q/Real.log 2)*Real.log y≤(1/Real.log 2)*(Real.sqrt x*L^2+Z) := by
    have hs := le_mul_of_one_le_left (sq_nonneg L) (Real.one_le_sqrt.mpr hx₁)
    calc
      _ = (1/Real.log 2)*(Real.log q*Real.log y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ ≤ ‖psiChar y χ-psiChar y χ.primitiveCharacter‖+‖psiChar y χ.primitiveCharacter‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith [hdiff.trans hD]

end AnalyticNumberTheory.PrimeDistribution
