import AnalyticNumberTheory.PrimeDistribution.ProgressionVariance
import AnalyticNumberTheory.PrimeDistribution.PrimitivePsiEnergy
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveConductorSums

/-! # Reducing the variance of arithmetic progressions to primitive characters -/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

theorem nonprincipal_inducer_energy {q : ℕ} [NeZero q] (x : ℝ) :
    (∑ χ : DirichletCharacter ℂ q,if χ=1 then 0 else ‖psiChar x χ.primitiveCharacter‖^2) =
      ∑ d∈q.divisors with 2≤d,primitivePsiEnergy x d := by
  rw [sum_by_primitive_conductor,sum_filter,←sum_attach q.divisors]
  apply sum_congr rfl;intro d _
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  let hd := Nat.dvd_of_mem_divisors d.property
  have ht (χ : DirichletCharacter ℂ d.val) (hp : χ.IsPrimitive) :
      χ.changeLevel hd=1 ↔ d.val=1 := by
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one,conductor_changeLevel_of_isPrimitive hd hp]
  by_cases he : 2≤d.val
  · rw [if_pos he];apply sum_congr rfl;intro χ hχ
    have hp := (mem_filter.mp hχ).2
    rw [if_neg (fun h => (by omega : d.val≠1) ((ht χ hp).mp h)),psiChar_primitiveCharacter_changeLevel hd hp]
  · rw [if_neg he];apply sum_eq_zero;intro χ hχ
    have hpos := Nat.pos_of_mem_divisors d.property
    rw [if_pos ((ht χ (mem_filter.mp hχ).2).mpr (by omega))]

/-- Parseval, induction to the conductor, and the missing Euler factors
separate the variance into a primitive mean, a PNT error and a local error. -/
theorem progressionVariance_le_conductor_energy {q : ℕ} [NeZero q] {x : ℝ} (hx : 1≤x) :
    progressionVariance x x q≤
      2*(q.totient:ℝ)⁻¹*(∑ d∈q.divisors with 2≤d,primitivePsiEnergy x d)+
      2*(q.totient:ℝ)⁻¹*|Chebyshev.psi x-x|^2+2*(Real.log q/Real.log 2*Real.log x)^2 := by
  let E := Real.log q/Real.log 2*Real.log x
  let P := |Chebyshev.psi x-x|
  let F (χ : DirichletCharacter ℂ q) := if χ=1 then P else ‖psiChar x χ.primitiveCharacter‖
  have hE : 0≤E := by dsimp [E];positivity [Real.log_nonneg (by exact_mod_cast NeZero.pos q : 1≤(q:ℝ)),Real.log_nonneg hx]
  have hF (χ) : 0≤F χ := by dsimp [F,P];split_ifs <;> positivity
  have hb (χ : DirichletCharacter ℂ q) : ‖psiChar x χ-(if χ=1 then (x:ℂ) else 0)‖≤F χ+E := by
    by_cases he : χ=1
    · subst χ;simp only [F,ite_true]
      have h := dist_triangle (psiChar x (1:DirichletCharacter ℂ q)) (Chebyshev.psi x:ℂ) (x:ℂ)
      simp only [dist_eq_norm] at h
      rw [norm_sub_rev (psiChar x _) (Chebyshev.psi x:ℂ),←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
      exact h.trans (by linarith only [norm_psi_sub_psiChar_one_le hx (NeZero.pos q)])
    · simp only [F,if_neg he,sub_zero]
      have h := norm_le_insert' (psiChar x χ) (psiChar x χ.primitiveCharacter)
      linarith only [h,norm_psiChar_sub_primitive_le hx (NeZero.pos q) χ]
  have h2 (χ : DirichletCharacter ℂ q) : ‖psiChar x χ-(if χ=1 then (x:ℂ) else 0)‖^2≤2*(F χ)^2+2*E^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (hb χ) 2).trans (by nlinarith only [sq_nonneg (F χ-E)])
  have hg : (∑ χ : DirichletCharacter ℂ q,(F χ)^2)=P^2+∑ d∈q.divisors with 2≤d,primitivePsiEnergy x d := by
    rw [←nonprincipal_inducer_energy]
    calc _ = ∑ χ : DirichletCharacter ℂ q, ((if χ=1 then P^2 else 0)+(if χ=1 then 0 else ‖psiChar x χ.primitiveCharacter‖^2)) := by
               apply sum_congr rfl;intro χ _;by_cases h : χ=1 <;> simp [F,h]
         _ = _ := by rw [sum_add_distrib];simp
  have hs := sum_le_sum (s:=(univ : Finset (DirichletCharacter ℂ q))) (fun χ _ => h2 χ)
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,card_univ,card_dirichletCharacter_eq_totient,hg] at hs
  rw [progressionVariance_eq_character_mean]
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq (by
    dsimp only [P,E];field_simp [show (q.totient:ℝ)≠0 by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'];ring)

end AnalyticNumberTheory.PrimeDistribution
