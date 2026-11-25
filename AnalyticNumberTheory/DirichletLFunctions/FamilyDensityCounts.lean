import AnalyticNumberTheory.DirichletLFunctions.PrimitiveConductorSums
import AnalyticNumberTheory.DirichletLFunctions.ZeroCounting

/-! # Critical-strip density counts for a fixed modulus and for primitive characters

All zeros are counted with analytic multiplicity, at both signs of height. The
principal character is included. Induction from a proper conductor leaves the count
unchanged because the omitted Euler factors have no zeros of positive real part.
-/
noncomputable section
open Finset Complex Real
open scoped Classical
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Number of critical-strip zeros of a character with real part at least σ
and absolute ordinate at most T. -/
def characterDensityCount {q : ℕ} (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ :=
  if h : q≠0 then
    letI : NeZero q := ⟨h⟩
    ∑ z ∈ (criticalStripZeroFinset χ (-T) T).filter (fun z => σ≤z.re),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) z
  else 0

/-- Sum of critical-strip density counts over every character of a fixed modulus. -/
def modulusDensityCount (q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ χ : DirichletCharacter ℂ q, characterDensityCount χ σ T

/-- Sum over only the primitive characters of a fixed modulus. -/
def primitiveModulusDensityCount (q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive), characterDensityCount χ σ T

theorem characterDensityCount_changeLevel {d q : ℕ} [NeZero d] [NeZero q] (hdq : d∣q)
    (χ : DirichletCharacter ℂ d) (σ T : ℝ) :
    characterDensityCount (χ.changeLevel hdq) σ T = characterDensityCount χ σ T := by
  simp only [characterDensityCount,dite_eq_left (NeZero.ne q),dite_eq_left (NeZero.ne d),
    criticalStripZeroFinset_changeLevel]
  apply sum_congr rfl
  intro z hz
  obtain ⟨h₀,h₁,_⟩ := (mem_criticalStripZeroFinset χ).mp (mem_filter.mp hz).1
  exact (LFunction_changeLevel_strip_zero_order hdq χ h₀ h₁).2

theorem characterDensityCount_eq_primitiveCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    characterDensityCount χ σ T = characterDensityCount χ.primitiveCharacter σ T := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [χ.changeLevel_primitiveCharacter] using
    characterDensityCount_changeLevel χ.conductor_dvd_level χ.primitiveCharacter σ T

/-- The full zero count is the sum of the primitive counts over all conductors dividing q. -/
theorem modulusDensityCount_eq_sum_primitive {q : ℕ} [NeZero q] (σ T : ℝ) :
    modulusDensityCount q σ T = ∑ d∈q.divisors,primitiveModulusDensityCount d σ T := by
  rw [modulusDensityCount,sum_by_primitive_conductor,←sum_attach q.divisors (fun d => primitiveModulusDensityCount d σ T)]
  refine sum_congr rfl fun d _ => ?_
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  exact sum_congr rfl (fun χ _ => characterDensityCount_changeLevel _ χ σ T)

theorem characterDensityCount_le_zeroCountL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    characterDensityCount χ σ T ≤ zeroCountL χ T := by
  simp only [characterDensityCount,dite_eq_left (NeZero.ne q),zeroCountL]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros;omega)

/-- The elementary zero-density bound for every fixed modulus, uniform also
close to the critical line. -/
theorem modulusDensityCount_trivial :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {T : ℝ}, 2≤T → ∀ σ : ℝ,
      (modulusDensityCount q σ T:ℝ) ≤ C*q.totient*T*Real.log ((q:ℝ)*T) := by
  obtain ⟨B,hB,HB⟩ := zeroCountL_riemannVonMangoldt_uniform
  refine ⟨B+1,by linarith,?_⟩
  intro q _ T hT σ
  have hT₀ : 0<T := by linarith
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : 0 ≤ Real.log ((q:ℝ)*T) := Real.log_nonneg
    ((by linarith : 1≤T).trans (le_mul_of_one_le_left hT₀.le hq₁))
  have hc (χ : DirichletCharacter ℂ q) : (characterDensityCount χ σ T:ℝ) ≤
      (B+1)*T*Real.log ((q:ℝ)*T) := by
    have hd : (0:ℝ)<χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hdq : (χ.conductor:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    let Y := (χ.conductor:ℝ)*T
    let Q := (q:ℝ)*T
    have hY : 0<Y := mul_pos hd hT₀
    have hYQ : Y≤Q := mul_le_mul_of_nonneg_right hdq hT₀.le
    have hL := Real.log_le_log hY hYQ
    have hp : 1≤2*Real.pi*Real.exp 1 := by nlinarith [Real.pi_gt_three,Real.add_one_le_exp (1:ℝ)]
    have hL' := Real.log_le_log (div_pos hY (by positivity : 0<2*Real.pi*Real.exp 1))
      ((div_le_self hY.le hp).trans hYQ)
    have hpi : T/Real.pi≤T := div_le_self hT₀.le (by linarith [Real.pi_gt_three])
    have hm := (mul_le_mul_of_nonneg_left hL' (div_nonneg hT₀.le Real.pi_pos.le)).trans
      (mul_le_mul_of_nonneg_right hpi hlog)
    have he := (abs_le.mp (HB χ T hT)).2
    have hn : (characterDensityCount χ σ T:ℝ) ≤ (zeroCountL χ T:ℝ) := by exact_mod_cast characterDensityCount_le_zeroCountL χ σ T
    have hbl := mul_le_mul_of_nonneg_left hL hB
    have hpad := mul_le_mul_of_nonneg_right (by linarith : 1≤T) (mul_nonneg hB hlog)
    dsimp only [Y,Q] at hm hbl
    linarith only [hn,he,hm,hbl,hpad]
  simp only [modulusDensityCount,Nat.cast_sum]
  apply (sum_le_sum (fun χ _ => hc χ)).trans
  simp only [sum_const,card_univ,card_dirichletCharacter_eq_totient,nsmul_eq_mul]
  ring_nf
  exact le_rfl

end AnalyticNumberTheory.DirichletLFunctions
