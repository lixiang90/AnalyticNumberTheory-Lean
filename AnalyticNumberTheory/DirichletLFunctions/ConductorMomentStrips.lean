import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment

/-!
# Logarithmic strips and changes of conductor

A single strip determined by the largest modulus lies in every smaller
conductor strip. Both choices of Euler factors therefore inherit a
uniform fourth-moment bound from the primitive family.
-/
noncomputable section
open Real Complex Set Finset MeasureTheory
open scoped Classical Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The family estimate persists on the entire strip after summing all
primitive lifts or retaining the actual Euler factors of each character. -/
theorem full_character_fourth_narrow_of_primitive {D l : ℝ} (hD : 0<D) (hl : 0≤l)
    (H : ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in (-(l*T))..(l*T),‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤D*q.totient*T*(Real.log (q*T))^4) :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      ((∑χ : DirichletCharacter ℂ q,∫t in (-(l*T))..(l*T),‖inducingLFunction χ ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) ∧
      ((∑χ : DirichletCharacter ℂ q,∫t in (-(l*T))..(l*T),‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q*T*(Real.log (q*T))^4) := by
  obtain ⟨E,hE,K⟩ := family_fourth_of_primitive_bounds
  refine ⟨D*(1+E),by positivity,?_⟩
  intro q _ σ T hT hσ
  let L := (Real.log ((q:ℝ)*T))^4
  let B := D*T*L
  have hT₀ : 0<T := by linarith
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hlog {m : ℕ} (hm : 1≤m) : 1/2≤Real.log ((m:ℝ)*T) := by
    have h₁ : 2≤(m:ℝ)*T := hT.trans (le_mul_of_one_le_left hT₀.le (by exact_mod_cast hm))
    exact (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) h₁)
  have hlogq := hlog (NeZero.pos q)
  have hl' : 0<200*Real.log ((q:ℝ)*T) := by linarith
  have hwidth : 1/(200*Real.log ((q:ℝ)*T))≤1/4 := (div_le_iff₀ hl').mpr (by linarith)
  have habs := abs_le.mp (hσ.trans hwidth)
  have hL : 0≤L := by dsimp [L];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have Hdiv (d : q.divisors) : letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
      (∑ψ : DirichletCharacter ℂ d.val with ψ.IsPrimitive,∫t in (-(l*T))..(l*T),‖ψ.LFunction ((σ:ℂ)+t*I)‖^4)≤d.val.totient*B := by
    letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
    have hdq : (d.val:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors d.property)
    have hld := hlog (Nat.pos_of_mem_divisors d.property)
    have hdT : 0<(d.val:ℝ)*T := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_mem_divisors d.property)) hT₀
    have hmono := Real.log_le_log hdT (mul_le_mul_of_nonneg_right hdq hT₀.le)
    have hsd := hσ.trans (one_div_le_one_div_of_le (by linarith : 0<200*Real.log ((d.val:ℝ)*T)) (by linarith only [hmono]))
    apply (H (q:=d.val) hT hsd).trans
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0≤Real.log ((d.val:ℝ)*T)) hmono 4)
      (by positivity : 0≤D*(d.val.totient:ℝ)*T)).trans_eq
    dsimp [B,L];ring
  have hk := K (q:=q) (σ:=σ) (by linarith [habs.1]) (by linarith [habs.2]) (neg_le_self (mul_nonneg hl hT₀.le)) hB Hdiv
  have hX : 0≤(q:ℝ)*B := by positivity
  constructor
  · apply hk.1.trans;change _≤D*(1+E)*q*T*L
    dsimp only [B] at *;nlinarith only [mul_nonneg hE.le hX]
  · apply hk.2.trans;change _≤D*(1+E)*q*T*L
    dsimp only [B] at *;nlinarith only [hX]

/-- Up to a cutoff Q, a common strip defined by Q admits the sum of the
primitive-family estimates at every smaller modulus. -/
theorem primitive_conductors_fourth_narrow_of_fixed {D : ℝ} (hD : 0<D)
    (H : ∀{q : ℕ} [NeZero q] {σ T : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in (-T)..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤D*q.totient*T*(Real.log (q*T))^4)
    {Q : ℕ} {σ T : ℝ} (hQ : 1≤Q) (hT : 2≤T) (hσ : |σ-1/2|≤1/(200*Real.log (Q*T))) :
    (∑p∈PrimeDistribution.primitiveCharacterFamily Q,∫t in (-T)..T,‖familyLFunction p ((σ:ℂ)+t*I)‖^4)≤
        D*(Q:ℝ)^2*T*(Real.log (Q*T))^4 := by
  simp only [PrimeDistribution.primitiveCharacterFamily,sum_sigma]
  let B := D*(Q:ℝ)*T*(Real.log (Q*T))^4
  apply (sum_le_sum (g:=fun _ : ℕ=>B) (fun q hq=>?_)).trans_eq
  · simp [B,Nat.card_Icc];ring
  · have hp := (Finset.mem_Icc.mp hq).1
    have hqn : q≠0 := by omega
    letI : NeZero q := ⟨hqn⟩
    simp only [familyLFunction,dif_neg hqn]
    have hle : (q:ℝ)≤Q := by exact_mod_cast (Finset.mem_Icc.mp hq).2
    have hqt : 2≤(q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) (by exact_mod_cast hp))
    have hpos : 0<Real.log ((q:ℝ)*T) := Real.log_pos (by linarith)
    have hl := Real.log_le_log (by linarith : 0<(q:ℝ)*T) (mul_le_mul_of_nonneg_right hle (by linarith : 0≤T))
    have hsq := hσ.trans (one_div_le_one_div_of_le (by positivity : 0<200*Real.log ((q:ℝ)*T)) (by linarith only [hl]))
    apply (H (q:=q) hT hsq).trans
    have hφ : (q.totient:ℝ)≤Q := (by exact_mod_cast Nat.totient_le q : (q.totient:ℝ)≤q).trans hle
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ hD.le) (by linarith)) (pow_le_pow_left₀ hpos.le hl 4) (by positivity) (by positivity)

end AnalyticNumberTheory.DirichletLFunctions
