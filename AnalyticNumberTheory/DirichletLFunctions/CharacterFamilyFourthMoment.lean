import AnalyticNumberTheory.DirichletLFunctions.PrimitiveFamilyCriticalFourth
import AnalyticNumberTheory.DirichletLFunctions.ConductorFourthMomentTransfer
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovBilinear

/-!
# Fourth moments of complete character families

The complete family contains both the original functions and the primitive
functions inducing them. Both sums satisfy a fourth-logarithm bound on a
symmetric height interval. Summing primitive families up to Q costs Q squared.
-/
noncomputable section
open Real Complex Set Finset MeasureTheory
open scoped Classical Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A common fourth-moment bound for the two complete families attached to
a fixed modulus. The second integral uses the original Euler factors. -/
theorem full_character_critical_fourth_moments :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T : ℝ},1≤T →
      (∑χ : DirichletCharacter ℂ q,∫t in (-T)..T,‖inducingLFunction χ ((1/2:ℂ)+t*I)‖^4)≤
        C*q*T*(1+Real.log (q*T))^4 ∧
      (∑χ : DirichletCharacter ℂ q,∫t in (-T)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤
        C*q*T*(1+Real.log (q*T))^4 := by
  obtain ⟨D,hD,H⟩ := primitive_family_critical_fourth_moment
  obtain ⟨E,hE,K⟩ := family_fourth_of_primitive_bounds
  refine ⟨D*(1+E),by positivity,?_⟩;intro q _ T hT
  let L := (1+Real.log ((q:ℝ)*T))^4
  let B := D*T*L
  have hL : 0≤L := by dsimp [L];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have Hdiv (d : q.divisors) : letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
      (∑ψ : DirichletCharacter ℂ d.val with ψ.IsPrimitive,∫t in (-T)..T,‖ψ.LFunction (((1/2:ℝ):ℂ)+t*I)‖^4)≤d.val.totient*B := by
    letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
    simp only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one]
    apply (H (q:=d.val) hT).trans
    have hd : (1:ℝ)≤d.val := by exact_mod_cast Nat.pos_of_mem_divisors d.property
    have hdq : (d.val:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors d.property)
    have h₁ := one_le_mul_of_one_le_of_one_le hd hT
    have hl := Real.log_le_log (by linarith : 0<(d.val:ℝ)*T) (mul_le_mul_of_nonneg_right hdq (by linarith : 0≤T))
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg h₁]) (add_le_add_right hl 1) 4) (by positivity : 0≤D*(d.val.totient:ℝ)*T)).trans_eq
    dsimp only [B,L];ring
  have hk := K (q:=q) (σ:=1/2) (by norm_num) (by norm_num) (by linarith : -T≤T) hB Hdiv
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] at hk
  have hX : 0≤(q:ℝ)*B := by positivity
  constructor
  · apply hk.1.trans;change _≤D*(1+E)*q*T*L
    dsimp only [B] at *;nlinarith only [mul_nonneg hE.le hX]
  · apply hk.2.trans;change _≤D*(1+E)*q*T*L
    dsimp only [B] at *;nlinarith only [hX]

/-- Evaluation on the dependent pair used for finite families of primitive
characters. Every pair occurring in such a family has positive level. -/
def familyLFunction (p : (q : ℕ) × DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if h : p.1=0 then 0 else
    haveI : NeZero p.1 := ⟨h⟩
    p.2.LFunction s

/-- Fourth moment on the critical line, summed over primitive characters
of every modulus up to Q. -/
theorem primitive_conductors_critical_fourth_moment :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ} {T : ℝ},1≤Q → 1≤T →
      (∑p∈PrimeDistribution.primitiveCharacterFamily Q,∫t in (-T)..T,‖familyLFunction p ((1/2:ℂ)+t*I)‖^4)≤
        C*(Q:ℝ)^2*T*(1+Real.log (Q*T))^4 := by
  obtain ⟨C,hC,H⟩ := primitive_family_critical_fourth_moment
  refine ⟨C,hC,?_⟩;intro Q T hQ hT
  simp only [PrimeDistribution.primitiveCharacterFamily,sum_sigma]
  let B := C*(Q:ℝ)*T*(1+Real.log (Q*T))^4
  apply (sum_le_sum (g:=fun _ : ℕ=>B) (fun q hq=>?_)).trans_eq
  · simp [B,Nat.card_Icc];ring
  · have hpos := (Finset.mem_Icc.mp hq).1
    have hqn : q≠0 := by omega
    letI : NeZero q := ⟨hqn⟩
    simp only [familyLFunction,dif_neg hqn]
    apply (H (q:=q) hT).trans
    have hp : 1≤(q:ℝ)*T := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hpos) hT
    have hle : (q:ℝ)≤Q := by exact_mod_cast (Finset.mem_Icc.mp hq).2
    have hl := Real.log_le_log (by linarith : 0<(q:ℝ)*T) (mul_le_mul_of_nonneg_right hle (by linarith : 0≤T))
    have hφ : (q.totient:ℝ)≤Q := (by exact_mod_cast Nat.totient_le q : (q.totient:ℝ)≤q).trans hle
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ hC.le) (by linarith))
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hp]) (add_le_add_right hl 1) 4) (by positivity) (by positivity)

end AnalyticNumberTheory.DirichletLFunctions
