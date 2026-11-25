import AnalyticNumberTheory.DirichletLFunctions.PrimitiveCriticalSecondMoment
import AnalyticNumberTheory.AnalyticTools.ReducedResidueHarmonics

/-!
# Prime-factor formulas for the linear character-moment coefficients

The reduced digamma sum has an elementary expression involving the
distinct prime divisors of the modulus. In a primitive individual
moment the prime correction occurs twice. In the full family average
it occurs once.
-/
noncomputable section
open Real Complex Finset Set Filter MeasureTheory Asymptotics
open scoped Topology Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Evaluation of the digamma sum over a reduced residue system. -/
theorem reducedHarmonicConstant_eq_prime_sum (q : ℕ) [NeZero q] :
    reducedHarmonicConstant q=(q.totient/q:ℝ)*(Real.eulerMascheroniConstant+Real.log q+primeDivisorLogSum q) := by
  let k := (q.totient/q:ℝ)
  let R := reducedHarmonicConstant q
  let S := k*(Real.eulerMascheroniConstant+Real.log q+primeDivisorLogSum q)
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hk : 0≤k := by dsimp [k];positivity
  have err (x : ℝ) (hx : 2≤x) : |R-S|≤(4*k+1)/x := by
    have hx' : 0<x := by linarith
    let H := reducedReciprocalSum q (q*x)
    have h (n : ℕ) : ‖(1:DirichletCharacter ℂ q) (n:ZMod q)‖^2/(n:ℝ)=if n.Coprime q then (n:ℝ)⁻¹ else 0 := by
      split_ifs with hn
      · rw [norm_char_eq_one_of_coprime _ hn];simp
      · rw [(char_nat_eq_zero_iff_not_coprime _ _).mpr hn];simp
    have h₁ := reduced_harmonic_sum_error (1:DirichletCharacter ℂ q) hx
    simp_rw [h] at h₁
    change |H-(k*Real.log x+R)|≤4*k/x at h₁
    have h₂ := reduced_reciprocal_prime_sum_error q (NeZero.pos q) (mul_pos hq hx')
    rw [Real.log_mul hq.ne' hx'.ne',show (q:ℝ)/(q*x)=1/x by field_simp] at h₂
    change |H-k*(_+_+_)|≤_ at h₂
    have he : k*(Real.log q+Real.log x+Real.eulerMascheroniConstant+primeDivisorLogSum q)=k*Real.log x+S := by dsimp [S];ring
    rw [he] at h₂
    rw [show R-S=(k*Real.log x+R-H)+(H-(k*Real.log x+S)) by ring]
    apply (abs_add_le ..).trans
    rw [abs_sub_comm (k*Real.log x+R)]
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  by_contra hh
  have hpos : 0 < |R-S| := abs_pos.mpr (sub_ne_zero.mpr hh)
  let x := 2+(4*k+1)/|R-S|
  have hx : 2≤x := by dsimp [x];exact le_add_of_nonneg_right (by positivity)
  have hh := (le_div_iff₀ (show 0<x by linarith)).mp (err x hx)
  have he : |R-S| * x=2*|R-S|+(4*k+1) := by dsimp [x];field_simp
  linarith

/-- The familiar conductor and prime-factor coefficient for a single
primitive character. -/
theorem primitiveMomentLinearTerm_eq_prime_sum (q : ℕ) [NeZero q] :
    primitiveMomentLinearTerm q=(q.totient/q:ℝ)*(2*Real.eulerMascheroniConstant-1+Real.log q+2*primeDivisorLogSum q) := by
  rw [primitiveMomentLinearTerm,reducedHarmonicConstant_eq_prime_sum];ring

/-- The full character family has one copy of the prime-factor sum. -/
theorem characterFamilyLinearTerm_eq_prime_sum (q : ℕ) [NeZero q] :
    characterFamilyLinearTerm q=((q.totient:ℝ)^2/q)*(2*Real.eulerMascheroniConstant-1+Real.log q+primeDivisorLogSum q) := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have h := reducedHarmonicConstant_eq_prime_sum q
  unfold reducedHarmonicConstant at h
  let d := ∑r∈characterUnitIndices q,AnalyticTools.Gamma.realDigamma (((r+1:ℕ):ℝ)/q)
  change -d/q=_ at h
  have he : d= -(q.totient:ℝ)*(Real.eulerMascheroniConstant+Real.log q+primeDivisorLogSum q) := by
    apply (mul_right_inj' hq.ne').mp;field_simp at h ⊢;linarith
  unfold characterFamilyLinearTerm
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,card_characterUnitIndices,mul_one]
  change (q.totient/q:ℝ)*(q.totient*Real.eulerMascheroniConstant-d-q.totient)=_
  rw [he];ring

/-- Prime-factor version of the two-term critical-line expansion for
one primitive Dirichlet character. -/
theorem primitive_character_second_moment {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    (fun T : ℝ => (∫t in (1:ℝ)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
      (q.totient/q:ℝ)*(T*Real.log (T/(2*Real.pi))+
        (2*Real.eulerMascheroniConstant-1+Real.log q+2*primeDivisorLogSum q)*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  have h := primitive_critical_second_moment_expansion hχ
  rw [primitiveMomentLinearTerm_eq_prime_sum] at h
  convert h using 2;ring

/-- Prime-factor version of the full-family second moment. -/
theorem full_character_second_moment (q : ℕ) [NeZero q] :
    (fun T : ℝ => (∫t in (1:ℝ)..T,∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)-
      ((q.totient:ℝ)^2/q)*(T*Real.log (T/(2*Real.pi))+
        (2*Real.eulerMascheroniConstant-1+Real.log q+primeDivisorLogSum q)*T)) =O[atTop]
      (fun T : ℝ => T^(3/4:ℝ)*Real.sqrt (Real.log (T+2))) := by
  have h := character_family_critical_second_moment q
  rw [characterFamilyLinearTerm_eq_prime_sum] at h
  convert h using 2;ring

end AnalyticNumberTheory.DirichletLFunctions
