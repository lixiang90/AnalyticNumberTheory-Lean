import AnalyticNumberTheory.AnalyticTools.ReciprocalLargeSieveWeights
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-! # The reciprocal-totient large sieve above a conductor cutoff -/
noncomputable section
open Finset Real Complex
open scoped Classical
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.SieveMethods

/-- For arbitrary coefficients in an interval of length N, partial
summation saves the lower conductor cutoff in the length term. -/
theorem reciprocal_conductor_large_sieve (a : ℕ→ℂ) (M N : ℕ) {D : ℕ} (hD : 1≤D) (Q : ℕ) :
    (∑q∈Ioc D Q,(q.totient:ℝ)⁻¹*∑χ∈(univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑n∈Ioc M (M+N),a n*χ n‖^2) ≤
      (2*(Q:ℝ)+(N:ℝ)/D)*(∑n∈Ioc M (M+N),‖a n‖^2) := by
  let F (q:ℕ) := ∑χ∈(univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑n∈Ioc M (M+N),a n*χ n‖^2
  have hf (q) : 0≤F q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := reciprocal_sum_of_quadratic_cumulative (fun q => (q/q.totient:ℝ)*F q)
    (fun q => mul_nonneg (by positivity) (hf q)) (sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg (α:=ℝ) N) hD (character_large_sieve_dirichlet a M N) (U:=Q)
  apply le_trans _ hp
  apply sum_le_sum;intro q hq
  have hq₀ : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hq).1).ne'
  change (q.totient:ℝ)⁻¹*F q≤(q/q.totient:ℝ)*F q/q
  exact le_of_eq (by field_simp [hq₀])

/-- The same bound with real conductor limits; rounding the lower cutoff
costs at most a factor two for D≥1. -/
theorem reciprocal_conductor_large_sieve_real (a : ℕ→ℂ) (M N : ℕ) {D Q : ℝ} (hD : 1≤D) (hQ : 0≤Q) :
    (∑q∈Ioc ⌊D⌋₊ ⌊Q⌋₊,(q.totient:ℝ)⁻¹*∑χ∈(univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑n∈Ioc M (M+N),a n*χ n‖^2) ≤
      (2*Q+2*N/D)*(∑n∈Ioc M (M+N),‖a n‖^2) := by
  have hd : 1≤⌊D⌋₊ := Nat.le_floor (by simpa using hD)
  have hd' : (1:ℝ)≤⌊D⌋₊ := by exact_mod_cast hd
  have hx : (N:ℝ)/(⌊D⌋₊:ℝ)≤2*N/D := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (by linarith only [Nat.lt_floor_add_one D,hd'] : D≤2*⌊D⌋₊) (Nat.cast_nonneg (α:=ℝ) N)]
  exact (reciprocal_conductor_large_sieve a M N hd ⌊Q⌋₊).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hx,Nat.floor_le hQ]) (sum_nonneg (fun _ _ => sq_nonneg _)))

end AnalyticNumberTheory.SieveMethods
