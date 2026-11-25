import AnalyticNumberTheory.DirichletLFunctions.WeightedCharacterEnergy
import AnalyticNumberTheory.DirichletLFunctions.HarmonicResidueTails
import AnalyticNumberTheory.DirichletLFunctions.IntervalPerronProducts

/-! # Second moments of fixed-modulus tail polynomials at real part one -/

open Complex Real Finset

namespace AnalyticNumberTheory.DirichletLFunctions

/-- On the line Re s = 1, removing the first A terms replaces the full
length cost by q/A plus a single logarithm. The coefficient energy is
the harmonic sum on the actual interval, for all characters of one modulus. -/
theorem fixed_modulus_tail_energy {q A : ℕ} [NeZero q] (hA : 1≤A) (X : ℕ) (a : ℕ → ℂ)
    {s : ℂ} (hs : s.re=1) :
    (∑ χ : DirichletCharacter ℂ q, ‖intervalCharacterPolynomial χ a A X s‖^2) ≤
      ((q : ℝ)/A + (1+Real.log X)) * ∑ n ∈ Ioc A X, ‖a n‖^2/(n : ℝ) := by
  let S := Ioc A X
  let w (n : ℕ) := (n : ℝ)⁻¹
  let v (n : ℕ) := ‖a n‖^2/(n : ℝ)
  let b (n : ℕ) := a n*(n : ℂ)^(-s)
  have ha (n : ℕ) (hn : n ∈ S) : ‖b n‖^2 ≤ w n*v n := by
    have hpos := (Nat.zero_le A).trans_lt (mem_Ioc.mp hn).1
    dsimp only [b,w,v]
    rw [norm_mul, mul_pow, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re, hs, Real.rpow_neg_one]
    exact le_of_eq (by ring)
  have H := character_sum_sq_le_of_fiber_weight (q := q) S (fun n : ℕ => (n : ZMod q)) b w v
    (fun _ _ => by dsimp [w]; positivity) (fun _ _ => by dsimp [v]; positivity) ha (sum_residue_tail_inv_le hA X)
  have hpoly (χ : DirichletCharacter ℂ q) :
      intervalCharacterPolynomial χ a A X s = ∑ n ∈ S, χ n*b n := by
    apply sum_congr rfl
    intro n _
    dsimp only [b]
    ring
  simp_rw [hpoly]
  apply H.trans (mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => by dsimp [v]; positivity))
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  calc
    _ ≤ (q : ℝ)*((A : ℝ)⁻¹+(q : ℝ)⁻¹*(1+Real.log X)) := mul_le_mul_of_nonneg_right hφ (by positivity)
    _ = _ := by field_simp

end AnalyticNumberTheory.DirichletLFunctions
