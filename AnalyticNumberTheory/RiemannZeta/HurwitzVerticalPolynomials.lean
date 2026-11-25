import AnalyticNumberTheory.RiemannZeta.HurwitzPolynomials

/-!
# Vertical Dirichlet polynomials with a real shift

Separation of the frequencies `log (n+a)` gives a mean value theorem on every
vertical line. The finite set of indices may include zero.
-/

open Real Complex Finset Filter MeasureTheory
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.RiemannZeta

/-- A finite Hurwitz polynomial on the vertical line of real part `σ`. -/
noncomputable def hurwitzVerticalPolynomial (a σ : ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, ((n : ℂ) + a) ^ (-((σ : ℂ) + t*I))

/-- Squared coefficient mass of the vertical Hurwitz polynomial. -/
noncomputable def hurwitzVerticalEnergy (a σ : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, ((n : ℝ) + a) ^ (-2*σ)

theorem hurwitzVerticalEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) (σ : ℝ) (S : Finset ℕ) :
    0 ≤ hurwitzVerticalEnergy a σ S :=
  sum_nonneg fun n _ => Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg n) ha) _

private theorem shifted_monomial {a : ℝ} (ha : 0 < a) (σ t : ℝ) (n : ℕ) :
    ((n : ℂ) + a) ^ (-((σ : ℂ) + t*I)) =
      ((((n : ℝ)+a)^(-σ) : ℝ) : ℂ)*Complex.exp (I*((-Real.log ((n:ℝ)+a) : ℝ) : ℂ)*t) := by
  have h := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha
  rw [← Complex.ofReal_natCast,← Complex.ofReal_add,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),
    ← Complex.ofReal_log h.le,Real.rpow_def_of_pos h,Complex.ofReal_exp,← Complex.exp_add]
  congr 1; push_cast; ring

theorem continuous_hurwitzVerticalPolynomial {a : ℝ} (ha : 0 < a) (σ : ℝ) (S : Finset ℕ) :
    Continuous (hurwitzVerticalPolynomial a σ S) := by
  unfold hurwitzVerticalPolynomial
  simp_rw [shifted_monomial ha]
  fun_prop

/-- Mean square of a finite shifted Dirichlet polynomial over an arbitrary interval. -/
theorem hurwitzVerticalPolynomial_mean_square {a : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1)
    (σ : ℝ) {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ N) (u v : ℝ) :
    |(∫ t in u..v, ‖hurwitzVerticalPolynomial a σ S t‖^2) - (v-u)*hurwitzVerticalEnergy a σ S| ≤
      4*π*N*hurwitzVerticalEnergy a σ S := by
  let x := fun n : ℕ => -Real.log ((n:ℝ)+a)
  let c := fun n : ℕ => ((((n:ℝ)+a)^(-σ) : ℝ) : ℂ)
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hsep (i : ℕ) (hi : i∈S) (j : ℕ) (hj : j∈S) (hne : i≠j) :
      (2*(N:ℝ))⁻¹ ≤ |x i-x j| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := log_shift_gap ha h (hS j hj)
      dsimp [x]; rw [neg_sub_neg]; exact hh.trans (le_abs_self _)
    · have hh := log_shift_gap ha h (hS i hi)
      rw [abs_sub_comm]; dsimp [x]; rw [neg_sub_neg]; exact hh.trans (le_abs_self _)
  have H := separated_frequency_mean_square S x c (by positivity : 0<(2*(N:ℝ))⁻¹) hsep u v
  have hc (n : ℕ) : ‖c n‖^2 = ((n:ℝ)+a)^(-2*σ) := by
    have hp := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1
    dsimp only [c]
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),← Real.rpow_natCast _ 2,← Real.rpow_mul hp.le]
    congr 1; push_cast; ring
  have hp (t : ℝ) : hurwitzVerticalPolynomial a σ S t = ∑ n ∈ S,c n*Complex.exp (I*(x n:ℂ)*t) :=
    sum_congr rfl fun n _ => shifted_monomial ha.1 σ t n
  simp only [← hp,hc,inv_inv] at H
  exact H.trans_eq (by unfold hurwitzVerticalEnergy; ring)

/-- The infinite shifted diagonal converges precisely on the side needed for the square mean. -/
theorem summable_hurwitzVerticalEnergy {a σ : ℝ} (ha : 0 < a) (hσ : 1/2 < σ) :
    Summable (fun n : ℕ => ((n:ℝ)+a)^(-2*σ)) := by
  have h := Real.summable_nat_rpow.mpr (by linarith : -2*σ < -1)
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le _ _ ((summable_nat_add_iff 1).mpr h)
  · intro n; positivity
  · intro n
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

end AnalyticNumberTheory.RiemannZeta
