import AnalyticNumberTheory.ExponentialSums.SineHarmonicSums
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Symmetric reciprocal sums around a real frequency

Moving the center of a symmetric reciprocal kernel by a fractional part
changes its terms by an absolutely summable inverse-square sequence.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
namespace AnalyticNumberTheory.ExponentialSums

theorem sum_Ioc_inverse_square {R : ℕ} (hR : 1≤R) (N : ℕ) :
    ∑ j∈Ioc R N, 1/(j:ℝ)^2 ≤ 1/(R:ℝ) := by
  by_cases h : R≤N
  · suffices H : ∑ j∈Ioc R N, 1/(j:ℝ)^2 ≤ 1/(R:ℝ)-1/(N:ℝ) by
      exact H.trans (sub_le_self _ (by positivity))
    induction N,h using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [sum_Ioc_succ_top hk];push_cast
      have hp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
      have H : 1/((k:ℝ)+1)^2≤1/(k:ℝ)-1/((k:ℝ)+1) := by field_simp;linarith
      linarith
  · simp [Ioc_eq_empty_of_le (le_of_not_ge h)]

theorem sum_Ioc_inverse_cube {R : ℕ} (hR : 1≤R) (N : ℕ) :
    ∑ j∈Ioc R N, 1/(j:ℝ)^3 ≤ 1/(R:ℝ)^2 := by
  have hp : 0<(R:ℝ) := by exact_mod_cast (by omega : 0<R)
  calc
    _ ≤ ∑ j∈Ioc R N, (1/(R:ℝ))*(1/(j:ℝ)^2) := by
      apply sum_le_sum
      intro j hj
      have hj' : (R:ℝ)≤j := by exact_mod_cast (mem_Ioc.mp hj).1.le
      have hjp := hp.trans_le hj'
      rw [pow_succ,one_div_mul_one_div,one_div_le_one_div (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hj' (sq_nonneg (j:ℝ))]
    _ ≤ _ := by
      rw [←mul_sum]
      apply (mul_le_mul_of_nonneg_left (sum_Ioc_inverse_square hR N) (by positivity)).trans_eq
      ring

private lemma interval_harmonic (N R : ℕ) {z : ℂ} (hz : ‖z‖=1) :
    ‖∑ j∈Ioc R N,(z^j-(conj z)^j)/(j:ℂ)‖≤4*(Real.pi+2) := by
  by_cases h : R≤N
  · let f (j : ℕ) := (z^j-(conj z)^j)/(j:ℂ)
    have H (n : ℕ) : ‖∑ j∈range n,f (j+1)‖≤2*(Real.pi+2) := by
      simpa only [f,Nat.cast_add,Nat.cast_one] using norm_symmetric_harmonic_sum_le n hz
    have he : ∑ j∈Ioc R N,f j = (∑ j∈range N,f (j+1))-(∑ j∈range R,f (j+1)) := by
      induction N,h using Nat.le_induction with
      | base => simp
      | succ k hk ih => rw [sum_Ioc_succ_top hk,sum_range_succ,ih];abel
    change ‖∑ j∈Ioc R N,f j‖≤_
    rw [he];exact (norm_sub_le _ _).trans (by linarith [H N,H R])
  · simp [Ioc_eq_empty_of_le (le_of_not_ge h)];positivity

/-- The portion from R+1 to N of the paired Hilbert kernel around a real
frequency, with arbitrary fractional displacement between zero and one. -/
theorem norm_shifted_symmetric_harmonic_sum {R : ℕ} (hR : 1≤R) (N : ℕ)
    {δ : ℝ} (hδ : 0≤δ) (hδ' : δ≤1) {z : ℂ} (hz : ‖z‖=1) :
    ‖∑ j∈Ioc R N,(z^j/((j:ℂ)-δ)-(conj z)^j/((j:ℂ)+δ))‖≤4*(Real.pi+2)+3 := by
  let f (j : ℕ) := z^j/((j:ℂ)-δ)-(conj z)^j/((j:ℂ)+δ)
  let g (j : ℕ) := (z^j-(conj z)^j)/(j:ℂ)
  have hpoint (j : ℕ) (hj : j∈Ioc R N) : ‖f j-g j‖≤3/(j:ℝ)^2 := by
    have hj' : 2≤(j:ℝ) := by exact_mod_cast (by have := (mem_Ioc.mp hj).1;omega : 2≤j)
    have h₀ : 0<(j:ℝ)-δ := by linarith
    have h₁ : 0<(j:ℝ)+δ := by linarith
    have hjp : 0<(j:ℝ) := by linarith
    have hn₀ : (j:ℂ)-(δ:ℂ)≠0 := by exact_mod_cast h₀.ne'
    have hn₁ : (j:ℂ)+(δ:ℂ)≠0 := by exact_mod_cast h₁.ne'
    have hn : (j:ℂ)≠0 := by exact_mod_cast hjp.ne'
    have he : f j-g j=z^j*(δ:ℂ)/((j:ℂ)*((j:ℂ)-δ))+
      (conj z)^j*(δ:ℂ)/((j:ℂ)*((j:ℂ)+δ)) := by dsimp [f,g];field_simp;ring
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_div,norm_mul,norm_pow,hz,Complex.norm_conj,one_pow,one_mul,
      ←Complex.ofReal_natCast,←Complex.ofReal_sub,←Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ,abs_of_pos h₀,abs_of_pos h₁,abs_of_pos hjp]
    have H₀ : δ/((j:ℝ)*(j-δ))≤2/(j:ℝ)^2 := by
      rw [div_le_div_iff₀ (mul_pos hjp h₀) (sq_pos_of_pos hjp)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ') (sq_nonneg (j:ℝ)),
        mul_nonneg hjp.le (show 0≤(j:ℝ)-2*δ by linarith)]
    have H₁ : δ/((j:ℝ)*(j+δ))≤1/(j:ℝ)^2 := by
      rw [div_le_div_iff₀ (mul_pos hjp h₁) (sq_pos_of_pos hjp)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ') (sq_nonneg (j:ℝ)),mul_nonneg hjp.le hδ]
    exact (add_le_add H₀ H₁).trans_eq (by ring)
  have H := interval_harmonic N R hz
  have H' : ‖∑ j∈Ioc R N,(f j-g j)‖≤3 := by
    apply (norm_sum_le _ _).trans ((sum_le_sum hpoint).trans ?_)
    simp_rw [show ∀ j : ℕ,3/(j:ℝ)^2=3*(1/(j:ℝ)^2) by intro j;ring,←mul_sum]
    apply (mul_le_mul_of_nonneg_left (sum_Ioc_inverse_square hR N) (by norm_num : (0:ℝ)≤3)).trans
    have hR' : 1≤(R:ℝ) := by exact_mod_cast hR
    nlinarith [one_div_le_one_div_of_le (by norm_num : 0<(1:ℝ)) hR']
  change ‖∑ j∈Ioc R N,f j‖≤_
  rw [show (∑ j∈Ioc R N,f j)=(∑ j∈Ioc R N,g j)+(∑ j∈Ioc R N,(f j-g j)) by rw [sum_sub_distrib (f:=f) (g:=g)];abel]
  exact (norm_add_le _ _).trans (add_le_add H H')

end AnalyticNumberTheory.ExponentialSums
