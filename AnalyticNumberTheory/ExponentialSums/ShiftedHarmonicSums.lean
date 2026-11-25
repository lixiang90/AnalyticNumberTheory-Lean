import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Round

/-!
# Shifted harmonic sums over integer frequencies
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Uniform harmonic bound on an arbitrary subset of the integers within
a prescribed distance of a real frequency. The shift can be integral. -/
theorem sum_shifted_inv_one_add_abs_le (S : Finset ℤ) {y : ℝ} {K : ℕ}
    (hS : ∀ n ∈ S, |(n:ℝ)-y|≤K) :
    (∑ n ∈ S, 1/(1+|(n:ℝ)-y|)) ≤ 4*(1+Real.log (K+2:ℝ)) := by
  classical
  let c := ⌊y⌋
  let d (n : ℤ) := (n-c).natAbs+1
  have hcard (n : ℤ) : ((n-c).natAbs:ℝ) = |(n:ℝ)-c| := by
    rw [←Int.cast_sub,←Int.cast_abs,←Int.natCast_natAbs]; simp
  have hc : |y-(c:ℝ)|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le y))]; linarith [Int.lt_floor_add_one y]
  have hnear (n : ℤ) : (d n:ℝ) ≤ 2+|(n:ℝ)-y| := by
    have h := abs_sub_le (n:ℝ) y (c:ℝ)
    dsimp [d]; push_cast; rw [hcard]; linarith
  have hd (n : ℤ) : 0<(d n:ℝ) := by dsimp [d]; positivity
  have hbound (n : ℤ) : 1/(1+|(n:ℝ)-y|)≤2/(d n:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (hd n)).mpr
    linarith [hnear n,abs_nonneg ((n:ℝ)-y)]
  have him (n : ℤ) (hn : n∈S) : d n∈Icc 1 (K+2) := by
    refine mem_Icc.mpr ⟨by dsimp [d]; omega,?_⟩
    have HH : (d n:ℝ)≤((K+2:ℕ):ℝ) := by push_cast; linarith [hnear n,hS n hn]
    exact_mod_cast HH
  have hhalf (P : Finset ℤ) (hP : P⊆S) (hin : (P:Set ℤ).InjOn d) :
      (∑ n∈P,1/(1+|(n:ℝ)-y|)) ≤ 2*(1+Real.log (K+2:ℝ)) := by
    calc
      (∑ n∈P,1/(1+|(n:ℝ)-y|)) ≤ ∑ n∈P,2/(d n:ℝ) := sum_le_sum fun n _ => hbound n
      _ = ∑ m∈P.image d,2/(m:ℝ) := (sum_image (f:=fun m : ℕ => 2/(m:ℝ)) hin).symm
      _ ≤ ∑ m∈Icc 1 (K+2),2/(m:ℝ) := sum_le_sum_of_subset_of_nonneg
        (by intro m hm; obtain ⟨n,hn,rfl⟩ := mem_image.mp hm; exact him n (hP hn))
        (by intros; positivity)
      _ = 2*(harmonic (K+2):ℝ) := by
        rw [harmonic_eq_sum_Icc,Rat.cast_sum,mul_sum]
        apply sum_congr rfl; intro m _; simp [div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using harmonic_le_one_add_log (K+2)) (by norm_num)
  have hL := hhalf (S.filter (fun n => n≤c)) (filter_subset _ _) (by
    intro m hm n hn he
    have hm' := (mem_filter.mp hm).2
    have hn' := (mem_filter.mp hn).2
    have H : (m-c).natAbs=(n-c).natAbs := Nat.add_right_cancel he
    have H' := congrArg ((↑):ℕ→ℤ) H
    simp only [Int.natCast_natAbs,abs_of_nonpos (sub_nonpos.mpr hm'),abs_of_nonpos (sub_nonpos.mpr hn')] at H'
    omega)
  have hR := hhalf (S.filter (fun n => ¬n≤c)) (filter_subset _ _) (by
    intro m hm n hn he
    have hm' := (mem_filter.mp hm).2
    have hn' := (mem_filter.mp hn).2
    have H : (m-c).natAbs=(n-c).natAbs := Nat.add_right_cancel he
    have H' := congrArg ((↑):ℕ→ℤ) H
    simp only [Int.natCast_natAbs,abs_of_nonneg (sub_nonneg.mpr (not_le.mp hm').le),
      abs_of_nonneg (sub_nonneg.mpr (not_le.mp hn').le)] at H'
    omega)
  have he := sum_filter_add_sum_filter_not S (fun n => n≤c) (fun n => 1/(1+|(n:ℝ)-y|))
  linarith only [he,hL,hR]

end AnalyticNumberTheory.ExponentialSums
