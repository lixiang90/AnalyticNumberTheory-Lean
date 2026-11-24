import AnalyticNumberTheory.AdditiveNumberTheory.WaringAsymptotic
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSeriesPositivity

/-!
# Waring's theorem

The circle-method asymptotic and a uniform positive lower bound on the singular
series give representations of every sufficiently large integer. Padding by
zeros and representing the finitely many smaller targets by ones provides
one bound on the number of summands for all targets at each fixed degree.
-/

open Finset Filter

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Extra zero coordinates preserve representability by positive-degree powers. -/
theorem waringCount_pos_mono {k s t n : ℕ} (hk : 0 < k) (hst : s ≤ t)
    (hn : 0 < waringCount k s n) : 0 < waringCount k t n := by
  induction t, hst using Nat.le_induction with
  | base => exact hn
  | succ t _ ih =>
    obtain ⟨x,hx⟩ := (waringCount_pos_iff hk).mp ih
    exact (waringCount_pos_iff hk).mpr ⟨Fin.cons 0 x, by simp [Fin.sum_univ_succ, hk.ne', hx]⟩

/-- If one order represents all sufficiently large integers, a possibly larger
fixed order represents every integer. -/
theorem exists_order_of_eventually_waringCount_pos {k s : ℕ} (hk : 0 < k)
    (h : ∀ᶠ n : ℕ in atTop, 0 < waringCount k s n) : ∃ t : ℕ, ∀ n, 0 < waringCount k t n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨max s N, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact waringCount_pos_mono hk (le_max_left _ _) (hN n hn)
  · have hsmall : 0 < waringCount k n n := (waringCount_pos_iff hk).mpr ⟨fun _ => 1, by simp⟩
    exact waringCount_pos_mono hk ((le_of_not_ge hn).trans (le_max_right _ _)) hsmall

/-- Every sufficiently large integer is a sum of `s` nonnegative `k`-th powers
when `2ᵏ < s` and `k³ ≤ s`. -/
theorem eventually_waringCount_pos {k s : ℕ} (hk : 2 ≤ k) (hs : 2^k < s) (hcube : k^3 ≤ s) :
    ∀ᶠ n : ℕ in atTop, 0 < waringCount k s n := by
  have hks : 2*k < s := calc
    2*k ≤ k^2 := by rw [sq]; gcongr
    _ < k^3 := Nat.pow_lt_pow_right (by omega) (by decide)
    _ ≤ s := hcube
  obtain ⟨c,hc,hpos⟩ := exists_pos_le_waringSingularSeries_re_of_cube (by omega : 0<k) hks hcube
  exact eventually_waringCount_pos_of_singularSeries hk hs ⟨c,hc,.of_forall fun n => (hpos n).trans (Complex.re_le_norm _)⟩

/-- **Hilbert–Waring theorem**. For every positive degree, some fixed number
of nonnegative `k`-th powers represents every natural number. -/
theorem hilbert_waring {k : ℕ} (hk : 0 < k) :
    ∃ s : ℕ, ∀ n : ℕ, ∃ x : Fin s → ℕ, ∑ i, x i ^ k = n := by
  by_cases h1 : k = 1
  · subst k
    exact ⟨1, fun n => ⟨fun _ => n, by simp⟩⟩
  · let s := 2^k + k^3 + 1
    have hlarge := eventually_waringCount_pos (k := k) (s := s) (by omega)
      (Nat.lt_succ_of_le (Nat.le_add_right _ _))
      ((Nat.le_add_left _ _).trans (Nat.le_succ _))
    obtain ⟨t,ht⟩ := exists_order_of_eventually_waringCount_pos hk hlarge
    exact ⟨t, fun n => (waringCount_pos_iff hk).mp (ht n)⟩

end AnalyticNumberTheory.AdditiveNumberTheory
