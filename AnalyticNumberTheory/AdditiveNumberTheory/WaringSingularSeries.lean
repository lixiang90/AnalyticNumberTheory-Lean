import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocal
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries

/-!
# The Waring singular series

The complete Weyl sum bound gives an absolutely summable majorant for the
primitive-frequency terms when the number of variables exceeds twice the degree.
-/

open Finset Filter
open AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Primitive-frequency contribution at modulus `q`; its value at zero is the empty sum. -/
noncomputable def waringSingularTerm (k s n q : ℕ) : ℂ :=
  ∑ a ∈ coprimeResidues q, (completeExpSum q a k / q) ^ s * e (-(a : ℝ) * n / q)

/-- With all frequencies included, the normalized sum measures the density of
solutions relative to one congruence in `s` variables. -/
theorem waringLocalCount_normalized {q : ℕ} [NeZero q] (k s n : ℕ) :
    ∑ a ∈ range q, (completeExpSum q a k / q) ^ s * e (-(a : ℝ) * n / q) =
      (q : ℂ) * waringLocalCount k s (n : ZMod q) / (q : ℂ) ^ s := by
  have phase (a : ZMod q) :
      ZMod.stdAddChar (-(a * (n : ZMod q))) = e (-(a.val : ℝ) * n / q) := by
    rw [show -(a * (n : ZMod q)) = ((-((a.val : ℤ) * n) : ℤ) : ZMod q) by simp,
      ZMod.stdAddChar_coe, e]
    push_cast
    congr 1
    ring
  rw [← waringLocalCount_fourier, Finset.sum_div]
  symm
  refine sum_bij (fun a _ => a.val) (fun a _ => mem_range.mpr a.val_lt)
    (fun _ _ _ _ h => ZMod.val_injective q h) ?_ ?_
  · exact fun b hb => ⟨(b : ZMod q), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hb)⟩
  · intro a _
    rw [phase, div_pow]
    ring

/-- At a prime modulus every nonzero frequency is primitive. The zero frequency
contributes one, leaving the first local correction to the singular series. -/
theorem one_add_waringSingularTerm_prime (p : ℕ) [Fact p.Prime] (k s n : ℕ) :
    1 + waringSingularTerm k s n p =
      (p : ℂ) * waringLocalCount k s (q := p) (n : ZMod p) / (p : ℂ) ^ s := by
  have hp : p.Prime := Fact.out
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [← waringLocalCount_normalized]
  have hres : coprimeResidues p = (range p).erase 0 := by
    ext a
    simp only [coprimeResidues, mem_filter, mem_erase, mem_range]
    refine ⟨fun ⟨ha, hc⟩ => ⟨?_, ha⟩, fun ⟨ha, hlt⟩ => ⟨hlt, ?_⟩⟩
    · rintro rfl
      exact hp.ne_one (by simpa using hc)
    · exact (hp.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha) hlt)).symm
  rw [waringSingularTerm, hres, ← Finset.sum_erase_add _ _ (mem_range.mpr hp.pos)]
  simp [completeExpSum, e, hp', add_comm]

/-- A bound for every positive modulus, uniform in the target `n`. -/
theorem norm_waringSingularTerm_le {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s n q : ℕ), 1 ≤ q →
      ‖waringSingularTerm k s n q‖ ≤ C ^ s * (q : ℝ) ^ (1 - (s : ℝ) / k) := by
  obtain ⟨C, hC, hbound⟩ := completeExpSum_bound hk
  refine ⟨C, hC, fun s n q hq => ?_⟩
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hnormalized (a : ℕ) (ha : a ∈ coprimeResidues q) :
      ‖completeExpSum q a k / (q : ℂ)‖ ≤ C * (q : ℝ) ^ (-(1 / (k : ℝ))) := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hq']
    calc ‖completeExpSum q a k‖ ≤ C * (q : ℝ) ^ (1 - 1 / (k : ℝ)) :=
            hbound q a hq (mem_filter.mp ha).2
      _ = C * (q : ℝ) ^ (-(1 / (k : ℝ))) * q := by
            rw [sub_eq_add_neg, Real.rpow_add hq', Real.rpow_one]; ring
  have hc : (coprimeResidues q).card ≤ q := by
    simpa [coprimeResidues] using (card_filter_le (range q) (fun a => Nat.Coprime a q))
  let B := C * (q : ℝ) ^ (-(1 / (k : ℝ)))
  calc ‖waringSingularTerm k s n q‖ ≤
        ∑ a ∈ coprimeResidues q, ‖(completeExpSum q a k / q) ^ s * e (-(a : ℝ) * n / q)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _a ∈ coprimeResidues q, B ^ s := by
          apply sum_le_sum
          intro a ha
          rw [norm_mul, norm_pow, norm_e, mul_one]
          gcongr
          exact hnormalized a ha
    _ ≤ (q : ℝ) * B ^ s := by
          simp only [sum_const, nsmul_eq_mul]
          have hB : 0 ≤ B := mul_nonneg hC.le (Real.rpow_nonneg hq'.le _)
          gcongr
    _ = C ^ s * (q : ℝ) ^ (1 - (s : ℝ) / k) := by
          dsimp [B]
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(1 / (k : ℝ)))) s,
            ← Real.rpow_mul hq'.le, sub_eq_add_neg,
            Real.rpow_add hq', Real.rpow_one]
          ring_nf

/-- A single summable majorant controls all target integers. -/
theorem waringSeries_majorant {k s : ℕ} (hk : 1 ≤ k) (hs : 2 * k < s) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ q n, ‖waringSingularTerm k s n q‖ ≤ b q := by
  obtain ⟨C, hpos, hC⟩ := norm_waringSingularTerm_le hk
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hs' : (2 : ℝ) < (s : ℝ) / k := (lt_div_iff₀ hk').mpr (by exact_mod_cast hs)
  have hsum := (Real.summable_nat_rpow.mpr (show 1 - (s : ℝ) / k < -1 by linarith)).mul_left
    (C ^ s)
  refine ⟨_, hsum, fun q n => ?_⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [waringSingularTerm, coprimeResidues, range_zero, filter_empty, sum_empty,
      norm_zero, Nat.cast_zero]
    positivity
  · exact hC s n q hq

/-- Absolute convergence when the number of variables exceeds twice the degree. -/
theorem summable_norm_waringSingularTerm {k s : ℕ} (hk : 1 ≤ k) (hs : 2 * k < s) (n : ℕ) :
    Summable fun q => ‖waringSingularTerm k s n q‖ := by
  obtain ⟨b, hb, h⟩ := waringSeries_majorant hk hs
  exact hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => h q n)

/-- The singular series for representations of `n` by `s` nonnegative `k`-th powers. -/
noncomputable def waringSingularSeries (k s n : ℕ) : ℂ :=
  ∑' q, waringSingularTerm k s n q

theorem hasSum_waringSingularSeries {k s : ℕ} (hk : 1 ≤ k) (hs : 2 * k < s) (n : ℕ) :
    HasSum (waringSingularTerm k s n) (waringSingularSeries k s n) :=
  (summable_norm_iff.mp (summable_norm_waringSingularTerm hk hs n)).hasSum

/-- A single truncation level approximates the series for all target integers. -/
theorem tendstoUniformly_waringSingularSeries {k s : ℕ} (hk : 1 ≤ k) (hs : 2 * k < s) :
    TendstoUniformly (fun Q n => ∑ q ∈ range Q, waringSingularTerm k s n q)
      (waringSingularSeries k s) atTop := by
  obtain ⟨b, hb, h⟩ := waringSeries_majorant hk hs
  exact tendstoUniformly_tsum_nat hb h

/-- A common bound for all finite singular-series sums, independent of the target. -/
theorem exists_bound_waringSingularTerm_sum {k s : ℕ} (hk : 1 ≤ k) (hs : 2 * k < s) :
    ∃ C : ℝ, ∀ (U : Finset ℕ) (n : ℕ), ‖∑ q ∈ U, waringSingularTerm k s n q‖ ≤ C := by
  obtain ⟨b, hb, h⟩ := waringSeries_majorant hk hs
  exact ⟨∑' q, b q, fun U n => (norm_sum_le _ _).trans
    ((sum_le_sum (fun q _ => h q n)).trans (hb.sum_le_tsum U (fun q _ => (norm_nonneg _).trans (h q n))))⟩

end AnalyticNumberTheory.AdditiveNumberTheory
