import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocalPositivity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.Complex.Order

/-!
# A uniform positive lower bound for Waring's singular series

The deviations of the local factors from one have a summable majorant
independent of the target. An infinite product of explicit positive lower
bounds then controls the singular series uniformly in the target.
-/

open Finset Filter
open scoped Topology ComplexOrder

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A summable majorant for the tails of the local Euler factors, independent
of the target. Each positive prime power occurs only once. -/
theorem exists_summable_waringLocalFactor_majorant {k s : ℕ} (hk : 0 < k) (hs : 2*k < s) :
    ∃ b : Nat.Primes → ℝ, Summable b ∧ ∀ (p : Nat.Primes) (n : ℕ), ‖waringLocalFactor k s n p - 1‖ ≤ b p := by
  obtain ⟨B,hB,hbound⟩ := waringSeries_majorant hk hs
  let powMap (u : Nat.Primes × ℕ) : ℕ := u.1.val ^ (u.2+1)
  have hi : Function.Injective powMap := by
    rintro ⟨p,a⟩ ⟨q,b⟩ he
    obtain ⟨hp,h⟩ := p.prop.pow_inj q.prop he
    exact Prod.ext (Subtype.ext hp) h
  have hn (q : ℕ) : 0 ≤ B q := (norm_nonneg _).trans (hbound q 0)
  have h := (summable_prod_of_nonneg (fun u => hn (powMap u))).mp (hB.comp_injective hi)
  refine ⟨_, h.2, fun p n => ?_⟩
  let A := waringSingularTerm k s n
  have hsum := (summable_norm_waringSingularTerm hk hs n).comp_injective
    (Nat.pow_right_injective p.prop.one_lt)
  have htail : Summable (fun j : ℕ => ‖A (p.val^(j+1))‖) :=
    hsum.comp_injective (add_left_injective 1)
  have h1 : A 1 = 1 := (isMultiplicative_waringCoefficient k s n).1
  have he : waringLocalFactor k s n p - 1 = ∑' j : ℕ, A (p.val^(j+1)) := by
    unfold waringLocalFactor
    rw [(summable_norm_iff.mp hsum).tsum_eq_zero_add]
    change A (p.val^0) + _ - 1 = _
    rw [pow_zero,h1,add_sub_cancel_left]
  rw [he]
  exact (norm_tsum_le_tsum_norm htail).trans (htail.tsum_le_tsum (fun j => hbound _ _) (h.1 p))

/-- Uniform lower bounds for each local factor imply a single positive
lower bound for the norm of the Euler product, independent of the target. -/
theorem exists_pos_le_norm_waringSingularSeries_of_local {k s : ℕ} (hk : 0 < k)
    (hs : 2*k < s) (hpos : ∀ p : Nat.Primes, ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ ‖waringLocalFactor k s n p‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, C ≤ ‖waringSingularSeries k s n‖ := by
  classical
  choose c hc hbound using hpos
  obtain ⟨b,hb,hd⟩ := exists_summable_waringLocalFactor_majorant hk hs
  let f (p : Nat.Primes) := if b p < 1/2 then 1-b p else c p
  have hf (p) : 0 < f p := by
    dsimp [f]
    split_ifs with h
    · linarith
    · exact hc p
  have hf_le (p n) : f p ≤ ‖waringLocalFactor k s n p‖ := by
    dsimp [f]
    split_ifs with h
    · have ht := norm_sub_norm_le (1:ℂ) (waringLocalFactor k s n p)
      rw [norm_one, norm_sub_rev] at ht
      linarith [hd p n]
    · exact hbound p n
  have hsmall := hb.tendsto_cofinite_zero.eventually_lt_const one_half_pos
  have hdev : Summable (fun p => ‖f p - 1‖) := hb.congr_cofinite (by
    filter_upwards [hsmall] with p hp
    have hn := (norm_nonneg _).trans (hd p 0)
    rw [show f p = 1-b p from ite_eq_left hp, show 1-b p-1 = -b p by ring, norm_neg, Real.norm_of_nonneg hn])
  have hm : Multipliable f := by simpa using multipliable_one_add_of_summable hdev
  have hne : ∏' p, f p ≠ 0 := by
    simpa using tprod_one_add_ne_zero_of_summable (f := fun p => f p - 1)
      (fun p => by simpa using (hf p).ne') hdev
  refine ⟨_, lt_of_le_of_ne (by exact tprod_nonneg fun p => (hf p).le) (Ne.symm hne), fun n => ?_⟩
  apply le_of_tendsto_of_tendsto' hm.hasProd (hasProd_waringLocalFactor hk hs n).norm
  exact fun U => Finset.prod_le_prod₀ (fun p _ => (hf p).le) (fun p _ => hf_le p n)

/-- It suffices to check the starting precision only at primes dividing the
degree. All other primes use prime-field solubility. -/
theorem exists_pos_le_norm_waringSingularSeries {k s : ℕ} (hk : 0 < k) (hs : 2*k < s+1)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ k → p^waringHenselLevel p k ≤ s+1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, C ≤ ‖waringSingularSeries k (s+1) n‖ := by
  apply exists_pos_le_norm_waringSingularSeries_of_local hk hs
  intro p
  have : Fact p.val.Prime := ⟨p.prop⟩
  let q := p.val ^ waringHenselLevel p.val k
  have hq : 0 < (q:ℝ) := by exact_mod_cast pow_pos p.prop.pos _
  refine ⟨1/(q:ℝ)^s, one_div_pos.mpr (pow_pos hq s), fun n => ?_⟩
  apply le_trans _ (Complex.re_le_norm _)
  by_cases hd : p.val ∣ k
  · exact waringLocalFactor_re_ge_of_henselLevel hk hs n
      (waringLocalCount_pos_of_modulus_le hk (hbad _ p.prop hd) _)
  · have he : q = p.val := by simp [q, waringHenselLevel, Nat.factorization_eq_zero_of_not_dvd hd]
    rw [he]
    exact waringLocalFactor_re_ge_of_coprime hk hs (p.prop.coprime_iff_not_dvd.mpr hd) n

/-- The normalized solution counts place every limiting local density on the
nonnegative real axis. -/
theorem waringLocalFactor_nonneg {k s : ℕ} (hk : 0 < k) (hs : 2*k < s)
    (n p : ℕ) [Fact p.Prime] : 0 ≤ waringLocalFactor k s n p := by
  apply ge_of_tendsto (tendsto_waringLocalCount_localFactor hk hs n p)
  exact .of_forall fun r => by positivity

/-- The singular series is real and nonnegative throughout its range of
absolute convergence. -/
theorem waringSingularSeries_nonneg {k s : ℕ} (hk : 0 < k) (hs : 2*k < s) (n : ℕ) :
    0 ≤ waringSingularSeries k s n := by
  apply ge_of_tendsto (hasProd_waringLocalFactor hk hs n)
  exact .of_forall fun U => prod_nonneg (fun p _ => by
    have : Fact p.val.Prime := ⟨p.prop⟩
    exact waringLocalFactor_nonneg hk hs n p)

/-- The elementary condition `s ≥ k³` implies every exceptional-prime size
condition, hence a uniform positive lower bound for the real singular series. -/
theorem exists_pos_le_waringSingularSeries_re_of_cube {k s : ℕ} (hk : 0 < k)
    (hs : 2*k < s) (hcube : k^3 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, C ≤ (waringSingularSeries k s n).re := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  obtain ⟨C,hC,hl⟩ := exists_pos_le_norm_waringSingularSeries hk hs (by
    intro p hp hd
    have hpk := Nat.le_of_dvd hk hd
    have hv : p ^ k.factorization p ≤ k := Nat.ordProj_le p hk.ne'
    calc
      p ^ waringHenselLevel p k = (p^k.factorization p)^2 * p := by
        rw [waringHenselLevel, pow_add, pow_one, mul_comm 2, pow_mul]
      _ ≤ k^2 * k := Nat.mul_le_mul (Nat.pow_le_pow_left hv 2) hpk
      _ ≤ d+1 := by simpa [pow_succ] using hcube)
  exact ⟨C,hC,fun n => (Complex.re_eq_norm.mpr (waringSingularSeries_nonneg hk hs n)).symm ▸ hl n⟩

end AnalyticNumberTheory.AdditiveNumberTheory
