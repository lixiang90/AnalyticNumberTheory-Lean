import AnalyticNumberTheory.AdditiveNumberTheory.WaringPrimeModuli
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The local factors of Waring's singular series

Partitioning the frequencies modulo `q` by their reduced denominator identifies
the divisor sum of the primitive terms with the normalized local representation
count. Chinese remaindering and Möbius inversion give multiplicativity.
-/

open Finset Filter
open AnalyticNumberTheory.ExponentialSums
open scoped ArithmeticFunction Topology

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A common factor in a frequency and its modulus repeats the shorter complete sum. -/
theorem completeExpSum_scale {g q : ℕ} (hg : 0 < g) (hq : 0 < q) (a k : ℕ) :
    completeExpSum (g*q) (g*a) k = (g : ℂ) * completeExpSum q a k := by
  let w (j : ℕ) := e ((a : ℝ) / q * j ^ k)
  let _ : NeZero q := ⟨hq.ne'⟩
  have hchar (j : ℕ) : w j = ZMod.stdAddChar ((a : ZMod q) * (j : ZMod q) ^ k) := by
    rw [show (a : ZMod q) * (j : ZMod q) ^ k = (((a : ℤ) * (j : ℤ) ^ k : ℤ) : ZMod q) by simp,
      ZMod.stdAddChar_coe]
    unfold w e
    congr 1
    push_cast
    ring
  have hperiod (m j : ℕ) : w (m * q + j) = w j := by rw [hchar, hchar]; simp
  have hsum (m : ℕ) : ∑ j ∈ range (m*q), w j = (m : ℂ) * ∑ j ∈ range q, w j := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      simp_rw [hperiod]
      push_cast
      ring
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs (u v : ℕ) : completeExpSum u v k = ∑ j ∈ range u, e ((v : ℝ) / u * j ^ k) := by
    refine sum_congr rfl fun j _ => ?_
    unfold e
    congr 1
    push_cast
    ring
  rw [hs, hs]
  calc
    _ = ∑ j ∈ range (g*q), w j := by
      refine sum_congr rfl fun j _ => ?_
      dsimp only [w]
      congr 1
      push_cast
      field_simp
    _ = _ := hsum g

private noncomputable def frequency (k s n q a : ℕ) : ℂ :=
  (completeExpSum q a k / q) ^ s * e (-(a : ℝ) * n / q)

private theorem frequency_scale {g q : ℕ} (hg : 0 < g) (hq : 0 < q) (k s n a : ℕ) :
    frequency k s n (g*q) (g*a) = frequency k s n q a := by
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold frequency
  rw [completeExpSum_scale hg hq, Nat.cast_mul, mul_div_mul_left _ _ hg']
  congr 2
  push_cast
  field_simp

private theorem sum_frequency_gcd {g q : ℕ} (hg : 0 < g) (hq : 0 < q) (k s n : ℕ) :
    ∑ a ∈ (range (g*q)).filter (fun a => (g*q).gcd a = g), frequency k s n (g*q) a =
      waringSingularTerm k s n q := by
  symm
  refine sum_bij (fun a _ => g*a) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hlt,hcop⟩ := mem_filter.mp ha
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ((Nat.mul_lt_mul_left hg).mpr (mem_range.mp hlt)), ?_⟩
    rw [Nat.gcd_mul_left, hcop.symm.gcd_eq_one, mul_one]
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hg he
  · intro b hb
    obtain ⟨hb,hgcd⟩ := mem_filter.mp hb
    have hd : g ∣ b := hgcd ▸ Nat.gcd_dvd_right (g*q) b
    obtain ⟨a,rfl⟩ := hd
    rw [Nat.gcd_mul_left, Nat.mul_eq_left hg.ne'] at hgcd
    refine ⟨a, mem_filter.mpr ⟨mem_range.mpr ((Nat.mul_lt_mul_left hg).mp (mem_range.mp hb)), ?_⟩, rfl⟩
    exact Nat.Coprime.symm hgcd
  · intro a _
    exact (frequency_scale hg hq k s n a).symm

/-- The sum of the primitive coefficients over all divisors of a modulus
equals its representation count divided by the expected number of solutions. -/
theorem sum_divisors_waringSingularTerm {q : ℕ} [NeZero q] (k s n : ℕ) :
    ∑ d ∈ q.divisors, waringSingularTerm k s n d =
      (q : ℂ) * waringLocalCount k s (n : ZMod q) / (q : ℂ) ^ s := by
  rw [← waringLocalCount_normalized, ← Nat.sum_div_divisors q (waringSingularTerm k s n)]
  have hf : ∀ a ∈ range q, q.gcd a ∈ q.divisors := fun a _ =>
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne q⟩
  change _ = ∑ a ∈ range q, frequency k s n q a
  rw [← sum_fiberwise_of_maps_to hf (frequency k s n q)]
  apply sum_congr rfl
  intro g hg
  obtain ⟨d, hd⟩ := Nat.dvd_of_mem_divisors hg
  have hpos := Nat.pos_of_mem_divisors hg
  subst q
  rw [Nat.mul_div_cancel_left _ hpos]
  exact (sum_frequency_gcd hpos (Nat.pos_of_mul_pos_left (NeZero.pos (g*d))) k s n).symm

/-- The primitive coefficients, bundled as an arithmetic function. -/
noncomputable def waringCoefficient (k s n : ℕ) : ArithmeticFunction ℂ :=
  ⟨waringSingularTerm k s n, by simp [waringSingularTerm, coprimeResidues]⟩

@[simp] theorem waringCoefficient_apply (k s n q : ℕ) :
    waringCoefficient k s n q = waringSingularTerm k s n q := rfl

private theorem waringSingularTerm_one (k s n : ℕ) : waringSingularTerm k s n 1 = 1 := by
  simp [waringSingularTerm, coprimeResidues, completeExpSum, e]

/-- Möbius inversion of the CRT identity for normalized solution counts proves
that primitive-frequency contributions multiply at coprime moduli. -/
theorem isMultiplicative_waringCoefficient (k s n : ℕ) :
    (waringCoefficient k s n).IsMultiplicative := by
  let A := waringCoefficient k s n
  let F := (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * A
  have hF {q : ℕ} [NeZero q] :
      F q = (q : ℂ) * waringLocalCount k s (n : ZMod q) / (q : ℂ) ^ s := by
    rw [show F q = ∑ d ∈ q.divisors, A d from ArithmeticFunction.coe_zeta_mul_apply]
    exact sum_divisors_waringSingularTerm k s n
  have hmult : F.IsMultiplicative := by
    constructor
    · simp [F, A, waringSingularTerm_one]
    · intro u v huv
      obtain rfl | hu := Nat.eq_zero_or_pos u
      · simp
      obtain rfl | hv := Nat.eq_zero_or_pos v
      · simp
      let _ : NeZero u := ⟨hu.ne'⟩
      let _ : NeZero v := ⟨hv.ne'⟩
      rw [hF, hF, hF, waringLocalCount_mul huv, Nat.cast_mul, Nat.cast_mul, mul_pow]
      ring
  have hrecover : A = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F := by
    simp only [F, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  change A.IsMultiplicative
  rw [hrecover]
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul hmult

/-- The local factor at `p`, initially expressed as a series over its powers. -/
noncomputable def waringLocalFactor (k s n p : ℕ) : ℂ :=
  ∑' r : ℕ, waringSingularTerm k s n (p^r)

/-- At every prime, the local factor is the limit of the normalized numbers
of solutions modulo its powers. -/
theorem tendsto_waringLocalCount_localFactor {k s : ℕ} (hk : 0 < k) (hs : 2*k < s)
    (n p : ℕ) [Fact p.Prime] :
    Tendsto (fun r : ℕ => (p^r : ℕ) * (waringLocalCount k s (n : ZMod (p^r)) : ℂ) /
      ((p^r : ℕ) : ℂ)^s) atTop (𝓝 (waringLocalFactor k s n p)) := by
  have hp : p.Prime := Fact.out
  have hsum := (summable_norm_iff.mp (summable_norm_waringSingularTerm hk hs n)).comp_injective
    (Nat.pow_right_injective hp.one_lt)
  have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply h.congr'
  exact .of_forall fun r => by
    simpa only [Function.comp_apply, ← Nat.sum_divisors_prime_pow hp] using
      sum_divisors_waringSingularTerm (q := p^r) k s n

/-- Euler product for Waring's absolutely convergent singular series. -/
theorem hasProd_waringLocalFactor {k s : ℕ} (hk : 0 < k) (hs : 2*k < s) (n : ℕ) :
    HasProd (fun p : Nat.Primes => waringLocalFactor k s n p) (waringSingularSeries k s n) := by
  exact (isMultiplicative_waringCoefficient k s n).eulerProduct_hasProd
    (summable_norm_waringSingularTerm hk hs n)

theorem waringSingularSeries_eq_tprod {k s : ℕ} (hk : 0 < k) (hs : 2*k < s) (n : ℕ) :
    waringSingularSeries k s n = ∏' p : Nat.Primes, waringLocalFactor k s n p :=
  (hasProd_waringLocalFactor hk hs n).tprod_eq.symm

end AnalyticNumberTheory.AdditiveNumberTheory
