import AnalyticNumberTheory.AnalyticTools.QuadraticEulerFactors
import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod
import AnalyticNumberTheory.AnalyticTools.Gamma.InfiniteProducts
import AnalyticNumberTheory.DirichletLFunctions.GaussSums
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions
import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Goldbach representation counts and singular series

This file formalizes the circle-method theory for the ternary and binary Goldbach problems:

- Ramanujan sums `ramanujanSum q n := ∑ a coprime q, e (a * n / q)`, bridging
  `DirichletLFunctions.gaussSum`, establishing the divisor-sum and Hölder closed forms
  `μ(q / d) * φ(q) / φ(q / d)` (`d = gcd(q, n)`), multiplicativity, and `|c_q(n)| ≤ gcd(q, n)`.
- Weighted and unweighted ternary and binary Goldbach representation counts, comparison between
  `Λ`-weighted counts `R₃(N)` and prime-tuple counts `T(N)`, and representation-integral formulas.
- A uniform minor-arc bound for the prime exponential sum from Vaughan's estimate, and a
  bound for the ternary minor-arc integral using the second moment of the prime exponential sum.
- Absolute convergence of the ternary and binary singular series, a uniform tail estimate
  for the ternary series, and Euler products for both series. The ternary series is positive
  on odd inputs, the binary series on positive even inputs. In each case the opposite parity
  makes the Euler factor at two vanish.
-/

noncomputable section

open Complex Finset MeasureTheory Set Filter
open scoped Topology Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.ExponentialSums
open AnalyticNumberTheory.PrimeDistribution

namespace AnalyticNumberTheory.AdditiveNumberTheory

section RamanujanSums

/-- The Ramanujan sum `c_q(n) = ∑_{0 ≤ a < q, gcd(a, q) = 1} e(a n / q)`. -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ coprimeResidues q, e ((a : ℝ) * (n : ℝ) / (q : ℝ))

/-- Bridge between `ramanujanSum q n` and the Gauss sum of the principal character modulo `q`. -/
theorem ramanujanSum_eq_gaussSum_principal {q : ℕ} [NeZero q] (n : ℤ) :
    ramanujanSum q n = gaussSum (1 : DirichletCharacter ℂ q) (n : ZMod q) := by
  rw [gaussSum_int_eq_sum_range, ramanujanSum, coprimeResidues, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : Nat.Coprime a q
  · have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
    have hchar : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 := MulChar.one_apply hunit
    split_ifs
    simp only [hchar, one_mul]
    unfold e
    congr 1
    push_cast
    ring
  · have hnon : ¬ IsUnit ((a : ℕ) : ZMod q) := fun hu => ha ((ZMod.isUnit_iff_coprime a q).mp hu)
    have hchar : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 0 := MulChar.map_nonunit _ hnon
    split_ifs
    simp only [hchar, zero_mul]

/-- Divisor-sum formula for the Ramanujan sum:
`ramanujanSum q n = ∑ ℓ ∈ (Nat.gcd n.natAbs q).divisors, μ (q / ℓ) * ℓ`. -/
theorem ramanujanSum_eq_sum_divisors {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n =
      ∑ ℓ ∈ (Nat.gcd n.natAbs q).divisors, (μ (q / ℓ) : ℂ) * (ℓ : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  rw [ramanujanSum_eq_gaussSum_principal]
  exact gaussSum_principal_eq_ramanujan n

/-- `ramanujanSum q n` has zero imaginary part. -/
theorem ramanujanSum_im_eq_zero {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    (ramanujanSum q n).im = 0 := by
  rw [ramanujanSum_eq_sum_divisors hq n]
  simp

/-- `ramanujanSum q n` equals the complex cast of its real part. -/
theorem ramanujanSum_eq_ofReal_re {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n = ((ramanujanSum q n).re : ℂ) :=
  Complex.ext rfl (ramanujanSum_im_eq_zero hq n)

/-- Symmetry under negation: `ramanujanSum q (-n) = ramanujanSum q n`. -/
theorem ramanujanSum_neg {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q (-n) = ramanujanSum q n := by
  simp only [ramanujanSum_eq_sum_divisors hq, Int.natAbs_neg]

/-- At `q = 1`, `ramanujanSum 1 n = 1`. -/
@[simp]
theorem ramanujanSum_one_left (n : ℤ) : ramanujanSum 1 n = 1 := by
  simp [ramanujanSum, coprimeResidues]

/-- At `n = 0`, `ramanujanSum q 0 = q.totient` for `q ≥ 1`. -/
theorem ramanujanSum_zero_right {q : ℕ} (hq : 1 ≤ q) :
    ramanujanSum q 0 = (q.totient : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  rw [ramanujanSum_eq_gaussSum_principal]
  simpa using gaussSum_zero_right (1 : DirichletCharacter ℂ q)

/-- Multiplicativity of `ramanujanSum q n` in `q` for coprime moduli `q₁, q₂`. -/
theorem ramanujanSum_mul_coprime {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℤ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  have hq12 : 1 ≤ q₁ * q₂ := Nat.mul_pos hq₁ hq₂
  rw [ramanujanSum_eq_sum_divisors hq12, ramanujanSum_eq_sum_divisors hq₁,
    ramanujanSum_eq_sum_divisors hq₂]
  set d₁ := Nat.gcd n.natAbs q₁
  set d₂ := Nat.gcd n.natAbs q₂
  have hgcd : Nat.gcd n.natAbs (q₁ * q₂) = d₁ * d₂ :=
    Nat.Coprime.gcd_mul n.natAbs hcop
  have hd_cop : Nat.Coprime d₁ d₂ :=
    (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
  rw [hgcd, Finset.sum_mul]
  have hprod :
      ∑ ℓ₁ ∈ d₁.divisors, (μ (q₁ / ℓ₁) : ℂ) * (ℓ₁ : ℂ) *
          ∑ ℓ₂ ∈ d₂.divisors, (μ (q₂ / ℓ₂) : ℂ) * (ℓ₂ : ℂ) =
        ∑ p ∈ d₁.divisors ×ˢ d₂.divisors,
          ((μ (q₁ / p.1) : ℂ) * (p.1 : ℂ)) * ((μ (q₂ / p.2) : ℂ) * (p.2 : ℂ)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun ℓ₁ _ => Finset.mul_sum _ _ _
  rw [hprod]
  refine Finset.sum_bij (fun ℓ _ => (Nat.gcd ℓ d₁, Nat.gcd ℓ d₂)) ?_ ?_ ?_ ?_
  · intro ℓ _
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    have hd1_ne : d₁ ≠ 0 := (Nat.gcd_pos_of_pos_right _ hq₁).ne'
    have hd2_ne : d₂ ≠ 0 := (Nat.gcd_pos_of_pos_right _ hq₂).ne'
    exact ⟨⟨Nat.gcd_dvd_right _ _, hd1_ne⟩, ⟨Nat.gcd_dvd_right _ _, hd2_ne⟩⟩
  · intro a ha b hb heq
    have ha_dvd : a ∣ d₁ * d₂ := (Nat.mem_divisors.mp ha).1
    have hb_dvd : b ∣ d₁ * d₂ := (Nat.mem_divisors.mp hb).1
    have hca : a = Nat.gcd a d₁ * Nat.gcd a d₂ := by
      simpa [Nat.gcd_comm] using ((hd_cop.gcd_mul a).symm.trans (Nat.gcd_eq_left ha_dvd)).symm
    have hcb : b = Nat.gcd b d₁ * Nat.gcd b d₂ := by
      simpa [Nat.gcd_comm] using ((hd_cop.gcd_mul b).symm.trans (Nat.gcd_eq_left hb_dvd)).symm
    have h1 : Nat.gcd a d₁ = Nat.gcd b d₁ := congrArg Prod.fst heq
    have h2 : Nat.gcd a d₂ = Nat.gcd b d₂ := congrArg Prod.snd heq
    rw [hca, hcb, h1, h2]
  · intro p hp
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
    have hp1_dvd : p.1 ∣ d₁ := hp.1.1
    have hp2_dvd : p.2 ∣ d₂ := hp.2.1
    have hd12_ne : d₁ * d₂ ≠ 0 := mul_ne_zero hp.1.2 hp.2.2
    refine ⟨p.1 * p.2, Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hp1_dvd hp2_dvd, hd12_ne⟩, ?_⟩
    ext
    · have h1 : Nat.Coprime p.2 d₁ := hd_cop.symm.coprime_dvd_left hp2_dvd
      calc
        Nat.gcd (p.1 * p.2) d₁ = Nat.gcd p.1 d₁ := h1.gcd_mul_right_cancel p.1
        _ = p.1 := Nat.gcd_eq_left hp1_dvd
    · have h2 : Nat.Coprime p.1 d₂ := hd_cop.coprime_dvd_left hp1_dvd
      calc
        Nat.gcd (p.1 * p.2) d₂ = Nat.gcd p.2 d₂ := by
          rw [mul_comm]; exact h2.gcd_mul_right_cancel p.2
        _ = p.2 := Nat.gcd_eq_left hp2_dvd
  · intro ℓ hℓ
    have hℓ_dvd : ℓ ∣ d₁ * d₂ := (Nat.mem_divisors.mp hℓ).1
    set a₁ := Nat.gcd ℓ d₁
    set a₂ := Nat.gcd ℓ d₂
    have ha1_dvd_q1 : a₁ ∣ q₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have ha2_dvd_q2 : a₂ ∣ q₂ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have hℓ_eq : ℓ = a₁ * a₂ := by
      simpa [a₁, a₂, Nat.gcd_comm] using
        ((hd_cop.gcd_mul ℓ).symm.trans (Nat.gcd_eq_left hℓ_dvd)).symm
    have hdiv_eq : q₁ * q₂ / ℓ = (q₁ / a₁) * (q₂ / a₂) := by
      rw [hℓ_eq]
      have h1 := Nat.mul_div_cancel' ha1_dvd_q1
      have h2 := Nat.mul_div_cancel' ha2_dvd_q2
      have ha1_pos : 0 < a₁ := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right _ hq₁)
      have ha2_pos : 0 < a₂ := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right _ hq₂)
      have hm_eq : q₁ * q₂ = (q₁ / a₁ * (q₂ / a₂)) * (a₁ * a₂) := by
        calc
          q₁ * q₂ = (a₁ * (q₁ / a₁)) * (a₂ * (q₂ / a₂)) := by rw [h1, h2]
          _ = (q₁ / a₁ * (q₂ / a₂)) * (a₁ * a₂) := by ring
      rw [hm_eq, Nat.mul_div_cancel _ (mul_pos ha1_pos ha2_pos)]
    have hq_cop : Nat.Coprime (q₁ / a₁) (q₂ / a₂) :=
      (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd ha1_dvd_q1)).coprime_dvd_right
        (Nat.div_dvd_of_dvd ha2_dvd_q2)
    have hmu : μ (q₁ * q₂ / ℓ) = μ (q₁ / a₁) * μ (q₂ / a₂) := by
      rw [hdiv_eq]
      exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hq_cop
    rw [hmu]
    conv_lhs => rw [hℓ_eq]
    push_cast
    ring

/-- Evaluation of `ramanujanSum (p ^ k) n` for a prime power `p ^ k` (`k ≥ 1`). -/
theorem ramanujanSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (n : ℤ) :
    ramanujanSum (p ^ k) n =
      if p ^ k ∣ n.natAbs then ((p ^ k).totient : ℂ)
      else if p ^ (k - 1) ∣ n.natAbs then -((p ^ (k - 1) : ℕ) : ℂ)
      else 0 := by
  have hpk_pos : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  rw [ramanujanSum_eq_sum_divisors hpk_pos n]
  obtain ⟨r, hr_le, hd_eq⟩ :=
    (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n.natAbs (p ^ k))
  rw [hd_eq, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hr_iff : ∀ j : ℕ, j ≤ k → (p ^ j ∣ n.natAbs ↔ j ≤ r) := by
    intro j hjk
    have h1 : p ^ j ∣ Nat.gcd n.natAbs (p ^ k) ↔ p ^ j ∣ n.natAbs ∧ p ^ j ∣ p ^ k :=
      Nat.dvd_gcd_iff
    rw [hd_eq] at h1
    constructor
    · intro hjn
      have hj_dvd_r : p ^ j ∣ p ^ r := h1.mpr ⟨hjn, Nat.pow_dvd_pow p hjk⟩
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hj_dvd_r
    · intro hjr
      exact (Nat.pow_dvd_pow p hjr).trans (hd_eq ▸ Nat.gcd_dvd_left _ _)
  have hterm : ∀ j ∈ Finset.range (r + 1),
      (μ (p ^ k / p ^ j) : ℂ) * ((p ^ j : ℕ) : ℂ) =
        if j = k then ((p ^ k : ℕ) : ℂ)
        else if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ)
        else 0 := by
    intro j hj
    have hj_le_r : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj_le_k : j ≤ k := hj_le_r.trans hr_le
    rw [Nat.pow_div hj_le_k hp.pos]
    by_cases hjk : j = k
    · subst hjk; simp
    · by_cases hjk1 : j = k - 1
      · rw [hjk1]
        have hsub : k - (k - 1) = 1 := by omega
        simp only [hsub, pow_one, ArithmeticFunction.moebius_apply_prime hp]
        simp [show k - 1 ≠ k by omega]
      · have hsub_ge2 : 2 ≤ k - j := by omega
        have hmu0 : μ (p ^ (k - j)) = 0 := by
          rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k - j ≠ 0)]
          simp [show k - j ≠ 1 by omega]
        simp [hmu0, hjk, hjk1]
  rw [Finset.sum_congr rfl hterm]
  simp_rw [hr_iff k le_rfl, hr_iff (k - 1) (Nat.sub_le k 1)]
  by_cases hrk : k ≤ r
  · have hr_eq : r = k := le_antisymm hr_le hrk
    rw [hr_eq]
    simp only [le_rfl, ↓reduceIte]
    have hsum_k :
        ∑ j ∈ Finset.range (k + 1),
            (if j = k then ((p ^ k : ℕ) : ℂ)
              else if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ)
              else 0) =
          ((p ^ k : ℕ) : ℂ) - ((p ^ (k - 1) : ℕ) : ℂ) := by
      have hk1_mem : k - 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_range_succ]
      simp only [↓reduceIte]
      have hprev :
          ∑ j ∈ Finset.range k,
              (if j = k then ((p ^ k : ℕ) : ℂ)
                else if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ)
                else 0) =
            -((p ^ (k - 1) : ℕ) : ℂ) := by
        have hcongr :
            ∑ j ∈ Finset.range k,
                (if j = k then ((p ^ k : ℕ) : ℂ)
                  else if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ)
                  else 0) =
              ∑ j ∈ Finset.range k, if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [(Finset.mem_range.mp hj).ne, ↓reduceIte]
        rw [hcongr, Finset.sum_ite_eq']
        simp only [hk1_mem, ↓reduceIte]
      rw [hprev]
      ring
    rw [hsum_k]
    have htot : (p ^ k).totient = p ^ k - p ^ (k - 1) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [Nat.totient_prime_pow_succ hp m, Nat.succ_sub_one,
        Nat.mul_sub_left_distrib, mul_one, ← Nat.pow_succ]
    rw [htot, Nat.cast_sub (Nat.pow_le_pow_right hp.pos (by omega))]
  · by_cases hrk1 : k - 1 ≤ r
    · have hr_eq : r = k - 1 := by omega
      rw [hr_eq]
      simp only [show ¬ (k ≤ k - 1) by omega, ↓reduceIte, le_rfl]
      have hk1_mem : k - 1 ∈ Finset.range (k - 1 + 1) := Finset.mem_range.mpr (by omega)
      have hcongr :
          ∑ j ∈ Finset.range (k - 1 + 1),
              (if j = k then ((p ^ k : ℕ) : ℂ)
                else if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ)
                else 0) =
            ∑ j ∈ Finset.range (k - 1 + 1),
              if j = k - 1 then -((p ^ (k - 1) : ℕ) : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≠ k := by have := Finset.mem_range.mp hj; omega
        simp only [hjk, ↓reduceIte]
      rw [hcongr, Finset.sum_ite_eq']
      simp only [hk1_mem, ↓reduceIte]
    · simp only [hrk, ↓reduceIte, hrk1]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp only [show j ≠ k by omega, ↓reduceIte, show j ≠ k - 1 by omega]

/-- **Hölder's closed form for Ramanujan sums**:
for every `q ≥ 1` and `n : ℤ`, setting `d = Nat.gcd n.natAbs q`,
`ramanujanSum q n = μ (q / d) * q.totient / (q / d).totient`. -/
theorem ramanujanSum_eq_moebius_mul_totient {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n =
      (μ (q / Nat.gcd n.natAbs q) : ℂ) * (q.totient : ℂ) /
        ((q / Nat.gcd n.natAbs q).totient : ℂ) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp
  | prime_pow p k hp hk =>
      clear hq
      rw [ramanujanSum_prime_pow hp hk n]
      obtain ⟨r, hr_le, hd_eq⟩ :=
        (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n.natAbs (p ^ k))
      rw [hd_eq, Nat.pow_div hr_le hp.pos]
      have hr_iff : ∀ j : ℕ, j ≤ k → (p ^ j ∣ n.natAbs ↔ j ≤ r) := by
        intro j hjk
        have h1 : p ^ j ∣ Nat.gcd n.natAbs (p ^ k) ↔ p ^ j ∣ n.natAbs ∧ p ^ j ∣ p ^ k :=
          Nat.dvd_gcd_iff
        rw [hd_eq] at h1
        exact ⟨fun hjn => (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
            (h1.mpr ⟨hjn, Nat.pow_dvd_pow p hjk⟩),
          fun hjr => (Nat.pow_dvd_pow p hjr).trans (hd_eq ▸ Nat.gcd_dvd_left _ _)⟩
      simp_rw [hr_iff k le_rfl, hr_iff (k - 1) (Nat.sub_le k 1)]
      by_cases hrk : k ≤ r
      · have heq : r = k := le_antisymm hr_le hrk
        rw [heq]; simp
      · by_cases hrk1 : k - 1 ≤ r
        · have heq : r = k - 1 := by omega
          rw [heq]
          simp only [show ¬ (k ≤ k - 1) by omega, ↓reduceIte, le_rfl,
            show k - (k - 1) = 1 by omega, pow_one,
            ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [hm, Nat.totient_prime_pow_succ hp m, Nat.succ_sub_one]
          have hp1 : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
            have := hp.two_le; exact_mod_cast (by omega : p - 1 ≠ 0)
          push_cast
          field_simp [hp1]
        · have hk_ne0 : k - r ≠ 0 := by omega
          have hk_ne1 : k - r ≠ 1 := by omega
          have hmu0 : μ (p ^ (k - r)) = 0 := by
            rw [ArithmeticFunction.moebius_apply_prime_pow hp hk_ne0]
            simp [hk_ne1]
          simp [hrk, hrk1, hmu0]
  | coprime a b ha hb hcop iha ihb =>
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      rw [ramanujanSum_mul_coprime ha1 hb1 hcop, iha ha1, ihb hb1]
      set da := Nat.gcd n.natAbs a
      set db := Nat.gcd n.natAbs b
      have hgcd : Nat.gcd n.natAbs (a * b) = da * db := Nat.Coprime.gcd_mul n.natAbs hcop
      have hda_dvd : da ∣ a := Nat.gcd_dvd_right _ _
      have hdb_dvd : db ∣ b := Nat.gcd_dvd_right _ _
      have hdiv_eq : a * b / (da * db) = (a / da) * (b / db) := by
        have h1 := Nat.mul_div_cancel' hda_dvd
        have h2 := Nat.mul_div_cancel' hdb_dvd
        have hda_pos : 0 < da := Nat.gcd_pos_of_pos_right _ ha1
        have hdb_pos : 0 < db := Nat.gcd_pos_of_pos_right _ hb1
        have hm : a * b = (a / da * (b / db)) * (da * db) := by
          calc
            a * b = (da * (a / da)) * (db * (b / db)) := by rw [h1, h2]
            _ = (a / da * (b / db)) * (da * db) := by ring
        rw [hm, Nat.mul_div_cancel _ (mul_pos hda_pos hdb_pos)]
      have hq_cop : Nat.Coprime (a / da) (b / db) :=
        (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hda_dvd)).coprime_dvd_right
          (Nat.div_dvd_of_dvd hdb_dvd)
      rw [hgcd, hdiv_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hq_cop,
        Nat.totient_mul hcop, Nat.totient_mul hq_cop]
      push_cast
      ring

/-- Special case when `Nat.Coprime n.natAbs q`: `ramanujanSum q n = μ q`. -/
theorem ramanujanSum_coprime {q : ℕ} (hq : 1 ≤ q) {n : ℤ} (hcop : Nat.Coprime n.natAbs q) :
    ramanujanSum q n = (μ q : ℂ) := by
  rw [ramanujanSum_eq_moebius_mul_totient hq n]
  have hgcd : Nat.gcd n.natAbs q = 1 := hcop
  rw [hgcd, Nat.div_one]
  have htot_ne : (q.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq).ne'
  rw [mul_div_cancel_right₀ _ htot_ne]

/-- Modulus bound `‖ramanujanSum q n‖ ≤ Nat.gcd n.natAbs q` for `q ≥ 1`. -/
private lemma totient_mul_le (a b : ℕ) : (a * b).totient ≤ a * b.totient := by
  by_cases hb : b = 0
  · subst hb; simp
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
  rw [Nat.totient_eq_card_coprime, Nat.totient_eq_card_coprime]
  calc
    ((Finset.range (a * b)).filter (a * b).Coprime).card
        ≤ (Finset.range a ×ˢ (Finset.range b).filter b.Coprime).card := by
      refine Finset.card_le_card_of_injOn (fun x => (x / b, x % b)) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_product,
          Set.mem_prod, Finset.mem_coe] at hx ⊢
        refine ⟨(Nat.div_lt_iff_lt_mul hb_pos).mpr (by simpa [mul_comm] using hx.1),
          Nat.mod_lt x hb_pos, ?_⟩
        have hcop_xb : Nat.Coprime b x := hx.2.coprime_dvd_left (dvd_mul_left b a)
        refine Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_one_of_dvd_one ?_)
        have hg1 : b.gcd (x % b) ∣ b := Nat.gcd_dvd_left b (x % b)
        have hg2 : b.gcd (x % b) ∣ x := by
          have hdiv := Nat.div_add_mod x b
          exact (dvd_add (dvd_mul_of_dvd_left hg1 (x / b)) (Nat.gcd_dvd_right b (x % b))).trans
            (dvd_of_eq hdiv)
        exact hcop_xb.gcd_eq_one ▸ Nat.dvd_gcd hg1 hg2
      · intro x _ y _ hxy
        have hx_eq := Nat.div_add_mod x b
        have hy_eq := Nat.div_add_mod y b
        have h1 : x / b = y / b := congrArg Prod.fst hxy
        have h2 : x % b = y % b := congrArg Prod.snd hxy
        rw [← hx_eq, ← hy_eq, h1, h2]
    _ = a * ((Finset.range b).filter b.Coprime).card := by
      rw [Finset.card_product, Finset.card_range]

theorem norm_ramanujanSum_le_gcd {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ (Nat.gcd n.natAbs q : ℝ) := by
  rw [ramanujanSum_eq_moebius_mul_totient hq n]
  set d := Nat.gcd n.natAbs q
  set m := q / d
  have hd_dvd : d ∣ q := Nat.gcd_dvd_right _ _
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right _ hq
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hq hd_dvd) hd_pos
  have htot_m_pos : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm_pos
  have hq_eq : q = d * m := (Nat.mul_div_cancel' hd_dvd).symm
  have htot_le : q.totient ≤ d * m.totient := by
    rw [hq_eq]
    exact totient_mul_le d m
  have hmu : ‖(μ m : ℂ)‖ ≤ 1 := by
    have h1 : (|μ m| : ℝ) ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
    simpa [Complex.norm_intCast] using h1
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ htot_m_pos]
  calc
    ‖(μ m : ℂ)‖ * (q.totient : ℝ) ≤ 1 * (q.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    _ = (q.totient : ℝ) := one_mul _
    _ ≤ (d : ℝ) * (m.totient : ℝ) := by exact_mod_cast htot_le

/-- Universal modulus bound `‖ramanujanSum q n‖ ≤ q.totient`. -/
theorem norm_ramanujanSum_le_totient (q : ℕ) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ (q.totient : ℝ) := by
  unfold ramanujanSum
  refine (norm_sum_le _ _).trans_eq ?_
  have hcard : (coprimeResidues q).card = q.totient := by
    simp [coprimeResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm]
  calc
    ∑ a ∈ coprimeResidues q, ‖e ((a : ℝ) * (n : ℝ) / (q : ℝ))‖
        = ∑ _a ∈ coprimeResidues q, (1 : ℝ) := by simp [norm_e]
    _ = ((coprimeResidues q).card : ℝ) := by simp
    _ = (q.totient : ℝ) := by rw [hcard]

end RamanujanSums

section GoldbachCounts

/-- Ternary Goldbach prime-triple count: number of `(p₁, p₂, p₃) ∈ [2, N]^3` of primes
satisfying `p₁ + p₂ + p₃ = N`. -/
def goldbachTernaryCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N ×ˢ Finset.Icc 2 N ×ˢ Finset.Icc 2 N).filter fun p =>
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N).card

/-- Ternary Goldbach odd-prime count: number of `(p₁, p₂, p₃) ∈ [3, N]^3` of odd primes
satisfying `p₁ + p₂ + p₃ = N`. -/
def goldbachTernaryOddCount (N : ℕ) : ℕ :=
  ((Finset.Icc 3 N ×ˢ Finset.Icc 3 N ×ˢ Finset.Icc 3 N).filter fun p =>
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N).card

/-- Binary Goldbach prime-pair count: number of `(p₁, p₂) ∈ [2, N]^2` of primes
satisfying `p₁ + p₂ = N`. -/
def goldbachBinaryCount (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N ×ˢ Finset.Icc 2 N).filter fun p =>
    p.1.Prime ∧ p.2.Prime ∧ p.1 + p.2 = N).card

/-- Von Mangoldt weighted ternary Goldbach count
`R₃(N) = ∑_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃)`. -/
def goldbachTernaryWeighted (N : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
    if n₁ + n₂ + n₃ = N then Λ n₁ * Λ n₂ * Λ n₃ else 0

/-- Prime-only log-weighted ternary Goldbach count
`∑_{p₁ + p₂ + p₃ = N} log p₁ * log p₂ * log p₃` over primes `p_i ≥ 2`. -/
def goldbachTernaryThetaWeighted (N : ℕ) : ℝ :=
  ∑ p₁ ∈ Finset.Icc 2 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N,
    if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N then
      Real.log p₁ * Real.log p₂ * Real.log p₃
    else 0

/-- Von Mangoldt weighted binary Goldbach count
`R₂(N) = ∑_{n₁ + n₂ = N} Λ(n₁) Λ(n₂)`. -/
def goldbachBinaryWeighted (N : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
    if n₁ + n₂ = N then Λ n₁ * Λ n₂ else 0

/-- The prime exponential sum `S(α, x) = ∑_{1 ≤ n ≤ x} Λ(n) e(α n)`. -/
def primeExpSum (x : ℝ) (α : ℝ) : ℂ :=
  expSum (fun n => (Λ n : ℂ)) (Finset.Icc 1 ⌊x⌋₊) α

/-- The main approximating geometric sum `M(N, β) = ∑_{1 ≤ n ≤ N} e(β n)`. -/
def mainExpSum (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, e (β * (n : ℝ))

/-- `primeExpSum` is continuous in `α`. -/
@[fun_prop]
theorem continuous_primeExpSum (x : ℝ) : Continuous (primeExpSum x) :=
  continuous_expSum _ _

/-- `primeExpSum` is 1-periodic in `α`. -/
theorem periodic_primeExpSum (x : ℝ) : Function.Periodic (primeExpSum x) 1 :=
  periodic_expSum _ _

/-- `mainExpSum` is continuous in `β`. -/
@[fun_prop]
theorem continuous_mainExpSum (N : ℕ) : Continuous (mainExpSum N) := by
  unfold mainExpSum
  refine continuous_finsetSum _ fun n _ => ?_
  exact continuous_e.comp (continuous_id.mul continuous_const)

/-- `mainExpSum` is 1-periodic in `β`. -/
theorem periodic_mainExpSum (N : ℕ) : Function.Periodic (mainExpSum N) 1 := by
  intro β
  unfold mainExpSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := e_periodic_mul_nat n β
  dsimp only at h
  exact h

/-- Trivial upper bound `‖primeExpSum x α‖ ≤ Chebyshev.psi x` for `x ≥ 0`. -/
theorem norm_primeExpSum_le_psi {x : ℝ} (_hx : 0 ≤ x) (α : ℝ) :
    ‖primeExpSum x α‖ ≤ Chebyshev.psi x := by
  unfold primeExpSum
  refine (norm_expSum_le _ _ _).trans_eq ?_
  have hnorm : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(Λ n : ℂ)‖ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hnorm, psi_eq_sum_Icc]

/-- Trivial upper bound `‖primeExpSum x α‖ ≤ 6 * x` for `x ≥ 0`. -/
theorem norm_primeExpSum_le {x : ℝ} (hx : 0 ≤ x) (α : ℝ) :
    ‖primeExpSum x α‖ ≤ 6 * x := by
  refine (norm_primeExpSum_le_psi hx α).trans ((psi_le_const_mul_self hx).trans ?_)
  have hlog4 : Real.log 4 < 2 := by
    have hexp2 : (4 : ℝ) < Real.exp 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    rw [← Real.log_exp 2]
    exact Real.log_lt_log (by norm_num) hexp2
  nlinarith

/-- Trivial upper bound `‖mainExpSum N β‖ ≤ N`. -/
theorem norm_mainExpSum_le (N : ℕ) (β : ℝ) : ‖mainExpSum N β‖ ≤ (N : ℝ) := by
  unfold mainExpSum
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- Circle-method integral representation of `goldbachTernaryWeighted N`. -/
theorem goldbachTernaryWeighted_eq_representationIntegral (N : ℕ) :
    (goldbachTernaryWeighted N : ℂ) =
      representationIntegral (fun α => primeExpSum N α ^ 3 * e (-α * (N : ℝ))) := by
  unfold goldbachTernaryWeighted representationIntegral primeExpSum
  rw [Nat.floor_natCast, integral_expSum_pow_three_mul_e_neg]
  push_cast
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ =>
    Finset.sum_congr rfl fun n₃ _ => ?_
  split_ifs <;> simp

/-- Circle-method integral representation of `goldbachBinaryWeighted N`. -/
theorem goldbachBinaryWeighted_eq_representationIntegral (N : ℕ) :
    (goldbachBinaryWeighted N : ℂ) =
      representationIntegral (fun α => primeExpSum N α ^ 2 * e (-α * (N : ℝ))) := by
  unfold goldbachBinaryWeighted representationIntegral primeExpSum
  rw [Nat.floor_natCast]
  have hpow : ∀ α : ℝ,
      expSum (fun n => (Λ n : ℂ)) (Finset.Icc 1 N) α ^ 2 =
        expSum (fun n => (Λ n : ℂ)) (Finset.Icc 1 N) α *
          expSum (fun n => (Λ n : ℂ)) (Finset.Icc 1 N) α := fun α => sq _
  simp_rw [hpow, integral_expSum_mul_expSum_mul_e_neg]
  push_cast
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  split_ifs <;> simp

/-- Upper bound `goldbachTernaryThetaWeighted N ≤ (log N)^3 * goldbachTernaryCount N` for `N ≥ 1`. -/
theorem goldbachTernaryThetaWeighted_le_log_cube_mul_count {N : ℕ} (hN : 1 ≤ N) :
    goldbachTernaryThetaWeighted N ≤ (Real.log N) ^ 3 * (goldbachTernaryCount N : ℝ) := by
  unfold goldbachTernaryThetaWeighted goldbachTernaryCount
  have hlog_nonneg : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hrewrite :
      ∑ p₁ ∈ Finset.Icc 2 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N,
          (if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N then
            Real.log p₁ * Real.log p₂ * Real.log p₃
          else 0) =
        ∑ p ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N ×ˢ Finset.Icc 2 N).filter (fun p =>
          p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N),
          Real.log p.1 * Real.log p.2.1 * Real.log p.2.2 := by
    simp_rw [Finset.sum_filter, Finset.sum_product]
  rw [hrewrite]
  have hterm : ∀ p ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N ×ˢ Finset.Icc 2 N).filter (fun p =>
        p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N),
      Real.log p.1 * Real.log p.2.1 * Real.log p.2.2 ≤ (Real.log N) ^ 3 := by
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
      Finset.mem_Icc] at hmem
    have hl1 : Real.log p.1 ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p.1)) (by exact_mod_cast hmem.1.2)
    have hl2 : Real.log p.2.1 ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p.2.1)) (by exact_mod_cast hmem.2.1.2)
    have hl3 : Real.log p.2.2 ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p.2.2)) (by exact_mod_cast hmem.2.2.2)
    have hl1_nn : 0 ≤ Real.log p.1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.1))
    have hl2_nn : 0 ≤ Real.log p.2.1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.2.1))
    have hl3_nn : 0 ≤ Real.log p.2.2 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.2.2))
    calc
      Real.log p.1 * Real.log p.2.1 * Real.log p.2.2
          ≤ Real.log N * Real.log N * Real.log N :=
        mul_le_mul (mul_le_mul hl1 hl2 hl2_nn hlog_nonneg) hl3 hl3_nn
          (mul_nonneg hlog_nonneg hlog_nonneg)
      _ = (Real.log N) ^ 3 := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  simp [mul_comm]

/-- Helper bounding `∑_{n₂ ≤ N} ∑_{n₃ ≤ N} 1_{n₁+n₂+n₃=N} Λ(n₂) Λ(n₃) ≤ 6 * N * log N`. -/
private lemma sum_pair_vonMangoldt_le {N : ℕ} (hN : 2 ≤ N) (n₁ : ℕ) :
    (∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
        if n₁ + n₂ + n₃ = N then Λ n₂ * Λ n₃ else 0) ≤
      6 * (N : ℝ) * Real.log N := by
  have hlogN_nn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hinner : ∀ n₂ ∈ Finset.Icc 1 N,
      (∑ n₃ ∈ Finset.Icc 1 N, if n₁ + n₂ + n₃ = N then Λ n₂ * Λ n₃ else 0) ≤
        Λ n₂ * Real.log N := by
    intro n₂ _
    by_cases hle : n₁ + n₂ < N
    · set m := N - (n₁ + n₂)
      have hm_mem : m ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hcongr :
          (∑ n₃ ∈ Finset.Icc 1 N, if n₁ + n₂ + n₃ = N then Λ n₂ * Λ n₃ else 0) =
            ∑ n₃ ∈ Finset.Icc 1 N, if n₃ = m then Λ n₂ * Λ m else 0 := by
        refine Finset.sum_congr rfl fun n₃ _ => ?_
        by_cases heq : n₃ = m
        · subst heq; simp [m, show n₁ + n₂ + (N - (n₁ + n₂)) = N by omega]
        · simp only [heq, ↓reduceIte, show n₁ + n₂ + n₃ ≠ N by omega]
      rw [hcongr, Finset.sum_ite_eq']
      simp only [hm_mem, ↓reduceIte]
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      have hm_le_N : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : m ≤ N)
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hm_pos hm_le_N)
    · have hzero : (∑ n₃ ∈ Finset.Icc 1 N, if n₁ + n₂ + n₃ = N then Λ n₂ * Λ n₃ else 0) = 0 := by
        refine Finset.sum_eq_zero fun n₃ hn₃ => ?_
        have hn3_pos := (Finset.mem_Icc.mp hn₃).1
        simp only [show n₁ + n₂ + n₃ ≠ N by omega, ↓reduceIte]
      rw [hzero]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlogN_nn
  refine (Finset.sum_le_sum hinner).trans ?_
  have hsum_lam : ∑ n ∈ Finset.Icc 1 N, Λ n = Chebyshev.psi (N : ℝ) := by
    rw [psi_eq_sum_Icc (N : ℝ), Nat.floor_natCast]
  rw [← Finset.sum_mul, hsum_lam]
  have hpsi : Chebyshev.psi (N : ℝ) ≤ 6 * (N : ℝ) := by
    have hlog4 : Real.log 4 < 2 := by
      have hexp2 : (4 : ℝ) < Real.exp 2 := by
        have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      rw [← Real.log_exp 2]
      exact Real.log_lt_log (by norm_num) hexp2
    exact (psi_le_const_mul_self (Nat.cast_nonneg N)).trans (by nlinarith)
  exact mul_le_mul_of_nonneg_right hpsi hlogN_nn

/-- Comparison between von Mangoldt weighted count `goldbachTernaryWeighted N` and prime-only
count `goldbachTernaryThetaWeighted N`:
`goldbachTernaryWeighted N - goldbachTernaryThetaWeighted N ≤ 324 * N^(3/2) * log N` for `N ≥ 2`. -/
theorem goldbachTernaryWeighted_sub_thetaWeighted_le {N : ℕ} (hN : 2 ≤ N) :
    goldbachTernaryWeighted N - goldbachTernaryThetaWeighted N ≤
      324 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by
  have hlogN_nn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  let R : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n
  have hR_nn : ∀ n, 0 ≤ R n := fun n => by
    dsimp [R]; split_ifs <;> [exact le_rfl; exact ArithmeticFunction.vonMangoldt_nonneg]
  have hsum_R : ∑ n ∈ Finset.Icc 1 N, R n ≤ 18 * Real.sqrt N := by
    have hcongr : ∑ n ∈ Finset.Icc 1 N, R n =
        (∑ n ∈ Finset.Icc 1 N, Λ n) - ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p := by
      have hsub_prime :
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p =
            ∑ n ∈ Finset.Icc 1 N, if n.Prime then Λ n else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs with hp
        · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
        · rfl
      rw [hsub_prime, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [R]
      split_ifs <;> ring
    rw [hcongr]
    have hpsi_eq : ∑ n ∈ Finset.Icc 1 N, Λ n = Chebyshev.psi (N : ℝ) := by
      rw [psi_eq_sum_Icc (N : ℝ), Nat.floor_natCast]
    have htheta_eq :
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p = Chebyshev.theta (N : ℝ) := by
      rw [theta_eq_sum_Icc (N : ℝ), Nat.floor_natCast]
    rw [hpsi_eq, htheta_eq]
    have hbd := abs_psi_sub_theta_le_mul_sqrt (N : ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr (theta_le_psi _))] at hbd
    have hlog4 : Real.log 4 < 2 := by
      have hexp2 : (4 : ℝ) < Real.exp 2 := by
        have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      rw [← Real.log_exp 2]
      exact Real.log_lt_log (by norm_num) hexp2
    exact hbd.trans (by nlinarith [Real.sqrt_nonneg (N : ℝ)])
  have htheta_split :
      goldbachTernaryThetaWeighted N =
        ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
          if n₁.Prime ∧ n₂.Prime ∧ n₃.Prime ∧ n₁ + n₂ + n₃ = N then
            Λ n₁ * Λ n₂ * Λ n₃
          else 0 := by
    unfold goldbachTernaryThetaWeighted
    have hIcc_sub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := fun x hx => by
      simp only [Finset.mem_Icc] at hx ⊢; omega
    have hcongr : ∀ n₁ n₂ n₃ : ℕ,
        (if n₁.Prime ∧ n₂.Prime ∧ n₃.Prime ∧ n₁ + n₂ + n₃ = N then
          Λ n₁ * Λ n₂ * Λ n₃ else 0) =
        (if n₁.Prime ∧ n₂.Prime ∧ n₃.Prime ∧ n₁ + n₂ + n₃ = N then
          Real.log n₁ * Real.log n₂ * Real.log n₃ else 0) := by
      intro n₁ n₂ n₃
      split_ifs with h
      · rw [ArithmeticFunction.vonMangoldt_apply_prime h.1,
          ArithmeticFunction.vonMangoldt_apply_prime h.2.1,
          ArithmeticFunction.vonMangoldt_apply_prime h.2.2.1]
      · rfl
    simp_rw [hcongr]
    rw [← Finset.sum_subset hIcc_sub (fun x hx1 hx2 => by
      have hx_lt : x < 2 := by simp only [Finset.mem_Icc] at hx1 hx2; omega
      have hnp : ¬ x.Prime := fun hp => by linarith [hp.two_le]
      simp [hnp])]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [← Finset.sum_subset hIcc_sub (fun y hy1 hy2 => by
      have hy_lt : y < 2 := by simp only [Finset.mem_Icc] at hy1 hy2; omega
      have hnp : ¬ y.Prime := fun hp => by linarith [hp.two_le]
      simp [hnp])]
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    rw [← Finset.sum_subset hIcc_sub (fun z hz1 hz2 => by
      have hz_lt : z < 2 := by simp only [Finset.mem_Icc] at hz1 hz2; omega
      have hnp : ¬ z.Prime := fun hp => by linarith [hp.two_le]
      simp [hnp])]
  rw [goldbachTernaryWeighted, htheta_split, ← Finset.sum_sub_distrib]
  have hpoint :
      ∑ x ∈ Finset.Icc 1 N,
        ((∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if x + n₂ + n₃ = N then Λ x * Λ n₂ * Λ n₃ else 0) -
          (∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if x.Prime ∧ n₂.Prime ∧ n₃.Prime ∧ x + n₂ + n₃ = N then
              Λ x * Λ n₂ * Λ n₃ else 0)) ≤
        ∑ n₁ ∈ Finset.Icc 1 N, R n₁ * (6 * (N : ℝ) * Real.log N) +
          ∑ n₂ ∈ Finset.Icc 1 N, R n₂ * (6 * (N : ℝ) * Real.log N) +
          ∑ n₃ ∈ Finset.Icc 1 N, R n₃ * (6 * (N : ℝ) * Real.log N) := by
    have hcomb :
        (∑ x ∈ Finset.Icc 1 N,
          ((∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if x + n₂ + n₃ = N then Λ x * Λ n₂ * Λ n₃ else 0) -
            (∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if x.Prime ∧ n₂.Prime ∧ n₃.Prime ∧ x + n₂ + n₃ = N then
                Λ x * Λ n₂ * Λ n₃ else 0))) ≤
          ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if n₁ + n₂ + n₃ = N then
              R n₁ * (Λ n₂ * Λ n₃) + R n₂ * (Λ n₁ * Λ n₃) + R n₃ * (Λ n₁ * Λ n₂)
            else 0 := by
      refine Finset.sum_le_sum fun n₁ _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun n₂ _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun n₃ _ => ?_
      by_cases hsum : n₁ + n₂ + n₃ = N
      · have hnn12 : 0 ≤ Λ n₁ * Λ n₂ :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
        have hnn13 : 0 ≤ Λ n₁ * Λ n₃ :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
        have hnn23 : 0 ≤ Λ n₂ * Λ n₃ :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
        by_cases h1 : n₁.Prime <;> by_cases h2 : n₂.Prime <;> by_cases h3 : n₃.Prime <;>
          simp [R, h1, h2, h3, hsum] <;>
          nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n₁),
            ArithmeticFunction.vonMangoldt_nonneg (n := n₂),
            ArithmeticFunction.vonMangoldt_nonneg (n := n₃)]
      · simp [hsum]
    refine hcomb.trans ?_
    have hsplit_ite : ∀ n₁ n₂ n₃ : ℕ,
        (if n₁ + n₂ + n₃ = N then
          R n₁ * (Λ n₂ * Λ n₃) + R n₂ * (Λ n₁ * Λ n₃) + R n₃ * (Λ n₁ * Λ n₂)
        else 0) =
        (if n₁ + n₂ + n₃ = N then R n₁ * (Λ n₂ * Λ n₃) else 0) +
        (if n₁ + n₂ + n₃ = N then R n₂ * (Λ n₁ * Λ n₃) else 0) +
        (if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else 0) := by
      intro n₁ n₂ n₃; split_ifs <;> ring
    simp_rw [hsplit_ite, Finset.sum_add_distrib]
    have h1_bd :
        (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if n₁ + n₂ + n₃ = N then R n₁ * (Λ n₂ * Λ n₃) else 0) ≤
          ∑ n₁ ∈ Finset.Icc 1 N, R n₁ * (6 * (N : ℝ) * Real.log N) := by
      refine Finset.sum_le_sum fun n₁ _ => ?_
      have hpull :
          (∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₁ * (Λ n₂ * Λ n₃) else 0) =
            R n₁ * ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then Λ n₂ * Λ n₃ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₃ _ => ?_
        split_ifs <;> ring
      rw [hpull]
      exact mul_le_mul_of_nonneg_left (sum_pair_vonMangoldt_le hN n₁) (hR_nn n₁)
    have h2_bd :
        (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if n₁ + n₂ + n₃ = N then R n₂ * (Λ n₁ * Λ n₃) else 0) ≤
          ∑ n₂ ∈ Finset.Icc 1 N, R n₂ * (6 * (N : ℝ) * Real.log N) := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun n₂ _ => ?_
      have hpull :
          (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₂ * (Λ n₁ * Λ n₃) else 0) =
            R n₂ * ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₂ + n₁ + n₃ = N then Λ n₁ * Λ n₃ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₃ _ => ?_
        have hcomm : n₁ + n₂ + n₃ = N ↔ n₂ + n₁ + n₃ = N := by omega
        simp only [hcomm]
        split_ifs <;> ring
      rw [hpull]
      exact mul_le_mul_of_nonneg_left (sum_pair_vonMangoldt_le hN n₂) (hR_nn n₂)
    have h3_bd :
        (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
            if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else 0) ≤
          ∑ n₃ ∈ Finset.Icc 1 N, R n₃ * (6 * (N : ℝ) * Real.log N) := by
      have hswap :
          (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else 0) =
            ∑ n₃ ∈ Finset.Icc 1 N, ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else 0 := by
        calc
          (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else (0 : ℝ))
              = ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₃ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
                  if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else (0 : ℝ) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ n₃ ∈ Finset.Icc 1 N, ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
                if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else (0 : ℝ) := Finset.sum_comm
      rw [hswap]
      refine Finset.sum_le_sum fun n₃ _ => ?_
      have hpull :
          (∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
              if n₁ + n₂ + n₃ = N then R n₃ * (Λ n₁ * Λ n₂) else 0) =
            R n₃ * ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
              if n₃ + n₁ + n₂ = N then Λ n₁ * Λ n₂ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₂ _ => ?_
        have hcomm : n₁ + n₂ + n₃ = N ↔ n₃ + n₁ + n₂ = N := by omega
        simp only [hcomm]
        split_ifs <;> ring
      rw [hpull]
      exact mul_le_mul_of_nonneg_left (sum_pair_vonMangoldt_le hN n₃) (hR_nn n₃)
    linarith
  refine hpoint.trans ?_
  rw [← Finset.sum_mul]
  have hmul_bd : (∑ n ∈ Finset.Icc 1 N, R n) * (6 * (N : ℝ) * Real.log N) ≤
      (18 * Real.sqrt N) * (6 * (N : ℝ) * Real.log N) :=
    mul_le_mul_of_nonneg_right hsum_R (by positivity)
  have hpow : Real.sqrt N * (N : ℝ) = (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    conv_lhs => rhs; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N))]
    norm_num
  calc
    (∑ n ∈ Finset.Icc 1 N, R n) * (6 * (N : ℝ) * Real.log N) +
        (∑ n ∈ Finset.Icc 1 N, R n) * (6 * (N : ℝ) * Real.log N) +
        (∑ n ∈ Finset.Icc 1 N, R n) * (6 * (N : ℝ) * Real.log N)
        = 3 * ((∑ n ∈ Finset.Icc 1 N, R n) * (6 * (N : ℝ) * Real.log N)) := by ring
    _ ≤ 3 * ((18 * Real.sqrt N) * (6 * (N : ℝ) * Real.log N)) := by linarith
    _ = 324 * (Real.sqrt N * (N : ℝ)) * Real.log N := by ring
    _ = 324 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by rw [hpow]

/-- Bounds the difference between `goldbachTernaryThetaWeighted N` and the odd-prime count
`(log N)^3 * goldbachTernaryOddCount N` by `3 * N * (log N)^2`. -/
theorem goldbachTernaryThetaWeighted_sub_odd_le {N : ℕ} (hN : 2 ≤ N) :
    goldbachTernaryThetaWeighted N - (Real.log N) ^ 3 * (goldbachTernaryOddCount N : ℝ) ≤
      3 * (N : ℝ) * (Real.log N) ^ 2 := by
  have hlogN_nn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hodd_bound :
      (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N,
          if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N then
            Real.log p₁ * Real.log p₂ * Real.log p₃
          else 0) ≤
        (Real.log N) ^ 3 * (goldbachTernaryOddCount N : ℝ) := by
    unfold goldbachTernaryOddCount
    have hrewrite :
        (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N,
            if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N then
              Real.log p₁ * Real.log p₂ * Real.log p₃
            else 0) =
          ∑ p ∈ (Finset.Icc 3 N ×ˢ Finset.Icc 3 N ×ˢ Finset.Icc 3 N).filter (fun p =>
            p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N),
            Real.log p.1 * Real.log p.2.1 * Real.log p.2.2 := by
      simp_rw [Finset.sum_filter, Finset.sum_product]
    rw [hrewrite]
    have hsum_bd :
        (∑ p ∈ (Finset.Icc 3 N ×ˢ Finset.Icc 3 N ×ˢ Finset.Icc 3 N).filter (fun p =>
            p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N),
            Real.log p.1 * Real.log p.2.1 * Real.log p.2.2) ≤
          ∑ _p ∈ (Finset.Icc 3 N ×ˢ Finset.Icc 3 N ×ˢ Finset.Icc 3 N).filter (fun p =>
            p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N),
            (Real.log N) ^ 3 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hmem := (Finset.mem_filter.mp hp).1
      rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
        Finset.mem_Icc] at hmem
      have hl1 : Real.log p.1 ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < p.1)) (by exact_mod_cast hmem.1.2)
      have hl2 : Real.log p.2.1 ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < p.2.1)) (by exact_mod_cast hmem.2.1.2)
      have hl3 : Real.log p.2.2 ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < p.2.2)) (by exact_mod_cast hmem.2.2.2)
      have hl1_nn : 0 ≤ Real.log p.1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.1))
      have hl2_nn : 0 ≤ Real.log p.2.1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.2.1))
      have hl3_nn : 0 ≤ Real.log p.2.2 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.2.2))
      calc
        Real.log p.1 * Real.log p.2.1 * Real.log p.2.2
            ≤ Real.log N * Real.log N * Real.log N :=
          mul_le_mul (mul_le_mul hl1 hl2 hl2_nn hlogN_nn) hl3 hl3_nn
            (mul_nonneg hlogN_nn hlogN_nn)
        _ = (Real.log N) ^ 3 := by ring
    exact hsum_bd.trans_eq (by rw [Finset.sum_const, nsmul_eq_mul, mul_comm])
  have hpair : ∀ c : ℕ, 2 ≤ c →
      (∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N,
          if c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N then
            Real.log c * Real.log p₂ * Real.log p₃ else 0) ≤
        Real.log c * (N : ℝ) * (Real.log N) ^ 2 := by
    intro c hc
    have hc_nn : 0 ≤ Real.log c := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
    have hinner : ∀ p₂ ∈ Finset.Icc 2 N,
        (∑ p₃ ∈ Finset.Icc 2 N,
            if c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N then
              Real.log c * Real.log p₂ * Real.log p₃ else 0) ≤
          Real.log c * (Real.log N) ^ 2 := by
      intro p₂ hp₂
      have hp2_ge := (Finset.mem_Icc.mp hp₂).1
      have hp2_le := (Finset.mem_Icc.mp hp₂).2
      by_cases hlt : c + p₂ + 2 ≤ N
      · set m := N - (c + p₂)
        have hm_mem : m ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hcongr :
            (∑ p₃ ∈ Finset.Icc 2 N,
                if c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N then
                  Real.log c * Real.log p₂ * Real.log p₃ else 0) =
              ∑ p₃ ∈ Finset.Icc 2 N,
                if p₃ = m then
                  if c.Prime ∧ p₂.Prime ∧ m.Prime then
                    Real.log c * Real.log p₂ * Real.log m else 0
                else 0 := by
          refine Finset.sum_congr rfl fun p₃ _ => ?_
          by_cases heq : p₃ = m
          · subst heq; simp [m, show c + p₂ + (N - (c + p₂)) = N by omega]
          · simp only [heq, ↓reduceIte, show ¬ (c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N)
              by intro h; omega]
        rw [hcongr, Finset.sum_ite_eq']
        simp only [hm_mem, ↓reduceIte]
        split_ifs
        · have hl2 : Real.log p₂ ≤ Real.log N :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < p₂)) (by exact_mod_cast hp2_le)
          have hlm : Real.log m ≤ Real.log N :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast (by omega : m ≤ N))
          have hl2_nn : 0 ≤ Real.log p₂ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p₂))
          have hlm_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
          calc
            Real.log c * Real.log p₂ * Real.log m
                = Real.log c * (Real.log p₂ * Real.log m) := by ring
            _ ≤ Real.log c * (Real.log N * Real.log N) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hl2 hlm hlm_nn hlogN_nn) hc_nn
            _ = Real.log c * (Real.log N) ^ 2 := by ring
        · positivity
      · have hz : (∑ p₃ ∈ Finset.Icc 2 N,
            if c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N then
              Real.log c * Real.log p₂ * Real.log p₃ else 0) = 0 := by
          refine Finset.sum_eq_zero fun p₃ hp₃ => ?_
          have hp3_ge := (Finset.mem_Icc.mp hp₃).1
          simp only [show ¬ (c.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ c + p₂ + p₃ = N) by intro h; omega,
            ↓reduceIte]
        rw [hz]; positivity
    refine (Finset.sum_le_sum hinner).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((N + 1 - 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    calc
      ((N + 1 - 2 : ℕ) : ℝ) * (Real.log c * (Real.log N) ^ 2)
          ≤ (N : ℝ) * (Real.log c * (Real.log N) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Real.log c * (N : ℝ) * (Real.log N) ^ 2 := by ring
  have hlog2_le : Real.log 2 ≤ 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hIcc3_sub : Finset.Icc 3 N ⊆ Finset.Icc 2 N := fun x hx => by
    simp only [Finset.mem_Icc] at hx ⊢; omega
  let F : ℕ → ℕ → ℕ → ℝ := fun p₁ p₂ p₃ =>
    if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N then
      Real.log p₁ * Real.log p₂ * Real.log p₃
    else 0
  have hF_nn : ∀ p₁ p₂ p₃ : ℕ, 2 ≤ p₁ → 2 ≤ p₂ → 2 ≤ p₃ → 0 ≤ F p₁ p₂ p₃ := by
    intro p₁ p₂ p₃ h1 h2 h3
    dsimp [F]
    split_ifs
    · have hp1r : (1 : ℝ) ≤ p₁ := by exact_mod_cast (by omega : 1 ≤ p₁)
      have hp2r : (1 : ℝ) ≤ p₂ := by exact_mod_cast (by omega : 1 ≤ p₂)
      have hp3r : (1 : ℝ) ≤ p₃ := by exact_mod_cast (by omega : 1 ≤ p₃)
      have := Real.log_nonneg hp1r
      have := Real.log_nonneg hp2r
      have := Real.log_nonneg hp3r
      positivity
    · exact le_rfl
  have hF_sym12 : ∀ a b c : ℕ, F a b c = F b a c := by
    intro a b c
    dsimp [F]
    have hsum : a + b + c = N ↔ b + a + c = N := by omega
    have hc : (a.Prime ∧ b.Prime ∧ c.Prime ∧ a + b + c = N) ↔
        (b.Prime ∧ a.Prime ∧ c.Prime ∧ b + a + c = N) := by tauto
    simp only [hc]
    split_ifs <;> ring
  have hF_sym13 : ∀ a b c : ℕ, F a b c = F c b a := by
    intro a b c
    dsimp [F]
    have hsum : a + b + c = N ↔ c + b + a = N := by omega
    have hc : (a.Prime ∧ b.Prime ∧ c.Prime ∧ a + b + c = N) ↔
        (c.Prime ∧ b.Prime ∧ a.Prime ∧ c + b + a = N) := by tauto
    simp only [hc]
    split_ifs <;> ring
  have hpair2 : (∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F 2 p₂ p₃) ≤
      (N : ℝ) * (Real.log N) ^ 2 := by
    have h2 := hpair 2 le_rfl
    have hmul : Real.log 2 * (N : ℝ) * (Real.log N) ^ 2 ≤ (N : ℝ) * (Real.log N) ^ 2 := by
      have : 0 ≤ (N : ℝ) * (Real.log N) ^ 2 := by positivity
      nlinarith [hlog2_le]
    exact h2.trans hmul
  have hIcc2 : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot2 : (2 : ℕ) ∉ Finset.Icc 3 N := by
    simp only [Finset.mem_Icc]; omega
  have herase2 : (Finset.Icc 2 N).erase 2 = Finset.Icc 3 N := by
    rw [hIcc2, Finset.erase_insert hnot2]
  have h2mem : (2 : ℕ) ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hdiff : goldbachTernaryThetaWeighted N -
      ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃ ≤
      3 * (N : ℝ) * (Real.log N) ^ 2 := by
    have hstep1 :
        goldbachTernaryThetaWeighted N ≤
          (N : ℝ) * (Real.log N) ^ 2 +
            ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃ := by
      change (∑ p₁ ∈ Finset.Icc 2 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) ≤ _
      rw [← Finset.add_sum_erase _ _ h2mem, herase2]
      exact add_le_add hpair2 le_rfl
    have hstep2 :
        (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) ≤
          (N : ℝ) * (Real.log N) ^ 2 +
            ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃ := by
      have hsplit : ∀ p₁ ∈ Finset.Icc 3 N,
          (∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) =
            (∑ p₃ ∈ Finset.Icc 2 N, F p₁ 2 p₃) +
              ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃ := by
        intro p₁ _
        rw [← Finset.add_sum_erase _ _ h2mem, herase2]
      have hcongr :
          (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) =
            (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ 2 p₃) +
              ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃ := by
        calc
          ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃
              = ∑ p₁ ∈ Finset.Icc 3 N, ((∑ p₃ ∈ Finset.Icc 2 N, F p₁ 2 p₃) +
                  ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) :=
            Finset.sum_congr rfl fun p₁ hp₁ => hsplit p₁ hp₁
          _ = _ := Finset.sum_add_distrib
      rw [hcongr]
      refine add_le_add ?_ le_rfl
      have hle2 :
          (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ 2 p₃) ≤
            ∑ p₁ ∈ Finset.Icc 2 N, ∑ p₃ ∈ Finset.Icc 2 N, F 2 p₁ p₃ := by
        have hswap :
            (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ 2 p₃) =
              ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F 2 p₁ p₃ :=
          Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₃ _ => hF_sym12 p₁ 2 p₃
        rw [hswap]
        exact Finset.sum_le_sum_of_subset_of_nonneg hIcc3_sub fun p₁ hp₁ _ =>
          Finset.sum_nonneg fun p₃ hp₃ =>
            hF_nn 2 p₁ p₃ le_rfl (Finset.mem_Icc.mp hp₁).1 (Finset.mem_Icc.mp hp₃).1
      exact hle2.trans hpair2
    have hstep3 :
        (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) ≤
          (N : ℝ) * (Real.log N) ^ 2 +
            ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃ := by
      have hsplit : ∀ p₁ ∈ Finset.Icc 3 N, ∀ p₂ ∈ Finset.Icc 3 N,
          (∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) =
            F p₁ p₂ 2 + ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃ := by
        intro p₁ _ p₂ _
        rw [hIcc2, Finset.sum_insert hnot2]
      have hcongr :
          (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃) =
            (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, F p₁ p₂ 2) +
              ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃ := by
        calc
          ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 2 N, F p₁ p₂ p₃
              = ∑ p₁ ∈ Finset.Icc 3 N,
                  ∑ p₂ ∈ Finset.Icc 3 N, (F p₁ p₂ 2 + ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃) :=
            Finset.sum_congr rfl fun p₁ hp₁ => Finset.sum_congr rfl fun p₂ hp₂ =>
              hsplit p₁ hp₁ p₂ hp₂
          _ = _ := by simp_rw [Finset.sum_add_distrib]
      rw [hcongr]
      refine add_le_add ?_ le_rfl
      have hle3 :
          (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, F p₁ p₂ 2) ≤
            ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₁ ∈ Finset.Icc 2 N, F 2 p₂ p₁ := by
        have hswap :
            (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, F p₁ p₂ 2) =
              ∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, F 2 p₂ p₁ :=
          Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => hF_sym13 p₁ p₂ 2
        rw [hswap, Finset.sum_comm]
        calc
          ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₁ ∈ Finset.Icc 3 N, F 2 p₂ p₁
              ≤ ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₁ ∈ Finset.Icc 2 N, F 2 p₂ p₁ := by
            refine Finset.sum_le_sum fun p₂ hp₂ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg hIcc3_sub fun p₁ hp₁ _ =>
              hF_nn 2 p₂ p₁ le_rfl (by have := (Finset.mem_Icc.mp hp₂).1; omega)
                (Finset.mem_Icc.mp hp₁).1
          _ ≤ ∑ p₂ ∈ Finset.Icc 2 N, ∑ p₁ ∈ Finset.Icc 2 N, F 2 p₂ p₁ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hIcc3_sub fun p₂ hp₂ _ =>
              Finset.sum_nonneg fun p₁ hp₁ =>
                hF_nn 2 p₂ p₁ le_rfl (Finset.mem_Icc.mp hp₂).1 (Finset.mem_Icc.mp hp₁).1
      exact hle3.trans hpair2
    change _ - (∑ p₁ ∈ Finset.Icc 3 N, ∑ p₂ ∈ Finset.Icc 3 N, ∑ p₃ ∈ Finset.Icc 3 N, F p₁ p₂ p₃) ≤ _
    linarith
  linarith

end GoldbachCounts

section MinorArcs

/-- Uniform bound for the prime exponential sum on the minor arcs. The lower bound on the
denominator controls the first term, and its upper bound controls the third. -/
theorem norm_primeExpSum_le_on_minorArcs {x P Q α : ℝ} (hx : 2 ≤ x) (hP : 1 ≤ P)
    (hPQ : 2 * P ≤ Q) (hα : α ∈ minorArcs P Q) :
    ‖primeExpSum x α‖ ≤ 10000 * (x * P ^ (-(1 / 2 : ℝ)) + x ^ (4 / 5 : ℝ) +
      x ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log x) ^ 4 := by
  obtain ⟨a, q, hPq, hqQ, hcop, happ⟩ := mem_minorArcs_approx hP hPQ hα
  have hq : 1 ≤ q := by exact_mod_cast (hP.trans hPq.le)
  have hqpos : (0 : ℝ) < q := by linarith
  have hxpos : 0 < x := by linarith
  have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 :=
    happ.trans (one_div_le_one_div_of_le (sq_pos_of_pos hqpos) (by rw [sq]; gcongr))
  apply (vinogradov_prime_exp_sum_bound hq hcop happ' hx).trans
  have hfirst := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < P) hPq.le
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hthird := Real.rpow_le_rpow hqpos.le hqQ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  gcongr

/-- Parseval's identity bounds the second moment of the prime exponential sum by
`ψ(x) log x`. -/
theorem integral_norm_sq_primeExpSum_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ α in (0 : ℝ)..1, ‖primeExpSum x α‖ ^ 2 ≤ Chebyshev.psi x * Real.log x := by
  unfold primeExpSum
  rw [integral_norm_sq_expSum, psi_eq_sum_Icc, Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnx' : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp hnx
  rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, sq]
  exact mul_le_mul_of_nonneg_left (ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log hn_pos hnx')) ArithmeticFunction.vonMangoldt_nonneg

/-- Ternary Goldbach minor-arc estimate from Vaughan's bound and Parseval's identity. -/
theorem norm_goldbachTernary_minorArcIntegral_le {N : ℕ} (hN : 2 ≤ N) {P Q : ℝ}
    (hP : 1 ≤ P) (hPQ : 2 * P ≤ Q) :
    ‖∫ α in minorArcs P Q, primeExpSum N α ^ 3 * e (-α * (N : ℝ))‖ ≤
      10000 * (N * P ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
        (N : ℝ) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log N) ^ 4 *
        (Chebyshev.psi N * Real.log N) := by
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ : 0 ≤ Q := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hM : 0 ≤ 10000 * (N * P ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
      (N : ℝ) ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * (Real.log N) ^ 4 := by positivity
  have h := norm_minorArcIntegral_mul_pow_e_neg_le_of_bound
    (continuous_primeExpSum N) (continuous_primeExpSum N) (periodic_primeExpSum N) hM
    (fun _ hα => norm_primeExpSum_le_on_minorArcs hx hP hPQ hα) 3 (N : ℤ)
  simp only [Nat.reduceSub, Int.cast_natCast, ← pow_succ'] at h
  exact h.trans (mul_le_mul_of_nonneg_left (integral_norm_sq_primeExpSum_le (by linarith)) hM)

end MinorArcs

section SingularSeriesAndPositivity

/-- Auxiliary elementary bound: for every prime `p ≥ 5` and `k ≥ 1`,
`p ^ (3 * k) ≤ (p ^ (k - 1) * (p - 1)) ^ 4`. -/
private lemma prime_pow_cube_le_totient_pow_four {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 1 ≤ k) :
    p ^ (3 * k) ≤ (p ^ (k - 1) * (p - 1)) ^ 4 := by
  have h1 : p ^ 3 ≤ (p - 1) ^ 4 := by
    have hp_eq : p = (p - 5) + 5 := by omega
    have hm_eq : p - 1 = (p - 5) + 4 := by omega
    rw [hm_eq]
    conv_lhs => rw [hp_eq]
    ring_nf
    omega
  by_cases hk4 : 4 ≤ k
  · have hle_exp : 3 * k ≤ 4 * (k - 1) := by omega
    have hp1_pos : 1 ≤ (p - 1) ^ 4 := Nat.pow_pos (by omega)
    calc
      p ^ (3 * k) ≤ p ^ (4 * (k - 1)) := Nat.pow_le_pow_right hp.pos hle_exp
      _ = p ^ (4 * (k - 1)) * 1 := (mul_one _).symm
      _ ≤ p ^ (4 * (k - 1)) * (p - 1) ^ 4 := Nat.mul_le_mul_left _ hp1_pos
      _ = (p ^ (k - 1) * (p - 1)) ^ 4 := by
        rw [mul_pow, ← Nat.pow_mul, mul_comm (k - 1) 4]
  · have hpow : p ^ (3 * k) = p ^ (4 * (k - 1)) * p ^ (4 - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hle_cube : p ^ (4 - k) ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by omega)
    calc
      p ^ (3 * k) = p ^ (4 * (k - 1)) * p ^ (4 - k) := hpow
      _ ≤ p ^ (4 * (k - 1)) * p ^ 3 := Nat.mul_le_mul_left _ hle_cube
      _ ≤ p ^ (4 * (k - 1)) * (p - 1) ^ 4 := Nat.mul_le_mul_left _ h1
      _ = (p ^ (k - 1) * (p - 1)) ^ 4 := by
        rw [mul_pow, ← Nat.pow_mul, mul_comm (k - 1) 4]

/-- Elementary totient lower bound in `ℕ`: for all `q ≥ 1`, `q ^ 3 ≤ 256 * (q.totient) ^ 4`. -/
theorem totient_pow_four_ge {q : ℕ} (hq : 1 ≤ q) : q ^ 3 ≤ 256 * q.totient ^ 4 := by
  let multC : ℕ → ℕ := fun n =>
    (if 2 ∣ n then 16 else 1) * (if 3 ∣ n then 16 else 1)
  suffices h : ∀ n : ℕ, 1 ≤ n → n ^ 3 ≤ multC n * n.totient ^ 4 by
    refine (h q hq).trans (Nat.mul_le_mul_right _ ?_)
    dsimp [multC]
    split_ifs <;> norm_num
  intro n hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [multC]
  | prime_pow p k hp hk =>
      clear hq hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [Nat.totient_prime_pow_succ hp m]
      by_cases hp2 : p = 2
      · subst hp2
        have hdvd2 : 2 ∣ 2 ^ (m + 1) := dvd_pow_self 2 (Nat.succ_ne_zero m)
        have hnd3 : ¬ (3 ∣ 2 ^ (m + 1)) := by
          intro h3
          have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
          norm_num at this
        simp only [multC, hdvd2, hnd3, ↓reduceIte, mul_one, show (2 - 1 : ℕ) = 1 by rfl]
        have heq : 16 * (2 ^ m) ^ 4 = 2 ^ (4 * m + 4) := by
          rw [← Nat.pow_mul, show 16 = 2 ^ 4 by norm_num, ← Nat.pow_add]
          ring_nf
        rw [heq, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · by_cases hp3 : p = 3
        · subst hp3
          have hdvd3 : 3 ∣ 3 ^ (m + 1) := dvd_pow_self 3 (Nat.succ_ne_zero m)
          have hnd2 : ¬ (2 ∣ 3 ^ (m + 1)) := by
            intro h2
            have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
            norm_num at this
          simp only [multC, hnd2, hdvd3, ↓reduceIte, one_mul, show 3 - 1 = 2 by rfl]
          by_cases hm3 : m ≤ 3
          · have hpow : (3 ^ (m + 1)) ^ 3 = 3 ^ (4 * m) * 3 ^ (3 - m) := by
              rw [← Nat.pow_mul, ← Nat.pow_add]
              congr 1
              omega
            have h1 : 3 ^ (3 - m) ≤ 256 := by
              calc
                3 ^ (3 - m) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 27 := by norm_num
                _ ≤ 256 := by norm_num
            calc
              (3 ^ (m + 1)) ^ 3 = 3 ^ (4 * m) * 3 ^ (3 - m) := hpow
              _ ≤ 3 ^ (4 * m) * 256 := Nat.mul_le_mul_left _ h1
              _ = 16 * (3 ^ m * 2) ^ 4 := by
                rw [mul_pow, ← Nat.pow_mul]; ring
          · calc
              (3 ^ (m + 1)) ^ 3 = 3 ^ (3 * (m + 1)) := by rw [← Nat.pow_mul]; congr 1; ring
              _ ≤ 3 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ ≤ 3 ^ (4 * m) * 256 := Nat.le_mul_of_pos_right _ (by norm_num)
              _ = 16 * (3 ^ m * 2) ^ 4 := by
                rw [mul_pow, ← Nat.pow_mul]; ring
        · have hp5 : 5 ≤ p := by
            by_contra hlt
            have hp2' := hp.two_le
            interval_cases p
            · exact hp2 rfl
            · exact hp3 rfl
            · exact absurd hp (by decide)
          have hnd2 : ¬ (2 ∣ p ^ (m + 1)) := fun h2 => by
            have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
            exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
          have hnd3 : ¬ (3 ∣ p ^ (m + 1)) := fun h3 => by
            have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
            exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this).symm
          simp only [multC, hnd2, hnd3, ↓reduceIte, mul_one, one_mul]
          rw [← Nat.pow_mul, mul_comm (m + 1) 3]
          have hbound := prime_pow_cube_le_totient_pow_four hp hp5 (Nat.succ_pos m)
          rw [Nat.succ_sub_one] at hbound
          exact hbound
  | coprime a b ha hb hcop iha ihb =>
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      have ha' := iha ha1
      have hb' := ihb hb1
      have h2_iff : (2 ∣ a * b) ↔ (2 ∣ a ∨ 2 ∣ b) := Nat.Prime.dvd_mul Nat.prime_two
      have h3_iff : (3 ∣ a * b) ↔ (3 ∣ a ∨ 3 ∣ b) := Nat.Prime.dvd_mul Nat.prime_three
      have h2_nd : ¬ (2 ∣ a ∧ 2 ∣ b) := fun ⟨h1, h2⟩ => by
        have := Nat.dvd_gcd h1 h2; rw [hcop.gcd_eq_one] at this; omega
      have h3_nd : ¬ (3 ∣ a ∧ 3 ∣ b) := fun ⟨h1, h2⟩ => by
        have := Nat.dvd_gcd h1 h2; rw [hcop.gcd_eq_one] at this; omega
      have hmult_eq : multC a * multC b = multC (a * b) := by
        dsimp [multC]
        by_cases ha2 : 2 ∣ a <;> by_cases hb2 : 2 ∣ b <;>
          by_cases ha3 : 3 ∣ a <;> by_cases hb3 : 3 ∣ b <;>
          simp [ha2, hb2, ha3, hb3, h2_iff, h3_iff] at h2_nd h3_nd ⊢
      rw [mul_pow, Nat.totient_mul hcop, mul_pow, ← hmult_eq]
      calc
        a ^ 3 * b ^ 3 ≤ (multC a * a.totient ^ 4) * (multC b * b.totient ^ 4) :=
          Nat.mul_le_mul ha' hb'
        _ = multC a * multC b * (a.totient ^ 4 * b.totient ^ 4) := by ring

/-- Real totient lower bound `(q : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (q.totient : ℝ)` for `q ≥ 1`. -/
theorem rpow_three_quarters_le_four_mul_totient {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (q.totient : ℝ) := by
  have hnat : ((q : ℝ) ^ 3) ≤ (4 * (q.totient : ℝ)) ^ 4 := by
    have hq4 := totient_pow_four_ge hq
    have hreal : (q : ℝ) ^ 3 ≤ 256 * (q.totient : ℝ) ^ 4 := by exact_mod_cast hq4
    linarith [show (4 * (q.totient : ℝ)) ^ 4 = 256 * (q.totient : ℝ) ^ 4 by ring]
  have hrpow := Real.rpow_le_rpow (by positivity) hnat (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hl : ((q : ℝ) ^ 3) ^ (1 / 4 : ℝ) = (q : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast (q : ℝ) 3, ← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num
  have hr : ((4 * (q.totient : ℝ)) ^ 4) ^ (1 / 4 : ℝ) = 4 * (q.totient : ℝ) := by
    rw [← Real.rpow_natCast (4 * (q.totient : ℝ)) 4, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [hl, hr] at hrpow

/-- The `q`-th term of the ternary Goldbach singular series:
`μ(q) / φ(q)^3 * c_q(-N)`. -/
def singularTermTernary (q N : ℕ) : ℝ :=
  if q = 0 then 0
  else (μ q : ℝ) / (q.totient : ℝ) ^ 3 * (ramanujanSum q (-(N : ℤ))).re

/-- The `q`-th term of the binary Goldbach singular series:
`μ(q)^2 / φ(q)^2 * c_q(-N)`. -/
def singularTermBinary (q N : ℕ) : ℝ :=
  if q = 0 then 0
  else (μ q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujanSum q (-(N : ℤ))).re

/-- The ternary Goldbach singular series `S₃(N) = ∑_{q ≥ 1} μ(q) c_q(-N) / φ(q)^3`. -/
def goldbachTernarySingularSeries (N : ℕ) : ℝ :=
  ∑' q : ℕ, singularTermTernary q N

/-- The binary Goldbach singular series `S₂(N) = ∑_{q ≥ 1} μ(q)^2 c_q(-N) / φ(q)^2`. -/
def goldbachBinarySingularSeries (N : ℕ) : ℝ :=
  ∑' q : ℕ, singularTermBinary q N

@[simp]
theorem singularTermTernary_zero (N : ℕ) : singularTermTernary 0 N = 0 := by
  simp [singularTermTernary]

@[simp]
theorem singularTermTernary_one (N : ℕ) : singularTermTernary 1 N = 1 := by
  simp [singularTermTernary]

@[simp]
theorem singularTermBinary_zero (N : ℕ) : singularTermBinary 0 N = 0 := by
  simp [singularTermBinary]

@[simp]
theorem singularTermBinary_one (N : ℕ) : singularTermBinary 1 N = 1 := by
  simp [singularTermBinary]

/-- Multiplicativity of `singularTermTernary q N` in `q` for coprime moduli. -/
theorem singularTermTernary_mul_coprime {q₁ q₂ : ℕ} (hcop : Nat.Coprime q₁ q₂) (N : ℕ) :
    singularTermTernary (q₁ * q₂) N = singularTermTernary q₁ N * singularTermTernary q₂ N := by
  by_cases hq1 : q₁ = 0
  · subst hq1; simp
  by_cases hq2 : q₂ = 0
  · subst hq2; simp
  have h1 : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr hq1
  have h2 : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr hq2
  have h12 : q₁ * q₂ ≠ 0 := mul_ne_zero hq1 hq2
  simp only [singularTermTernary, hq1, hq2, h12, ↓reduceIte]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, ramanujanSum_mul_coprime h1 h2 hcop,
    ramanujanSum_eq_ofReal_re h1, ramanujanSum_eq_ofReal_re h2]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  ring

/-- Multiplicativity of `singularTermBinary q N` in `q` for coprime moduli. -/
theorem singularTermBinary_mul_coprime {q₁ q₂ : ℕ} (hcop : Nat.Coprime q₁ q₂) (N : ℕ) :
    singularTermBinary (q₁ * q₂) N = singularTermBinary q₁ N * singularTermBinary q₂ N := by
  by_cases hq1 : q₁ = 0
  · subst hq1; simp
  by_cases hq2 : q₂ = 0
  · subst hq2; simp
  have h1 : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr hq1
  have h2 : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr hq2
  have h12 : q₁ * q₂ ≠ 0 := mul_ne_zero hq1 hq2
  simp only [singularTermBinary, hq1, hq2, h12, ↓reduceIte]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, ramanujanSum_mul_coprime h1 h2 hcop,
    ramanujanSum_eq_ofReal_re h1, ramanujanSum_eq_ofReal_re h2]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  ring

/-- Vanishing of `singularTermTernary` at higher prime powers `p ^ k` (`k ≥ 2`). -/
theorem singularTermTernary_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (N : ℕ) :
    singularTermTernary (p ^ k) N = 0 := by
  rw [singularTermTernary]
  have hmu : μ (p ^ k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  simp [hmu]

/-- Vanishing of `singularTermBinary` at higher prime powers `p ^ k` (`k ≥ 2`). -/
theorem singularTermBinary_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (N : ℕ) :
    singularTermBinary (p ^ k) N = 0 := by
  rw [singularTermBinary]
  have hmu : μ (p ^ k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  simp [hmu]

/-- Value of `singularTermTernary p N` at a prime `p`. -/
theorem singularTermTernary_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    singularTermTernary p N =
      if p ∣ N then -(1 / ((p : ℝ) - 1) ^ 2) else 1 / ((p : ℝ) - 1) ^ 3 := by
  have hne : p ≠ 0 := hp.ne_zero
  have htot : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have := hp.two_le
    linarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast this]
  rw [singularTermTernary]
  simp only [hne, ↓reduceIte, ArithmeticFunction.moebius_apply_prime hp, htot]
  have hram : (ramanujanSum p (-(N : ℤ))).re = if p ∣ N then (p : ℝ) - 1 else -1 := by
    have hpp := ramanujanSum_prime_pow hp le_rfl (-(N : ℤ))
    simp only [pow_one, Nat.sub_self, pow_zero, Int.natAbs_neg, Int.natAbs_natCast, one_dvd,
      ↓reduceIte, Nat.cast_one] at hpp
    rw [hpp]
    split_ifs with hdvd
    · rw [Nat.totient_prime hp, ← Complex.ofReal_natCast, Complex.ofReal_re,
        Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    · simp
  rw [hram]
  split_ifs with hdvd
  · field_simp [hp1_ne]
    ring
  · push_cast
    ring

/-- Value of `singularTermBinary p N` at a prime `p`. -/
theorem singularTermBinary_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    singularTermBinary p N =
      if p ∣ N then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2) := by
  have hne : p ≠ 0 := hp.ne_zero
  have htot : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have := hp.two_le
    linarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast this]
  rw [singularTermBinary]
  simp only [hne, ↓reduceIte, ArithmeticFunction.moebius_apply_prime hp, htot]
  have hram : (ramanujanSum p (-(N : ℤ))).re = if p ∣ N then (p : ℝ) - 1 else -1 := by
    have hpp := ramanujanSum_prime_pow hp le_rfl (-(N : ℤ))
    simp only [pow_one, Nat.sub_self, pow_zero, Int.natAbs_neg, Int.natAbs_natCast, one_dvd,
      ↓reduceIte, Nat.cast_one] at hpp
    rw [hpp]
    split_ifs with hdvd
    · rw [Nat.totient_prime hp, ← Complex.ofReal_natCast, Complex.ofReal_re,
        Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    · simp
  rw [hram]
  split_ifs with hdvd
  · norm_num; field_simp [hp1_ne]
  · push_cast
    ring

/-- Squarefree factorization of `singularTermTernary q N` along `d = gcd(q, N)` and `m = q / d`. -/
theorem singularTermTernary_eq_of_squarefree {q N : ℕ} (hq : Squarefree q) :
    let d := Nat.gcd q N
    let m := q / d
    singularTermTernary q N =
      (μ d : ℝ) / ((d.totient : ℝ) ^ 2 * (m.totient : ℝ) ^ 3) := by
  intro d m
  have hq_pos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have hd_dvd : d ∣ q := Nat.gcd_dvd_left q N
  have hdm : d * m = q := Nat.mul_div_cancel' hd_dvd
  have hcop_dm : Nat.Coprime d m := by
    by_contra hnc
    obtain ⟨p, hp, hpd, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hp2 : p * p ∣ q := hdm ▸ Nat.mul_dvd_mul hpd hpm
    exact absurd (hq p hp2) hp.1
  have htot_q : q.totient = d.totient * m.totient := by
    rw [← hdm, Nat.totient_mul hcop_dm]
  have hmu_q : μ q = μ d * μ m := by
    rw [← hdm]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_dm
  have hm_sqf : Squarefree m := hq.squarefree_of_dvd (hdm ▸ dvd_mul_left m d)
  have hmu_m_sq : (μ m : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hm_sqf
  have hgcd_neg : Nat.gcd (-(N : ℤ)).natAbs q = d := by
    rw [Int.natAbs_neg, Int.natAbs_natCast, Nat.gcd_comm]
  have hram : (ramanujanSum q (-(N : ℤ))).re = (μ m : ℝ) * (d.totient : ℝ) := by
    have hr := ramanujanSum_eq_moebius_mul_totient hq_pos (-(N : ℤ))
    rw [hgcd_neg] at hr
    change _ = _ at hr
    have hdiv : q / d = m := rfl
    rw [hdiv, htot_q] at hr
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hq_pos hd_dvd)
      (Nat.gcd_pos_of_pos_left N hq_pos)
    have hmt_ne : (m.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hm_pos).ne'
    have hramC : ramanujanSum q (-(N : ℤ)) = ((μ m : ℝ) * (d.totient : ℝ) : ℂ) := by
      rw [hr]
      push_cast
      field_simp [hmt_ne]
    simp [hramC]
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left N hq_pos
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hq_pos hd_dvd) hd_pos
  have hdt_ne : (d.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd_pos).ne'
  have hmt_ne : (m.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hm_pos).ne'
  rw [singularTermTernary]
  simp only [hq.ne_zero, ↓reduceIte, hmu_q, htot_q, hram]
  push_cast
  calc
    (μ d : ℝ) * (μ m : ℝ) / ((d.totient : ℝ) * (m.totient : ℝ)) ^ 3 * ((μ m : ℝ) * (d.totient : ℝ))
        = (μ d : ℝ) * (μ m : ℝ) ^ 2 * (d.totient : ℝ) /
            ((d.totient : ℝ) ^ 3 * (m.totient : ℝ) ^ 3) := by ring
    _ = (μ d : ℝ) / ((d.totient : ℝ) ^ 2 * (m.totient : ℝ) ^ 3) := by
      rw [hmu_m_sq]
      field_simp [hdt_ne, hmt_ne]

/-- Bound `|singularTermTernary q N| ≤ 16 * (q : ℝ) ^ (-3 / 2 : ℝ)` for every `q ≥ 1`. -/
theorem abs_singularTermTernary_le {q N : ℕ} (hq : 1 ≤ q) :
    |singularTermTernary q N| ≤ 16 * (q : ℝ) ^ (-3 / 2 : ℝ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have htot_ge : (q : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (q.totient : ℝ) :=
    rpow_three_quarters_le_four_mul_totient hq
  have htot_sq : (q : ℝ) ^ (3 / 2 : ℝ) ≤ 16 * (q.totient : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) htot_ge 2
    have hpow : ((q : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (q : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((q : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hq_pos.le]
      norm_num
    linarith [show (4 * (q.totient : ℝ)) ^ 2 = 16 * (q.totient : ℝ) ^ 2 by ring]
  have hmu : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hram : |(ramanujanSum q (-(N : ℤ))).re| ≤ (q.totient : ℝ) := by
    have h1 := Complex.abs_re_le_norm (ramanujanSum q (-(N : ℤ)))
    exact h1.trans (norm_ramanujanSum_le_totient q (-(N : ℤ)))
  have hq_ne : q ≠ 0 := by omega
  rw [singularTermTernary]
  simp only [hq_ne, ↓reduceIte, abs_mul, abs_div, abs_pow, abs_of_pos htot_pos]
  have hinv_le : 1 / (q.totient : ℝ) ^ 2 ≤ 16 * (q : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hq_pos.le,
      ← div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_pos htot_pos) (Real.rpow_pos_of_pos hq_pos _)]
    linarith
  calc
    |(μ q : ℝ)| / (q.totient : ℝ) ^ 3 * |(ramanujanSum q (-(N : ℤ))).re|
        ≤ 1 / (q.totient : ℝ) ^ 3 * (q.totient : ℝ) := by
      refine mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hram (abs_nonneg _)
        (by positivity)
    _ = 1 / (q.totient : ℝ) ^ 2 := by field_simp [htot_pos.ne']
    _ ≤ 16 * (q : ℝ) ^ (-3 / 2 : ℝ) := hinv_le

/-- Bound `|singularTermBinary q N| ≤ 16 * (N : ℝ) * (q : ℝ) ^ (-3 / 2 : ℝ)` for `1 ≤ q`, `1 ≤ N`. -/
theorem abs_singularTermBinary_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    |singularTermBinary q N| ≤ 16 * (N : ℝ) * (q : ℝ) ^ (-3 / 2 : ℝ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have htot_ge : (q : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (q.totient : ℝ) :=
    rpow_three_quarters_le_four_mul_totient hq
  have htot_sq : (q : ℝ) ^ (3 / 2 : ℝ) ≤ 16 * (q.totient : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) htot_ge 2
    have hpow : ((q : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (q : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((q : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hq_pos.le]
      norm_num
    linarith [show (4 * (q.totient : ℝ)) ^ 2 = 16 * (q.totient : ℝ) ^ 2 by ring]
  have hmu : |(μ q : ℝ) ^ 2| ≤ 1 := by
    have h1 : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    rw [abs_pow]
    nlinarith [abs_nonneg (μ q : ℝ)]
  have hram : |(ramanujanSum q (-(N : ℤ))).re| ≤ (N : ℝ) := by
    have h1 := (Complex.abs_re_le_norm (ramanujanSum q (-(N : ℤ)))).trans
      (norm_ramanujanSum_le_gcd hq (-(N : ℤ)))
    have hgcd : Nat.gcd (-(N : ℤ)).natAbs q ≤ N := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.gcd_le_left q hN
    exact h1.trans (by exact_mod_cast hgcd)
  have hq_ne : q ≠ 0 := by omega
  rw [singularTermBinary]
  simp only [hq_ne, ↓reduceIte, abs_mul, abs_div, abs_of_pos (pow_pos htot_pos 2)]
  have hinv_le : 1 / (q.totient : ℝ) ^ 2 ≤ 16 * (q : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hq_pos.le,
      ← div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_pos htot_pos) (Real.rpow_pos_of_pos hq_pos _)]
    linarith
  calc
    |(μ q : ℝ) ^ 2| / (q.totient : ℝ) ^ 2 * |(ramanujanSum q (-(N : ℤ))).re|
        ≤ (1 / (q.totient : ℝ) ^ 2) * (N : ℝ) := by
      refine mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hram (abs_nonneg _)
        (by positivity)
    _ ≤ (16 * (q : ℝ) ^ (-3 / 2 : ℝ)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hinv_le (Nat.cast_nonneg N)
    _ = 16 * (N : ℝ) * (q : ℝ) ^ (-3 / 2 : ℝ) := by ring

/-- Helper: `(k : ℝ) ^ (-3 / 2 : ℝ) ≤ 2 * ((k - 1 : ℝ) ^ (-1 / 2 : ℝ) - (k : ℝ) ^ (-1 / 2 : ℝ))`
for every `k ≥ 2`. -/
private lemma rpow_neg_three_halves_le_telescoping {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ (-3 / 2 : ℝ) ≤
      2 * (((k - 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) - (k : ℝ) ^ (-1 / 2 : ℝ)) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  set u : ℝ := Real.sqrt ((k - 1 : ℕ) : ℝ)
  set v : ℝ := Real.sqrt (k : ℝ)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hk1_pos
  have hv_pos : 0 < v := Real.sqrt_pos.mpr hk_pos
  have huv_sq : v ^ 2 - u ^ 2 = 1 := by
    dsimp [u, v]
    rw [Real.sq_sqrt hk_pos.le, Real.sq_sqrt hk1_pos.le, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_one]
    ring
  have hu_le_v : u ≤ v := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : k - 1 ≤ k))
  have huv_sub : 1 ≤ (v - u) * (2 * v) := by
    have hprod : (v - u) * (v + u) = 1 := by linarith [show (v - u) * (v + u) = v ^ 2 - u ^ 2 by ring]
    have hle : v + u ≤ 2 * v := by linarith
    calc
      1 = (v - u) * (v + u) := hprod.symm
      _ ≤ (v - u) * (2 * v) := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hu_le_v)
  have hr_u : ((k - 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) = u⁻¹ := by
    dsimp [u]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hk1_pos.le,
      Real.sqrt_eq_rpow]
  have hr_v : (k : ℝ) ^ (-1 / 2 : ℝ) = v⁻¹ := by
    dsimp [v]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hk_pos.le,
      Real.sqrt_eq_rpow]
  have hr_k : (k : ℝ) ^ (-3 / 2 : ℝ) = (v ^ 3)⁻¹ := by
    have hv3 : (k : ℝ) ^ (3 / 2 : ℝ) = v ^ 3 := by
      dsimp [v]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((k : ℝ) ^ (1 / 2 : ℝ)) 3,
        ← Real.rpow_mul hk_pos.le]
      norm_num
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hk_pos.le, hv3]
  rw [hr_u, hr_v, hr_k]
  have hdiff : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by field_simp [hu_pos.ne', hv_pos.ne']
  rw [hdiff]
  have hdenom : 2 * u * v ^ 2 ≤ 2 * v ^ 3 := by nlinarith
  calc
    (v ^ 3)⁻¹ = 2 / (2 * v ^ 3) := by field_simp [hv_pos.ne']
    _ ≤ 2 * (v - u) / (u * v) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    _ = 2 * ((v - u) / (u * v)) := by ring

/-- Telescoping tail bound for `∑ k ∈ Finset.Ioc M K, (k : ℝ) ^ (-3 / 2 : ℝ) ≤ 2 * M ^ (-1 / 2)`. -/
theorem sum_Ioc_rpow_neg_three_halves_le {M : ℕ} (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.Ioc M K, (k : ℝ) ^ (-3 / 2 : ℝ) ≤ 2 * (M : ℝ) ^ (-1 / 2 : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rcases le_or_gt K M with hKM | hMK
  · rw [Finset.Ioc_eq_empty (not_lt.mpr hKM), Finset.sum_empty]
    positivity
  · have hsum :
        ∑ k ∈ Finset.Ioc M K, (k : ℝ) ^ (-3 / 2 : ℝ) ≤
          ∑ k ∈ Finset.Ioc M K,
            2 * (((k - 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) - (k : ℝ) ^ (-1 / 2 : ℝ)) :=
      Finset.sum_le_sum fun k hk =>
        rpow_neg_three_halves_le_telescoping (by have := (Finset.mem_Ioc.mp hk).1; omega)
    refine hsum.trans ?_
    rw [← Finset.mul_sum]
    have htele :
        ∑ k ∈ Finset.Ioc M K, (((k - 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) - (k : ℝ) ^ (-1 / 2 : ℝ)) =
          (M : ℝ) ^ (-1 / 2 : ℝ) - (K : ℝ) ^ (-1 / 2 : ℝ) := by
      clear hsum
      induction K, hMK using Nat.le_induction with
      | base =>
          rw [Nat.Ioc_succ_singleton, Finset.sum_singleton, Nat.add_sub_cancel]
      | succ K' hMK' ih =>
          have hIoc : Finset.Ioc M (K' + 1) = insert (K' + 1) (Finset.Ioc M K') := by
            ext x
            simp only [Finset.mem_Ioc, Finset.mem_insert]
            omega
          rw [hIoc, Finset.sum_insert (by simp), Nat.add_sub_cancel, ih]
          ring
    rw [htele]
    have hK_nn : 0 ≤ (K : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg K) _
    linarith

/-- Summability of `q ↦ |singularTermTernary q N|`. -/
theorem summable_abs_singularTermTernary (N : ℕ) :
    Summable fun q : ℕ => |singularTermTernary q N| := by
  have hp : Summable fun q : ℕ => 16 * (q : ℝ) ^ (-3 / 2 : ℝ) := by
    have hs : Summable fun q : ℕ => (q : ℝ) ^ (-3 / 2 : ℝ) :=
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).congr fun q => by
        rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg q)]
    exact hs.mul_left 16
  refine hp.of_nonneg_of_le (fun q => abs_nonneg _) fun q => ?_
  by_cases hq : q = 0
  · subst hq; simp
  · exact abs_singularTermTernary_le (Nat.one_le_iff_ne_zero.mpr hq)

/-- Summability of `singularTermTernary q N`. -/
theorem summable_singularTermTernary (N : ℕ) :
    Summable fun q : ℕ => singularTermTernary q N :=
  (summable_abs_singularTermTernary N).of_abs

/-- Summability of `q ↦ |singularTermBinary q N|` for `N ≥ 1`. -/
theorem summable_abs_singularTermBinary {N : ℕ} (hN : 1 ≤ N) :
    Summable fun q : ℕ => |singularTermBinary q N| := by
  have hp : Summable fun q : ℕ => 16 * (N : ℝ) * (q : ℝ) ^ (-3 / 2 : ℝ) := by
    have hs : Summable fun q : ℕ => (q : ℝ) ^ (-3 / 2 : ℝ) :=
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).congr fun q => by
        rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg q)]
    exact hs.mul_left (16 * (N : ℝ))
  refine hp.of_nonneg_of_le (fun q => abs_nonneg _) fun q => ?_
  by_cases hq : q = 0
  · subst hq; simp
  · exact abs_singularTermBinary_le (Nat.one_le_iff_ne_zero.mpr hq) hN

/-- Summability of `singularTermBinary q N` for `N ≥ 1`. -/
theorem summable_singularTermBinary {N : ℕ} (hN : 1 ≤ N) :
    Summable fun q : ℕ => singularTermBinary q N :=
  (summable_abs_singularTermBinary hN).of_abs

/-- Uniform tail bound for `∑_{M < q} |singularTermTernary q N|`:
for every `M ≥ 1` and every `N : ℕ`,
`∑' q : ℕ, (if M < q then |singularTermTernary q N| else 0) ≤ 32 * M ^ (-1 / 2 : ℝ)`. -/
theorem tsum_tail_abs_singularTermTernary_le {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    ∑' q : ℕ, (if M < q then |singularTermTernary q N| else 0) ≤
      32 * (M : ℝ) ^ (-1 / 2 : ℝ) := by
  have hsumm : Summable fun q : ℕ => if M < q then |singularTermTernary q N| else 0 := by
    refine (summable_abs_singularTermTernary N).of_nonneg_of_le (fun q => by split_ifs <;> positivity)
      fun q => by split_ifs <;> [exact le_rfl; exact abs_nonneg _]
  refine hsumm.tsum_le_of_sum_le fun s => ?_
  let K := max M (s.sup id)
  have hsub : s ⊆ Finset.Iic K := fun q hq => Finset.mem_Iic.mpr (le_max_of_le_right (Finset.le_sup (f := id) hq))
  calc
    ∑ q ∈ s, (if M < q then |singularTermTernary q N| else 0)
        ≤ ∑ q ∈ Finset.Iic K, (if M < q then |singularTermTernary q N| else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by split_ifs <;> positivity
    _ = ∑ q ∈ Finset.Ioc M K, |singularTermTernary q N| := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext q
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      tauto
    _ ≤ ∑ q ∈ Finset.Ioc M K, 16 * (q : ℝ) ^ (-3 / 2 : ℝ) :=
      Finset.sum_le_sum fun q hq =>
        abs_singularTermTernary_le (by have := (Finset.mem_Ioc.mp hq).1; omega)
    _ = 16 * ∑ q ∈ Finset.Ioc M K, (q : ℝ) ^ (-3 / 2 : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ 16 * (2 * (M : ℝ) ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_three_halves_le hM K) (by norm_num)
    _ = 32 * (M : ℝ) ^ (-1 / 2 : ℝ) := by ring

/-- **Squarefree Euler product theorem**:
for any multiplicative `f : ℕ → ℝ` with `f 0 = 0`, `f 1 = 1`, vanishing on higher prime powers
`p ^ k` (`k ≥ 2`), and `Summable (fun q => |f q|)`,
`∑' q : ℕ, f q = ∏' p : Nat.Primes, (1 + f p)`. -/
theorem tsum_eq_tprod_prime_one_add {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hf_mul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a * b) = f a * f b)
    (hf_pp : ∀ {p k : ℕ}, p.Prime → 2 ≤ k → f (p ^ k) = 0)
    (hf_sum : Summable fun q : ℕ => |f q|) :
    Multipliable (fun p : Nat.Primes => 1 + f p) ∧
      ∑' q : ℕ, f q = ∏' p : Nat.Primes, (1 + f p) := by
  have hp_sum : Summable fun p : Nat.Primes => |f p| :=
    hf_sum.comp_injective Subtype.val_injective
  have hmult : Multipliable fun p : Nat.Primes => 1 + f p :=
    AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_one_add_of_summable_abs hp_sum
  refine ⟨hmult, ?_⟩
  have hf_nsqf : ∀ q : ℕ, ¬ Squarefree q → f q = 0 := by
    intro q hnsq
    induction q using Nat.recOnPosPrimePosCoprime with
    | zero => exact hf0
    | one => exact False.elim (hnsq squarefree_one)
    | prime_pow p k hp hk =>
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have hk1 : k = 1 := by omega
          subst hk1
          rw [pow_one] at hnsq
          exact hnsq hp.squarefree
        exact hf_pp hp hk2
    | coprime a b _ _ hcop iha ihb =>
        rw [hf_mul hcop]
        by_cases ha : Squarefree a <;> by_cases hb : Squarefree b
        · exact False.elim (hnsq ((Nat.squarefree_mul hcop).mpr ⟨ha, hb⟩))
        · rw [ihb hb, mul_zero]
        · rw [iha ha, zero_mul]
        · rw [iha ha, zero_mul]
  have hprod_eq_sum : ∀ T : Finset Nat.Primes,
      ∏ p ∈ T, (1 + f (p : ℕ)) = ∑ d ∈ (∏ p ∈ T, (p : ℕ)).divisors, f d := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [hf1]
    | insert p T hpT ih =>
        rw [Finset.prod_insert hpT, Finset.prod_insert hpT, ih]
        set M := ∏ q ∈ T, (q : ℕ)
        have hM_pos : 0 < M := Finset.prod_pos fun q _ => q.2.pos
        have hp_ndvd : ¬ (p : ℕ) ∣ M := by
          intro hdvd
          have hdvd_ex : ∀ S : Finset Nat.Primes, (p : ℕ) ∣ ∏ q ∈ S, (q : ℕ) →
              ∃ q ∈ S, (p : ℕ) ∣ (q : ℕ) := by
            intro S hS
            induction S using Finset.induction_on with
            | empty =>
                rw [Finset.prod_empty] at hS
                exact False.elim (p.2.not_dvd_one hS)
            | insert q S hqS ihS =>
                rw [Finset.prod_insert hqS] at hS
                rcases p.2.dvd_mul.mp hS with h1 | h2
                · exact ⟨q, Finset.mem_insert_self _ _, h1⟩
                · obtain ⟨r, hr, hpr⟩ := ihS h2
                  exact ⟨r, Finset.mem_insert_of_mem hr, hpr⟩
          obtain ⟨q, hqT, hpq⟩ := hdvd_ex T hdvd
          have heq : (p : ℕ) = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hpq
          exact hpT (Subtype.ext heq ▸ hqT)
        have hcop : Nat.Coprime (p : ℕ) M := p.2.coprime_iff_not_dvd.mpr hp_ndvd
        have hdiv_mul :
            ∑ d ∈ ((p : ℕ) * M).divisors, f d =
              (f 1 + f (p : ℕ)) * ∑ m ∈ M.divisors, f m := by
          have hbij :
              ∑ d ∈ ((p : ℕ) * M).divisors, f d =
                ∑ x ∈ (p : ℕ).divisors ×ˢ M.divisors, f (x.1 * x.2) := by
            refine (Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_).symm
            · intro x hx
              rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hx
              exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hx.1.1 hx.2.1, mul_ne_zero p.2.ne_zero hM_pos.ne'⟩
            · intro x hx y hy hxy
              rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hx hy
              have hx1 : x.1 ∣ (p : ℕ) := hx.1.1
              have hy1 : y.1 ∣ (p : ℕ) := hy.1.1
              have hx2 : x.2 ∣ M := hx.2.1
              have hy2 : y.2 ∣ M := hy.2.1
              have hcop12 : Nat.Coprime x.1 y.2 := hcop.coprime_dvd_left hx1 |>.coprime_dvd_right hy2
              have hcop21 : Nat.Coprime y.1 x.2 := hcop.coprime_dvd_left hy1 |>.coprime_dvd_right hx2
              have hdvd_x1 : x.1 ∣ y.1 := hcop12.dvd_of_dvd_mul_right ⟨x.2, hxy.symm⟩
              have hdvd_y1 : y.1 ∣ x.1 := hcop21.dvd_of_dvd_mul_right ⟨y.2, hxy⟩
              have h1 : x.1 = y.1 := Nat.dvd_antisymm hdvd_x1 hdvd_y1
              have hx1_pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hx1 p.2.pos
              have h2 : x.2 = y.2 := mul_left_cancel₀ hx1_pos.ne' (by rwa [← h1] at hxy)
              exact Prod.ext h1 h2
            · intro d hd
              have hd_dvd : d ∣ (p : ℕ) * M := (Nat.mem_divisors.mp hd).1
              by_cases hpd : (p : ℕ) ∣ d
              · refine ⟨((p : ℕ), d / (p : ℕ)), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
                · exact Nat.mem_divisors.mpr ⟨dvd_rfl, p.2.ne_zero⟩
                · exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left p.2.pos).mp
                    (by rwa [Nat.mul_div_cancel' hpd]), hM_pos.ne'⟩
                · exact Nat.mul_div_cancel' hpd
              · have hd_M : d ∣ M := (p.2.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hd_dvd
                refine ⟨(1, d), Finset.mem_product.mpr ⟨?_, ?_⟩, one_mul d⟩
                · exact Nat.mem_divisors.mpr ⟨one_dvd _, p.2.ne_zero⟩
                · exact Nat.mem_divisors.mpr ⟨hd_M, hM_pos.ne'⟩
            · intro x _
              rfl
          rw [hbij, Finset.sum_product, p.2.divisors, Finset.sum_pair p.2.ne_one.symm]
          have hc1 : ∀ m ∈ M.divisors, f (1 * m) = f 1 * f m := fun m _ => by simp [hf1]
          have hcp : ∀ m ∈ M.divisors, f ((p : ℕ) * m) = f (p : ℕ) * f m := fun m hm =>
            hf_mul (hcop.coprime_dvd_right (Nat.mem_divisors.mp hm).1)
          rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hcp, ← Finset.mul_sum,
            ← Finset.mul_sum, ← add_mul]
        rw [hdiv_mul, hf1]
  let S : ℕ → Finset Nat.Primes := fun n =>
    ((Finset.Icc 2 n).filter Nat.Prime).attach.image fun x =>
      ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
  have hS_tendsto : Tendsto S atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro T
    refine ⟨T.sup Subtype.val + 2, fun n hn p hp => ?_⟩
    have hsup : (p : ℕ) ≤ T.sup Subtype.val := Finset.le_sup (f := Subtype.val) hp
    have hp_le : (p : ℕ) ≤ n := by omega
    have hmem : (p : ℕ) ∈ (Finset.Icc 2 n).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨p.2.two_le, hp_le⟩, p.2⟩
    refine Finset.mem_image.mpr ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hprod_tendsto :
      Tendsto (fun n => ∏ p ∈ S n, (1 + f (p : ℕ))) atTop (𝓝 (∏' p : Nat.Primes, (1 + f p))) :=
    hmult.hasProd.comp hS_tendsto
  have hsum_tendsto : Tendsto (fun n => ∑ q ∈ Finset.Icc 1 n, f q) atTop (𝓝 (∑' q : ℕ, f q)) := by
    have hsum : Summable f := hf_sum.of_abs
    have hrange : Tendsto (fun n => ∑ q ∈ Finset.range (n + 1), f q) atTop (𝓝 (∑' q : ℕ, f q)) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine hrange.congr fun n => ?_
    have hrange_eq : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext q; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange_eq, Finset.sum_insert (by simp), hf0, zero_add]
  have hdiff_tendsto :
      Tendsto (fun n => (∏ p ∈ S n, (1 + f (p : ℕ))) - ∑ q ∈ Finset.Icc 1 n, f q) atTop (𝓝 0) := by
    have htail : Tendsto (fun n : ℕ => ∑' q : {q : ℕ // n < q}, |f q|) atTop (𝓝 0) := by
      have hhas : HasSum (fun q => |f q|) (∑' q, |f q|) := hf_sum.hasSum
      have hlim : Tendsto (fun n => (∑' q, |f q|) - ∑ q ∈ Finset.range (n + 1), |f q|)
          atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := ∑' q, |f q|)).sub
          (hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
        simpa using this
      refine squeeze_zero (fun n => tsum_nonneg fun _ => abs_nonneg _) (fun n => ?_) hlim
      have hsub_le :
          ∑' q : {q : ℕ // n < q}, |f q| ≤
            (∑' q, |f q|) - ∑ q ∈ Finset.range (n + 1), |f q| := by
        have hs_tail : Summable fun q : {q : ℕ // n < q} => |f q| := hf_sum.subtype _
        have hadd_le :
            ∑ q ∈ Finset.range (n + 1), |f q| + ∑' q : {q : ℕ // n < q}, |f q| ≤
              ∑' q, |f q| := by
          have ht :
              Tendsto (fun F : Finset {q : ℕ // n < q} =>
                  ∑ q ∈ Finset.range (n + 1), |f q| + ∑ x ∈ F, |f x.1|)
                atTop (𝓝 (∑ q ∈ Finset.range (n + 1), |f q| +
                  ∑' q : {q : ℕ // n < q}, |f q|)) :=
            tendsto_const_nhds.add hs_tail.hasSum
          refine le_of_tendsto ht (Filter.Eventually.of_forall fun F => ?_)
          have hdisj : Disjoint (Finset.range (n + 1)) (F.map ⟨Subtype.val, Subtype.val_injective⟩) := by
            rw [Finset.disjoint_left]
            intro q hq1 hq2
            rw [Finset.mem_range] at hq1
            rw [Finset.mem_map] at hq2
            obtain ⟨x, _, hqx⟩ := hq2
            have hqx' : x.1 = q := hqx
            have hx_gt : n < x.1 := x.2
            omega
          have hunion :
              ∑ q ∈ Finset.range (n + 1), |f q| + ∑ x ∈ F, |f x.1| =
                ∑ q ∈ Finset.range (n + 1) ∪ F.map ⟨Subtype.val, Subtype.val_injective⟩, |f q| := by
            rw [Finset.sum_union hdisj, Finset.sum_map]
            rfl
          rw [hunion]
          exact hf_sum.sum_le_tsum _ (fun _ _ => abs_nonneg _)
        linarith
      exact hsub_le
    refine squeeze_zero_norm (fun n => ?_) htail
    rw [hprod_eq_sum (S n)]
    set A := (∏ p ∈ S n, (p : ℕ)).divisors
    have hM_pos : 0 < ∏ p ∈ S n, (p : ℕ) := Finset.prod_pos fun p _ => p.2.pos
    have hIcc_eq : ∑ q ∈ Finset.Icc 1 n, f q = ∑ q ∈ Finset.Icc 1 n ∩ A, f q := by
      have hsub : Finset.Icc 1 n ∩ A ⊆ Finset.Icc 1 n := Finset.inter_subset_left
      refine (Finset.sum_subset hsub fun q hq hnmem => ?_).symm
      apply hf_nsqf
      intro hsq
      apply hnmem
      rw [Finset.mem_inter, Nat.mem_divisors]
      have hq_le : q ≤ n := (Finset.mem_Icc.mp hq).2
      refine ⟨hq, ?_, hM_pos.ne'⟩
      clear hnmem hq
      induction q using Nat.recOnPosPrimePosCoprime with
      | zero => exact False.elim (by exact absurd (hsq 2 (by simp)) (by norm_num))
      | one => exact one_dvd _
      | prime_pow p k hp hk =>
          have hk1 : k = 1 := by
            by_contra hne1
            have hk2 : 2 ≤ k := by omega
            have hpp : p * p ∣ p ^ k := by
              rw [← pow_two]
              exact Nat.pow_dvd_pow p hk2
            exact absurd (hsq p hpp) hp.not_isUnit
          subst hk1
          rw [pow_one] at hq_le ⊢
          have hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hq_le⟩, hp⟩
          have hp_mem : (⟨p, hp⟩ : Nat.Primes) ∈ S n :=
            Finset.mem_image.mpr ⟨⟨p, hmem⟩, Finset.mem_attach _ _, rfl⟩
          exact Finset.dvd_prod_of_mem (fun x : Nat.Primes => (x : ℕ)) hp_mem
      | coprime a b ha hb hcop iha ihb =>
          have hsqa : Squarefree a := hsq.squarefree_of_dvd (dvd_mul_right a b)
          have hsqb : Squarefree b := hsq.squarefree_of_dvd (dvd_mul_left b a)
          have ha_le : a ≤ n := le_trans (Nat.le_mul_of_pos_right a (Nat.zero_lt_of_lt hb)) hq_le
          have hb_le : b ≤ n := le_trans (Nat.le_mul_of_pos_left b (Nat.zero_lt_of_lt ha)) hq_le
          exact hcop.mul_dvd_of_dvd_of_dvd (iha hsqa ha_le) (ihb hsqb hb_le)
    rw [hIcc_eq, ← Finset.sum_sdiff (Finset.inter_subset_right : Finset.Icc 1 n ∩ A ⊆ A),
      add_sub_cancel_right, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsdiff_sub : ∀ d ∈ A \ (Finset.Icc 1 n ∩ A), n < d := by
      intro d hd
      simp_rw [Finset.mem_sdiff, Finset.mem_inter, A, Nat.mem_divisors] at hd
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 hM_pos
      by_contra hle
      push Not at hle
      exact hd.2 ⟨Finset.mem_Icc.mpr ⟨hd_pos, hle⟩, hd.1⟩
    let eSub : {d : ℕ // d ∈ A \ (Finset.Icc 1 n ∩ A)} ↪ {q : ℕ // n < q} :=
      ⟨fun x => ⟨x.1, hsdiff_sub x.1 x.2⟩,
        fun _ _ h => Subtype.ext (congrArg (fun z : {q : ℕ // n < q} => z.1) h)⟩
    have hsum_le :
        (∑ d ∈ A \ (Finset.Icc 1 n ∩ A), |f d|) =
          ∑ x : {d : ℕ // d ∈ A \ (Finset.Icc 1 n ∩ A)}, |f x.1| := by
      rw [← Finset.sum_coe_sort]
    rw [hsum_le]
    have hs_sub : Summable fun x : {q : ℕ // n < q} => |f x.1| := hf_sum.subtype _
    have himg :
        ∑ x : {d : ℕ // d ∈ A \ (Finset.Icc 1 n ∩ A)}, |f x.1| =
          ∑ y ∈ Finset.univ.map eSub, |f y.1| := by
      rw [Finset.sum_map]; rfl
    rw [himg]
    exact hs_sub.sum_le_tsum _ (fun _ _ => abs_nonneg _)
  have hprod_sub :
      Tendsto (fun n => (∏ p ∈ S n, (1 + f (p : ℕ))) - ∑ q ∈ Finset.Icc 1 n, f q)
        atTop (𝓝 ((∏' p : Nat.Primes, (1 + f p)) - ∑' q : ℕ, f q)) :=
    hprod_tendsto.sub hsum_tendsto
  exact sub_eq_zero.mp (tendsto_nhds_unique hprod_sub hdiff_tendsto) |>.symm

/-- **Euler product for the ternary Goldbach singular series**:
`goldbachTernarySingularSeries N = ∏' p : Nat.Primes, (1 + singularTermTernary p N)`. -/
theorem goldbachTernarySingularSeries_eq_tprod (N : ℕ) :
    Multipliable (fun p : Nat.Primes => 1 + singularTermTernary p N) ∧
      goldbachTernarySingularSeries N =
        ∏' p : Nat.Primes, (1 + singularTermTernary p N) :=
  tsum_eq_tprod_prime_one_add (f := fun q => singularTermTernary q N)
    (singularTermTernary_zero N) (singularTermTernary_one N)
    (fun hcop => singularTermTernary_mul_coprime hcop N)
    (fun hp hk => singularTermTernary_prime_pow_eq_zero hp hk N)
    (summable_abs_singularTermTernary N)

/-- **Euler product for the binary Goldbach singular series** (`1 ≤ N`):
`goldbachBinarySingularSeries N = ∏' p : Nat.Primes, (1 + singularTermBinary p N)`. -/
theorem goldbachBinarySingularSeries_eq_tprod {N : ℕ} (hN : 1 ≤ N) :
    Multipliable (fun p : Nat.Primes => 1 + singularTermBinary p N) ∧
      goldbachBinarySingularSeries N =
        ∏' p : Nat.Primes, (1 + singularTermBinary p N) :=
  tsum_eq_tprod_prime_one_add (f := fun q => singularTermBinary q N)
    (singularTermBinary_zero N) (singularTermBinary_one N)
    (fun hcop => singularTermBinary_mul_coprime hcop N)
    (fun hp hk => singularTermBinary_prime_pow_eq_zero hp hk N)
    (summable_abs_singularTermBinary hN)

/-- The ternary Goldbach singular series vanishes for every even `N`. -/
theorem goldbachTernarySingularSeries_eq_zero_of_even {N : ℕ} (hN : Even N) :
    goldbachTernarySingularSeries N = 0 := by
  obtain ⟨_hmult, heq⟩ := goldbachTernarySingularSeries_eq_tprod N
  rw [heq]
  have h2 : (1 + singularTermTernary ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) N) = 0 := by
    rw [singularTermTernary_prime Nat.prime_two N]
    simp only [even_iff_two_dvd.mp hN, ↓reduceIte]
    norm_num
  have hp2 : Summable fun p : Nat.Primes => ‖1 + singularTermTernary p N - 1‖ := by
    simp only [add_sub_cancel_left, Real.norm_eq_abs]
    exact (summable_abs_singularTermTernary N).comp_injective Subtype.val_injective
  rw [AnalyticNumberTheory.AnalyticTools.Gamma.tprod_eq_zero_iff_exists_eq_zero hp2]
  exact ⟨⟨2, Nat.prime_two⟩, h2⟩

/-- The binary Goldbach singular series vanishes on odd inputs by its Euler factor at two. -/
theorem goldbachBinarySingularSeries_eq_zero_of_odd {N : ℕ} (hN : Odd N) :
    goldbachBinarySingularSeries N = 0 := by
  have hpos : 1 ≤ N := by obtain ⟨k, hk⟩ := hN; omega
  rw [(goldbachBinarySingularSeries_eq_tprod hpos).2]
  apply tprod_of_exists_eq_zero
  refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
  rw [singularTermBinary_prime Nat.prime_two]
  have h2 : ¬ 2 ∣ N := fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  norm_num [h2]

/-- Universal prime-product lower factor used to bound both `S₃(N)` (odd `N`) and `S₂(N)` (even `N`):
`2` at `p = 2` and `1 - 1 / (p - 1)^2` at odd primes `p ≥ 3`. -/
private def twinPrimeLowerFactor (p : Nat.Primes) : ℝ :=
  if (p : ℕ) = 2 then 2 else 1 - 1 / ((p : ℝ) - 1) ^ 2

private lemma twinPrimeLowerFactor_pos (p : Nat.Primes) : 0 < twinPrimeLowerFactor p := by
  dsimp [twinPrimeLowerFactor]
  split_ifs with hp2
  · norm_num
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h2 := p.2.two_le
      exact_mod_cast (by omega : 3 ≤ (p : ℕ))
    have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hinv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
    linarith

private lemma summable_abs_twinPrimeLowerFactor_sub_one :
    Summable fun p : Nat.Primes => |twinPrimeLowerFactor p - 1| := by
  have hs : Summable fun n : ℕ => 4 * ((n : ℝ) ^ 2)⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).mul_left 4 |>.congr
      fun n => by simp
  refine (hs.comp_injective Subtype.val_injective).of_nonneg_of_le (fun _ => abs_nonneg _)
    fun p => ?_
  change |twinPrimeLowerFactor p - 1| ≤ 4 * (((p : ℕ) : ℝ) ^ 2)⁻¹
  dsimp [twinPrimeLowerFactor]
  split_ifs with hp2
  · rw [hp2]; norm_num
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h2 := p.2.two_le
      exact_mod_cast (by omega : 3 ≤ (p : ℕ))
    have hsub_ge : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hsq : ((p : ℝ) / 2) ^ 2 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hinv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
      rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)]
      have hsub2 : (p : ℝ) ^ 2 / 4 ≤ ((p : ℝ) - 1) ^ 2 := by linarith
      have hmul : 1 ≤ ((p : ℝ) - 1) ^ 2 * (4 * ((p : ℝ) ^ 2)⁻¹) := by
        calc
          1 = (p : ℝ) ^ 2 / 4 * (4 * ((p : ℝ) ^ 2)⁻¹) := by field_simp [hp0.ne']
          _ ≤ ((p : ℝ) - 1) ^ 2 * (4 * ((p : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_right hsub2 (by positivity)
      linarith
    have hpos_term : 0 < 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    rw [show 1 - 1 / ((p : ℝ) - 1) ^ 2 - 1 = -(1 / ((p : ℝ) - 1) ^ 2) by ring,
      abs_neg, abs_of_pos hpos_term]
    exact hinv

private lemma multipliable_twinPrimeLowerFactor : Multipliable twinPrimeLowerFactor :=
  AnalyticNumberTheory.AnalyticTools.Gamma.multipliable_of_summable_norm_sub_one
    (by simpa [Real.norm_eq_abs] using summable_abs_twinPrimeLowerFactor_sub_one)

private lemma one_le_twinPrimeLowerFactor_tprod :
    1 ≤ ∏' p : Nat.Primes, twinPrimeLowerFactor p := by
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  let shift (p : Nat.Primes) := (p:ℕ)-1
  refine ge_of_tendsto multipliable_twinPrimeLowerFactor.hasProd ?_
  filter_upwards [eventually_ge_atTop ({two}:Finset Nat.Primes)] with S hS
  have htwo : two ∈ S := hS (by simp)
  have hp (p : Nat.Primes) (hn : p ∈ S.erase two) : (p:ℕ)≠2 := by
    intro h
    exact (mem_erase.mp hn).1 (Subtype.ext h)
  have hs : ∀ n∈(S.erase two).image shift, 2≤n := by
    intro n hn
    obtain ⟨p,hpS,rfl⟩ := mem_image.mp hn
    dsimp only [shift]
    have := hp p hpS
    have := p.2.two_le
    omega
  have hinj : Function.Injective shift := by
    intro p q he
    apply Subtype.ext
    dsimp only [shift] at he
    have := p.2.two_le
    have := q.2.two_le
    omega
  have he := AnalyticNumberTheory.AnalyticTools.half_le_prod_one_sub_inv_sq hs
  rw [prod_image hinj.injOn] at he
  have hprod : ∏ p ∈ S.erase two, twinPrimeLowerFactor p =
      ∏ p ∈ S.erase two, (1-1/((shift p:ℕ):ℝ)^2) := by
    apply prod_congr rfl
    intro p hpS
    simp [twinPrimeLowerFactor,hp p hpS,shift,Nat.cast_sub p.2.one_lt.le]
  rw [← mul_prod_erase S twinPrimeLowerFactor htwo,hprod,
    show twinPrimeLowerFactor two=2 by simp [twinPrimeLowerFactor,two]]
  linarith only [he]

private lemma prod_le_prod_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_mem : a ∈ insert a s := Finset.mem_insert_self a s
      have hs_sub : s ⊆ insert a s := Finset.subset_insert a s
      have hf_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (hs_sub hi)
      have hg_nonneg : 0 ≤ g a := (hf a ha_mem).trans (hfg a ha_mem)
      have hprod_nn : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf_s
      exact mul_le_mul (hfg a ha_mem) (ih hf_s fun i hi => hfg i (hs_sub hi)) hprod_nn hg_nonneg

/-- The ternary Goldbach singular series is at least one on odd inputs. -/
theorem one_le_goldbachTernarySingularSeries_of_odd {N : ℕ} (hN_odd : Odd N) :
    1 ≤ goldbachTernarySingularSeries N := by
  apply one_le_twinPrimeLowerFactor_tprod.trans
  obtain ⟨hmult_N, heq_N⟩ := goldbachTernarySingularSeries_eq_tprod N
  rw [heq_N]
  refine le_of_tendsto_of_tendsto' multipliable_twinPrimeLowerFactor.hasProd hmult_N.hasProd fun S => ?_
  refine prod_le_prod_of_nonneg S (fun p _ => (twinPrimeLowerFactor_pos p).le) fun p _ => ?_
  rw [singularTermTernary_prime p.2 N]
  dsimp [twinPrimeLowerFactor]
  by_cases hp2 : (p : ℕ) = 2
  · have hnd : ¬ (2 ∣ N) := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hN_odd
    simp [hp2, hnd]
    norm_num
  · simp only [hp2, ↓reduceIte]
    split_ifs with hdvd
    · exact le_rfl
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have h2 := p.2.two_le
        exact_mod_cast (by omega : 3 ≤ (p : ℕ))
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      linarith [show (0 : ℝ) < 1 / ((p : ℝ) - 1) ^ 2 by positivity,
        show (0 : ℝ) < 1 / ((p : ℝ) - 1) ^ 3 by positivity]

/-- The binary Goldbach singular series is at least one on positive even inputs. -/
theorem one_le_goldbachBinarySingularSeries_of_even {N : ℕ} (hN_even : Even N) (hN2 : 2≤N) :
    1 ≤ goldbachBinarySingularSeries N := by
  apply one_le_twinPrimeLowerFactor_tprod.trans
  obtain ⟨hmult_N, heq_N⟩ := goldbachBinarySingularSeries_eq_tprod (by omega : 1 ≤ N)
  rw [heq_N]
  refine le_of_tendsto_of_tendsto' multipliable_twinPrimeLowerFactor.hasProd hmult_N.hasProd fun S => ?_
  refine prod_le_prod_of_nonneg S (fun p _ => (twinPrimeLowerFactor_pos p).le) fun p _ => ?_
  rw [singularTermBinary_prime p.2 N]
  dsimp [twinPrimeLowerFactor]
  by_cases hp2 : (p : ℕ) = 2
  · have hd : 2 ∣ N := even_iff_two_dvd.mp hN_even
    simp [hp2, hd]
    norm_num
  · simp only [hp2, ↓reduceIte]
    split_ifs with hdvd
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have h2 := p.2.two_le
        exact_mod_cast (by omega : 3 ≤ (p : ℕ))
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      linarith [show (0 : ℝ) < 1 / ((p : ℝ) - 1) by positivity,
        show (0 : ℝ) < 1 / ((p : ℝ) - 1) ^ 2 by positivity]
    · exact le_rfl

/-- Uniform positivity of the ternary singular series for odd inputs. -/
theorem goldbachTernarySingularSeries_pos_of_odd :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, Odd N → c ≤ goldbachTernarySingularSeries N :=
  ⟨1, zero_lt_one, fun _ => one_le_goldbachTernarySingularSeries_of_odd⟩

/-- Uniform positivity of the binary singular series for positive even inputs. -/
theorem goldbachBinarySingularSeries_pos_of_even :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, Even N → 2 ≤ N → c ≤ goldbachBinarySingularSeries N :=
  ⟨1, zero_lt_one, fun _ => one_le_goldbachBinarySingularSeries_of_even⟩

end SingularSeriesAndPositivity

end AnalyticNumberTheory.AdditiveNumberTheory
