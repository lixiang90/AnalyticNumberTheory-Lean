import AnalyticNumberTheory.SieveMethods.BrunTitchmarshReduction

/-! # Finite wheel sieve for primes in progressions

Legendre inclusion-exclusion gives a discrepancy of at most one per divisor
in a real interval. Selberg's translation retains the totient density for
an arbitrary modulus.
-/
noncomputable section
open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private theorem bt_multiple_count {a b d : ℕ} (hab : a≤b) :
    (sieveMultiple (Ioc a b) d).card=b/d-a/d := by
  let M := fun n => (range (n+1)).filter (fun k => k≠0 ∧ d∣k)
  have hsub : M a⊆M b := by
    intro k hk
    obtain ⟨hk,H⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hk; omega),H⟩
  have he : sieveMultiple (Ioc a b) d=M b \ M a := by
    ext k
    simp [sieveMultiple,M]
    omega
  rw [he,card_sdiff_of_subset hsub]
  exact congrArg₂ (·-·) (Nat.card_multiples' b d) (Nat.card_multiples' a d)

private theorem bt_multiple_discrepancy {x u : ℝ} (hx : 0≤x) (hu : 0≤u) {d : ℕ} (hd : 0<d) :
    |((sieveMultiple (Ioc ⌊x⌋₊ ⌊x+u⌋₊) d).card:ℝ)-u*(d:ℝ)⁻¹|≤1 := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hm : ⌊x⌋₊≤⌊x+u⌋₊ := Nat.floor_mono (by linarith)
  rw [bt_multiple_count hm,Nat.cast_sub (Nat.div_le_div_right hm),←Nat.floor_div_natCast,
    ←Nat.floor_div_natCast,abs_le]
  have H := Nat.floor_le (div_nonneg (add_nonneg hx hu) hd'.le)
  have J := Nat.floor_le (div_nonneg hx hd'.le)
  have A := Nat.sub_one_lt_floor ((x+u)/d)
  have B := Nat.sub_one_lt_floor (x/d)
  rw [add_div] at H A ⊢
  rw [←div_eq_mul_inv]
  constructor <;> linarith

/-- A real interval contains at most its wheel density times its length
plus one unit of discrepancy per squarefree divisor of the wheel. -/
theorem bt_wheel_interval {x u : ℝ} (hx : 0≤x) (hu : 0≤u) (z : ℝ) :
    (siftedCountOf (Ioc ⌊x⌋₊ ⌊x+u⌋₊) (primeProd z):ℝ) ≤
      u*(∏ p∈primeFinset z,(1-(p:ℝ)⁻¹)) + (2:ℝ)^(primeFinset z).card := by
  let A := Ioc ⌊x⌋₊ ⌊x+u⌋₊
  let W := primeProd z
  have hW : W≠0 := primeProd_ne_zero z
  let ν : ArithmeticFunction ℝ := ⟨fun d : ℕ => (d:ℝ)⁻¹,by simp⟩
  have hν : ν.IsMultiplicative := by
    constructor
    · simp [ν]
    · intro m n _
      simp [ν,Nat.cast_mul] <;> ring
  have hprod := hν.prodPrimeFactors_one_sub ν hW
  change (∏ p∈W.primeFactors,(1-(p:ℝ)⁻¹)) = ∑ d∈W.divisors,(μ d:ℝ)*(d:ℝ)⁻¹ at hprod
  have hcard : W.divisors.card=2^(primeFinset z).card := by
    rw [Nat.card_divisors hW]
    calc _ = ∏ p∈W.primeFactors,2 := by
            apply prod_congr rfl
            intro p hp
            rw [Nat.factorization_eq_one_of_squarefree (primeProd_squarefree z)
              (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
         _ = _ := by rw [show W.primeFactors=primeFinset z from primeFactors_primeProd z]; simp
  rw [legendre_inclusion_exclusion A hW,←primeFactors_primeProd z,hprod,mul_sum]
  calc _ ≤ ∑d∈W.divisors,(u*((μ d:ℝ)*(d:ℝ)⁻¹)+1) := by
          apply sum_le_sum; intro d hd
          have D := bt_multiple_discrepancy hx hu (Nat.pos_of_mem_divisors hd)
          have M : |(μ d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
          have H := mul_le_mul M D (abs_nonneg _) zero_le_one
          rw [←abs_mul,one_mul] at H
          have H' := (abs_le.mp H).2
          change (μ d:ℝ)*(sieveMultiple A d).card ≤ _
          change (μ d:ℝ)*((sieveMultiple A d).card-u*(d:ℝ)⁻¹)≤1 at H'
          linarith only [H']
       _ = _ := by rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,hcard,Nat.cast_pow,Nat.cast_ofNat,primeFactors_primeProd]

/-- The wheel majorant for the prime-progression counting function. The
additive prime count includes all primes at or below the wheel cutoff. -/
theorem brun_titchmarsh_wheel {x y : ℝ} {q a : ℕ} (hx : 0≤x) (hy : 0<y)
    (hq : 1≤q) (z : ℝ) :
    (piAP (x+y) q a-piAP x q a)*(q.totient:ℝ) ≤ q*
      ((y/q)*(∏ p∈primeFinset z,(1-(p:ℝ)⁻¹)) + 2^(primeFinset z).card+(primeFinset z).card) := by
  apply brun_titchmarsh_of_rough_interval hx hy hq z
  intro t ht T hI hr
  have hsub : T⊆(Ioc ⌊t⌋₊ ⌊t+y/q⌋₊).filter (fun n : ℕ => Nat.Coprime n (primeProd z)) := by
    intro n hn
    refine mem_filter.mpr ⟨hI hn,?_⟩
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hh
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hh
    have hdW := hpd.trans (Nat.gcd_dvd_right ..)
    exact hr n hn p hp.one_lt ((prime_dvd_primeProd_iff hp).mp hdW)
      (hpd.trans (Nat.gcd_dvd_left ..))
  have hcount : (T.card:ℝ)≤siftedCountOf (Ioc ⌊t⌋₊ ⌊t+y/q⌋₊) (primeProd z) := by
    exact_mod_cast card_le_card hsub
  exact hcount.trans (bt_wheel_interval ht (div_nonneg hy.le (Nat.cast_nonneg _)) z)

end AnalyticNumberTheory.SieveMethods
