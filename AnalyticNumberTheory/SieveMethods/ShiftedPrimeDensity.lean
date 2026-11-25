import AnalyticNumberTheory.SieveMethods.LinearSieve
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovPrimeCounting

/-!
# The dimension-one density for a shifted prime

For a fixed nonzero even shift h, a prime divisor not dividing h has
density 1/(p-1) in the shifted sequence. Uniform logarithmic mass bounds
follow from the first theorem of Mertens. Primes dividing h comprise a
fixed finite exceptional set.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

/-- Numerator of the local density of a shift by an integer of absolute value h. -/
def shiftedPrimeOmega (h : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n.Coprime h then (n:ℝ)/n.totient else 0
  map_zero' := by simp

theorem shiftedPrimeOmega_multiplicative (h : ℕ) : (shiftedPrimeOmega h).IsMultiplicative := by
  constructor
  · simp [shiftedPrimeOmega]
  · intro a b hc
    simp only [shiftedPrimeOmega,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left,Nat.totient_mul hc,Nat.cast_mul]
    split_ifs with h₁ h₂ h₃ <;> try ring <;> tauto

private theorem shifted_locals {h p : ℕ} (hh : Even h) (hp : p.Prime) :
    0≤shiftedPrimeOmega h p ∧ shiftedPrimeOmega h p<(p:ℝ) := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
  change 0≤(if p.Coprime h then (p:ℝ)/p.totient else 0) ∧ (if p.Coprime h then (p:ℝ)/p.totient else 0)<p
  by_cases hc : p.Coprime h
  · have hp₃ : 3≤p := by
      have h₂ : p≠2 := fun he => (hp.coprime_iff_not_dvd.mp hc) (he ▸ hh.two_dvd)
      have := hp.two_le; omega
    have hphi : 1<(p.totient:ℝ) := by rw [Nat.totient_prime hp]; exact_mod_cast (by omega : 1<p-1)
    rw [ite_eq_left hc]
    exact ⟨div_nonneg hp'.le (by positivity),div_lt_self hp' hphi⟩
  · rw [ite_eq_right hc]; exact ⟨le_rfl,hp'⟩

/-- Arithmetic sieve datum using the shifted-prime local density. -/
def shiftedPrimeSieveData (A : Finset ℕ) (X : ℝ) (h : ℕ) (hh : Even h) : SieveData where
  A := A
  X := X
  prodPrimes := fun _ => 1
  prodPrimes_squarefree := fun _ => squarefree_one
  omega := shiftedPrimeOmega h
  omega_mult := shiftedPrimeOmega_multiplicative h
  omega_nonneg_of_prime := fun _ hp => (shifted_locals hh hp).1
  omega_lt_of_prime := fun _ hp => (shifted_locals hh hp).2

theorem shiftedPrime_density (A : Finset ℕ) (X : ℝ) {h : ℕ} (hh : Even h) {d : ℕ}
    (hd : d≠0) (hc : d.Coprime h) :
    (shiftedPrimeSieveData A X h hh).density d=1/(d.totient:ℝ) := by
  change (if d.Coprime h then (d:ℝ)/d.totient else 0)/d=_
  rw [ite_eq_left hc]; field_simp [show (d:ℝ)≠0 by exact_mod_cast hd]

/-- Primes available for sifting, with the fixed prime divisors of h removed. -/
def shiftedSievePrimes (h : ℕ) (z : ℝ) := (primeFinsetLT z).filter (fun p => p.Coprime h)

theorem mem_shiftedSievePrimes {h p : ℕ} {z : ℝ} :
    p∈shiftedSievePrimes h z ↔ p.Prime ∧ (p:ℝ)<z ∧ p.Coprime h := by
  simp [shiftedSievePrimes,mem_primeFinsetLT_iff,and_assoc]

theorem shiftedPrime_separation (A : Finset ℕ) (X : ℝ) {h : ℕ} (hh : Even h) {z : ℝ} :
    ∀p∈shiftedSievePrimes h z,(shiftedPrimeSieveData A X h hh).density p≤1-1/(2:ℝ) := by
  intro p hp; obtain ⟨hp,_,hc⟩ := mem_shiftedSievePrimes.mp hp
  have hp₃ : 3≤p := by
    have h₂ : p≠2 := fun he => (hp.coprime_iff_not_dvd.mp hc) (he ▸ hh.two_dvd)
    have := hp.two_le; omega
  rw [shiftedPrime_density A X hh hp.ne_zero hc,Nat.totient_prime hp]
  have hh' : (2:ℝ)≤↑(p-1) := by exact_mod_cast (by omega : 2≤p-1)
  exact (one_div_le_one_div_of_le (by norm_num) hh').trans_eq (by norm_num)

private theorem mertens_strict {t : ℝ} (ht : 2≤t) :
    |(∑p∈primeFinsetLT t,log p/p)-log t|≤mertensOneBound+1 := by
  let S := primeFinset t
  let T := primeFinsetLT t
  have hsub : T⊆S := filter_subset ..
  have hsum : (∑p∈S,log p/p)=(∑p∈S\T,log p/p)+(∑p∈T,log p/p) := (sum_sdiff hsub).symm
  have hone : S\T⊆{⌊t⌋₊} := by
    intro p hp; obtain ⟨hs,hn⟩ := mem_sdiff.mp hp
    obtain ⟨hP,hpt⟩ := mem_primeFinset_iff.mp hs
    have he : (p:ℝ)=t := le_antisymm hpt (not_lt.mp (fun hl => hn (mem_primeFinsetLT_iff.mpr ⟨hP,hl⟩)))
    rw [←he,Nat.floor_natCast]; simp
  have hterm (p : ℕ) (hp : p∈S) : 0≤log p/p ∧ log p/p≤1 := by
    have hP := (mem_primeFinset_iff.mp hp).1
    have hp' : (0:ℝ)<p := by exact_mod_cast hP.pos
    exact ⟨div_nonneg (log_nonneg (by exact_mod_cast hP.one_lt.le)) hp'.le,
      (div_le_one hp').mpr ((Real.log_le_sub_one_of_pos hp').trans (by linarith))⟩
  have htail : (∑p∈S\T,log p/p)≤1 := by
    apply (sum_le_sum (fun p hp => (hterm p (mem_sdiff.mp hp).1).2)).trans
    simpa only [sum_const, nsmul_eq_mul,mul_one,Finset.card_singleton,Nat.cast_one] using!
      (show (((S\T).card:ℕ):ℝ)≤(({⌊t⌋₊}:Finset ℕ).card:ℝ) by exact_mod_cast Finset.card_le_card hone)
  have H := abs_le.mp (abs_mertens_one_sub_log_le (by linarith : 1≤t))
  change -(mertensOneBound)≤(∑p∈S,log p/p)-log t ∧ (∑p∈S,log p/p)-log t≤mertensOneBound at H
  have hpos := sum_nonneg (s:=S\T) (fun p hp => (hterm p (mem_sdiff.mp hp).1).1)
  change |(∑p∈T,log p/p)-log t|≤_
  rw [abs_le]; constructor <;> linarith only [hsum,H.1,H.2,htail,hpos]

private theorem prime_correction_sum :
    ∃ C : ℝ, 0≤C ∧ ∀ S : Finset ℕ, (∀p∈S,p.Prime) →
      (∑p∈S,log p/((p:ℝ)*(p-1)))≤C := by
  let F := fun n : ℕ => (n:ℝ)^(-(3/2:ℝ))
  have hF : Summable F := Real.summable_nat_rpow.mpr (by norm_num)
  have hFn (n : ℕ) : 0≤F n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨4*∑'n,F n,mul_nonneg (by norm_num) (tsum_nonneg hFn),?_⟩
  intro S hP
  calc _ ≤ ∑p∈S,4*F p := by
          apply sum_le_sum; intro p hp
          have hp₂ : (2:ℝ)≤p := by exact_mod_cast (hP p hp).two_le
          have hp₀ : (0:ℝ)<p := by linarith
          have hs := Real.sq_sqrt hp₀.le
          have hlog : log p≤2*sqrt p := by
            have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp₀)
            rw [Real.log_sqrt hp₀.le] at hh; linarith
          have hs' : 0<sqrt p := Real.sqrt_pos.mpr hp₀
          have he : F p=1/((p:ℝ)*sqrt p) := by
            dsimp only [F]; rw [Real.rpow_neg hp₀.le,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hp₀,
              Real.rpow_one,←Real.sqrt_eq_rpow,one_div]
          rw [he,div_le_iff₀ (mul_pos hp₀ (by linarith))]
          field_simp [hs'.ne',hp₀.ne']
          nlinarith only [mul_le_mul_of_nonneg_right hlog hs'.le,hs,hp₂]
       _ = 4*∑p∈S,F p := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (hF.sum_le_tsum S (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by norm_num)


/-- Fixed logarithmic mass discrepancy for the local factors 1/(p-1).
The constants depend on h alone. -/
theorem shiftedPrime_log_mass {h : ℕ} (hh : Even h) (hh₀ : h≠0) :
    ∃ K : ℝ, 0≤K ∧ ∀ (A : Finset ℕ) (X z : ℝ),
      SieveLogMassBounds (shiftedSievePrimes h z) (shiftedPrimeSieveData A X h hh).density 2 z K K := by
  obtain ⟨C,hC,hcorr⟩ := prime_correction_sum
  let G := ∑p∈h.primeFactors, log p/p
  have hnn {p : ℕ} (hp : p.Prime) : 0≤log p/p :=
    div_nonneg (log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg _)
  have hG : 0≤G := sum_nonneg (fun p hp => hnn (Nat.prime_of_mem_primeFactors hp))
  let D := mertensOneBound+1+G+C
  have hD : 0≤D := by dsimp only [D]; linarith [mertensOneBound_pos]
  refine ⟨2*D,by positivity,?_⟩
  intro A X z
  let g := (shiftedPrimeSieveData A X h hh).density
  let S := shiftedSievePrimes h
  have hcum (t : ℝ) (ht : 2≤t) : |(∑p∈S t,g p*log p)-log t|≤D := by
    let T := primeFinsetLT t
    have hsub : S t⊆T := filter_subset ..
    have hd : T\S t ⊆ h.primeFactors := by
      intro p hp; obtain ⟨hp,hn⟩ := mem_sdiff.mp hp
      have hP := (mem_primeFinsetLT_iff.mp hp).1
      have hc : ¬p.Coprime h := fun hc => hn (mem_filter.mpr ⟨hp,hc⟩)
      exact Nat.mem_primeFactors.mpr ⟨hP,hP.dvd_iff_not_coprime.mpr hc,hh₀⟩
    have hT := abs_le.mp (mertens_strict ht)
    have hsplit : (∑p∈T\S t,log p/p)+(∑p∈S t,log p/p)=∑p∈T,log p/p := sum_sdiff hsub
    have hdel : (∑p∈T\S t,log p/p)≤G := sum_le_sum_of_subset_of_nonneg hd (fun p hp _ => hnn (Nat.prime_of_mem_primeFactors hp))
    have hpos : 0≤∑p∈T\S t,log p/p := sum_nonneg (fun p hp => hnn (prime_of_mem_primeFinsetLT (mem_sdiff.mp hp).1))
    have hpar (p : ℕ) (hp : p∈S t) := (mem_shiftedSievePrimes.mp hp).1
    have he : (∑p∈S t,g p*log p)=(∑p∈S t,log p/p)+(∑p∈S t,log p/((p:ℝ)*(p-1))) := by
      rw [←sum_add_distrib]; apply sum_congr rfl; intro p hp
      have ⟨hP,_,hc⟩ := mem_shiftedSievePrimes.mp hp
      dsimp only [g]; rw [shiftedPrime_density A X hh hP.ne_zero hc,Nat.totient_prime hP,Nat.cast_sub (by have := hP.two_le; omega),Nat.cast_one]
      have hp' : (2:ℝ)≤p := by exact_mod_cast hP.two_le
      field_simp [show (p:ℝ)≠0 by linarith,show (p:ℝ)-1≠0 by linarith] <;> ring
    have hcorr' := hcorr (S t) hpar
    have hcpos : 0≤∑p∈S t,log p/((p:ℝ)*(p-1)) := by
      apply sum_nonneg; intro p hp; have hp' : (2:ℝ)≤p := by exact_mod_cast (hpar p hp).two_le
      positivity [log_nonneg (by linarith : 1≤(p:ℝ)),show 0≤(p:ℝ)-1 by linarith]
    rw [he,abs_le]; dsimp only [D]; change -(mertensOneBound+1)≤(∑p∈T,log p/p)-log t ∧ (∑p∈T,log p/p)-log t≤mertensOneBound+1 at hT
    constructor <;> linarith only [hT.1,hT.2,hdel,hpos,hsplit,hcorr',hcpos,hC,hG]
  intro a b ha hab hb
  have hsub : S a⊆S b := fun p hp => mem_shiftedSievePrimes.mpr
    ⟨(mem_shiftedSievePrimes.mp hp).1,(mem_shiftedSievePrimes.mp hp).2.1.trans_le hab,(mem_shiftedSievePrimes.mp hp).2.2⟩
  have he : (shiftedSievePrimes h z).filter (fun p : ℕ => a≤p ∧ (p:ℝ)<b)=S b\S a := by
    ext p; simp [S,mem_shiftedSievePrimes]; grind
  rw [he,Real.log_div (by linarith) (by linarith)]
  have hsum := Finset.sum_sdiff (f:=fun p : ℕ => g p*log p) hsub
  have H₁ := abs_le.mp (hcum a ha)
  have H₂ := abs_le.mp (hcum b (ha.trans hab))
  change -(2*D)≤(∑p∈S b\S a,g p*log p)-(log b-log a) ∧ _
  constructor <;> linarith only [hsum,H₁.1,H₁.2,H₂.1,H₂.2]


end AnalyticNumberTheory.SieveMethods
