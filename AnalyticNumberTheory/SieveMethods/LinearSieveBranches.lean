import AnalyticNumberTheory.SieveMethods.LinearSieveSmallPrimes
import AnalyticNumberTheory.SieveMethods.LinearSieveTerminal

/-!
# Arithmetic data on a branch of the linear sieve

At an accepted node d the combination of large primes is coprime to the
remaining sifting modulus. The small-prime lemma on the subsequence of
multiples of d therefore has remainder r(de), at the original level.
-/
noncomputable section
open Finset Set Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The arithmetic sequence restricted to multiples of d. -/
def SieveData.atMultiple (s : SieveData) (d : ℕ) : SieveData :=
  {s with A:=sieveMultiple s.A d,X:=s.X*s.density d}

theorem sieveMultiple_coprime {d e : ℕ} (hc : d.Coprime e) (A : Finset ℕ) :
    sieveMultiple (sieveMultiple A d) e=sieveMultiple A (d*e) := by
  ext n; simp only [mem_sieveMultiple_iff]; constructor
  · rintro ⟨⟨hn,hd⟩,he⟩; exact ⟨hn,hc.mul_dvd_of_dvd_of_dvd hd he⟩
  · rintro ⟨hn,hde⟩; exact ⟨⟨hn,(dvd_mul_right d e).trans hde⟩,(dvd_mul_left e d).trans hde⟩

theorem SieveData.atMultiple_rem (s : SieveData) {d e : ℕ} (hc : d.Coprime e) :
    (s.atMultiple d).rem e=s.rem (d*e) := by
  change (↑(sieveMultiple (sieveMultiple s.A d) e).card:ℝ)-s.density e*(s.X*s.density d)=_
  rw [sieveMultiple_coprime hc]
  change _ = _-s.densityArith (d*e)*s.X
  rw [s.densityArith_isMultiplicative.map_mul_of_coprime hc]
  change _ = _-(s.density d*s.density e)*s.X; ring

/-- Conditions on the prefix already selected above the cutoff z. -/
structure LinearSieveBranch (P : Finset ℕ) (Z L : ℝ) (d : ℕ) (Y z : ℝ) : Prop where
  dvd : d∣sieveProductBelow P Z
  coprime : d.Coprime (sieveProductBelow P z)
  level : Y=L-log d

private theorem lower_product_dvd {P : Finset ℕ} {a z : ℝ} (ha : a≤z) :
    sieveProductBelow P a∣sieveProductBelow P z := Finset.prod_dvd_prod_of_subset _ _ _
      (fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans_le ha⟩)

theorem LinearSieveBranch.child {P : Finset ℕ} {w z Z Y L : ℝ} {d p : ℕ}
    (hP : ∀p∈P,p.Prime) (hz : z≤Z) (hp : p∈sievePrimeWindow P w z)
    (h : LinearSieveBranch P Z L d Y z) :
    d.Coprime p ∧ LinearSieveBranch P Z L (d*p) (Y-log p) p := by
  obtain ⟨hPp,_,hpz⟩ := mem_filter.mp hp
  have hpD : p∣sieveProductBelow P z := dvd_prod_of_mem _ (mem_filter.mpr ⟨hPp,hpz⟩)
  have hc := h.coprime.of_dvd_right hpD
  have hdp : d≠0 := fun he => (sieveProductBelow_squarefree hP Z).ne_zero (zero_dvd_iff.mp (he ▸ h.dvd))
  have hcp : p.Coprime (sieveProductBelow P p) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq; obtain ⟨hqP,hqp⟩ := mem_filter.mp hq
    exact (Nat.coprime_primes (hP _ hPp) (hP _ hqP)).mpr (by exact_mod_cast (ne_of_gt hqp))
  refine ⟨hc,⟨hc.mul_dvd_of_dvd_of_dvd h.dvd (hpD.trans (lower_product_dvd hz)),
    (Nat.coprime_mul_iff_left.mpr ⟨h.coprime.of_dvd_right (lower_product_dvd hpz.le),hcp⟩),?_⟩⟩
  rw [h.level,Nat.cast_mul,Real.log_mul (by exact_mod_cast hdp) (by exact_mod_cast (hP _ hPp).ne_zero)]
  ring

/-- The local divisor errors, at the original level exp(L), having d as
their already determined large-prime part. -/
def linearSieveBudget (P : Finset ℕ) (r : ℕ → ℝ) (L : ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  sieveSubsetBudget (sievePrimesBelow P z) (fun n => if (n:ℝ)<exp L then |r n| else 0) d

theorem linearSieveBudget_nonneg (P : Finset ℕ) (r : ℕ → ℝ) (L : ℝ) (d : ℕ) (z : ℝ) :
    0≤linearSieveBudget P r L d z := sum_nonneg (fun n _ => by dsimp only; split <;> positivity)

theorem linearSieveBudget_window (P : Finset ℕ) (r : ℕ → ℝ) (L : ℝ) (d : ℕ) {w z : ℝ}
    (hwz : w≤z) :
    linearSieveBudget P r L d w+∑p∈sievePrimeWindow P w z,linearSieveBudget P r L (d*p) p=
      linearSieveBudget P r L d z :=
  sieve_divisor_budget_window (P:=P) (fun n : ℕ => if (n:ℝ)<exp L then |r n| else 0) d hwz

theorem linearSieveBudget_divisors {P : Finset ℕ} (hP : ∀p∈P,p.Prime) (r : ℕ → ℝ)
    (L : ℝ) (d : ℕ) (z : ℝ) :
    linearSieveBudget P r L d z=∑e∈(sieveProductBelow P z).divisors.filter (fun e : ℕ => (d*e:ℕ)<(exp L:ℝ)),|r (d*e)| := by
  rw [sum_filter]
  exact sieve_divisor_budget_eq hP (fun n : ℕ => if (n:ℝ)<exp L then |r n| else 0) d z

/-- The small-prime approximation at every admissible prefix, with the
density of that prefix and the correct arithmetic error. -/
theorem linearSieve_small_branch {K : ℝ} (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      ∀ {w z Z L Y : ℝ} {d : ℕ}, 2≤w → w≤z → log w≤Y →
        SieveEulerDimensionOne P s.density w K → LinearSieveBranch P Z L d Y z →
        ∀ b, |(siftedCountOf (sieveMultiple s.A d) (sieveProductBelow P w):ℝ)-
          (s.X*s.density d)*sieveEulerBelow P s.density w*linearSieveProfile b (Y/log w)|≤
          (s.X*s.density d)*C*linearSieveExpWeight P s.density Y w+linearSieveBudget P s.rem L d w := by
  obtain ⟨C,hC,hh⟩ := linearSieve_small_prime_estimate hK
  refine ⟨C,hC,?_⟩; intro s P hP hX w z Z L Y d hw hwz hY hdim h b
  have hd : 0≤s.density d := (s.withPrimeSet hP).density_nonneg_of_dvd (z:=Z) h.dvd
  have hM := mul_nonneg hX hd
  have hSmall := hh (s.atMultiple d) P hP hM hw hY hdim b
  have hdpNat : 0<d := Nat.pos_of_dvd_of_pos h.dvd (Nat.pos_of_ne_zero (sieveProductBelow_squarefree hP Z).ne_zero)
  have hdp : (0:ℝ)<d := by exact_mod_cast hdpNat
  have hexp : exp Y=exp L/d := by rw [h.level,Real.exp_sub,Real.exp_log hdp]
  have hcop := h.coprime.of_dvd_right (lower_product_dvd hwz)
  have hcut (e : ℕ) : ((e:ℝ)<exp Y) ↔ ((d*e:ℕ):ℝ)<exp L := by
    rw [hexp,lt_div_iff₀ hdp,Nat.cast_mul,mul_comm (d:ℝ)]
  have he : (∑e∈(sieveProductBelow P w).divisors.filter (fun e : ℕ => (e:ℝ)<exp Y),
      |(s.atMultiple d).rem e|)=linearSieveBudget P s.rem L d w := by
    rw [linearSieveBudget_divisors hP]
    simp_rw [hcut]
    apply sum_congr rfl; intro e he
    rw [s.atMultiple_rem (hcop.of_dvd_right (Nat.dvd_of_mem_divisors (mem_filter.mp he).1))]
  rw [he] at hSmall
  change |_-(_*_)*_*_|≤C*(s.X*s.density d)*sieveEulerBelow P s.density w*exp (-(Y/log w))+_ at hSmall
  exact hSmall.trans_eq (by dsimp only [linearSieveExpWeight]; ring)

end AnalyticNumberTheory.SieveMethods
