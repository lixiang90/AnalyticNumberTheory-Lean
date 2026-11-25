import AnalyticNumberTheory.SieveMethods.LinearSieveIteration
import AnalyticNumberTheory.SieveMethods.RosserSiftedCount

/-!
# Buchstab decomposition and arithmetic remainders for the linear sieve

A branch is labelled by the product of its chosen primes. Splitting the
divisor sum by its largest prime keeps the arithmetic remainder at level y
with coefficient one.
-/
noncomputable section
open Finset Set Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- Sifting primes below a strict real cutoff. -/
def sievePrimesBelow (P : Finset ℕ) (z : ℝ) := P.filter (fun p : ℕ => (p:ℝ)<z)

/-- Product of the sifting primes below the given cutoff. -/
def sieveProductBelow (P : Finset ℕ) (z : ℝ) : ℕ := ∏p∈sievePrimesBelow P z,p

theorem sieveProductBelow_squarefree {P : Finset ℕ} (hP : ∀p∈P,p.Prime) (z : ℝ) :
    Squarefree (sieveProductBelow P z) := by
  apply squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p (mem_filter.mp hp).1) (hP q (mem_filter.mp hq).1)).mpr hpq)
  · intro p hp; exact (hP p (mem_filter.mp hp).1).prime.squarefree

theorem sieveProductBelow_primeFactors {P : Finset ℕ} (hP : ∀p∈P,p.Prime) (z : ℝ) :
    (sieveProductBelow P z).primeFactors=sievePrimesBelow P z :=
  Nat.primeFactors_prod (fun p hp => hP p (mem_filter.mp hp).1)

private theorem below_mono (P : Finset ℕ) {w z : ℝ} (hwz : w≤z) :
    sievePrimesBelow P w⊆sievePrimesBelow P z :=
  fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans_le hwz⟩

private theorem below_sdiff (P : Finset ℕ) {w z : ℝ} :
    sievePrimesBelow P z \ sievePrimesBelow P w=sievePrimeWindow P w z := by
  ext p; simp [sievePrimesBelow,sievePrimeWindow]; grind

private theorem below_filter {P : Finset ℕ} {z : ℝ} {p : ℕ} (hp : p∈sievePrimesBelow P z) :
    (sievePrimesBelow P z).filter (·<p)=sievePrimesBelow P p := by
  ext q; simp only [sievePrimesBelow,mem_filter,Nat.cast_lt]
  constructor
  · rintro ⟨⟨hq,_⟩,h⟩; exact ⟨hq,h⟩
  · rintro ⟨hq,h⟩
    exact ⟨⟨hq,(show (q:ℝ)<p by exact_mod_cast h).trans (mem_filter.mp hp).2⟩,h⟩

/-- Buchstab's identity with the same windows as the sieve tree. -/
theorem sieve_buchstab_window (A : Finset ℕ) {P : Finset ℕ} (hP : ∀p∈P,p.Prime) {w z : ℝ}
    (hwz : w≤z) :
    (siftedCountOf A (sieveProductBelow P w):ℝ)=siftedCountOf A (sieveProductBelow P z)+
      ∑p∈sievePrimeWindow P w z,(siftedCountOf (sieveMultiple A p) (sieveProductBelow P p):ℝ) := by
  have h := buchstab_identity_finset A (below_mono P hwz) (fun p hp q hq hpq =>
    mem_filter.mpr ⟨(mem_filter.mp hp).1, (show (p:ℝ)≤q by exact_mod_cast hpq).trans_lt (mem_filter.mp hq).2⟩)
    (fun p hp => hP p (mem_filter.mp hp).1)
  rw [below_sdiff] at h
  have hsum : (∑p∈sievePrimeWindow P w z,siftedCountOf (sieveMultiple A p) (∏q∈(sievePrimesBelow P z).filter (·<p),q))=
      ∑p∈sievePrimeWindow P w z,siftedCountOf (sieveMultiple A p) (sieveProductBelow P p) := by
    apply sum_congr rfl; intro p hp
    rw [below_filter (mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.2⟩)]
    rfl
  rw [hsum] at h
  exact_mod_cast h

private theorem sum_subsets_largest (P : Finset ℕ) (F : Finset ℕ → ℝ) :
    (∑T∈P.powerset,F T)=F ∅+∑p∈P,∑T∈(P.filter (·<p)).powerset,F (insert p T) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a P ha ih =>
    have ha' : a∉P := fun h => lt_irrefl _ (ha _ h)
    have he : (insert a P).filter (·<a)=P := by
      ext p; simp only [mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨h|h,h'⟩; · exact False.elim (h'.ne h)
        · exact h
      · intro h; exact ⟨Or.inr h,ha _ h⟩
    have he' (p : ℕ) (hp : p∈P) : (insert a P).filter (·<p)=P.filter (·<p) := by
      rw [filter_insert,if_neg (not_lt.mpr (ha p hp).le)]
    rw [sum_powerset_insert ha',ih,sum_insert ha',he]
    have H := sum_congr (s₁:=P) rfl (fun p hp => congrArg (fun S : Finset ℕ => ∑T∈S.powerset,F (insert p T)) (he' p hp))
    rw [H]; ring

def sieveSubsetBudget (S : Finset ℕ) (R : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑T∈S.powerset,R (d*∏p∈T,p)

/-- A discrete antiderivative for the budget, with the old branch product d
multiplied by the newly chosen largest prime. -/
private theorem subsetBudget_cumulative (P : Finset ℕ) (R : ℕ → ℝ) (d : ℕ) (z : ℝ) :
    sieveSubsetBudget (sievePrimesBelow P z) R d =
      R d+∑p∈sievePrimesBelow P z,sieveSubsetBudget (sievePrimesBelow P p) R (d*p) := by
  rw [sieveSubsetBudget,sum_subsets_largest]
  congr 1
  · simp
  apply sum_congr rfl; intro p hp; rw [below_filter hp]
  apply sum_congr rfl; intro T hT
  have hnot : p∉T := fun hh => lt_irrefl _ (by exact_mod_cast (mem_filter.mp (mem_powerset.mp hT hh)).2)
  rw [prod_insert hnot,mul_assoc]

/-- The arithmetic remainder budget is partitioned exactly by the next large prime. -/
theorem sieve_divisor_budget_window {P : Finset ℕ} (R : ℕ → ℝ) (d : ℕ) {w z : ℝ} (hwz : w≤z) :
    (∑T∈(sievePrimesBelow P w).powerset,R (d*∏p∈T,p))+
      (∑p∈sievePrimeWindow P w z,∑T∈(sievePrimesBelow P p).powerset,R ((d*p)*∏q∈T,q))=
        ∑T∈(sievePrimesBelow P z).powerset,R (d*∏p∈T,p) := by
  change sieveSubsetBudget (sievePrimesBelow P w) R d+(∑p∈sievePrimeWindow P w z,sieveSubsetBudget (sievePrimesBelow P p) R (d*p))=
    sieveSubsetBudget (sievePrimesBelow P z) R d
  rw [subsetBudget_cumulative P R d w,subsetBudget_cumulative P R d z,←below_sdiff,add_assoc,add_comm (∑p∈sievePrimesBelow P w, _)]
  rw [Finset.sum_sdiff (below_mono P hwz)]

/-- A powerset budget coincides with the usual sum over squarefree divisors. -/
theorem sieve_divisor_budget_eq {P : Finset ℕ} (hP : ∀p∈P,p.Prime) (R : ℕ → ℝ) (d : ℕ) (z : ℝ) :
    (∑T∈(sievePrimesBelow P z).powerset,R (d*∏p∈T,p))=
      ∑e∈(sieveProductBelow P z).divisors,R (d*e) := by
  let D := sieveProductBelow P z
  have hs : Squarefree D := sieveProductBelow_squarefree hP z
  symm; apply sum_bij (fun e _ => e.primeFactors)
  · intro e he; rw [Finset.mem_powerset,←sieveProductBelow_primeFactors hP]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors he) hs.ne_zero
  · intro e he f hf hh
    have h₁ := hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
    have h₂ := hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hf)
    rw [←Nat.prod_primeFactors_of_squarefree h₁,←Nat.prod_primeFactors_of_squarefree h₂,hh]
  · intro T hT
    refine ⟨∏p∈T,p,Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hT),hs.ne_zero⟩,?_⟩
    exact Nat.primeFactors_prod (fun p hp => hP p (mem_filter.mp (mem_powerset.mp hT hp)).1)
  · intro e he
    rw [Nat.prod_primeFactors_of_squarefree (hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors he))]

end AnalyticNumberTheory.SieveMethods
