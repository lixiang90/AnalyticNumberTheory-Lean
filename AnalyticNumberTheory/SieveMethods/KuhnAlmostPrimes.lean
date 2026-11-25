import AnalyticNumberTheory.SieveMethods.KuhnRemainders
import AnalyticNumberTheory.SieveMethods.ShiftedPrimeProgressions

/-!
# The combinatorial inequality in the weighted sieve

An integer below t³ has at most two prime factors at least t, counted with
multiplicity. Thus a sifted integer with four or more prime factors either
carries two distinct tagged primes or is divisible by the square of a tag.
-/
noncomputable section
open Finset Set Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

private theorem cast_prod_ge (l : List ℕ) {t : ℝ} (ht : 0≤t) (hl : ∀p∈l,t≤p) :
    t^l.length≤(l.prod:ℝ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.length_cons,List.prod_cons,Nat.cast_mul,pow_succ']
    exact mul_le_mul (hl _ (List.mem_cons_self ..)) (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))) (pow_nonneg ht _) (Nat.cast_nonneg p)

theorem kuhn_two_tags {n : ℕ} {M : Finset ℕ} {t : ℝ} (hn : n≠0)
    (ht : 1≤t) (hsize : (n:ℝ)<t^3)
    (hs : ∀p∈n.primeFactorsList,(p:ℝ)<t → p∈M)
    (hsq : ∀q∈M,¬ q^2∣n) (hfour : 4≤n.primeFactorsList.length) :
    2≤(M.filter (·∣n)).card := by
  let f := fun p : ℕ => decide ((p:ℝ)<t)
  let A := n.primeFactorsList.filter f
  let B := n.primeFactorsList.filter (!f ·)
  have hb : B.length≤2 := by
    have hh := cast_prod_ge B (zero_le_one.trans ht) (fun p hp => by
      obtain ⟨_,hp⟩ := List.mem_filter.mp hp
      simpa [f] using hp)
    have hd := (List.filter_sublist (p:=(!f ·)) (l:=n.primeFactorsList)).prod_dvd_prod
    rw [Nat.prod_primeFactorsList hn] at hd
    have hp : (B.prod:ℝ)≤n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
    by_contra h; exact (not_le.mpr hsize) ((pow_le_pow_right₀ ht (by omega : 3≤B.length)).trans (hh.trans hp))
  have hlen := List.length_eq_length_filter_add (l:=n.primeFactorsList) f
  change n.primeFactorsList.length=A.length+B.length at hlen
  have hA : ∀p∈A, p.Prime ∧ p∈M ∧ p∣n := by
    intro p hp; obtain ⟨hmem,hlt⟩ := List.mem_filter.mp hp
    obtain ⟨hP,hd⟩ := (Nat.mem_primeFactorsList hn).mp hmem
    exact ⟨hP,hs p hmem (of_decide_eq_true hlt),hd⟩
  have hnA : A.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro p
    by_cases hm : p∈A
    · have h := hA p hm
      have hcnt : A.count p≤n.primeFactorsList.count p := List.Sublist.count_le p (List.filter_sublist (p:=f) (l:=n.primeFactorsList))
      rw [Nat.primeFactorsList_count_eq] at hcnt
      by_contra h'; exact hsq p h.2.1 ((h.1.pow_dvd_iff_le_factorization hn).mpr (by omega))
    · simp [List.count_eq_zero_of_not_mem hm]
  have hsub : A.toFinset⊆M.filter (·∣n) := by
    intro p hp; exact mem_filter.mpr (hA p (List.mem_toFinset.mp hp)).2
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnA] at hcard
  omega

/-- Integers in A with at most three prime factors, counted with multiplicity. -/
def atMostThreeFactors (A : Finset ℕ) := A.filter (fun n => n.primeFactorsList.length≤3)

/-- Integers lost to squares of tagged primes. -/
def kuhnSquareExceptions (A M : Finset ℕ) := A.filter (fun n => ∃q∈M,q^2∣n)

theorem kuhn_combinatorial_lower (A M : Finset ℕ) (D : ℕ) {t : ℝ} (ht : 1≤t)
    (hn : ∀n∈A,n≠0 ∧ (n:ℝ)<t^3)
    (hs : ∀n∈A,n.Coprime D → ∀p∈n.primeFactorsList,(p:ℝ)<t → p∈M) :
    (siftedCountOf A D:ℝ)-(1/2:ℝ)*(∑q∈M,(siftedCountOf (sieveMultiple A q) D:ℝ))-
      (kuhnSquareExceptions A M).card≤(atMostThreeFactors A).card := by
  let S := A.filter (fun n => n.Coprime D)
  let m := fun n : ℕ => (M.filter (·∣n)).card
  let good := fun n : ℕ => n.primeFactorsList.length≤3
  let bad := fun n : ℕ => ∃q∈M,q^2∣n
  have htag (n : ℕ) (hn' : n∈S) : (1:ℝ)≤(if good n then 1 else 0)+(if bad n then 1 else 0)+(1/2)*(m n:ℝ) := by
    obtain ⟨hnA,hcop⟩ := mem_filter.mp hn'
    have hp := Nat.cast_nonneg (α:=ℝ) (m n)
    by_cases h₁ : good n <;> by_cases h₂ : bad n <;> simp only [h₁,h₂,ite_true,ite_false,zero_add,add_zero] <;> try linarith
    have hfour : 4≤n.primeFactorsList.length := Nat.not_le.mp h₁
    have hh := kuhn_two_tags (hn n hnA).1 ht (hn n hnA).2 (hs n hnA hcop) (fun q hq hh => h₂ ⟨q,hq,hh⟩) hfour
    linarith only [show (2:ℝ)≤(m n:ℝ) by exact_mod_cast hh]
  have hsum := sum_le_sum htag
  have hsumTag : (∑n∈S,(m n:ℝ))=∑q∈M,(siftedCountOf (sieveMultiple A q) D:ℝ) := by
    simp only [m,Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,sum_filter]
    rw [sum_comm]; apply sum_congr rfl; intro q _
    have he : S.filter (q∣·)=(sieveMultiple A q).filter (fun n => n.Coprime D) := by
      ext n; simp only [S,sieveMultiple,mem_filter]; tauto
    simp only [Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
    rw [←sum_filter,he,sum_const,nsmul_eq_mul,mul_one]; rfl
  have hind (f : ℕ → Prop) [DecidablePred f] :
      (∑n∈S,if f n then (1:ℝ) else 0)≤((A.filter f).card:ℝ) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter f (Finset.filter_subset ..))
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,hsumTag] at hsum
  simp only [sum_const,nsmul_eq_mul,mul_one] at hsum
  change (S.card:ℝ)-1/2*(_ : ℝ)-((A.filter bad).card:ℝ)≤((A.filter good).card:ℝ)
  linarith only [hsum,hind good,hind bad]

/-- A square-divisor loss for an arbitrary finite set of positive integers
bounded by x. The implied constant is absolute. -/
theorem kuhn_square_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (A M : Finset ℕ) {x z : ℝ}, 0≤x → 1≤z →
      (∀n∈A,0<n ∧ (n:ℝ)≤x) → (∀q∈M,z≤q) →
        ((kuhnSquareExceptions A M).card:ℝ)≤C*x/sqrt z := by
  let F := fun n : ℕ => (n:ℝ)^(-(3/2:ℝ))
  have hF : Summable F := Real.summable_nat_rpow.mpr (by norm_num)
  have hpos (n : ℕ) : 0≤F n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let C := 1+∑'n,F n
  have hC : 0<C := by have hsum : 0≤∑'n,F n := tsum_nonneg hpos; dsimp [C]; linarith
  refine ⟨C,hC,?_⟩; intro A M x z hx hz hA hM
  let S := fun q : ℕ => (range (⌊x⌋₊+1)).filter (fun n => n≠0 ∧ q^2∣n)
  have hsub : kuhnSquareExceptions A M⊆M.biUnion S := by
    intro n hn; obtain ⟨hnA,q,hq,hdiv⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_floor (hA n hnA).2; omega),(hA n hnA).1.ne',hdiv⟩⟩
  have hcnt := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le ..)
  have hz₀ := zero_lt_one.trans_le hz
  have hsz := Real.sqrt_pos.mpr hz₀
  have hpoint (q : ℕ) (hq : q∈M) : ((S q).card:ℝ)≤(x/sqrt z)*F q := by
    have hqz := hM q hq
    have hqp := hz₀.trans_le hqz
    have hsq := Real.sqrt_pos.mpr hqp
    change (((range (⌊x⌋₊+1)).filter (fun n => n≠0 ∧ q^2∣n)).card:ℝ)≤_
    rw [Nat.card_multiples']
    have hh := (Nat.cast_div_le (α:=ℝ) (m:=⌊x⌋₊) (n:=q^2)).trans
      (div_le_div_of_nonneg_right (Nat.floor_le hx) (Nat.cast_nonneg (q^2)))
    apply hh.trans
    dsimp only [F]; rw [Nat.cast_pow,Real.rpow_neg hqp.le,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hqp,Real.rpow_one,←Real.sqrt_eq_rpow]
    have hcmp := Real.sqrt_le_sqrt hqz
    calc x/(q:ℝ)^2≤x/(sqrt z*((q:ℝ)*sqrt q)) := by
           apply div_le_div_of_nonneg_left hx (mul_pos hsz (mul_pos hqp hsq))
           calc sqrt z*((q:ℝ)*sqrt q)≤sqrt q*((q:ℝ)*sqrt q) :=
                  mul_le_mul_of_nonneg_right hcmp (mul_nonneg hqp.le hsq.le)
                _ = (q:ℝ)^2 := by rw [mul_left_comm,←pow_two,Real.sq_sqrt hqp.le,pow_two]
         _ = _ := by ring
  apply (show ((kuhnSquareExceptions A M).card:ℝ)≤∑q∈M,((S q).card:ℝ) by exact_mod_cast hcnt).trans
  apply (sum_le_sum hpoint).trans
  rw [←mul_sum]
  have hT := hF.sum_le_tsum M (fun n _ => hpos n)
  change _≤C*x/sqrt z
  have := mul_le_mul_of_nonneg_left (show (∑n∈M,F n)≤C by dsimp [C]; linarith) (div_nonneg hx hsz.le)
  convert this using 1 <;> ring

end AnalyticNumberTheory.SieveMethods
