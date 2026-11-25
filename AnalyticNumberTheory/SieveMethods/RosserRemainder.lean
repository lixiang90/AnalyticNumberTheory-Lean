import AnalyticNumberTheory.SieveMethods.CombinatorialSieve

/-!
# Exact remainders for Rosser's combinatorial sieve

The first rejected prefix of a descending selection of primes determines
an entire omitted branch of inclusion-exclusion. Summing that branch
leaves an Euler product over the primes after its last selected prime.
-/
noncomputable section
open Finset
open scoped ArithmeticFunction.Moebius
namespace AnalyticNumberTheory.SieveMethods
open Classical

private def accepts (b : Bool) (C : List ℕ → Prop) (L : List ℕ) : Prop :=
  if b then rosserCondPlus C L else rosserCondMinus C L

private theorem accepts_cons (b : Bool) (C : List ℕ → Prop) (p : ℕ) (L : List ℕ) :
    accepts b C (p::L) ↔ (b=false ∨ C [p]) ∧ accepts (!b) (fun u => C (p::u)) L := by
  cases b <;> simp [accepts,rosserCondPlus,rosserCondMinus]

/-- Each pair consists of the selected primes up to the first rejected prefix
and the remaining smaller primes. The input is ordered from largest to smallest. -/
def rosserFirstFailures : List ℕ → Bool → (List ℕ → Prop) → List (List ℕ × List ℕ)
  | [],_,_ => []
  | p::L,b,C => rosserFirstFailures L b C ++
      if b=false ∨ C [p] then
        (rosserFirstFailures L (!b) (fun u => C (p::u))).map (fun e => (p::e.1,e.2))
      else [([p],L)]

private def failureTerm (g : ℕ → ℝ) (e : List ℕ × List ℕ) : ℝ :=
  (e.1.map g).prod*(e.2.map (fun p => 1-g p)).prod

/-- Sum of the densities of the first rejected prefixes, each multiplied
by the Euler product over the remaining primes. -/
def rosserRemainder (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (L : List ℕ) : ℝ :=
  ((rosserFirstFailures L b C).map (failureTerm g)).sum

private def truncatedSum (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (L : List ℕ) : ℝ :=
  (L.sublists.map (fun e => if accepts b C e then (e.map (fun p => -g p)).prod else 0)).sum

private theorem truncatedSum_cons (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (p : ℕ) (L : List ℕ) :
    truncatedSum g C b (p::L)=truncatedSum g C b L+
      if b=false ∨ C [p] then -g p*truncatedSum g (fun u => C (p::u)) (!b) L else 0 := by
  unfold truncatedSum
  rw [sum_sublists_cons]
  congr 1
  by_cases h : b=false ∨ C [p]
  · simp only [accepts_cons,h,true_and,ite_true,List.map_cons,List.prod_cons]
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e he; split_ifs <;> simp
  · simp [accepts_cons,h]

private theorem rosserRemainder_cons (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (p : ℕ) (L : List ℕ) :
    rosserRemainder g C b (p::L)=rosserRemainder g C b L+g p*
      if b=false ∨ C [p] then rosserRemainder g (fun u => C (p::u)) (!b) L else (L.map (fun q => 1-g q)).prod := by
  unfold rosserRemainder
  rw [rosserFirstFailures,List.map_append,List.sum_append]
  congr 1
  by_cases h : b=false ∨ C [p]
  · simp only [h,ite_true,List.map_map,Function.comp_def]
    have he (e : List ℕ × List ℕ) : failureTerm g (p::e.1,e.2)=g p*failureTerm g e := by
      simp [failureTerm,mul_assoc]
    simp_rw [he]
    exact List.sum_map_mul_left ..
  · simp [h,failureTerm]

private theorem truncatedSum_eq (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (L : List ℕ) :
    truncatedSum g C b L=(L.map (fun p => 1-g p)).prod+
      (if b then rosserRemainder g C b L else -rosserRemainder g C b L) := by
  induction L generalizing C b with
  | nil => cases b <;> simp [truncatedSum,accepts,rosserCondPlus,rosserCondMinus,rosserRemainder,rosserFirstFailures]
  | cons p L ih =>
    rw [truncatedSum_cons,rosserRemainder_cons]
    cases b <;> by_cases h : C [p] <;> simp [h,ih] <;> ring

private theorem failures_sublist (L : List ℕ) (C : List ℕ → Prop) (b : Bool) :
    ∀ e∈rosserFirstFailures L b C, e.1.Sublist L ∧ e.2.Sublist L := by
  induction L generalizing C b with
  | nil => simp [rosserFirstFailures]
  | cons p L ih =>
    intro e he
    rw [rosserFirstFailures,List.mem_append] at he
    rcases he with he | he
    · exact ⟨(ih C b _ he).1.cons p,(ih C b _ he).2.cons p⟩
    split_ifs at he with h
    · obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
      exact ⟨(ih _ _ _ he').1.cons_cons p,(ih _ _ _ he').2.cons p⟩
    · obtain rfl := List.mem_singleton.mp he
      exact ⟨(List.nil_sublist L).cons_cons p,(List.Sublist.refl L).cons p⟩

theorem rosserRemainder_nonneg {g : ℕ → ℝ} (C : List ℕ → Prop) (b : Bool) {L : List ℕ}
    (hg : ∀ p∈L, 0≤g p ∧ g p≤1) : 0≤rosserRemainder g C b L := by
  unfold rosserRemainder
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
  obtain ⟨h₁,h₂⟩ := failures_sublist L C b e he
  apply mul_nonneg <;> apply List.prod_nonneg <;> intro y hy
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hy; exact (hg p (h₁.subset hp)).1
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hy; exact sub_nonneg.mpr (hg p (h₂.subset hp)).2



private theorem prod_desc_map (d : ℕ) (g : ℕ → ℝ) :
    ((descPrimeList d).map g).prod=∏ p∈d.primeFactors,g p := by
  have hf : (descPrimeList d).toFinset=d.primeFactors := by
    ext p; simp [mem_descPrimeList_iff]
  rw [←List.prod_toFinset g (descPrimeList_nodup _),hf]

private theorem signed_density_product (s : SieveData) {d : ℕ} (hsq : Squarefree d) :
    ((descPrimeList d).map (fun p => -s.density p)).prod=(μ d:ℝ)*s.density d := by
  have hm : (μ d:ℝ)=(-1:ℝ)^(descPrimeList d).length := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    congr 1
    have h := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).mpr hsq
    simpa [descPrimeList,ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] using h.symm
  rw [show (descPrimeList d).map (fun p => -s.density p)=((descPrimeList d).map s.density).map Neg.neg by simp,
      List.prod_map_neg,List.length_map,hm,prod_desc_map]
  congr 1
  have h := s.densityArith_isMultiplicative.map_prod_of_subset_primeFactors d d.primeFactors subset_rfl
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  exact h.symm

/-- Exact main term of a Rosser sieve. The error from the Euler product is
the sum over first failures with a positive sign for the upper sieve and a
negative sign for the lower sieve. This holds for any prefix condition. -/
theorem rosser_main_term_eq (s : SieveData) (z : ℝ) (C : List ℕ → Prop) (b : Bool) :
    (∑ d∈(s.prodPrimes z).divisors,
      (if b then rosserWeightsPlus C d else rosserWeightsMinus C d)*s.density d)=
      s.eulerProd z+(if b then rosserRemainder s.density C b (descPrimeList (s.prodPrimes z))
                     else -rosserRemainder s.density C b (descPrimeList (s.prodPrimes z))) := by
  let L := descPrimeList (s.prodPrimes z)
  have hmain : (∑ d∈(s.prodPrimes z).divisors,
      (if b then rosserWeightsPlus C d else rosserWeightsMinus C d)*s.density d)=truncatedSum s.density C b L := by
    apply sum_divisors_eq_sum_sublists_of_squarefree (s.prodPrimes_squarefree z)
    intro d hd
    have hsq := (s.prodPrimes_squarefree z).squarefree_of_dvd hd
    change _=if accepts b C (descPrimeList d) then _ else _
    rw [signed_density_product s hsq]
    cases b <;> simp [rosserWeightsPlus,rosserWeightsMinus,accepts,hsq,hsq.ne_zero,ite_mul]
  rw [hmain,truncatedSum_eq,prod_desc_map]
  rfl

/-- Exact model sums for the upper and lower beta sieve weights. -/
theorem betaSieve_main_terms (s : SieveData) (z β y : ℝ) :
    let C := (fun L => rosserTruncationFactor β L<y)
    let L := descPrimeList (s.prodPrimes z)
    (∑ d∈(s.prodPrimes z).divisors,betaSieveUpper β y d*s.density d)=
      s.eulerProd z+rosserRemainder s.density C true L ∧
    (∑ d∈(s.prodPrimes z).divisors,betaSieveLower β y d*s.density d)=
      s.eulerProd z-rosserRemainder s.density C false L := by
  dsimp only
  exact ⟨by simpa [betaSieveUpper] using (rosser_main_term_eq s z (fun L => rosserTruncationFactor β L<y) true),
    by simpa [betaSieveLower,sub_eq_add_neg] using (rosser_main_term_eq s z (fun L => rosserTruncationFactor β L<y) false)⟩



private theorem failure_spec (L : List ℕ) (C : List ℕ → Prop) (b : Bool) :
    ∀ e∈rosserFirstFailures L b C, e.1≠[] ∧ ¬C e.1 ∧ accepts b C e.1.dropLast ∧
      (if b then Odd e.1.length else Even e.1.length) := by
  induction L generalizing C b with
  | nil => simp [rosserFirstFailures]
  | cons p L ih =>
    intro e he
    rw [rosserFirstFailures,List.mem_append] at he
    rcases he with h | h
    · exact ih C b e h
    split_ifs at h with hpass
    · obtain ⟨e',he',rfl⟩ := List.mem_map.mp h
      obtain ⟨hne,hc,ha,hpar⟩ := ih _ _ e' he'
      refine ⟨by simp,hc,?_,?_⟩
      · rw [List.dropLast_cons_of_ne_nil hne,accepts_cons]; exact ⟨hpass,ha⟩
      · cases b <;> simp only [Bool.not_false,Bool.not_true,ite_true,ite_false,
          Bool.false_eq_true,List.length_cons] at hpar ⊢
        · exact hpar.add_one
        · exact hpar.add_one
    · obtain rfl := List.mem_singleton.mp h
      have hb : b=true := by cases b <;> simp_all
      subst b
      simp [accepts,rosserCondPlus] at hpass ⊢
      exact hpass

/-- A rejected branch ends exactly at the first unsuccessful test, with the
parity required for its contribution to the upper or lower remainder. -/
theorem rosserFirstFailures_spec {L : List ℕ} {C : List ℕ → Prop} {b : Bool}
    {e : List ℕ × List ℕ} (he : e∈rosserFirstFailures L b C) :
    e.1.Sublist L ∧ e.2.Sublist L ∧ e.1≠[] ∧ ¬C e.1 ∧
      (if b then rosserCondPlus C e.1.dropLast else rosserCondMinus C e.1.dropLast) ∧
      (if b then Odd e.1.length else Even e.1.length) :=
  ⟨(failures_sublist L C b e he).1,(failures_sublist L C b e he).2,failure_spec L C b e he⟩

/-- Every first failure of a beta sieve selects at least log(y)/log(z)−β
prime factors when the sifting primes are at most z. -/
theorem betaSieve_failure_length {L : List ℕ} {b : Bool} {z β y : ℝ} (hz : 1<z) (hβ : 0≤β)
    (hL : ∀ p∈L, (p:ℝ)≤z) {e : List ℕ × List ℕ}
    (he : e∈rosserFirstFailures L b (fun l => rosserTruncationFactor β l<y)) :
    y≤z^((e.1.length:ℝ)+β) := by
  obtain ⟨hsub,_,hn,hfail,_,_⟩ := rosserFirstFailures_spec he
  have hprod (l : List ℕ) (h : ∀ p∈l,(p:ℝ)≤z) : (l.prod:ℝ)≤z^l.length := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.prod_cons,List.length_cons,Nat.cast_mul,pow_succ']
      exact mul_le_mul (h _ (by simp)) (ih (fun q hq => h q (by simp [hq])))
        (Nat.cast_nonneg _) (by linarith)
  have hlast : e.1.getLastD 1∈e.1 := by
    cases heq : e.1 with
    | nil => exact False.elim (hn heq)
    | cons p l => exact List.getLast_mem (by simp)
  have hle : (e.1.getLastD 1:ℝ)≤z := hL _ (hsub.subset hlast)
  rw [Real.rpow_add (by linarith : 0<z),Real.rpow_natCast]
  exact (not_lt.mp hfail).trans (mul_le_mul (hprod _ (fun p hp => hL p (hsub.subset hp)))
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hle hβ) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))

end AnalyticNumberTheory.SieveMethods
