import AnalyticNumberTheory.SieveMethods.WeightedLargeSieve

/-!
# Denominator weights in the arithmetic large sieve

The local gap at a reduced fraction with denominator q is at least 1/(qQ).
Consequently the additive large-sieve weight retains the individual
denominator when the reduced fractions are combined into an arithmetic sieve.
-/

open Finset Real
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.SieveMethods

/-- The cost of a Farey fraction depends linearly on its denominator. -/
noncomputable def fareySieveCost (N Q q : ℕ) : ℝ :=
  (N:ℝ)+(weightedHilbertConstant/π)*(q:ℝ)*(Q:ℝ)

/-- Denominator-sensitive Farey large sieve. -/
theorem weighted_farey_large_sieve (a : ℕ→ℂ) (M N Q : ℕ) (hQ : 1≤Q) :
    (∑q∈Icc 1 Q,∑r∈(range q).filter (fun r => Nat.Coprime r q),
        ‖trigPoly a M N ((r:ℝ)/q)‖^2/fareySieveCost N Q q)≤
      ∑n∈Ioc M (M+N),‖a n‖^2 := by
  let J := fareyPairs Q
  let α (p : ↥J) := fareyFraction p.val
  let δ (p : ↥J) := ((p.val.1:ℝ)*(Q:ℝ))⁻¹
  have hb (p : ↥J) := mem_Icc.mp (farey_denominator_mem p.prop)
  have hden (p : ↥J) : 1≤(p.val.1:ℝ) := by exact_mod_cast (hb p).1
  have hQ' : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hd p : 0<δ p := inv_pos.mpr (mul_pos (zero_lt_one.trans_le (hden p)) (zero_lt_one.trans_le hQ'))
  have h₁ p : δ p≤1 := inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (hden p) hQ')
  have hsep (p q : ↥J) (hpq : p≠q) : δ p≤distToInt (α p-α q) := by
    apply le_trans _ (farey_pair_spacing p.prop q.prop (fun h => hpq (Subtype.ext h)))
    apply inv_anti₀ (mul_pos (zero_lt_one.trans_le (hden p)) (zero_lt_one.trans_le (hden q)))
    gcongr; exact_mod_cast (hb q).2
  have H := weighted_analytic_large_sieve α δ hd h₁ hsep a M N
  have he (p : ↥J) : (N:ℝ)+weightedHilbertConstant/(π*δ p)=fareySieveCost N Q p.val.1 := by
    unfold fareySieveCost δ; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
  simp_rw [he] at H
  change (∑p : ↥(fareyPairs Q),‖trigPoly a M N (fareyFraction p.val)‖^2/fareySieveCost N Q p.val.1)≤_ at H
  rw [Finset.sum_coe_sort (fareyPairs Q) (fun p => ‖trigPoly a M N (fareyFraction p)‖^2/fareySieveCost N Q p.1)] at H
  apply le_trans (le_of_eq _) H
  dsimp [fareyPairs,fareyFraction]
  rw [sum_biUnion]
  · refine sum_congr rfl fun q _ => ?_
    rw [sum_image]; intro r₁ _ r₂ _ h; exact (Prod.mk.inj h).2
  · intro q₁ _ q₂ _ hne
    rw [Function.onFun,Finset.disjoint_left]
    rintro ⟨q,r⟩ h₁ h₂
    obtain ⟨_,_,ha⟩ := mem_image.mp h₁
    obtain ⟨_,_,hb⟩ := mem_image.mp h₂
    exact hne (Prod.mk.inj (ha.trans hb.symm)).1

/-- Arithmetic large sieve with the full denominator-dependent cost in the sifting weight. -/
theorem weighted_arithmetic_large_sieve (Ω : ℕ→Finset ℕ) (a : ℕ→ℂ) (M N Q : ℕ) (hQ : 1≤Q)
    (hΩ : ∀p,p.Prime → p≤Q → Ω p⊆range p ∧ (Ω p).card<p)
    (ha : ∀p,p.Prime → p≤Q → ∀n∈Ioc M (M+N),n%p∈Ω p → a n=0) :
    (∑q∈(Icc 1 Q).filter Squarefree,sieveWeight Ω q/fareySieveCost N Q q)*
      ‖∑n∈Ioc M (M+N),a n‖^2≤∑n∈Ioc M (M+N),‖a n‖^2 := by
  have hC (q : ℕ) : 0≤fareySieveCost N Q q := by unfold fareySieveCost; positivity [weightedHilbertConstant_pos]
  rw [sum_mul]
  apply le_trans _ (weighted_farey_large_sieve a M N Q hQ)
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (filter_subset Squarefree (Icc 1 Q))
    (fun q _ _ => sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hC q)))
  refine sum_le_sum fun q hq => ?_
  obtain ⟨hqI,hsq⟩ := mem_filter.mp hq
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hqI
  have hpQ p (hp : p∈q.primeFactors) : p≤Q := (Nat.le_of_dvd hq₁ (Nat.mem_primeFactors.mp hp).2.1).trans hqQ
  have H := arithmetic_large_sieve_squarefree Ω a M N q hq₁ hsq
    (fun p hp => hΩ p (Nat.mem_primeFactors.mp hp).1 (hpQ p hp))
    (fun p hp => ha p (Nat.mem_primeFactors.mp hp).1 (hpQ p hp))
  rw [div_mul_eq_mul_div,←sum_div]
  exact div_le_div_of_nonneg_right H (hC q)

end AnalyticNumberTheory.SieveMethods
