import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.SieveMethods.SelbergSieve

/-!
# Removing logarithmic weights in the ternary Goldbach problem

After fixing any one prime of an ordered triple, the other two are counted
by the binary Goldbach representation function. This expresses the loss
from replacing each logarithm by the common logarithm of the target.
-/

noncomputable section
open Finset Real
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AdditiveNumberTheory

private def primeTriples (N : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  ((Icc 2 N) ×ˢ (Icc 2 N) ×ˢ (Icc 2 N)).filter fun p =>
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1+p.2.1+p.2.2=N

private theorem mem_primeTriples {N a b c : ℕ} :
    (a,b,c)∈primeTriples N ↔ a.Prime ∧ b.Prime ∧ c.Prime ∧ a+b+c=N := by
  simp only [primeTriples,mem_filter,mem_product,mem_Icc]
  constructor
  · exact And.right
  · intro h
    obtain ⟨ha,hb,hc,he⟩ := h
    exact ⟨⟨⟨ha.two_le,by omega⟩,⟨hb.two_le,by omega⟩,⟨hc.two_le,by omega⟩⟩,ha,hb,hc,he⟩

private theorem primeTriples_sum_first (N : ℕ) (f : ℕ→ℝ) :
    ∑v∈primeTriples N,f v.1 =
      ∑p∈(Icc 2 N).filter Nat.Prime,(goldbachRepCount (N-p):ℝ)*f p := by
  let P := (Icc 2 N).filter Nat.Prime
  have hmap : ∀v∈primeTriples N,v.1∈P := by
    rintro ⟨a,b,c⟩ hv
    obtain ⟨ha,_,_,h⟩ := mem_primeTriples.mp hv
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.two_le,by omega⟩,ha⟩
  rw [←sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpi,hp'⟩ := mem_filter.mp hp
  obtain ⟨_,hpN⟩ := mem_Icc.mp hpi
  let F := (primeTriples N).filter (fun v => v.1=p)
  have he : F.card=goldbachRepCount (N-p) := by
    apply card_bij (fun (v:ℕ×ℕ×ℕ) _ => v.2.1)
    · rintro ⟨a,b,c⟩ hv
      obtain ⟨hv,he⟩ := mem_filter.mp hv
      obtain ⟨ha,hb,hc,hs⟩ := mem_primeTriples.mp hv
      change a=p at he;subst a
      have hbc : N-p-b=c := by omega
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hb.pos,show b≤N-p by omega⟩,hb,by change (N-p-b).Prime;rw [hbc];exact hc⟩
    · rintro ⟨a,b,c⟩ hv ⟨a',b',c'⟩ hw h
      obtain ⟨hv,ha⟩ := mem_filter.mp hv
      obtain ⟨hw,ha'⟩ := mem_filter.mp hw
      have he := (mem_primeTriples.mp hv).2.2.2
      have he' := (mem_primeTriples.mp hw).2.2.2
      change b=b' at h
      change a=p at ha;change a'=p at ha'
      have hc : c=c' := by omega
      simp [ha,ha',h,hc]
    · intro b hb
      obtain ⟨hi,hb,hc⟩ := mem_filter.mp hb
      obtain ⟨_,hle⟩ := mem_Icc.mp hi
      exact ⟨(p,b,N-p-b),mem_filter.mpr ⟨mem_primeTriples.mpr ⟨hp',hb,hc,by omega⟩,rfl⟩,rfl⟩
  change (∑v∈F,f v.1)=_
  rw [←he,←nsmul_eq_mul,←sum_const]
  apply sum_congr rfl;intro v hv;rw [(mem_filter.mp hv).2]

private theorem triple_coordinates (N : ℕ) (f : ℕ→ℝ) :
    (∑v∈primeTriples N,f v.2.1)=(∑v∈primeTriples N,f v.1) ∧
    (∑v∈primeTriples N,f v.2.2)=(∑v∈primeTriples N,f v.1) := by
  have h₁ (v : ℕ×ℕ×ℕ) (hv : v∈primeTriples N) : (v.2.1,v.1,v.2.2)∈primeTriples N := by
    rcases v with ⟨a,b,c⟩
    obtain ⟨ha,hb,hc,h⟩ := mem_primeTriples.mp hv
    exact mem_primeTriples.mpr ⟨hb,ha,hc,show b+a+c=N by omega⟩
  have h₂ (v : ℕ×ℕ×ℕ) (hv : v∈primeTriples N) : (v.2.2,v.2.1,v.1)∈primeTriples N := by
    rcases v with ⟨a,b,c⟩
    obtain ⟨ha,hb,hc,h⟩ := mem_primeTriples.mp hv
    exact mem_primeTriples.mpr ⟨hc,hb,ha,show c+b+a=N by omega⟩
  constructor
  · exact sum_bij' _ _ h₁ h₁ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact sum_bij' _ _ h₂ h₂ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The one-sided error when the three prime logarithms are replaced by log N.
The remaining prime sum has one logarithmic deficit and a binary Goldbach count. -/
theorem goldbachTernaryCount_log_weight_loss {N : ℕ} (hN : 2≤N) :
    (log N)^3*(goldbachTernaryCount N:ℝ)-goldbachTernaryThetaWeighted N ≤
      3*(log N)^2*∑p∈(Icc 2 N).filter Nat.Prime,(goldbachRepCount (N-p):ℝ)*(log N-log p) := by
  let L := log N
  let f (n : ℕ) := L-log n
  have hL : 0≤L := log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hθ : goldbachTernaryThetaWeighted N =
      ∑v∈primeTriples N,log v.1*log v.2.1*log v.2.2 := by
    simp [goldbachTernaryThetaWeighted,primeTriples,sum_filter,sum_product]
  have hcard : (goldbachTernaryCount N:ℝ)*(log N)^3 = ∑_v∈primeTriples N,L^3 := by
    simp [goldbachTernaryCount,primeTriples,L]
  rw [mul_comm ((log N)^3),hcard,hθ,←sum_sub_distrib]
  have hpoint (v : ℕ×ℕ×ℕ) (hv : v∈primeTriples N) :
      L^3-log v.1*log v.2.1*log v.2.2 ≤ L^2*(f v.1+f v.2.1+f v.2.2) := by
    obtain ⟨ha,hb,hc,he⟩ := mem_primeTriples.mp hv
    have hlog {p : ℕ} (hp : p.Prime) (hle : p≤N) : 0≤log p ∧ log p≤L :=
      ⟨log_nonneg (by exact_mod_cast hp.one_le),log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hle)⟩
    obtain ⟨a₀,a⟩ := hlog ha (by omega)
    obtain ⟨b₀,b⟩ := hlog hb (by omega)
    obtain ⟨_,c⟩ := hlog hc (by omega)
    have h₁ := mul_le_mul_of_nonneg_right a (mul_nonneg hL (sub_nonneg.mpr b))
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul a b b₀ hL) (sub_nonneg.mpr c)
    dsimp only [f];nlinarith only [h₁,h₂]
  apply (sum_le_sum hpoint).trans_eq
  rw [←mul_sum,sum_add_distrib,sum_add_distrib,(triple_coordinates N f).1,
    (triple_coordinates N f).2,primeTriples_sum_first]
  change L^2*(_+_+_)=3*L^2*_;ring

/-- Restricting the three von Mangoldt variables to primes decreases the count. -/
theorem goldbachTernaryThetaWeighted_le_weighted (N : ℕ) :
    goldbachTernaryThetaWeighted N ≤ goldbachTernaryWeighted N := by
  let F (v : ℕ×ℕ×ℕ) := if v.1+v.2.1+v.2.2=N then ArithmeticFunction.vonMangoldt v.1*
    ArithmeticFunction.vonMangoldt v.2.1*ArithmeticFunction.vonMangoldt v.2.2 else 0
  have hθ : goldbachTernaryThetaWeighted N = ∑v∈primeTriples N,F v := by
    have he (v : ℕ×ℕ×ℕ) (hv : v∈primeTriples N) : F v=log v.1*log v.2.1*log v.2.2 := by
      obtain ⟨ha,hb,hc,h⟩ := mem_primeTriples.mp hv
      simp [F,h,ArithmeticFunction.vonMangoldt_apply_prime,ha,hb,hc]
    rw [sum_congr rfl he]
    simp [goldbachTernaryThetaWeighted,primeTriples,sum_filter,sum_product]
  rw [hθ]
  change _≤∑a∈Icc 1 N,∑b∈Icc 1 N,∑c∈Icc 1 N,F (a,b,c)
  simp_rw [←sum_product']
  apply sum_le_sum_of_subset_of_nonneg
  · rintro ⟨a,b,c⟩ hv
    obtain ⟨ha,hb,hc,h⟩ := mem_primeTriples.mp hv
    simp only [mem_product,mem_Icc]
    exact ⟨⟨ha.one_le,by omega⟩,⟨hb.one_le,by omega⟩,⟨hc.one_le,by omega⟩⟩
  · intro v _ _;dsimp [F];split_ifs <;> positivity

/-- Discarding the prime two can only decrease the ordered representation count. -/
theorem goldbachTernaryOddCount_le_count (N : ℕ) : goldbachTernaryOddCount N≤goldbachTernaryCount N := by
  apply card_le_card
  intro v hv
  obtain ⟨hi,h⟩ := mem_filter.mp hv
  refine mem_filter.mpr ⟨?_,h⟩
  simp only [mem_product,mem_Icc] at hi ⊢
  omega

end AnalyticNumberTheory.AdditiveNumberTheory
