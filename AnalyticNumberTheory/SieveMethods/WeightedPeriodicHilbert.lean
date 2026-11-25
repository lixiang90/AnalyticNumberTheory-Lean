import AnalyticNumberTheory.SieveMethods.LargeSieve
import AnalyticNumberTheory.AnalyticTools.WeightedHilbertInequality

/-!
# Periodization of the weighted Hilbert inequality

Translate a finite configuration by symmetric integers, alternating the signs of
the coefficients. Averaging gives the cosecant kernel with the individual gaps
on the circle. No ordering of the translated configuration is required.
-/

open Finset Filter Real Complex
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- A real-line Hilbert constant valid for all finite configurations with individual gaps. -/
def IsWeightedHilbertConstant.{u} (C : ℝ) : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (x δ : ι→ℝ), (∀i,0<δ i) →
    (∀i j,i≠j → δ i≤|x i-x j|) → ∀u : ι→ℂ,
    ‖∑s,∑t,star (u s)*u t/((x s-x t:ℝ):ℂ)‖≤C*∑s,‖u s‖^2/δ s

private theorem alternate_sign_sub (m n : ℤ) : (-1:ℂ)^(m-n)=(-1:ℂ)^m*(-1:ℂ)^n := by
  rw [sub_eq_add_neg,zpow_add₀ (by norm_num),zpow_neg,←inv_zpow]; norm_num

private abbrev copies (K : ℕ) := ↥(Finset.Icc (-(K:ℤ)) (K:ℤ))

private theorem copies_card (K : ℕ) : Fintype.card (copies K)=2*K+1 := by
  rw [Fintype.card_coe,Int.card_Icc]; omega

private theorem periodic_copies_bound.{u} {ι : Type u} [Fintype ι] [DecidableEq ι] {C : ℝ}
    (hC : IsWeightedHilbertConstant.{u} C) (α δ : ι→ℝ) (hδ : ∀i,0<δ i) (hδ₁ : ∀i,δ i≤1)
    (hsep : ∀i j,i≠j → δ i≤distToInt (α i-α j)) (u : ι→ℂ) (K : ℕ) :
    ‖∑i,∑j,star (u i)*u j*periodizedHilbertKernel K (α i-α j)‖≤C*∑i,‖u i‖^2/δ i := by
  let X (p : ι×copies K) := α p.1+(p.2:ℤ)
  let d (p : ι×copies K) := δ p.1
  let v (p : ι×copies K) := (-1:ℂ)^(p.2:ℤ)*u p.1
  let M := 2*K+1
  have hM : 0<(M:ℝ) := by dsimp [M]; positivity
  have hs (p q : ι×copies K) (h : p≠q) : d p≤|X p-X q| := by
    obtain ⟨i,m⟩ := p
    obtain ⟨j,n⟩ := q
    dsimp [X,d]
    rcases eq_or_ne i j with rfl|hij
    · have hmn : (m:ℤ)≠(n:ℤ) := fun e => h (by rw [Subtype.ext e])
      have hb : (1:ℤ)≤|((m:ℤ)-n)| := abs_pos.mpr (sub_ne_zero.mpr hmn)
      have hb' : (1:ℝ)≤|(m:ℝ)-(n:ℝ)| := by exact_mod_cast hb
      simpa [add_sub_add_left_eq_sub] using (hδ₁ i).trans hb'
    · have H := (hsep i j hij).trans (distToInt_le_abs_sub (α i-α j) ((n:ℤ)-m))
      convert H using 2; push_cast; ring
  have hh := hC X d (fun p => hδ p.1) hs v
  have hn : (∑p,‖v p‖^2/d p)=(M:ℝ)*∑i,‖u i‖^2/δ i := by
    rw [Fintype.sum_prod_type,mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp [v,d,norm_mul,norm_zpow,copies_card,M]
    left
    have he : ((K:ℤ)+1+K).toNat=2*K+1 := by omega
    push_cast [he]; ring
  have hkernel (i j : ι) : (M:ℂ)*periodizedHilbertKernel K (α i-α j) =
      ∑m : copies K,∑n : copies K,(-1:ℂ)^((m:ℤ)-n)/(((α i-α j:ℝ):ℂ)+(((m:ℤ)-n:ℤ):ℂ)) := by
    have hM' : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
    unfold periodizedHilbertKernel
    change (M:ℂ)*((M:ℂ)⁻¹*_) = _
    rw [←mul_assoc,mul_inv_cancel₀ hM',one_mul]
    let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
    let f (m n : ℤ) := (-1:ℂ)^(m-n)/(((α i-α j:ℝ):ℂ)+((m-n:ℤ):ℂ))
    change (∑m∈S,∑n∈S,f m n)=∑m : ↥S,∑n : ↥S,f m.val n.val
    symm
    calc
      _ = ∑m : ↥S,∑n∈S,f m.val n := sum_congr rfl fun m _ => Finset.sum_coe_sort S (f m.val)
      _ = _ := Finset.sum_coe_sort S (fun m => ∑n∈S,f m n)
  have heq : (∑p,∑q,star (v p)*v q/((X p-X q:ℝ):ℂ))=
      (M:ℂ)*∑i,∑j,star (u i)*u j*periodizedHilbertKernel K (α i-α j) := by
    simp only [Fintype.sum_prod_type]
    rw [mul_sum];refine sum_congr rfl fun i _ => ?_
    rw [sum_comm,mul_sum]; refine sum_congr rfl fun j _ => ?_
    rw [mul_left_comm (M:ℂ) (star (u i)*u j),hkernel i j,mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
    dsimp [v,X]; simp only [Complex.star_def,map_mul,map_zpow₀,map_neg,map_one,alternate_sign_sub]
    push_cast
    rw [show ((α i:ℂ)+(m:ℤ))-((α j:ℂ)+(n:ℤ))=((α i:ℂ)-(α j:ℂ))+((m:ℤ)-(n:ℤ)) by push_cast; ring]
    ring
  rw [heq,hn,norm_mul] at hh
  have nm : ‖(M:ℂ)‖=(M:ℝ) := by simp
  rw [nm,mul_left_comm C (M:ℝ)] at hh
  exact (mul_le_mul_iff_right₀ hM).mp hh

/-- The real weighted Hilbert constant divided by π is a valid constant for the
periodic cosecant kernel, with circular gaps at each sample. -/
theorem weighted_periodic_hilbert.{u} {ι : Type u} [Fintype ι] [DecidableEq ι] {C : ℝ}
    (hC : IsWeightedHilbertConstant.{u} C) (α δ : ι→ℝ) (hδ : ∀i,0<δ i) (hδ₁ : ∀i,δ i≤1)
    (hsep : ∀i j,i≠j → δ i≤distToInt (α i-α j)) (u : ι→ℂ) :
    ‖∑i,∑j,star (u i)*u j/((Real.sin (π*(α i-α j)):ℝ):ℂ)‖≤(C/π)*∑i,‖u i‖^2/δ i := by
  have hterm (i j : ι) : Tendsto (fun K => star (u i)*u j*periodizedHilbertKernel K (α i-α j))
      atTop (𝓝 ((π:ℂ)*(star (u i)*u j/((Real.sin (π*(α i-α j)):ℝ):ℂ)))) := by
    by_cases h : i=j
    · subst j; simp [periodizedHilbertKernel_zero]
    · have hni (k : ℤ) : α i-α j≠(k:ℝ) := by
        intro e
        have hb := (hsep i j h).trans (distToInt_le_abs_sub (α i-α j) k)
        rw [e,sub_self,abs_zero] at hb; exact (hδ i).not_ge hb
      convert (tendsto_periodizedHilbertKernel hni).const_mul (star (u i)*u j) using 2
      push_cast; ring
  have hlim := tendsto_finsetSum univ fun i _ => tendsto_finsetSum univ fun j _ => hterm i j
  simp only [←mul_sum] at hlim
  have H := le_of_tendsto hlim.norm (Eventually.of_forall (periodic_copies_bound hC α δ hδ hδ₁ hsep u))
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] at H
  rw [div_mul_eq_mul_div,le_div_iff₀ Real.pi_pos,mul_comm]; exact H

end AnalyticNumberTheory.SieveMethods
