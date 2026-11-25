import AnalyticNumberTheory.SieveMethods.WeightedPeriodicHilbert

/-!
# Analytic large sieve for locally spaced samples

Each squared sample is divided by its own large-sieve weight. Applying finite
duality after rescaling rows retains the coefficient one on the interval length.
-/

open Finset Real Complex
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.SieveMethods

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cosecant inequality for individually spaced points of the circle. -/
theorem weighted_hilbert_cosecant (α δ : ι→ℝ) (hδ : ∀i,0<δ i) (hδ₁ : ∀i,δ i≤1)
    (hsep : ∀i j,i≠j → δ i≤distToInt (α i-α j)) (u : ι→ℂ) :
    ‖∑i,∑j,star (u i)*u j/((Real.sin (π*(α i-α j)):ℝ):ℂ)‖≤
      (weightedHilbertConstant/π)*∑i,‖u i‖^2/δ i :=
  weighted_periodic_hilbert (@weighted_hilbert_inequality) α δ hδ hδ₁ hsep u

/-- For an interval of length N and circular local gaps δᵣ, the weight on sample r
is N + C/(πδᵣ), where C < 4.452. -/
theorem weighted_analytic_large_sieve (α δ : ι→ℝ) (hδ : ∀i,0<δ i) (hδ₁ : ∀i,δ i≤1)
    (hsep : ∀i j,i≠j → δ i≤distToInt (α i-α j)) (a : ℕ→ℂ) (M N : ℕ) :
    (∑r,‖trigPoly a M N (α r)‖^2/((N:ℝ)+weightedHilbertConstant/(π*δ r)))≤
      ∑n∈Ioc M (M+N),‖a n‖^2 := by
  let W := fun r => (N:ℝ)+weightedHilbertConstant/(π*δ r)
  let w := fun r => Real.sqrt (W r)
  have hW r : 0<W r := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (div_pos weightedHilbertConstant_pos (mul_pos pi_pos (hδ r)))
  have hw r : 0<w r := sqrt_pos.mpr (hW r)
  have hw2 r : w r^2=W r := Real.sq_sqrt (hW r).le
  let S := Ioc M (M+N)
  let c (r : ι) (n : ℕ) := e (α r*(n:ℝ))/(w r:ℂ)
  have hs r (_ : r∈(univ : Finset ι)) s (_ : s∈(univ : Finset ι)) (hrs : r≠s) :
      Real.sin (π*(α r-α s))≠0 := by
    intro he
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp he
    have hki : α r-α s=(k:ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by linarith)
    have hh := (hsep r s hrs).trans (distToInt_le_abs_sub (α r-α s) k)
    rw [hki,sub_self,abs_zero] at hh;exact (hδ r).not_ge hh
  have hp (u : ι→ℂ) : ‖∑r,∑s,if r=s then 0 else
      u r*star (u s)/((Real.sin (π*(α r-α s)):ℝ):ℂ)‖≤
      ∑r,(weightedHilbertConstant/(π*δ r))*‖u r‖^2 := by
    have hh := weighted_hilbert_cosecant α δ hδ hδ₁ hsep (fun r => star (u r))
    simp only [star_star,norm_star,mul_sum] at hh
    convert hh using 1
    · congr 1;refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
      by_cases h : r=s <;> simp [h]
    · refine sum_congr rfl fun r _ => ?_;ring
  have hdual (b : ι→ℂ) : (∑n∈S,‖∑r,b r*c r n‖^2)≤1*(∑r,‖b r‖^2) := by
    let v := fun r => b r/(w r:ℂ)
    have H := (abs_le.mp (dual_large_sieve_of_cosecant univ α (fun r => weightedHilbertConstant/(π*δ r))
      hs hp v M N)).2
    have hb (n : ℕ) : (∑r,b r*c r n)=∑r,v r*e (α r*(n:ℝ)) := by
      refine sum_congr rfl fun r _ => ?_; dsimp [c,v];ring
    simp_rw [hb];rw [one_mul]
    calc
      _ ≤ (N:ℝ)*(∑r,‖v r‖^2)+∑r,(weightedHilbertConstant/(π*δ r))*‖v r‖^2 := by
        dsimp [S]; linarith only [H]
      _ = _ := by
        rw [mul_sum,←sum_add_distrib];refine sum_congr rfl fun r _ => ?_
        rw [←add_mul];change W r*‖b r/(w r:ℂ)‖^2=_
        rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (hw r).le,div_pow,hw2]
        field_simp [(hW r).ne']
  have H := ((duality_iff S univ c (by norm_num : (0:ℝ)≤1)).mpr hdual) a
  rw [one_mul] at H
  convert H using 1
  refine sum_congr rfl fun r _ => ?_
  have he : (∑n∈S,a n*c r n)=trigPoly a M N (α r)/(w r:ℂ) := by
    unfold trigPoly;rw [sum_div];refine sum_congr rfl fun n _ => ?_;dsimp [c]; ring
  rw [he,norm_div,div_pow,Complex.norm_real,Real.norm_of_nonneg (hw r).le,hw2]

end AnalyticNumberTheory.SieveMethods
