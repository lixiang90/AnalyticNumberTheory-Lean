import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Covering a finite sample by height windows
-/
open Finset Complex
open scoped Classical
namespace AnalyticNumberTheory.SieveMethods

/-- If every window of length `W` contains at most `B` selected points,
a sample in a longer interval of length `L` has size at most
`(L/W+1)B`. Heights and both endpoints may be real. -/
theorem height_window_cover {ι : Type*} {F : Finset ι} (S : ι→Finset ℂ) {A L W B : ℝ}
    (hL : 0≤L) (hW : 0<W) (hB : 0≤B) (ht : ∀ i∈F,∀z∈S i,A≤z.im ∧ z.im<A+L)
    (hlocal : ∀(S' : ι→Finset ℂ), (∀i∈F,S' i⊆S i) → ∀ b : ℝ,
      (∀i∈F,∀z∈S' i,b≤z.im ∧ z.im<b+W) → (∑i∈F,((S' i).card:ℝ))≤B) :
    (∑i∈F,((S i).card:ℝ))≤(L/W+1)*B := by
  let J := range (⌊L/W⌋₊+1)
  let idx (z:ℂ) := ⌊(z.im-A)/W⌋₊
  let bin (j:ℕ) (i:ι) := (S i).filter (fun z => idx z=j)
  have hmap (i) (hi:i∈F) (z:ℂ) (hz:z∈S i) : idx z∈J := by
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right
      (by linarith [(ht i hi z hz).2]) hW.le)))
  have hsplit (i) (hi:i∈F) : (∑j∈J,((bin j i).card:ℝ))=(S i).card := by
    simpa only [bin,sum_const,nsmul_eq_mul,mul_one] using sum_fiberwise_of_maps_to (hmap i hi) (fun _ => (1:ℝ))
  have hbin (j:ℕ) : (∑i∈F,((bin j i).card:ℝ))≤B := by
    apply hlocal (bin j) (fun i _ => filter_subset ..) (A+j*W)
    intro i hi z hz
    obtain ⟨hz,he⟩ := mem_filter.mp hz
    have he' := (Nat.floor_eq_iff (div_nonneg (sub_nonneg.mpr (ht i hi z hz).1) hW.le)).mp he
    have ha := (le_div_iff₀ hW).mp he'.1
    have hb := (div_lt_iff₀ hW).mp he'.2
    constructor <;> linarith
  calc ∑i∈F,((S i).card:ℝ) = ∑i∈F,∑j∈J,((bin j i).card:ℝ) := sum_congr rfl (fun i hi => (hsplit i hi).symm)
       _ = _ := sum_comm
       _ ≤ ∑_j∈J,B := sum_le_sum (fun j _ => hbin j)
       _ ≤ _ := by
         simp only [J,sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
         exact mul_le_mul_of_nonneg_right (by linarith only [Nat.floor_le (div_nonneg hL hW.le)]) hB

/-- Unit-interval capacity of a height sample whose distinct ordinates
are separated by at least a positive number `δ`. -/
theorem separated_heights_unit_capacity (S : Finset ℂ) {δ : ℝ} (hδ : 0<δ)
    (hsep : ∀ z∈S,∀w∈S,z≠w → δ≤|z.im-w.im|) (b : ℝ) :
    (((S.filter fun z => b≤z.im ∧ z.im<b+1).card):ℝ)≤1+δ⁻¹ := by
  let P := S.filter (fun z => b≤z.im ∧ z.im<b+1)
  let idh (z:ℂ) := ⌊(z.im-b)/δ⌋₊
  have hsmall (z:ℂ) (hz:z∈P) : 0≤(z.im-b)/δ ∧ (z.im-b)/δ<1/δ := by
    have hh := (mem_filter.mp hz).2
    exact ⟨div_nonneg (sub_nonneg.mpr hh.1) hδ.le,(div_lt_div_iff_of_pos_right hδ).mpr (by linarith [hh.2])⟩
  have hc : P.card≤(range ⌈1/δ⌉₊).card := by
    apply card_le_card_of_injOn idh
    · intro z hz
      exact mem_range.mpr ((Nat.floor_lt (hsmall z hz).1).mpr ((hsmall z hz).2.trans_le (Nat.le_ceil _)))
    · intro z hz w hw he
      by_contra hne
      have hz' := (Nat.floor_eq_iff (hsmall z hz).1).mp (show ⌊(z.im-b)/δ⌋₊=idh w from he)
      have hw' := (Nat.floor_eq_iff (hsmall w hw).1).mp (show ⌊(w.im-b)/δ⌋₊=idh w from rfl)
      have hh : |z.im-w.im|<δ := abs_lt.mpr ⟨by
        linarith only [(le_div_iff₀ hδ).mp hz'.1,(div_lt_iff₀ hδ).mp hw'.2],by
        linarith only [(le_div_iff₀ hδ).mp hw'.1,(div_lt_iff₀ hδ).mp hz'.2]⟩
      exact hh.not_ge (hsep z (mem_filter.mp hz).1 w (mem_filter.mp hw).1 hne)
  rw [card_range] at hc
  have hc' : (P.card:ℝ)≤⌈1/δ⌉₊ := by exact_mod_cast hc
  exact hc'.trans (by linarith only [Nat.ceil_lt_add_one (show 0≤1/δ by positivity),one_div δ])

end AnalyticNumberTheory.SieveMethods
