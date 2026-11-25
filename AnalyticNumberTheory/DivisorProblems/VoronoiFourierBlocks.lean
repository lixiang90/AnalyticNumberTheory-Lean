import AnalyticNumberTheory.DivisorProblems.DivisorFourierTruncation
import AnalyticNumberTheory.ExponentialSums.ReciprocalRealBlocks

/-!
# Fourier blocks for the truncated Voronoï formula
-/

open Real Complex Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

private theorem transpose_divisor_cutoff {E : Type*} [AddCommMonoid E] {b R : ℝ}
    (hb : 0≤b) (hR : 1≤R) (f : ℕ→ℕ→E) :
    (∑ d∈Icc 1 ⌊b⌋₊,∑ h∈Ioc 0 (divisorFourierCutoff d R),f h d) =
    ∑ h∈Icc 1 ⌊b/R⌋₊,∑ d∈Ioc ⌊(h:ℝ)*R⌋₊ ⌊b⌋₊,f h d := by
  classical
  have hR' : 0<R := by linarith
  let D := Icc 1 ⌊b⌋₊
  let H := Icc 1 ⌊b/R⌋₊
  have hrow {d : ℕ} (hd : d∈D) :
      Ioc 0 (divisorFourierCutoff d R)=H.filter (fun h : ℕ => (h:ℝ)*R<d) := by
    ext h; simp only [D,H,mem_filter,mem_Ioc,mem_Icc] at hd ⊢
    constructor
    · rintro ⟨hh,hc⟩
      have hlt := (le_divisorFourierCutoff_iff hh hR').mp hc
      refine ⟨⟨hh,Nat.le_floor ((le_div_iff₀ hR').mpr ?_)⟩,hlt⟩
      exact hlt.le.trans ((Nat.cast_le.mpr hd.2).trans (Nat.floor_le hb))
    · rintro ⟨hh,ht⟩; exact ⟨hh.1,(le_divisorFourierCutoff_iff hh.1 hR').mpr ht⟩
  have hcol (h : ℕ) : D.filter (fun d : ℕ => (h:ℝ)*R<d)=Ioc ⌊(h:ℝ)*R⌋₊ ⌊b⌋₊ := by
    ext d; simp only [D,mem_filter,mem_Icc,mem_Ioc,Nat.floor_lt (show 0≤(h:ℝ)*R by positivity)]
    constructor
    · rintro ⟨⟨_,hd⟩,hh⟩; exact ⟨hh,hd⟩
    · rintro ⟨hh,hd⟩; refine ⟨⟨?_,hd⟩,hh⟩
      exact_mod_cast (lt_of_le_of_lt (show 0≤(h:ℝ)*R by positivity) hh)
  calc
    _ = ∑ d∈D,∑ h∈H,if (h:ℝ)*R<d then f h d else 0 := by
      apply sum_congr rfl; intro d hd; rw [hrow hd,sum_filter]
    _ = ∑ h∈H,∑ d∈D,if (h:ℝ)*R<d then f h d else 0 := sum_comm
    _ = _ := by apply sum_congr rfl; intro h _; rw [←sum_filter,hcol]

/-- Passing between positive natural divisors and all integers in a
positive interval preserves the sum and its real endpoints. -/
theorem sum_natFloor_eq_intFloor {E : Type*} [AddCommMonoid E] {a b : ℝ}
    (ha : 0≤a) (hb : 0≤b) (f : ℤ→E) :
    (∑ n∈Ioc ⌊a⌋₊ ⌊b⌋₊,f n)=∑ n∈Ioc ⌊a⌋ ⌊b⌋,f n := by
  apply sum_bij (fun (n:ℕ) _ => (n:ℤ))
  · intro n hn; obtain ⟨hl,hr⟩ := mem_Ioc.mp hn
    rw [←Int.natCast_floor_eq_floor ha,←Int.natCast_floor_eq_floor hb]
    exact mem_Ioc.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hr⟩
  · intro n _ m _ h; exact_mod_cast h
  · intro n hn; obtain ⟨hl,hr⟩ := mem_Ioc.mp hn
    have hn0 : 0≤n := (Int.floor_nonneg.mpr ha).trans hl.le
    refine ⟨n.toNat,mem_Ioc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hn0⟩
    · rw [←Int.natCast_floor_eq_floor ha] at hl; omega
    · rw [←Int.natCast_floor_eq_floor hb] at hr; omega
  · intro _ _; rfl

/-- The Fourier approximation as reciprocal exponential sums on physical
intervals with exact real endpoints. -/
theorem sum_sawtoothSineSum_eq_reciprocalBlocks {x R : ℝ} (_hx : 1≤x) (hR : 1≤R) :
    (∑ d∈Icc 1 ⌊Real.sqrt x⌋₊,sawtoothSineSum (divisorFourierCutoff d R) (x/d)) =
    (∑ h∈Icc 1 ⌊Real.sqrt x/R⌋₊, (((h:ℝ)⁻¹:ℝ):ℂ)*
      ∑ n∈Ioc ⌊(h:ℝ)*R⌋ ⌊Real.sqrt x⌋,e ((h:ℝ)*x/n)).im / Real.pi := by
  rw [Complex.im_sum,Finset.sum_div]
  calc
    _ = ∑ h∈Icc 1 ⌊Real.sqrt x/R⌋₊,∑ d∈Ioc ⌊(h:ℝ)*R⌋₊ ⌊Real.sqrt x⌋₊,
        Real.sin (2*Real.pi*h*(x/d))/(Real.pi*h) :=
      transpose_divisor_cutoff (Real.sqrt_nonneg _) hR _
    _ = _ := by
      apply sum_congr rfl; intro h hh
      have he := sum_natFloor_eq_intFloor (a:=(h:ℝ)*R) (b:=Real.sqrt x) (by positivity)
        (Real.sqrt_nonneg _) (fun n : ℤ => e ((h:ℝ)*x/n))
      rw [←he,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Complex.im_sum,Finset.mul_sum,Finset.sum_div]
      apply sum_congr rfl; intro d _
      have him (u : ℝ) : (e u).im=Real.sin (2*Real.pi*u) := by
        simp [e,Complex.exp_im,Complex.mul_re,Complex.mul_im]
      rw [him]; push_cast
      rw [show 2*Real.pi*((h:ℝ)*x/d)=2*Real.pi*h*(x/d) by ring]
      ring

end AnalyticNumberTheory.DivisorProblems
