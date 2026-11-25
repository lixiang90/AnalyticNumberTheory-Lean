import AnalyticNumberTheory.AdditiveNumberTheory.Goldbach
import AnalyticNumberTheory.SieveMethods.BrunTitchmarshFull

/-! # A uniform progression estimate for averaging sieve factors

For moduli d up to t², the count of primes below t in any class times
the fourth root of d is O(t/log t). Brun–Titchmarsh handles small moduli
and the length of a progression handles the complementary range.
-/
noncomputable section
open Finset Real
open AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem piAP_trivial {t : ℝ} (ht : 0≤t) {d : ℕ} (hd : 0<d) (a : ℕ) :
    piAP t d a ≤ t/d+1 := by
  let A := (Icc 1 ⌊t⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD d])
  have hi : Set.InjOn (fun n : ℕ => n/d) (↑A : Set ℕ) := by
    intro p hp q hq he
    change p/d=q/d at he
    have hp' : p%d=a%d := (mem_filter.mp hp).2.2
    have hq' : q%d=a%d := (mem_filter.mp hq).2.2
    exact (Nat.mod_add_div p d).symm.trans (by rw [hp',he,←hq',Nat.mod_add_div])
  have hsub : A.image (fun n : ℕ => n/d)⊆range (⌊t/d⌋₊+1) := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    apply mem_range.mpr
    rw [Nat.floor_div_natCast]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hn).1).2)
  have H := card_le_card hsub
  rw [card_image_of_injOn hi,card_range] at H
  have H' : (A.card:ℝ)≤(⌊t/d⌋₊:ℝ)+1 := by exact_mod_cast H
  change (A.card:ℝ)≤_
  linarith only [H',Nat.floor_le (div_nonneg ht (Nat.cast_nonneg d))]

private theorem fourth_root_fourth {r : ℝ} (hr : 0≤r) : (r^(1/4:ℝ))^4=r := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hr]
  norm_num

/-- Uniform bound for the fourth-root-weighted count in each residue class. -/
theorem goldbach_progression_quarter {t : ℝ} (ht : 2≤t) {d : ℕ} (hd : 0<d)
    (hdt : (d:ℝ)≤t^2) (a : ℕ) :
    piAP t d a*(d:ℝ)^(1/4:ℝ)≤16*t/log t := by
  have ht₀ : 0<t := by linarith
  have hd₀ : (0:ℝ)<d := by exact_mod_cast hd
  have hd₁ : (1:ℝ)≤d := by exact_mod_cast hd
  have hlog := Real.log_pos (show 1<t by linarith)
  let r := (d:ℝ)^(1/4:ℝ)
  have hr : 0<r := Real.rpow_pos_of_pos hd₀ _
  have hr4 : r^4=d := fourth_root_fourth hd₀.le
  by_cases hsmall : (d:ℝ)≤Real.sqrt t
  · have hsqrt : Real.sqrt t<t := by nlinarith only [Real.sq_sqrt ht₀.le,Real.sqrt_nonneg t,ht]
    have hlt : (d:ℝ)<t := hsmall.trans_lt hsqrt
    have H := brun_titchmarsh_two (x:=0) (a:=a) (by norm_num) hd hlt
    have he : piAP 0 d a=0 := by simp [piAP,primeCountingAP]
    rw [zero_add,he,sub_zero] at H
    have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
    have hw : r≤4*d.totient :=
      (Real.rpow_le_rpow_of_exponent_le hd₁ (by norm_num : (1/4:ℝ)≤3/4)).trans (rpow_three_quarters_le_four_mul_totient hd)
    have hl₁ := Real.log_le_log hd₀ hsmall
    rw [Real.log_sqrt ht₀.le] at hl₁
    have hl₂ : log t/2≤log (t/d) := by rw [Real.log_div ht₀.ne' hd₀.ne']; linarith
    have hden := mul_pos hφ (show 0<log (t/d) by linarith)
    have hp : 0≤piAP t d a := by unfold piAP; positivity
    apply (le_div_iff₀ hlog).2
    have H' := (le_div_iff₀ hden).mp H
    have HH := mul_le_mul_of_nonneg_left hl₂ (mul_nonneg hp hφ.le)
    have H₃ := mul_le_mul_of_nonneg_left hw (mul_nonneg hp hlog.le)
    dsimp only [r] at hw H₃
    nlinarith only [H',HH,H₃]
  · let v := t^(1/4:ℝ)
    have hv : 0<v := Real.rpow_pos_of_pos ht₀ _
    have hv₁ : 1≤v := Real.one_le_rpow (by linarith) (by norm_num)
    have hv4 : v^4=t := fourth_root_fourth ht₀.le
    have hd' : t ≤ (d:ℝ)^2 := by
      rw [←Real.sq_sqrt ht₀.le]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (not_le.mp hsmall).le _
    have hv' : v≤r^2 := by
      apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by positivity)
      rw [hv4,show (r^2)^4=(r^4)^2 by ring,hr4]
      exact hd'
    have hr' : r≤v^2 := by
      apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by positivity)
      rw [hr4,show (v^2)^4=(v^4)^2 by ring,hv4]
      exact hdt
    have hr₁ : 1≤r := Real.one_le_rpow hd₁ (by norm_num)
    have hrv : r*v≤(d:ℝ) := by
      rw [←hr4]
      calc _ ≤ r*r^2 := mul_le_mul_of_nonneg_left hv' hr.le
           _ ≤ r^4 := by rw [show r*r^2=r^3 by ring]; exact pow_le_pow_right₀ hr₁ (by decide)
    have hterm₁ : t/d*r*v≤t := by
      rw [show t/d*r*v=t*(r*v)/d by ring,div_le_iff₀ hd₀]
      exact mul_le_mul_of_nonneg_left hrv ht₀.le
    have hterm₂ : r*v≤t := by
      rw [←hv4]
      calc _ ≤ v^2*v := mul_le_mul_of_nonneg_right hr' hv.le
           _ ≤ v^4 := by rw [show v^2*v=v^3 by ring]; exact pow_le_pow_right₀ hv₁ (by decide)
    have hlv : log t≤4*v := by
      rw [←hv4,Real.log_pow]
      push_cast
      linarith only [Real.log_le_sub_one_of_pos hv]
    have H := mul_le_mul_of_nonneg_right (piAP_trivial ht₀.le hd a) (mul_nonneg hr.le hv.le)
    have hp : 0≤piAP t d a := by unfold piAP; positivity
    apply (le_div_iff₀ hlog).2
    change piAP t d a*r*log t≤_
    nlinarith only [hterm₁,hterm₂,H,ht₀.le,mul_le_mul_of_nonneg_left hlv (mul_nonneg hp hr.le)]

end AnalyticNumberTheory.AdditiveNumberTheory
