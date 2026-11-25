import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Absolute convergence from the prime-power masses

An absolutely summable bound for the nonconstant part of each local Euler
factor bounds all finite partial sums of the multiplicative coefficients.
-/

open Finset Nat Real
namespace AnalyticNumberTheory.DirichletSeries

/-- Summable local absolute tails imply absolute convergence of the global multiplicative series. -/
theorem summable_of_local_euler_bounds {f : ℕ→ℝ} (h₀ : f 0=0) (h₁ : f 1=1)
    (hm : ∀ {m n : ℕ}, m.Coprime n → f (m*n)=f m*f n)
    (b : ℕ→ℝ) (hb : ∀ n, 0≤b n) (hs : Summable b)
    (hlocal : ∀p : ℕ, p.Prime → Summable (fun j : ℕ => |f (p^j)|) ∧
      ∑' j : ℕ, |f (p^j)|≤1+b p) : Summable (fun n => |f n|) := by
  classical
  apply summable_of_sum_range_le (fun _ => abs_nonneg _) (c:=exp (∑' n, b n))
  intro N
  let S := (range N).erase 0
  have hS (n : ℕ) (hn : n∈S) : n∈N.smoothNumbers := by
    have hx := mem_erase.mp hn
    exact Nat.mem_smoothNumbers'.mpr fun p hp hpn => (Nat.le_of_dvd (Nat.pos_of_ne_zero hx.1) hpn).trans_lt (mem_range.mp hx.2)
  obtain ⟨_,H⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f:=fun n => |f n|) (by simp [h₁]) (fun {_ _} hc => by rw [hm hc,abs_mul])
    (fun {p} hp => by simpa [Real.norm_eq_abs] using (hlocal p hp).1) N
  let e : S ↪ N.smoothNumbers := ⟨fun n => ⟨n.val,hS n n.prop⟩, fun _ _ h => Subtype.ext (congrArg (fun x : N.smoothNumbers => (x:ℕ)) h)⟩
  have hadd : ∑ i∈S,|f i| ≤ ∑' n : N.smoothNumbers, |f n| := by
    have h := H.summable.sum_le_tsum (univ.map e) (fun _ _ => abs_nonneg _)
    rw [Finset.sum_map] at h
    change (∑ x : S, |f (x:ℕ)|) ≤ _ at h
    simpa only [Finset.univ_eq_attach,Finset.sum_attach S (fun i => |f i|)] using h
  have h0sum : ∑ n∈range N, |f n|=∑ i∈S, |f i| := by
    dsimp [S]
    by_cases hn : 0 ∈ range N
    · simpa [h₀] using (Finset.sum_erase_add (range N) (fun i => |f i|) hn).symm
    · rw [Finset.erase_eq_of_notMem hn]
  rw [h0sum]
  refine hadd.trans (H.tsum_eq.le.trans ?_)
  calc
    _ ≤ ∏p∈N.primesBelow, (1+b p) := Finset.prod_le_prod₀ (fun _ _ => tsum_nonneg fun _ => abs_nonneg _)
      (fun p hp => (hlocal p (Nat.mem_primesBelow.mp hp).2).2)
    _ ≤ exp (∑ p∈N.primesBelow,b p) := Real.prod_one_add_le_exp_sum _ hb
    _ ≤ _ := Real.exp_le_exp.mpr (hs.sum_le_tsum _ (fun n _ => hb n))

end AnalyticNumberTheory.DirichletSeries
