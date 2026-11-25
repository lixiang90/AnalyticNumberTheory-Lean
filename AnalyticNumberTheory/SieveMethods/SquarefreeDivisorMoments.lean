import AnalyticNumberTheory.PrimeDistribution.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree

/-!
# A divisor moment over squarefree moduli

The sum of τ(d)^4/φ(d) over squarefree d ≤ x is bounded by the
sixteenth power of Mertens' prime product. This estimates the weighted
factor in Cauchy–Schwarz applications of Bombieri–Vinogradov.
-/

open Finset Real Filter ArithmeticFunction
open scoped ArithmeticFunction.sigma Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution

private noncomputable def mass : ArithmeticFunction ℝ where
  toFun n := (n.divisors.card:ℝ)^4/n.totient
  map_zero' := by simp

private theorem mass_mult : mass.IsMultiplicative := by
  constructor
  · norm_num [mass]
  · intro a b hab
    simp only [mass,ArithmeticFunction.coe_mk,←sigma_zero_apply,Nat.totient_mul hab,
      isMultiplicative_sigma.2 hab,Nat.cast_mul,mul_pow]
    ring

private theorem local_mass {p : ℕ} (hp : p.Prime) : mass p=16/((p:ℝ)-1) := by
  have hσ := sigma_zero_apply_prime_pow (i:=1) hp
  simp only [pow_one,sigma_zero_apply] at hσ
  simp [mass,hσ,Nat.totient_prime hp,Nat.cast_sub hp.one_le]
  <;> norm_num

private theorem squarefree_mass_euler {x : ℝ} (hx : 1≤x) :
    (∑d∈(Icc 1 ⌊x⌋₊).filter Squarefree,(d.divisors.card:ℝ)^4/d.totient) ≤
      (∏p∈Nat.primesLE ⌊x⌋₊,(1-(p:ℝ)⁻¹)⁻¹)^16 := by
  classical
  let D := (Icc 1 ⌊x⌋₊).filter Squarefree
  let P := Nat.primesLE ⌊x⌋₊
  let f := fun p : ℕ => 16/((p:ℝ)-1)
  have hsub : D.image Nat.primeFactors⊆P.powerset := by
    intro T hT;obtain ⟨d,hd,rfl⟩ := mem_image.mp hT
    obtain ⟨hd,hs⟩ := mem_filter.mp hd
    apply mem_powerset.mpr
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hd).2,
      Nat.prime_of_mem_primeFactors hp⟩
  have hi : Set.InjOn Nat.primeFactors (D:Set ℕ) := by
    intro a ha b hb he
    rw [←Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2,←Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2,he]
  have hlocal (p : ℕ) (hp : p∈P) : 0≤f p := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact div_nonneg (by norm_num) (by linarith)
  calc _ = ∑T∈D.image Nat.primeFactors,∏p∈T,f p := by
             rw [sum_image hi]
             apply sum_congr rfl
             intro d hd
             change mass d=_
             rw [← mass_mult.prod_primeFactors (mem_filter.mp hd).2]
             exact prod_congr rfl (fun p hp => local_mass (Nat.prime_of_mem_primeFactors hp))
       _ ≤ ∑T∈P.powerset,∏p∈T,f p := sum_le_sum_of_subset_of_nonneg hsub
             (fun T hT _ => prod_nonneg fun p hp => hlocal p (mem_powerset.mp hT hp))
       _ = ∏p∈P, (1+f p) := (prod_one_add _).symm
       _ ≤ _ := by
             rw [← Finset.prod_pow]
             apply Finset.prod_le_prod₀ (fun p hp => by linarith [hlocal p hp])
             intro p hp
             have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
             have ht : (1-(p:ℝ)⁻¹)⁻¹=1+1/((p:ℝ)-1) := by field_simp [show (p:ℝ)≠0 by linarith,show (p:ℝ)-1≠0 by linarith];ring
             rw [ht]
             have hb := one_add_mul_le_pow (a:=1/((p:ℝ)-1)) (by have ht : 0≤1/((p:ℝ)-1) := div_nonneg zero_le_one (by linarith);linarith) 16
             simpa only [f,Nat.cast_ofNat,mul_one_div] using hb

/-- Total fourth divisor moment with reciprocal totient weight, over squarefree moduli. -/
theorem squarefree_divisor_fourth_over_totient :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      (∑d∈(Icc 1 ⌊x⌋₊).filter Squarefree,(d.divisors.card:ℝ)^4/d.totient) ≤ C*(log x)^16 := by
  let g := exp (-Real.eulerMascheroniConstant)
  have hg : 0<g := exp_pos _
  refine ⟨(2/g)^16,by positivity,?_⟩
  filter_upwards [mertens_third_theorem_tendsto.eventually_const_lt (show g/2<g by linarith),
    eventually_ge_atTop (2:ℝ)] with x h hx
  let V := ∏p∈Nat.primesLE ⌊x⌋₊, (1-(p:ℝ)⁻¹)
  have hl := Real.log_pos (show 1<x by linarith)
  change g/2<log x*V at h
  have hv : 0<V := pos_of_mul_pos_right (show 0<log x*V by linarith) hl.le
  have hbound : V⁻¹ ≤ (2/g)*log x := by rw [inv_le_iff_one_le_mul₀ hv];field_simp [hg.ne'];linarith
  have H := squarefree_mass_euler (show 1≤x by linarith)
  rw [Finset.prod_inv_distrib] at H
  exact H.trans ((pow_le_pow_left₀ (inv_nonneg.mpr hv.le) hbound 16).trans_eq (mul_pow ..))

end AnalyticNumberTheory.SieveMethods
