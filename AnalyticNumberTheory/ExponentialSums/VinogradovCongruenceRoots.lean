import AnalyticNumberTheory.ExponentialSums.VinogradovDiagonal
import Mathlib.Data.ZMod.Basic

/-!
# Separated solutions of the Vinogradov system modulo a prime power

Newton's identities recover a monic polynomial over the prime-power ring.
Reduction modulo the prime singles out one possible factor at each root.
All the other factors are units, so each separated tuple with the same
power sums is a permutation of the initial tuple.
-/

open Finset

namespace AnalyticNumberTheory.ExponentialSums

/-- Coordinatewise reduction to the residue field. -/
def vinogradovReduction (p d : ℕ) (hd : 0<d) : ZMod (p^d) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hd)) (ZMod p)

private theorem unit_of_reduction_ne {p d : ℕ} (hp : p.Prime) (hd : 0<d)
    {z : ZMod (p^d)} (hz : vinogradovReduction p d hd z ≠ 0) : IsUnit z := by
  letI : NeZero (p^d) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [←ZMod.natCast_zmod_val z] at hz ⊢
  rw [map_natCast] at hz
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).mpr (by simpa only [Ne,ZMod.natCast_eq_zero_iff] using hz)

/-- Over a prime power, two tuples separated modulo the prime with matching first
power sums differ only by a permutation. -/
theorem exists_perm_of_primePower_power_sums {p d n : ℕ} (hp : p.Prime) (hd : 0<d) (hnp : n<p)
    (x y : Fin n → ZMod (p^d))
    (hx : Function.Injective (vinogradovReduction p d hd ∘ x))
    (hy : Function.Injective (vinogradovReduction p d hd ∘ y))
    (hs : ∀ j : ℕ, 1≤j → j≤n → ∑ i,x i^j=∑ i,y i^j) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, x (e i)=y i := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let φ := vinogradovReduction p d hd
  have hu (j : ℕ) (hj : 1≤j) (hjn : j≤n) : IsUnit (j:ZMod (p^d)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).mpr (Nat.not_dvd_of_pos_of_lt hj (hjn.trans_lt hnp))
  have hpoly := prod_X_sub_C_eq_of_power_sums hu x y hs
  have hroot (i : Fin n) : ∏ k, (y i-x k) = 0 := by
    have h := congrArg (Polynomial.eval (y i)) hpoly
    simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at h
    exact h.trans (Finset.prod_eq_zero (mem_univ i) (by simp))
  have hmatch (i : Fin n) : ∃ k, x k = y i := by
    have hzero := congrArg φ (hroot i)
    simp only [map_prod,map_sub,map_zero] at hzero
    obtain ⟨k,_,he⟩ := Finset.prod_eq_zero_iff.mp hzero
    have hsame := sub_eq_zero.mp he
    let P := ∏ j ∈ univ.erase k, (y i-x j)
    have hunit : IsUnit P := by
      apply unit_of_reduction_ne hp hd
      change φ P ≠ 0
      rw [show φ P = ∏ j ∈ univ.erase k, (φ (y i)-φ (x j)) by simp [P]]
      apply prod_ne_zero_iff.mpr
      intro j hj
      apply sub_ne_zero.mpr
      intro he'
      apply (mem_erase.mp hj).1
      exact hx (show φ (x j)=φ (x k) from he'.symm.trans hsame)
    refine ⟨k,(sub_eq_zero.mp ?_).symm⟩
    apply hunit.mul_left_inj.mp
    calc (y i-x k)*P = ∏ j, (y i-x j) := mul_prod_erase univ (fun j => y i-x j) (mem_univ k)
         _ = 0*P := by rw [hroot,zero_mul]
  choose f hf using hmatch
  have hfi : Function.Injective f := by
    intro i j hij
    apply hy
    exact congrArg φ ((hf i).symm.trans ((congrArg x hij).trans (hf j)))
  exact ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hfi),hf⟩

/-- At most `n!` separated tuples have a prescribed complete power-sum vector. -/
theorem card_primePower_power_sums_le_factorial {p d n : ℕ} (hp : p.Prime) (hd : 0<d) (hnp : n<p)
    (h : Fin n → ZMod (p^d)) (S : Finset (Fin n → ZMod (p^d)))
    (hsep : ∀ x∈S, Function.Injective (vinogradovReduction p d hd ∘ x))
    (hsum : ∀ x∈S, ∀ j : Fin n, ∑ i,x i^(j.val+1) = h j) : S.card ≤ n.factorial := by
  classical
  obtain hS | ⟨x,hx⟩ := S.eq_empty_or_nonempty
  · simp [hS]
  have hcard := card_le_card_of_surjOn (s:=(univ : Finset (Equiv.Perm (Fin n)))) (t:=S) (fun e => x ∘ e) (by
    intro y hy
    obtain ⟨e,he⟩ := exists_perm_of_primePower_power_sums hp hd hnp x y (hsep x hx) (hsep y hy) (by
      intro j hj hjn
      let j' : Fin n := ⟨j-1,by omega⟩
      have h := (hsum x hx j').trans (hsum y hy j').symm
      simpa only [j',Nat.sub_add_cancel hj] using h)
    exact ⟨e,mem_univ e,funext he⟩)
  simpa only [card_univ,Fintype.card_perm,Fintype.card_fin] using hcard

end AnalyticNumberTheory.ExponentialSums
