import AnalyticNumberTheory.ExponentialSums.VinogradovCongruenceRoots
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Vinogradov's mixed-modulus congruence lemma

Completing the `j`-th power sum from modulus `p^j` to modulus `p^n` introduces
at most `p^(n-j)` choices. Each complete vector has at most `n!` separated
preimages. This gives the factor `p^(n(n-1)/2)` in the classical recursion.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Reduction of a completed power sum to the modulus appropriate to its degree. -/
def vinogradovPowerReduction (p : ℕ) {n : ℕ} (j : Fin n) :
    ZMod (p^n) →+* ZMod (p^(j.val+1)) :=
  ZMod.castHom (pow_dvd_pow p j.isLt) _

/-- Mixed prime-power congruences for tuples whose entries are separated modulo the prime. -/
theorem card_vinogradov_congruences_le {p n : ℕ} (hp : p.Prime) (hn : 0<n) (hnp : n<p)
    (h : (j : Fin n) → ZMod (p^(j.val+1))) (S : Finset (Fin n → ZMod (p^n)))
    (hsep : ∀ x∈S, Function.Injective (vinogradovReduction p n hn ∘ x))
    (hsum : ∀ x∈S, ∀ j : Fin n, vinogradovPowerReduction p j (∑ i,x i^(j.val+1)) = h j) :
    S.card ≤ n.factorial * p^(n*(n-1)/2) := by
  classical
  letI : NeZero (p^n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let g (x : Fin n → ZMod (p^n)) (j : Fin n) := ∑ i,x i^(j.val+1)
  let digits := (j : Fin n) → Fin (p^(n-(j.val+1)))
  let upper (x : Fin n → ZMod (p^n)) : digits := fun j =>
    ⟨(g x j).val / p^(j.val+1), (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr (by
      rw [←pow_add,Nat.sub_add_cancel j.isLt]; exact (g x j).val_lt)⟩
  have hf (v : digits) : (S.filter (fun x => upper x=v)).card ≤ n.factorial := by
    let B := S.filter (fun x => upper x=v)
    obtain hB | ⟨y,hy⟩ := B.eq_empty_or_nonempty
    · change B.card ≤ _; simp [hB]
    apply card_primePower_power_sums_le_factorial hp hn hnp (g y)
    · intro x hx; exact hsep x (mem_filter.mp hx).1
    · intro x hx j
      have hhi := congrArg (fun z : digits => (z j).val) ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
      have hlo := (hsum x (mem_filter.mp hx).1 j).trans (hsum y (mem_filter.mp hy).1 j).symm
      change vinogradovPowerReduction p j (g x j) = vinogradovPowerReduction p j (g y j) at hlo
      simp only [vinogradovPowerReduction,ZMod.castHom_apply,ZMod.cast_eq_val] at hlo
      have hmod := congrArg ZMod.val hlo
      simp only [ZMod.val_natCast] at hmod
      change (g x j).val / p^(j.val+1) = (g y j).val / p^(j.val+1) at hhi
      change g x j=g y j
      apply ZMod.val_injective
      calc _ = (g x j).val % p^(j.val+1) + p^(j.val+1)*((g x j).val / p^(j.val+1)) :=
                 (Nat.mod_add_div ..).symm
           _ = _ := by rw [hhi,hmod,Nat.mod_add_div]
  have hsumexp : (∑ j : Fin n, (n-(j.val+1)))=n*(n-1)/2 := by
    calc _ = ∑ j : Fin n, (Fin.rev j).val := by apply sum_congr rfl; intro j _; rfl
         _ = ∑ j : Fin n, j.val := Equiv.sum_comp (Fin.revPerm (n:=n)) (fun j => j.val)
         _ = ∑ j ∈ range n, j := Fin.sum_univ_eq_sum_range (fun k : ℕ => k) n
         _ = _ := Finset.sum_range_id n
  have hcard : Fintype.card digits = p^(n*(n-1)/2) := by
    dsimp only [digits]
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin,Finset.prod_pow_eq_pow_sum,hsumexp]
  rw [card_eq_sum_card_fiberwise (t:=univ) (fun x _ => mem_univ (upper x))]
  apply (sum_le_sum (fun v _ => hf v)).trans_eq
  simp [hcard,mul_comm]

/-- For fixed residues, each coordinate in a shifted integer interval of length
`m*q` has at most `m` lifts. -/
theorem card_lifts_in_integer_box {n q m : ℕ} (hq : 0<q) (A : ℤ)
    (S : Finset (Fin n → ℤ)) (hbox : ∀ x∈S, ∀ i, A<x i ∧ x i≤A+(m*q:ℕ))
    (y : Fin n → ZMod q) (hres : ∀ x∈S, ∀ i, (x i : ZMod q)=y i) : S.card ≤ m^n := by
  classical
  let off (x : Fin n → ℤ) (i : Fin n) := x i-A-1
  let b (x : Fin n → ℤ) (i : Fin n) := ((off x i)/(q:ℤ)).toNat
  let C := Fintype.piFinset (fun _ : Fin n => range m)
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have hoff (x) (hx : x∈S) (i) : 0≤off x i ∧ off x i<(m:ℤ)*q := by
    obtain ⟨h₀,h₁⟩ := hbox x hx i
    push_cast at h₁; dsimp [off]; omega
  have hcard := card_le_card_of_injOn (s:=S) (t:=C) b (by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_range.mpr
    have hd := (Int.ediv_lt_iff_lt_mul hqz).mpr (hoff x hx i).2
    have h₀ := Int.ediv_nonneg (hoff x hx i).1 hqz.le
    dsimp only [b]; omega) (by
    intro x hx z hz he
    funext i
    have hb := congrFun he i
    change ((off x i)/(q:ℤ)).toNat = ((off z i)/(q:ℤ)).toNat at hb
    have hd₁ := Int.ediv_nonneg (hoff x hx i).1 hqz.le
    have hd₂ := Int.ediv_nonneg (hoff z hz i).1 hqz.le
    have hd : (off x i)/(q:ℤ)=(off z i)/(q:ℤ) := by omega
    have hcast : (off x i:ZMod q)=(off z i:ZMod q) := by
      dsimp only [off]; push_cast; rw [hres x hx i,hres z hz i]
    have hr := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast
    have hxz := Int.emod_add_mul_ediv (off x i) q
    rw [hr,hd,Int.emod_add_mul_ediv] at hxz
    dsimp only [off] at hxz; omega)
  simpa only [C,Fintype.card_piFinset_const,card_range] using hcard

/-- Vinogradov's congruence bound in an arbitrary translated integer box.
The modulus of the `j`-th moment is `p^j`, and the side length is `m*p^n`. -/
theorem vinogradov_congruence_box_le {p n m : ℕ} (hp : p.Prime) (hn : 0<n) (hnp : n<p)
    (A : ℤ) (h : Fin n → ℤ) (S : Finset (Fin n → ℤ))
    (hbox : ∀ x∈S, ∀ i, A<x i ∧ x i≤A+(m*p^n:ℕ))
    (hsep : ∀ x∈S, Function.Injective (fun i => (x i : ZMod p)))
    (hsum : ∀ x∈S, ∀ j : Fin n, (∑ i, x i^(j.val+1)) ≡ h j [ZMOD (p^(j.val+1):ℕ)]) :
    S.card ≤ n.factorial*m^n*p^(n*(n-1)/2) := by
  classical
  let f (x : Fin n → ℤ) (i : Fin n) : ZMod (p^n) := x i
  let W := S.image f
  have hnsep (w) (hw : w∈W) : Function.Injective (vinogradovReduction p n hn ∘ w) := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
    simpa only [Function.comp_def,f,map_intCast] using hsep x hx
  have hnsum (w) (hw : w∈W) (j : Fin n) :
      vinogradovPowerReduction p j (∑ i,w i^(j.val+1)) = (h j : ZMod (p^(j.val+1))) := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
    have H := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hsum x hx j)
    simpa only [map_sum,map_pow,map_intCast,f,Int.cast_sum,Int.cast_pow] using H
  have hW := card_vinogradov_congruences_le hp hn hnp (fun j => (h j : ZMod (p^(j.val+1)))) W hnsep hnsum
  have hcell (z : Fin n → ZMod (p^n)) :
      (S.filter (fun x => f x=z)).card ≤ m^n :=
    card_lifts_in_integer_box (pow_pos hp.pos _) A _ (fun x hx => hbox x (mem_filter.mp hx).1)
      z (fun x hx i => congrFun (mem_filter.mp hx).2 i)
  rw [card_eq_sum_card_image f S]
  calc _ ≤ ∑ _z ∈ W, m^n := sum_le_sum fun z _ => hcell z
       _ = W.card*m^n := by simp
       _ ≤ _ := (Nat.mul_le_mul_right (m^n) hW).trans_eq (by ring)

end AnalyticNumberTheory.ExponentialSums
