import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocal
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index

/-!
# Solubility of Waring congruences at primes

A nonzero residue has at most `k` distinct `k`-th roots. Repeated sumsets
therefore fill the whole prime field after at most `k` summands by Cauchy–Davenport.
-/

open Finset Polynomial
open scoped Pointwise

namespace AnalyticNumberTheory.AdditiveNumberTheory

variable {p : ℕ} [Fact p.Prime]

private def powersMod (k : ℕ) : Finset (ZMod p) := univ.image (· ^ k)

private theorem card_powersMod {k : ℕ} (hk : 0 < k) :
    p ≤ 1 + ((powersMod (p := p) k).card - 1) * k := by
  classical
  let A := powersMod (p := p) k
  let F := fun b : ZMod p => univ.filter fun a : ZMod p => a ^ k = b
  have h0 : (0 : ZMod p) ∈ A := mem_image.mpr ⟨0, mem_univ _, zero_pow hk.ne'⟩
  have hcard : p = ∑ b ∈ A, (F b).card := by
    calc p = (univ : Finset (ZMod p)).card := by simp [ZMod.card]
         _ = _ := card_eq_sum_card_fiberwise (fun x _ => mem_image_of_mem _ (mem_univ x))
  have hzero : F 0 = {0} := by ext; simp [F, hk.ne']
  have hroot (b : ZMod p) : (F b).card ≤ k := by
    have he : F b = (nthRoots k b).toFinset := by ext x; simp [F, mem_nthRoots hk]
    exact he ▸ ((nthRoots k b).toFinset_card_le.trans (card_nthRoots k b))
  rw [← sum_erase_add _ _ h0, hzero, card_singleton] at hcard
  have hle := sum_le_sum (s := A.erase 0) (fun b _ => hroot b)
  simp only [sum_const, smul_eq_mul, card_erase_of_mem h0] at hle
  change p ≤ 1 + (A.card - 1) * k
  omega

private def sumsetMod (k s : ℕ) : Finset (ZMod p) :=
  univ.image (fun x : Fin s → ZMod p => ∑ i, x i ^ k)

private theorem sumsetMod_succ (k s : ℕ) :
    sumsetMod (p := p) k (s + 1) = powersMod k + sumsetMod k s := by
  ext b
  simp only [sumsetMod, powersMod, mem_image, mem_univ, true_and, mem_add]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x 0, rfl⟩, _, ⟨fun i => x i.succ, rfl⟩, (Fin.sum_univ_succ (fun i => x i ^ k)).symm⟩
  · rintro ⟨a, ⟨u, rfl⟩, b, ⟨x, rfl⟩, rfl⟩
    exact ⟨Fin.cons u x, by simp [Fin.sum_univ_succ]⟩

private theorem card_sumsetMod {k : ℕ} (hk : 0 < k) (s : ℕ) :
    min p (1 + s * ((powersMod (p := p) k).card - 1)) ≤ (sumsetMod (p := p) k s).card := by
  have hA : (powersMod (p := p) k).Nonempty := ⟨0, mem_image.mpr ⟨0, mem_univ _, zero_pow hk.ne'⟩⟩
  have hS (r : ℕ) : (sumsetMod (p := p) k r).Nonempty :=
    ⟨_, mem_image_of_mem _ (mem_univ (fun _ : Fin r => (0 : ZMod p)))⟩
  induction s with
  | zero => simpa using (min_le_right p 1).trans (card_pos.mpr (hS 0))
  | succ s ih =>
    rw [sumsetMod_succ]
    refine le_trans ?_ (ZMod.cauchy_davenport Fact.out hA (hS s))
    have hle := card_pos.mpr hA
    rw [Nat.succ_mul]
    omega

/-- Every residue modulo a prime is a sum of `s` powers of degree `k` as soon as `0 < k ≤ s`. -/
theorem waringLocalCount_pos_prime {k s : ℕ} (hk : 0 < k) (hs : k ≤ s) (n : ZMod p) :
    0 < waringLocalCount k s n := by
  have hbound := card_powersMod (p := p) hk
  have hlast : p ≤ 1 + s * ((powersMod (p := p) k).card - 1) := by
    rw [mul_comm] at hbound
    exact hbound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _)
  have hcard := card_sumsetMod (p := p) hk s
  rw [min_eq_left hlast] at hcard
  have he : sumsetMod (p := p) k s = univ := eq_univ_of_card _ (by
    rw [ZMod.card]; exact hcard.antisymm' (by simpa [ZMod.card] using card_le_univ (sumsetMod (p := p) k s)))
  have hn : n ∈ sumsetMod (p := p) k s := he ▸ mem_univ n
  obtain ⟨x, _, hx⟩ := mem_image.mp hn
  exact card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩

/-- Every principal unit modulo a prime power has a `k`-th root in the principal
units when `p` does not divide `k`. The kernel of reduction has order `p^r`. -/
theorem exists_pow_eq_of_reduce_eq_one {k : ℕ} (hpk : p.Coprime k) (r : ℕ)
    (b : ZMod (p ^ (r + 1))) (hb : ZMod.castHom (dvd_pow_self p (by omega : r+1 ≠ 0))
      (ZMod p) b = 1) :
    ∃ a : ZMod (p ^ (r + 1)), a ^ k = b ∧
      ZMod.castHom (dvd_pow_self p (by omega : r+1 ≠ 0)) (ZMod p) a = 1 := by
  have hp : p.Prime := Fact.out
  let hd : p ∣ p ^ (r + 1) := dvd_pow_self p (by omega)
  let red := ZMod.castHom hd (ZMod p)
  let f := ZMod.unitsMap hd
  change red b = 1 at hb
  have hc : Nat.card f.ker = p ^ r := by
    have h := Subgroup.card_ker_mul_card_of_surjective (ZMod.unitsMap_surjective hd)
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp,
      Nat.totient_prime_pow_succ hp] at h
    rw [Nat.card_eq_fintype_card]
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) h
  have hval : (b.val : ZMod p) = 1 := by
    calc (b.val : ZMod p) = red (b.val : ZMod (p ^ (r + 1))) := (map_natCast _ _).symm
         _ = 1 := by simpa using hb
  have hcop : p.Coprime b.val := hp.coprime_iff_not_dvd.mpr fun h => by
    have hz := (ZMod.natCast_eq_zero_iff b.val p).2 h
    exact zero_ne_one (hz.symm.trans hval)
  have hu : IsUnit b := by
    simpa using (ZMod.isUnit_iff_coprime b.val (p ^ (r + 1))).2 (hcop.symm.pow_right _)
  have hker : hu.unit ∈ f.ker := by
    apply Units.ext
    change red hu.unit.val = 1
    simpa using hb
  have hcard : (Nat.card f.ker).Coprime k := hc ▸ hpk.pow_left r
  obtain ⟨u, hu'⟩ := hcard.pow_left_bijective.surjective (⟨hu.unit, hker⟩ : f.ker)
  refine ⟨u.val.val, ?_, ?_⟩
  · simpa using congrArg (fun v : f.ker => v.val.val) hu'
  · exact congrArg Units.val (show f u.val = 1 from u.property)

/-- One extra summand fixes a coordinate to `1` modulo `p`, leaving a principal
unit to be lifted. All target residues are represented at every power of a prime
coprime to the degree. -/
theorem waringLocalCount_pos_prime_pow {k s : ℕ} (hk : 0 < k) (hks : k < s)
    (hpk : p.Coprime k) (r : ℕ) (n : ZMod (p ^ r)) : 0 < waringLocalCount k s n := by
  cases r with
  | zero =>
    refine card_pos.mpr ⟨fun _ => 0, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ r =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    let red := ZMod.castHom (dvd_pow_self p (by omega : r+1 ≠ 0)) (ZMod p)
    obtain ⟨x, hx⟩ := card_pos.mp (waringLocalCount_pos_prime hk (by omega : k ≤ s) (red n - 1))
    have hx' := (mem_filter.mp hx).2
    let y (i : Fin s) : ZMod (p ^ (r + 1)) := (x i).val
    have hred (i : Fin s) : red (y i) = x i := by simp [y]
    have hb : red (n - ∑ i, y i ^ k) = 1 := by
      rw [map_sub, map_sum]
      simp only [map_pow, hred, hx']
      ring
    obtain ⟨a, ha, _⟩ := exists_pow_eq_of_reduce_eq_one hpk r _ hb
    refine card_pos.mpr ⟨Fin.cons a y, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    simp [Fin.sum_univ_succ, ha]

end AnalyticNumberTheory.AdditiveNumberTheory
