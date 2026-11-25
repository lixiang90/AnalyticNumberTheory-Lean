import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-!
# Power classes among units modulo a prime power

For odd prime powers the cyclic unit group has at most `k` classes
modulo `k`-th powers. For powers of two a sign and a power of five
give at most `2k` such classes.
-/

open Finset
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem split_generator_power {G : Type*} [Group G] (g : G) {k : ℕ} (hk : 0<k) (m : ℤ) :
    ∃ i<k, ∃ v : G, g^m=g^i*v^k := by
  have hkp : (0:ℤ)<k := by exact_mod_cast hk
  let r := m%(k:ℤ)
  have hr : 0≤r := Int.emod_nonneg _ hkp.ne'
  refine ⟨r.toNat,by simpa using (Int.toNat_lt_toNat hkp).mpr (Int.emod_lt_of_pos m hkp),g^(m/(k:ℤ)),?_⟩
  rw [←zpow_natCast g r.toNat,Int.toNat_of_nonneg hr,←zpow_natCast (g^(m/(k:ℤ))) k,←zpow_mul,←zpow_add]
  congr 1
  dsimp only [r]
  linarith only [Int.emod_add_mul_ediv m k]

/-- At most two representatives for each of the `k` exponent remainders
suffice for every unit modulo any prime power. -/
theorem waring_unit_power_classes {p a k : ℕ} (hp : p.Prime) (hk : 0<k) :
    ∃ B : Finset (ZMod (p^a))ˣ, B.card≤2*k ∧
      ∀ u : (ZMod (p^a))ˣ, ∃ b∈B, ∃ v : (ZMod (p^a))ˣ, u=b*v^k := by
  classical
  by_cases hodd : p=2
  · subst p
    let g := (ZMod.unitFive : (ZMod (2^a))ˣ)
    let R := (range k).image (fun j => g^j)
    let B := R ∪ R.image (fun z => -z)
    have hR : R.card≤k := (card_image_le.trans_eq (card_range _))
    refine ⟨B,(card_union_le ..).trans (by have h := card_image_le (f:=fun z : (ZMod (2^a))ˣ => -z) (s:=R); omega),?_⟩
    intro u
    have hu : u ∈ Subgroup.zpowers g ⊔ Subgroup.zpowers (-1 : (ZMod (2^a))ˣ) := by
      rw [(ZMod.isComplement'_zpowers_unitFive_neg_one a).sup_eq_top]; trivial
    obtain ⟨x,hx,y,hy,hxy⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨j,rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨l,rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨i,hi,v,hv⟩ := split_generator_power g hk j
    have hr : g^i∈R := mem_image_of_mem _ (mem_range.mpr hi)
    rw [←hxy,hv,neg_one_zpow_eq_ite]
    split_ifs
    · exact ⟨g^i,mem_union_left _ hr,v,by simp⟩
    · exact ⟨-(g^i),mem_union_right _ (mem_image_of_mem _ hr),v,by simp⟩
  · obtain ⟨g,hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (ZMod.isCyclic_units_of_prime_pow p hp hodd a)
    let B := (range k).image (fun j => g^j)
    refine ⟨B,(card_image_le.trans_eq (card_range k)).trans (by omega),?_⟩
    intro u
    have hu : u∈Subgroup.zpowers g := by rw [hg]; trivial
    obtain ⟨j,rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨i,hi,v,hv⟩ := split_generator_power g hk j
    exact ⟨g^i,mem_image_of_mem _ (mem_range.mpr hi),v,hv⟩

end AnalyticNumberTheory.AdditiveNumberTheory
