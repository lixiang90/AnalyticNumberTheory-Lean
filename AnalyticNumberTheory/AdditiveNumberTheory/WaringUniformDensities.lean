import AnalyticNumberTheory.AdditiveNumberTheory.WaringUnitRepresentations
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSeriesPositivity
import AnalyticNumberTheory.AdditiveNumberTheory.WaringAsymptotic

/-!
# Uniform positivity of the Waring singular series

A unit coordinate at Hensel precision can absorb every choice of lifts of the
remaining coordinates. The resulting local lower bounds are independent of the target.
-/

open Finset Filter
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Removing any unit coordinate leaves a representation of the complementary class. -/
theorem WaringUnitRepresentation.exists_complement {q k s : ℕ} [NeZero q] {a : ZMod q}
    (h : WaringUnitRepresentation k (s+1) a) :
    ∃ u : (ZMod q)ˣ, 0 < waringLocalCount k s (a-(u : ZMod q)^k) := by
  obtain ⟨x,hx,i,hi⟩ := h
  refine ⟨hi.unit, card_pos.mpr ⟨fun j => x (i.succAbove j), mem_filter.mpr ⟨mem_univ _,?_⟩⟩⟩
  rw [IsUnit.unit_spec, ← hx, Fin.sum_univ_succAbove (fun j => x j^k) i]
  simp

/-- A unit power at the starting precision lifts to a power at every higher precision. -/
theorem exists_pow_eq_of_unit_henselLevel {p k r : ℕ} [Fact p.Prime] (hk : 0<k)
    (hr : waringHenselLevel p k ≤ r) (u : (ZMod (p^waringHenselLevel p k))ˣ)
    (b : ZMod (p^r)) (hb : ZMod.castHom (pow_dvd_pow p hr) _ b = (u : ZMod (p^waringHenselLevel p k))^k) :
    ∃ z : ZMod (p^r), z^k=b := by
  let hd := pow_dvd_pow p hr
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hd u
  let red := ZMod.castHom hd (ZMod (p^waringHenselLevel p k))
  change red b = (red v)^k at hb
  obtain ⟨z,hz⟩ := exists_pow_eq_of_henselLevel hk hr (b*(↑(v⁻¹) : ZMod (p^r))^k) (by
    change red _ = 1
    rw [map_mul, map_pow, hb, ← mul_pow, ← map_mul]
    simp)
  refine ⟨z*(v : ZMod (p^r)),?_⟩
  rw [mul_pow,hz,mul_assoc,← mul_pow]
  simp

/-- With at least four times the degree many summands, each local factor has a
positive lower bound depending only on the prime, degree and number of summands. -/
theorem waringLocalFactor_re_ge_of_four_mul {p k s : ℕ} [Fact p.Prime] (hk : 0<k)
    (hs : 4*k ≤ s+1) (n : ℕ) :
    1/((p^waringHenselLevel p k : ℕ) : ℝ)^s ≤ (waringLocalFactor k (s+1) n p).re := by
  apply waringLocalFactor_re_ge_of_count hk (by omega) n
  intro r hr
  let hd := pow_dvd_pow p hr
  obtain ⟨u,hu⟩ := (waring_prime_power_unit_representation (p:=p) (Fact.out : p.Prime)
    (show 0 < waringHenselLevel p k by unfold waringHenselLevel; omega) hk hs
    (ZMod.castHom hd _ (n : ZMod (p^r)))).exists_complement
  exact waringLocalCount_ge_of_liftable_residue hd k s _ _ hu (exists_pow_eq_of_unit_henselLevel hk hr u)

/-- The Waring singular series is uniformly positive for every target when `s ≥ 4k`. -/
theorem exists_pos_le_waringSingularSeries_re_of_four_mul {k s : ℕ} (hk : 0<k) (hs : 4*k≤s) :
    ∃ C : ℝ, 0<C ∧ ∀ n, C ≤ (waringSingularSeries k s n).re := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  have hks : 2*k<d+1 := by omega
  obtain ⟨C,hC,h⟩ := exists_pos_le_norm_waringSingularSeries_of_local hk hks (by
    intro p
    have : Fact p.val.Prime := ⟨p.prop⟩
    have hq : 0<((p.val^waringHenselLevel p.val k : ℕ) : ℝ) := by exact_mod_cast pow_pos p.prop.pos _
    exact ⟨_,one_div_pos.mpr (pow_pos hq d),fun n =>
      (waringLocalFactor_re_ge_of_four_mul (p:=p.val) hk hs n).trans (Complex.re_le_norm _)⟩)
  exact ⟨C,hC,fun n => (Complex.re_eq_norm.mpr (waringSingularSeries_nonneg hk hks n)).symm ▸ h n⟩

/-- Every sufficiently large target is represented if `s > 2^k` and `s ≥ 4k`. -/
theorem eventually_waringCount_pos_of_four_mul {k s : ℕ} (hk : 2≤k) (hs : 2^k<s) (hlocal : 4*k≤s) :
    ∀ᶠ n in atTop, 0 < waringCount k s n := by
  obtain ⟨c,hc,h⟩ := exists_pos_le_waringSingularSeries_re_of_four_mul (by omega : 0<k) hlocal
  exact eventually_waringCount_pos_of_singularSeries hk hs
    ⟨c,hc,.of_forall fun n => (h n).trans (Complex.re_le_norm _)⟩

end AnalyticNumberTheory.AdditiveNumberTheory
