import AnalyticNumberTheory.AnalyticTools.FareyFractions
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Farey dissection of a period

Sort the reduced fractions in the unit interval by their value. Cutting the gap
between each consecutive pair at its mediant assigns one interval to each
fraction. The fractions zero and one receive the two endpoint intervals.
-/

open Finset
open scoped Interval

namespace AnalyticNumberTheory.AnalyticTools

/-- The Farey fractions of order `N` in the unit interval. Rational
normalization in the image identifies different representations. -/
def fareyFractions (N : ℕ) : Finset ℚ :=
  (Icc 1 N).biUnion fun q => (Icc 0 q).image fun a : ℕ => mkRat a q

theorem mem_fareyFractions {N : ℕ} {x : ℚ} :
    x ∈ fareyFractions N ↔ 0 ≤ x ∧ x ≤ 1 ∧ x.den ≤ N := by
  constructor
  · intro hx
    obtain ⟨q,hq,him⟩ := mem_biUnion.mp hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp him
    have hq' := mem_Icc.mp hq
    have ha' := (mem_Icc.mp ha).2
    have hval : mkRat (a : ℤ) q = (a : ℚ) / q := by
      simpa only [Int.cast_natCast] using Rat.mkRat_eq_div (a : ℤ) q
    rw [hval]
    refine ⟨by positivity, (div_le_one (by exact_mod_cast hq'.1 : (0:ℚ)<q)).mpr (by exact_mod_cast ha'), ?_⟩
    rw [← hval, Rat.den_mkRat, ite_eq_right (by omega)]
    exact (Nat.div_le_self ..).trans hq'.2
  · rintro ⟨hx0,hx1,hN⟩
    have hn := Rat.num_nonneg.mpr hx0
    have heq : (x.num.natAbs : ℤ) = x.num := by rw [Int.natCast_natAbs, abs_of_nonneg hn]
    have hbound : x.num.natAbs ≤ x.den := by
      have hdiv : (x.num : ℚ) / x.den ≤ 1 := by rwa [Rat.num_div_den]
      have h := (div_le_one (by exact_mod_cast x.den_pos : (0:ℚ)<x.den)).mp hdiv
      have hh : x.num ≤ (x.den : ℤ) := by exact_mod_cast h
      exact_mod_cast heq ▸ hh
    exact mem_biUnion.mpr ⟨x.den, mem_Icc.mpr ⟨x.den_pos,hN⟩,
      mem_image.mpr ⟨x.num.natAbs, mem_Icc.mpr ⟨Nat.zero_le _,hbound⟩, by rw [heq, Rat.mkRat_self]⟩⟩

/-- Two consecutive members of the finite ordered set have determinant one
in their reduced representations. -/
theorem fareyAdjacent_of_consecutive {N : ℕ} {x y : ℚ} (hx : x ∈ fareyFractions N)
    (hy : y ∈ fareyFractions N) (hxy : x < y)
    (hgap : ∀ z ∈ fareyFractions N, ¬ (x < z ∧ z < y)) :
    FareyAdjacent N x.num x.den y.num y.den := by
  obtain ⟨hx0,_,hxN⟩ := mem_fareyFractions.mp hx
  obtain ⟨_,hy1,hyN⟩ := mem_fareyFractions.mp hy
  obtain ⟨b,r,h⟩ := exists_fareyAdjacent_right x.den_pos hxN x.isCoprime_num_den
  have hred : b.natAbs.Coprime r := by
    have hh := Int.isCoprime_iff_gcd_eq_one.mp h.right_coprime
    simpa [Int.gcd, Nat.Coprime] using hh
  let z : ℚ := ⟨b,r,h.right_pos.ne',hred⟩
  have hcast : (z : ℝ) = b/r := Rat.cast_def _
  have hxz : x < z := by
    have hh : (x : ℝ) < z := by rw [hcast, Rat.cast_def x]; exact h.lt
    exact_mod_cast hh
  have hzy : z ≤ y := by
    by_contra! hlt
    apply h.no_fraction_between y.den_pos hyN y.num
    constructor
    · simpa only [← Rat.cast_def] using (show (x : ℝ) < y by exact_mod_cast hxy)
    · have hh : (y : ℝ) < z := by exact_mod_cast hlt
      rwa [Rat.cast_def y, hcast] at hh
  have hmem : z ∈ fareyFractions N :=
    mem_fareyFractions.mpr ⟨hx0.trans hxz.le, hzy.trans hy1, h.right_le⟩
  obtain rfl : z = y := hzy.eq_of_not_lt (fun hz => hgap z hmem ⟨hxz,hz⟩)
  exact h

/-- The mediant between the reduced forms of two rational numbers. -/
noncomputable def fareyMediant (x y : ℚ) : ℝ := ((x.num : ℝ) + y.num) / ((x.den : ℝ) + y.den)

/-- Farey fractions in increasing order, with explicit finite indices. -/
noncomputable def fareyPoint (N : ℕ) : Fin (fareyFractions N).card ↪o ℚ :=
  (fareyFractions N).orderEmbOfFin rfl

theorem fareyPoint_mem (N : ℕ) (i : Fin (fareyFractions N).card) :
    fareyPoint N i ∈ fareyFractions N := (fareyFractions N).orderEmbOfFin_mem rfl i

theorem fareyPoint_adjacent {N i : ℕ} (hi : i+1 < (fareyFractions N).card) :
    let x := fareyPoint N ⟨i, by omega⟩
    let y := fareyPoint N ⟨i+1, hi⟩
    FareyAdjacent N x.num x.den y.num y.den := by
  intro x y
  apply fareyAdjacent_of_consecutive (fareyPoint_mem ..) (fareyPoint_mem ..)
    ((fareyPoint N).strictMono (by show i < i+1; omega))
  intro z hz hbetween
  obtain ⟨j,hj⟩ := (fareyFractions N).orderIsoOfFin rfl |>.surjective ⟨z,hz⟩
  have hzj : fareyPoint N j = z := congrArg Subtype.val hj
  rw [← hzj] at hbetween
  have ha : (⟨i,by omega⟩ : Fin (fareyFractions N).card) < j :=
    (fareyPoint N).lt_iff_lt.mp hbetween.1
  have hb : j < (⟨i+1,hi⟩ : Fin (fareyFractions N).card) :=
    (fareyPoint N).lt_iff_lt.mp hbetween.2
  change i < j.val at ha
  change j.val < i+1 at hb
  omega

theorem zero_mem_fareyFractions {N : ℕ} (hN : 0 < N) : 0 ∈ fareyFractions N :=
  mem_fareyFractions.mpr (by simp; exact hN)

theorem one_mem_fareyFractions {N : ℕ} (hN : 0 < N) : 1 ∈ fareyFractions N :=
  mem_fareyFractions.mpr (by simp; exact hN)

theorem two_le_card_fareyFractions {N : ℕ} (hN : 0 < N) : 2 ≤ (fareyFractions N).card :=
  one_lt_card.mpr ⟨0,zero_mem_fareyFractions hN,1,one_mem_fareyFractions hN,zero_ne_one⟩

theorem fareyPoint_first {N : ℕ} (hN : 0 < N) :
    fareyPoint N ⟨0, by have := two_le_card_fareyFractions hN; omega⟩ = 0 := by
  change (fareyFractions N).orderEmbOfFin _ _ = _
  rw [orderEmbOfFin_zero rfl (by have := two_le_card_fareyFractions hN; omega)]
  apply le_antisymm (min'_le _ _ (zero_mem_fareyFractions hN))
  exact (mem_fareyFractions.mp (min'_mem ..)).1

theorem fareyPoint_last {N : ℕ} (hN : 0 < N) :
    fareyPoint N ⟨(fareyFractions N).card-1, by have := two_le_card_fareyFractions hN; omega⟩ = 1 := by
  change (fareyFractions N).orderEmbOfFin _ _ = _
  rw [orderEmbOfFin_last rfl (by have := two_le_card_fareyFractions hN; omega)]
  apply le_antisymm (mem_fareyFractions.mp (max'_mem ..)).2.1
  exact le_max' _ _ (one_mem_fareyFractions hN)

/-- The cuts are zero, the consecutive mediants from left to right, and one. -/
noncomputable def fareyCut (N i : ℕ) : ℝ :=
  if i = 0 then 0
  else if hi : i < (fareyFractions N).card then
    fareyMediant (fareyPoint N ⟨i-1, by omega⟩) (fareyPoint N ⟨i,hi⟩)
  else 1

@[simp] theorem fareyCut_zero (N : ℕ) : fareyCut N 0 = 0 := by simp [fareyCut]

@[simp] theorem fareyCut_card {N : ℕ} (hN : 0 < N) :
    fareyCut N (fareyFractions N).card = 1 := by
  have hh := two_le_card_fareyFractions hN
  simp [fareyCut, show (fareyFractions N).card ≠ 0 by omega]

theorem fareyCut_succ {N i : ℕ} (hi : i+1 < (fareyFractions N).card) :
    fareyCut N (i+1) = fareyMediant (fareyPoint N ⟨i,by omega⟩) (fareyPoint N ⟨i+1,hi⟩) := by
  simp [fareyCut, hi]

/-- Exact right-hand width of the arc about the fraction at index `i`. -/
theorem fareyCut_sub_point {N i : ℕ} (hi : i+1 < (fareyFractions N).card) :
    let x := fareyPoint N ⟨i,by omega⟩
    let y := fareyPoint N ⟨i+1,hi⟩
    fareyCut N (i+1) - (x : ℝ) = 1 / ((x.den : ℝ)*(x.den+y.den)) := by
  intro x y
  rw [fareyCut_succ hi, Rat.cast_def x]
  exact (fareyPoint_adjacent hi).mediant_sub_left

/-- Exact left-hand width of the arc about the fraction at index `i+1`. -/
theorem fareyPoint_sub_cut {N i : ℕ} (hi : i+1 < (fareyFractions N).card) :
    let x := fareyPoint N ⟨i,by omega⟩
    let y := fareyPoint N ⟨i+1,hi⟩
    (y : ℝ) - fareyCut N (i+1) = 1 / ((y.den : ℝ)*(x.den+y.den)) := by
  intro x y
  rw [fareyCut_succ hi, Rat.cast_def y]
  exact (fareyPoint_adjacent hi).right_sub_mediant

/-- Summing integrals over the Farey arcs recovers the integral over a
period. The fractions zero and one each contribute a one-sided arc. -/
theorem sum_integral_fareyCut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} (hN : 0 < N) {f : ℝ → E} (hf : Continuous f) :
    ∑ i ∈ range (fareyFractions N).card, (∫ t in fareyCut N i..fareyCut N (i+1), f t) =
      ∫ t in (0 : ℝ)..1, f t := by
  have h (n : ℕ) : ∑ i ∈ range n, (∫ t in fareyCut N i..fareyCut N (i+1), f t) =
      ∫ t in (0 : ℝ)..fareyCut N n, f t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)
  simpa [hN] using h (fareyFractions N).card

private theorem mkRat_num_den {a q : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (mkRat a q).num = (a : ℤ) ∧ (mkRat a q).den = q := by
  simp [Rat.num_mkRat, Rat.den_mkRat, hq.ne', ha.symm.gcd_eq_one]

/-- Regroup an arbitrary sum over a Farey sequence by reduced denominators.
The endpoint one is counted separately, and zero occurs as `0/1`. -/
theorem sum_fareyFractions_eq {E : Type*} [AddCommMonoid E] {N : ℕ} (hN : 0 < N) (f : ℚ → E) :
    ∑ z ∈ fareyFractions N, f z = f 1 +
      ∑ q ∈ Icc 1 N, ∑ a ∈ (range q).filter (fun a => a.Coprime q), f (mkRat a q) := by
  let F := fareyFractions N
  let S := (Icc 1 N).sigma fun q => (range q).filter (fun a => a.Coprime q)
  have hsum : ∑ p ∈ S, f (mkRat p.2 p.1) = ∑ z ∈ F.erase 1, f z := by
    refine sum_bij (fun p _ => mkRat p.2 p.1) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨q,a⟩ hp
      obtain ⟨hq,ha⟩ := mem_sigma.mp hp
      obtain ⟨hal,hcop⟩ := mem_filter.mp ha
      have haq := mem_range.mp hal
      have hq' := mem_Icc.mp hq
      have hval : mkRat (a : ℤ) q = (a : ℚ)/q := by simpa only [Int.cast_natCast] using Rat.mkRat_eq_div (a : ℤ) q
      apply mem_erase.mpr
      refine ⟨?_,mem_biUnion.mpr ⟨q,hq,mem_image.mpr ⟨a,mem_Icc.mpr ⟨by omega,haq.le⟩,rfl⟩⟩⟩
      rw [hval]
      exact ((div_lt_one (by exact_mod_cast hq'.1 : (0:ℚ)<q)).mpr (by exact_mod_cast haq)).ne
    · rintro ⟨q,a⟩ hp ⟨r,b⟩ hp' h
      obtain ⟨hq,ha⟩ := mem_sigma.mp hp
      obtain ⟨hr,hb⟩ := mem_sigma.mp hp'
      obtain ⟨han,had⟩ := mkRat_num_den (mem_Icc.mp hq).1 (mem_filter.mp ha).2
      obtain ⟨hbn,hbd⟩ := mkRat_num_den (mem_Icc.mp hr).1 (mem_filter.mp hb).2
      change mkRat (a : ℤ) q = mkRat (b : ℤ) r at h
      have hd : q = r := by simpa only [had,hbd] using congrArg Rat.den h
      have hn : a = b := by exact_mod_cast (han.symm.trans ((congrArg Rat.num h).trans hbn))
      cases hd; cases hn; rfl
    · intro z hz
      obtain ⟨hz1,hF⟩ := mem_erase.mp hz
      obtain ⟨hz0,hzle,hden⟩ := mem_fareyFractions.mp hF
      have he : (z.num.natAbs : ℤ) = z.num := by rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hz0)]
      have hdiv : (z.num : ℚ) / z.den < 1 := by rw [Rat.num_div_den]; exact lt_of_le_of_ne hzle hz1
      have hh : z.num < (z.den : ℤ) := by exact_mod_cast (div_lt_one (by exact_mod_cast z.den_pos : (0:ℚ)<z.den)).mp hdiv
      have hn : z.num.natAbs < z.den := by exact_mod_cast he ▸ hh
      exact ⟨⟨z.den,z.num.natAbs⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨z.den_pos,hden⟩,
        mem_filter.mpr ⟨mem_range.mpr hn,z.reduced⟩⟩, by dsimp; rw [he,Rat.mkRat_self]⟩
  rw [sum_sigma] at hsum
  exact (add_sum_erase F f (one_mem_fareyFractions hN)).symm.trans (congrArg (f 1 + ·) hsum.symm)

/-- Each side of an interior Farey arc has width between `1/(2qN)`
and `1/(q(N+1))` for the denominator `q` at its centre. -/
theorem FareyAdjacent.width_bounds {N q r : ℕ} {a b : ℤ} (h : FareyAdjacent N a q b r) :
    1 / ((q : ℝ)*(2*N)) ≤ 1 / ((q : ℝ)*(q+r)) ∧
    1 / ((q : ℝ)*(q+r)) ≤ 1 / ((q : ℝ)*(N+1)) := by
  have hq : (0:ℝ) < q := Nat.cast_pos.mpr h.left_pos
  have hr : (0:ℝ) < r := Nat.cast_pos.mpr h.right_pos
  have hsum : (N : ℝ)+1 ≤ q+r := by exact_mod_cast h.sum_gt
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hq.le
    linarith [show (q:ℝ) ≤ N by exact_mod_cast h.left_le, show (r:ℝ) ≤ N by exact_mod_cast h.right_le]
  · exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsum hq.le)

/-- The position of a rational in the Farey ordering. -/
noncomputable def fareyIndex (N : ℕ) (z : ℚ) : ℕ := (fareyFractions N).sort.idxOf z

theorem fareyIndex_point (N : ℕ) (i : Fin (fareyFractions N).card) :
    fareyIndex N (fareyPoint N i) = i := by
  let e := (fareyFractions N).orderIsoOfFin rfl
  change (fareyFractions N).sort.idxOf (e i).val = i.val
  rw [← orderIsoOfFin_symm_apply _ rfl (e i)]
  exact congrArg Fin.val (e.symm_apply_apply i)

/-- The translated left endpoint of the Farey interval at `z`. -/
noncomputable def fareyLeft (N : ℕ) (z : ℚ) : ℝ := fareyCut N (fareyIndex N z) - z

/-- The translated right endpoint of the Farey interval at `z`. -/
noncomputable def fareyRight (N : ℕ) (z : ℚ) : ℝ := fareyCut N (fareyIndex N z + 1) - z

/-- The integral dissection with each interval translated to coordinates
relative to its rational centre. -/
theorem integral_eq_sum_fareyFractions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} (hN : 0 < N) {f : ℝ → E} (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) = ∑ z ∈ fareyFractions N, ∫ u in fareyLeft N z..fareyRight N z, f (z+u) := by
  rw [← sum_integral_fareyCut hN hf]
  refine sum_bij (fun i hi => fareyPoint N ⟨i,mem_range.mp hi⟩)
    (fun _ _ => fareyPoint_mem ..) ?_ ?_ ?_
  · intro i hi j hj heq
    exact congrArg Fin.val ((fareyPoint N).injective heq)
  · intro z hz
    obtain ⟨i,hi⟩ := (fareyFractions N).orderIsoOfFin rfl |>.surjective ⟨z,hz⟩
    exact ⟨i.val,mem_range.mpr i.isLt,congrArg Subtype.val hi⟩
  · intro i hi
    simp only [fareyLeft, fareyRight, fareyIndex_point, intervalIntegral.integral_comp_add_left,
      add_sub_cancel]

private theorem widths_at_index {N i : ℕ} (hi : i+1 < (fareyFractions N).card) :
    let x := fareyPoint N ⟨i,by omega⟩
    let y := fareyPoint N ⟨i+1,hi⟩
    (1 / ((x.den : ℝ)*(2*N)) ≤ fareyRight N x ∧
      fareyRight N x ≤ 1 / ((x.den : ℝ)*(N+1))) ∧
    (1 / ((y.den : ℝ)*(2*N)) ≤ -fareyLeft N y ∧
      -fareyLeft N y ≤ 1 / ((y.den : ℝ)*(N+1))) := by
  intro x y
  have h := fareyPoint_adjacent hi
  change FareyAdjacent N x.num x.den y.num y.den at h
  have rev : FareyAdjacent N (-y.num) y.den (-x.num) x.den :=
    ⟨h.right_pos,h.right_le,h.left_pos,h.left_le,by linarith only [h.determinant],by linarith [h.sum_gt]⟩
  have hx : fareyRight N x = 1/((x.den : ℝ)*(x.den+y.den)) := by
    simp only [fareyRight, x, fareyIndex_point]
    exact fareyCut_sub_point hi
  have hy : -fareyLeft N y = 1/((y.den : ℝ)*(x.den+y.den)) := by
    simp only [fareyLeft, y, fareyIndex_point, neg_sub]
    exact fareyPoint_sub_cut hi
  rw [hx,hy]
  exact ⟨h.width_bounds, by simpa only [add_comm (y.den:ℝ)] using rev.width_bounds⟩

/-- Interior Farey fractions have two nonexceptional endpoints. At zero the
left width is zero, and at one the right width is zero. -/
theorem farey_arc_width_bounds {N : ℕ} (hN : 0 < N) {z : ℚ} (hz : z ∈ fareyFractions N) :
    (if z = 0 then fareyLeft N z = 0 else
      1/((z.den:ℝ)*(2*N)) ≤ -fareyLeft N z ∧ -fareyLeft N z ≤ 1/((z.den:ℝ)*(N+1))) ∧
    (if z = 1 then fareyRight N z = 0 else
      1/((z.den:ℝ)*(2*N)) ≤ fareyRight N z ∧ fareyRight N z ≤ 1/((z.den:ℝ)*(N+1))) := by
  let m := (fareyFractions N).card
  have hm : 2 ≤ m := two_le_card_fareyFractions hN
  obtain ⟨i,hi⟩ := (fareyFractions N).orderIsoOfFin rfl |>.surjective ⟨z,hz⟩
  have hi' : fareyPoint N i = z := congrArg Subtype.val hi
  have hi0 : i.val = 0 ↔ z = 0 := by
    rw [← hi', ← fareyPoint_first hN, (fareyPoint N).injective.eq_iff]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hi1 : i.val = m-1 ↔ z = 1 := by
    rw [← hi', ← fareyPoint_last hN, (fareyPoint N).injective.eq_iff]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  constructor
  · split_ifs with he
    · rw [fareyLeft, ← hi', fareyIndex_point, hi0.mpr he, fareyCut_zero, hi', he]; simp
    · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => he (hi0.mp h))
      have hlt : j+1 < (fareyFractions N).card := by have := i.isLt; omega
      have hpt : fareyPoint N ⟨j+1,hlt⟩ = z := by
        rw [← hi']; congr 1; exact Fin.ext hj.symm
      exact hpt ▸ (widths_at_index hlt).2
  · split_ifs with he
    · have hlast : i.val+1 = m := by have := hi1.mpr he; omega
      rw [fareyRight, ← hi', fareyIndex_point, hlast, fareyCut_card hN, hi', he]; simp
    · have hlt : i.val+1 < (fareyFractions N).card := by
        have : i.val ≠ m-1 := fun h => he (hi1.mp h)
        have hi_lt : i.val < m := i.isLt
        omega
      exact hi' ▸ (widths_at_index hlt).1

/-- Translating the arc at one to the left of zero makes a complete arc
at every reduced residue of the period. -/
noncomputable def fareyFullLeft (N : ℕ) (z : ℚ) : ℝ :=
  if z = 0 then fareyLeft N 1 else fareyLeft N z

/-- The two widths of a complete Farey arc of denominator `q` both lie
between `1/(2qN)` and `1/(q(N+1))`. -/
theorem fareyFull_width_bounds {N : ℕ} (hN : 0 < N) {z : ℚ} (hz : z ∈ fareyFractions N)
    (hz1 : z ≠ 1) :
    (1/((z.den:ℝ)*(2*N)) ≤ -fareyFullLeft N z ∧ -fareyFullLeft N z ≤ 1/((z.den:ℝ)*(N+1))) ∧
    (1/((z.den:ℝ)*(2*N)) ≤ fareyRight N z ∧ fareyRight N z ≤ 1/((z.den:ℝ)*(N+1))) := by
  obtain ⟨hl,hr⟩ := farey_arc_width_bounds hN hz
  refine ⟨?_,by simpa [hz1] using hr⟩
  by_cases h : z = 0
  · subst z
    simpa [fareyFullLeft] using (farey_arc_width_bounds hN (one_mem_fareyFractions hN)).1
  · simpa [fareyFullLeft,h] using hl

/-- A period integral is the sum of full Farey arcs indexed by denominator
and reduced residue. Periodicity joins the left and right ends of the period
into the single arc indexed by `0/1`. -/
theorem integral_eq_sum_fareyArcs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} (hN : 0 < N) {f : ℝ → E} (hf : Continuous f)
    (hper : Function.Periodic f 1) :
    (∫ t in (0:ℝ)..1, f t) = ∑ q ∈ Icc 1 N, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      ∫ u in fareyFullLeft N (mkRat a q)..fareyRight N (mkRat a q), f (((mkRat a q : ℚ):ℝ)+u) := by
  let S := fareyFractions N
  let F (z : ℚ) := ∫ u in fareyLeft N z..fareyRight N z, f (z+u)
  let G (z : ℚ) := ∫ u in fareyFullLeft N z..fareyRight N z, f (z+u)
  have h1 : 1 ∈ S := one_mem_fareyFractions hN
  have h0 : 0 ∈ S.erase 1 := mem_erase.mpr ⟨zero_ne_one,zero_mem_fareyFractions hN⟩
  have he : F 1 + F 0 = G 0 := by
    have hl : fareyLeft N 0 = 0 := by simpa using (farey_arc_width_bounds hN (zero_mem_fareyFractions hN)).1
    have hr : fareyRight N 1 = 0 := by simpa using (farey_arc_width_bounds hN (one_mem_fareyFractions hN)).2
    have hp (t : ℝ) : f (1+t) = f t := by simpa [add_comm] using hper t
    simpa only [F,G,fareyFullLeft,if_pos rfl,if_true,hl,hr,Rat.cast_one,Rat.cast_zero,zero_add,hp] using
      (intervalIntegral.integral_add_adjacent_intervals (f := f) (a := fareyLeft N 1) (b := 0)
        (c := fareyRight N 0) (hf.intervalIntegrable ..) (hf.intervalIntegrable ..))
  have hrest : ∑ z ∈ (S.erase 1).erase 0, F z = ∑ z ∈ (S.erase 1).erase 0, G z := by
    apply sum_congr rfl
    intro z hz
    simp only [F,G,fareyFullLeft,if_neg (ne_of_mem_erase hz)]
  have heq : ∑ z ∈ S, F z = ∑ z ∈ S.erase 1, G z := by
    rw [← add_sum_erase S F h1, ← add_sum_erase (S.erase 1) F h0,
      ← add_sum_erase (S.erase 1) G h0, ← add_assoc, he, hrest]
  rw [integral_eq_sum_fareyFractions hN hf, heq]
  apply add_left_cancel (a := G 1)
  exact (add_sum_erase S G h1).trans (sum_fareyFractions_eq hN G)


/-- Endpoint bounds for the complete arc at a reduced residue, stated
directly in terms of the denominator indexing the dissection. -/
theorem fareyReduced_width_bounds {N k a : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (ha : a < k) (hcop : a.Coprime k) :
    let z := mkRat (a : ℤ) k
    (1/((k:ℝ)*(2*N)) ≤ -fareyFullLeft N z ∧ -fareyFullLeft N z ≤ 1/((k:ℝ)*N)) ∧
    (1/((k:ℝ)*(2*N)) ≤ fareyRight N z ∧ fareyRight N z ≤ 1/((k:ℝ)*N)) := by
  intro z
  have hN := hk.trans_le hkN
  have hk' : (0:ℚ) < k := by exact_mod_cast hk
  have hv : z = (a:ℚ)/k := by simpa [z] using Rat.mkRat_eq_div (a:ℤ) k
  have hl : z < 1 := by rw [hv,div_lt_one hk']; exact_mod_cast ha
  have hd : z.den = k := (mkRat_num_den hk hcop).2
  have hm : z ∈ fareyFractions N := mem_fareyFractions.mpr
    ⟨by rw [hv]; positivity, hl.le, hd ▸ hkN⟩
  have H := fareyFull_width_bounds hN hm hl.ne
  rw [hd] at H
  have h : 1/((k:ℝ)*(N+1)) ≤ 1/((k:ℝ)*N) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    linarith
  exact ⟨⟨H.1.1,H.1.2.trans h⟩, ⟨H.2.1,H.2.2.trans h⟩⟩

/-- The lengths of the complete Farey arcs add to one. -/
theorem sum_fareyArc_widths {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Icc 1 N, ∑ a ∈ (range k).filter (fun a => a.Coprime k),
      (fareyRight N (mkRat a k) - fareyFullLeft N (mkRat a k)) = 1 := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] using
    (integral_eq_sum_fareyArcs hN (f := fun _ : ℝ => (1 : ℝ)) continuous_const (fun _ => rfl)).symm

end AnalyticNumberTheory.AnalyticTools
