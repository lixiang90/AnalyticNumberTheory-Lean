import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola

/-!
# The Gauss circle problem

Count integer lattice points in the disk of squared radius `x` by horizontal slices
or by representations as a sum of two squares. Comparing the slices with the area of
the disk gives `|gaussCircleCount x - π * x| ≤ 5 * √x` for `1 ≤ x`.
-/

open scoped BigOperators
open Filter Topology MeasureTheory

namespace AnalyticNumberTheory.DivisorProblems

section GaussCircleElementary

theorem int_natAbs_sq_real (a : ℤ) : (a.natAbs : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]

theorem int_abs_le_of_natAbs_le {a : ℤ} {n : ℕ} (h : a.natAbs ≤ n) :
    -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ) := by
  have h1 : |a| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  exact abs_le.mp h1

theorem natAbs_le_of_abs_le {a : ℤ} {n : ℕ} (h : -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ)) :
    a.natAbs ≤ n := by
  have h1 : |a| ≤ (n : ℤ) := abs_le.mpr h
  rw [← Int.natCast_natAbs] at h1
  exact_mod_cast h1

/-- Finite set of lattice points `(a, b) ∈ ℤ × ℤ` satisfying `a ^ 2 + b ^ 2 ≤ x`. -/
noncomputable def gaussCircleFinset (x : ℝ) : Finset (ℤ × ℤ) :=
  if _hx : 0 ≤ x then
    let M : ℤ := (⌊Real.sqrt x⌋₊ : ℤ)
    (Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M).filter
      (fun p => (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ x)
  else ∅

/-- Membership criterion for `gaussCircleFinset`. -/
theorem mem_gaussCircleFinset {x : ℝ} {p : ℤ × ℤ} :
    p ∈ gaussCircleFinset x ↔ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ x := by
  unfold gaussCircleFinset
  split_ifs with hx
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
    intro hp
    have hp1_sq : (p.1.natAbs : ℝ) ^ 2 ≤ x := by
      have hnonneg : 0 ≤ (p.2 : ℝ) ^ 2 := sq_nonneg _
      have hcast := int_natAbs_sq_real p.1
      linarith
    have hp2_sq : (p.2.natAbs : ℝ) ^ 2 ≤ x := by
      have hnonneg : 0 ≤ (p.1 : ℝ) ^ 2 := sq_nonneg _
      have hcast := int_natAbs_sq_real p.2
      linarith
    exact ⟨int_abs_le_of_natAbs_le (Nat.le_floor (Real.le_sqrt_of_sq_le hp1_sq)),
      int_abs_le_of_natAbs_le (Nat.le_floor (Real.le_sqrt_of_sq_le hp2_sq))⟩
  · constructor
    · intro h; simp at h
    · intro hp
      have hnonneg : 0 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      exact (hx (hnonneg.trans hp)).elim

/-- Lattice point count `R₂(x) = #{(a, b) ∈ ℤ × ℤ : a ^ 2 + b ^ 2 ≤ x}` in the disk of
squared radius `x`. -/
noncomputable def gaussCircleCount (x : ℝ) : ℝ :=
  ((gaussCircleFinset x).card : ℝ)

/-- Gauss circle error term `P(x) = R₂(x) - π x`. -/
noncomputable def gaussCircleError (x : ℝ) : ℝ :=
  gaussCircleCount x - Real.pi * x

/-- Set of representations `(a, b) ∈ ℤ × ℤ` of `n` as a sum of two squares. -/
def repTwoSquaresFinset (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))

/-- Number of ordered representations of `n` as a sum of two integer squares. -/
def repTwoSquares (n : ℕ) : ℕ := (repTwoSquaresFinset n).card

theorem mem_repTwoSquaresFinset {n : ℕ} {p : ℤ × ℤ} :
    p ∈ repTwoSquaresFinset n ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
  unfold repTwoSquaresFinset
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hp
  have h1sq : p.1 ^ 2 ≤ (n : ℤ) := by linarith [sq_nonneg p.2]
  have h2sq : p.2 ^ 2 ≤ (n : ℤ) := by linarith [sq_nonneg p.1]
  have hn1 : p.1.natAbs ≤ n := by
    have hmul : p.1.natAbs * p.1.natAbs ≤ n := by
      zify
      simpa [sq, Int.natAbs_sq] using h1sq
    exact (Nat.le_mul_self p.1.natAbs).trans hmul
  have hn2 : p.2.natAbs ≤ n := by
    have hmul : p.2.natAbs * p.2.natAbs ≤ n := by
      zify
      simpa [sq, Int.natAbs_sq] using h2sq
    exact (Nat.le_mul_self p.2.natAbs).trans hmul
  exact ⟨int_abs_le_of_natAbs_le hn1, int_abs_le_of_natAbs_le hn2⟩

theorem repTwoSquaresFinset_card (n : ℕ) : (repTwoSquaresFinset n).card = repTwoSquares n := rfl

/-- `repTwoSquares 0 = 1`. -/
@[simp] theorem repTwoSquares_zero : repTwoSquares 0 = 1 := by
  rw [← repTwoSquaresFinset_card]
  have hsub : repTwoSquaresFinset 0 = {(0, 0)} := by
    ext p
    rw [mem_repTwoSquaresFinset, Finset.mem_singleton, Prod.ext_iff]
    constructor
    · intro h
      norm_cast at h
      have h1 : p.1 ^ 2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      have h2 : p.2 ^ 2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      exact ⟨sq_eq_zero_iff.mp h1, sq_eq_zero_iff.mp h2⟩
    · rcases p with ⟨x, y⟩
      rintro ⟨rfl, rfl⟩
      norm_num
  rw [hsub, Finset.card_singleton]

/-- Partition of `gaussCircleCount x` by the radius squared `n = a ^ 2 + b ^ 2`:
`R₂(x) = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, r₂(n)` for `0 ≤ x`. -/
theorem gaussCircleCount_eq_sum_repTwoSquares {x : ℝ} (hx : 0 ≤ x) :
    gaussCircleCount x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (repTwoSquares n : ℝ) := by
  classical
  have hpart :
      gaussCircleFinset x = (Finset.Icc 0 ⌊x⌋₊).biUnion repTwoSquaresFinset := by
    ext p
    rw [mem_gaussCircleFinset, Finset.mem_biUnion]
    constructor
    · intro hp
      let n : ℕ := (p.1 ^ 2 + p.2 ^ 2).natAbs
      have hn_cast : (n : ℤ) = p.1 ^ 2 + p.2 ^ 2 :=
        Int.natAbs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have hn_real : (n : ℝ) = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by exact_mod_cast hn_cast
      refine ⟨n, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (hn_real ▸ hp)⟩, ?_⟩
      exact mem_repTwoSquaresFinset.mpr hn_cast.symm
    · rintro ⟨n, hn, hp⟩
      rw [mem_repTwoSquaresFinset] at hp
      have hn_le : (n : ℝ) ≤ x :=
        (Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hn).2
      have hcast : (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast hp
      linarith
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.Icc 0 ⌊x⌋₊) : Set ℕ) repTwoSquaresFinset := by
    intro m _ n _ hmn
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hpm hpn
    rw [mem_repTwoSquaresFinset] at hpm hpn
    exact hmn (by exact_mod_cast hpm.symm.trans hpn)
  rw [gaussCircleCount, hpart, Finset.card_biUnion hdisj]
  push_cast
  rfl

/-- Alternative form starting at `n = 1`: `R₂(x) = 1 + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, r₂(n)`. -/
theorem gaussCircleCount_eq_one_add_sum_repTwoSquares {x : ℝ} (hx : 0 ≤ x) :
    gaussCircleCount x = 1 + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (repTwoSquares n : ℝ) := by
  rw [gaussCircleCount_eq_sum_repTwoSquares hx]
  have hsplit : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp), repTwoSquares_zero]
  norm_num

/-- Lattice points in the disk of squared radius `x` whose first coordinate
has absolute value at most `M`. -/
noncomputable def gaussCircleStrip (x : ℝ) (M : ℕ) : Finset (ℤ × ℤ) :=
  (gaussCircleFinset x).filter (fun p => p.1.natAbs ≤ M)

/-- Slice count in a vertical strip of the disk. -/
theorem gaussCircleStrip_card_eq_sum_slice {x : ℝ} (hx : 0≤x) {M : ℕ} (hM : (M:ℝ)≤Real.sqrt x) :
    ((gaussCircleStrip x M).card:ℝ) =
      ∑ a ∈ Finset.Icc (-(M:ℤ)) (M:ℤ), (2*(⌊Real.sqrt (x-(a:ℝ)^2)⌋₊:ℝ)+1) := by
  classical
  let S (a : ℤ) : Finset (ℤ × ℤ) :=
    let N : ℤ := (⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ : ℤ)
    (Finset.Icc (-N) N).map ⟨fun b => (a, b), fun _ _ h => (Prod.ext_iff.mp h).2⟩
  have ha_sq_le : ∀ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (a : ℝ) ^ 2 ≤ x := by
    intro a ha
    have habs : a.natAbs ≤ M := natAbs_le_of_abs_le (Finset.mem_Icc.mp ha)
    have hsqrt : (a.natAbs : ℝ) ≤ Real.sqrt x :=
      (Nat.cast_le.mpr habs).trans hM
    have hsq := sq_le_sq' (by linarith [Real.sqrt_nonneg x, (Nat.cast_nonneg a.natAbs : (0 : ℝ) ≤ a.natAbs)]) hsqrt
    rw [Real.sq_sqrt hx] at hsq
    have hcast := int_natAbs_sq_real a
    linarith
  have hpart : gaussCircleStrip x M = (Finset.Icc (-(M : ℤ)) (M : ℤ)).biUnion S := by
    ext p
    simp only [gaussCircleStrip,Finset.mem_filter,mem_gaussCircleFinset,Finset.mem_biUnion]
    constructor
    · rintro ⟨hp,ha_abs⟩
      have ha_mem : p.1 ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
        Finset.mem_Icc.mpr (int_abs_le_of_natAbs_le ha_abs)
      refine ⟨p.1, ha_mem, ?_⟩
      simp only [S, Finset.mem_map, Finset.mem_Icc]
      refine ⟨p.2, ?_, rfl⟩
      have hb_sq : (p.2.natAbs : ℝ) ^ 2 ≤ x - (p.1 : ℝ) ^ 2 := by
        have hcast := int_natAbs_sq_real p.2
        linarith
      have hb_abs : p.2.natAbs ≤ ⌊Real.sqrt (x - (p.1 : ℝ) ^ 2)⌋₊ :=
        Nat.le_floor (Real.le_sqrt_of_sq_le hb_sq)
      exact int_abs_le_of_natAbs_le hb_abs
    · rintro ⟨a, ha, hp⟩
      simp only [S, Finset.mem_map, Finset.mem_Icc] at hp
      rcases hp with ⟨b, hb, hp_eq⟩
      have hdiff : 0 ≤ x - (a : ℝ) ^ 2 := sub_nonneg.mpr (ha_sq_le a ha)
      have hb_abs : (b.natAbs : ℝ) ≤ (⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ : ℝ) :=
        Nat.cast_le.mpr (natAbs_le_of_abs_le hb)
      have hb_sqrt : (b.natAbs : ℝ) ≤ Real.sqrt (x - (a : ℝ) ^ 2) :=
        hb_abs.trans (Nat.floor_le (Real.sqrt_nonneg _))
      have hb_sq : (b.natAbs : ℝ) ^ 2 ≤ x - (a : ℝ) ^ 2 := by
        have h := sq_le_sq' (by linarith [Real.sqrt_nonneg (x - (a : ℝ) ^ 2), (Nat.cast_nonneg b.natAbs : (0 : ℝ) ≤ b.natAbs)]) hb_sqrt
        simpa [Real.sq_sqrt hdiff] using h
      have hcast := int_natAbs_sq_real b
      rw [← hp_eq]
      refine ⟨?_,natAbs_le_of_abs_le (Finset.mem_Icc.mp ha)⟩
      change (a : ℝ) ^ 2 + (b : ℝ) ^ 2 ≤ x
      linarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc (-(M : ℤ)) (M : ℤ)) : Set ℤ) S := by
    intro a₁ _ a₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S, Finset.mem_map] at hp1 hp2
    rcases hp1 with ⟨_, _, rfl⟩
    rcases hp2 with ⟨_, _, h2⟩
    exact hne (Prod.ext_iff.mp h2).1.symm
  rw [hpart, Finset.card_biUnion hdisj]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [S, Finset.card_map, Int.card_Icc]
  have hcard :
      ((⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ : ℤ) + 1 -
        (-(⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ : ℤ))).toNat =
        2 * ⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ + 1 := by
    omega
  rw [hcard]
  push_cast
  ring

/-- Vertical slice decomposition of `gaussCircleCount x`:
`R₂(x) = ∑ a ∈ Finset.Icc (-(⌊√x⌋₊ : ℤ)) ⌊√x⌋₊, (2 * ⌊√(x - a ^ 2)⌋₊ + 1)` for `0 ≤ x`. -/
theorem gaussCircleCount_eq_sum_slice {x : ℝ} (hx : 0 ≤ x) :
    let M : ℕ := ⌊Real.sqrt x⌋₊
    gaussCircleCount x =
      ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (2 * (⌊Real.sqrt (x - (a : ℝ) ^ 2)⌋₊ : ℝ) + 1) := by
  intro M
  have he : gaussCircleFinset x = gaussCircleStrip x M := by
    ext p
    simp only [gaussCircleStrip, Finset.mem_filter, mem_gaussCircleFinset, iff_self_and]
    intro hp
    apply Nat.le_floor
    apply Real.le_sqrt_of_sq_le
    rw [int_natAbs_sq_real]
    linarith [sq_nonneg (p.2:ℝ)]
  change ((gaussCircleFinset x).card:ℝ)=_
  rw [he]; exact gaussCircleStrip_card_eq_sum_slice hx (Nat.floor_le (Real.sqrt_nonneg _))

/-- Semicircle integral evaluation: `∫ t in (0 : ℝ)..R, √(R ^ 2 - t ^ 2) = π * R ^ 2 / 4`
for `0 ≤ R`. -/
theorem integral_sqrt_sq_sub_sq {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, Real.sqrt (R ^ 2 - t ^ 2) = Real.pi * R ^ 2 / 4 := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp
  have hint_full :
      ∫ t in (-R)..R, Real.sqrt (R ^ 2 - t ^ 2) = Real.pi * R ^ 2 / 2 := by
    have hcomp :=
      intervalIntegral.integral_comp_mul_left
        (fun t : ℝ => Real.sqrt (R ^ 2 - t ^ 2)) hRpos.ne' (a := (-1 : ℝ)) (b := 1)
    simp only [mul_neg, mul_one, smul_eq_mul] at hcomp
    have hcomp_mul :
        ∫ t in (-R)..R, Real.sqrt (R ^ 2 - t ^ 2) =
          R * ∫ u in (-1 : ℝ)..1, Real.sqrt (R ^ 2 - (R * u) ^ 2) := by
      have hr : R ≠ 0 := hRpos.ne'
      rw [hcomp]
      field_simp [hr]
    rw [hcomp_mul]
    have hfun :
        (fun u : ℝ => Real.sqrt (R ^ 2 - (R * u) ^ 2)) =
          (fun u : ℝ => R * Real.sqrt (1 - u ^ 2)) := by
      ext u
      have hsq : R ^ 2 - (R * u) ^ 2 = R ^ 2 * (1 - u ^ 2) := by ring
      rw [hsq, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]
    rw [hfun, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
    ring
  have heven :
      ∫ t in (-R)..0, Real.sqrt (R ^ 2 - t ^ 2) =
        ∫ t in (0 : ℝ)..R, Real.sqrt (R ^ 2 - t ^ 2) := by
    have hneg := intervalIntegral.integral_comp_neg
      (fun t : ℝ => Real.sqrt (R ^ 2 - t ^ 2)) (a := (0 : ℝ)) (b := R)
    simp only [neg_zero, neg_sq] at hneg
    exact hneg.symm
  have hcont : ContinuousOn (fun t : ℝ => Real.sqrt (R ^ 2 - t ^ 2)) (Set.Icc (-R) R) := by
    fun_prop
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (R ^ 2 - t ^ 2)) volume (-R) 0 :=
    (hcont.mono (by
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -R ≤ 0)] at ht
      exact ⟨ht.1, ht.2.trans hR⟩)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => Real.sqrt (R ^ 2 - t ^ 2)) volume 0 R :=
    (hcont.mono (by
      intro t ht
      rw [Set.uIcc_of_le hR] at ht
      exact ⟨(by linarith : -R ≤ 0).trans ht.1, ht.2⟩)).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [heven] at hadd
  linarith

/-- Symmetric `ℤ`-interval sum identity for even functions. -/
theorem sum_Icc_neg_self_even (M : ℕ) (g : ℝ → ℝ) (hg : ∀ t : ℝ, g (-t) = g t) :
    ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), g (a : ℝ) =
      g 0 + 2 * ∑ k ∈ Finset.Icc 1 M, g (k : ℝ) := by
  let negFn : ℕ → ℤ := fun k => -(k : ℤ)
  let Spos : Finset ℤ := (Finset.Icc 1 M).image (fun k : ℕ => (k : ℤ))
  let Sneg : Finset ℤ := (Finset.Icc 1 M).image negFn
  have hsplit : Finset.Icc (-(M : ℤ)) (M : ℤ) = insert 0 (Spos ∪ Sneg) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Spos, Sneg,
      negFn]
    constructor
    · intro ha
      rcases lt_trichotomy a 0 with hlt | rfl | hgt
      · right; right
        refine ⟨a.natAbs, ⟨Nat.succ_le_of_lt (Int.natAbs_pos.mpr hlt.ne), natAbs_le_of_abs_le ha⟩,
          ?_⟩
        have := Int.natCast_natAbs a
        rw [abs_of_neg hlt] at this
        omega
      · left; rfl
      · right; left
        exact ⟨a.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro (rfl | ⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩) <;> omega
  have h0 : (0 : ℤ) ∉ Spos ∪ Sneg := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Spos, Sneg, negFn]
    rintro (⟨k, ⟨hk1, _⟩, hk0⟩ | ⟨k, ⟨hk1, _⟩, hk0⟩) <;> omega
  have hdisj : Disjoint Spos Sneg := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_image, Finset.mem_Icc, Spos, Sneg, negFn] at ha1 ha2
    rcases ha1 with ⟨k1, ⟨hk1, _⟩, rfl⟩
    rcases ha2 with ⟨k2, ⟨hk2, _⟩, hk2'⟩
    omega
  have hsum_pos : ∑ a ∈ Spos, g (a : ℝ) = ∑ k ∈ Finset.Icc 1 M, g (k : ℝ) := by
    dsimp only [Spos]
    rw [Finset.sum_image (fun x _ y _ h => Nat.cast_injective (R := ℤ) h)]
    rfl
  have hsum_neg : ∑ a ∈ Sneg, g (a : ℝ) = ∑ k ∈ Finset.Icc 1 M, g (k : ℝ) := by
    dsimp only [Sneg, negFn]
    rw [Finset.sum_image (fun x _ y _ h => Nat.cast_injective (R := ℤ) (neg_inj.mp h))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simpa [negFn, Int.cast_neg] using hg (k : ℝ)
  rw [hsplit, Finset.sum_insert h0, Finset.sum_union hdisj, hsum_pos, hsum_neg]
  simp only [Int.cast_zero]
  ring

/-- Elementary boundary-layer bound for the Gauss circle problem:
`|R₂(x) - π x| ≤ 5 √x` for all `1 ≤ x`. -/
theorem abs_gaussCircleError_le {x : ℝ} (hx : 1 ≤ x) :
    |gaussCircleError x| ≤ 5 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  let R : ℝ := Real.sqrt x
  have hR1 : 1 ≤ R := Real.one_le_sqrt.mpr hx
  have hR0 : 0 ≤ R := by linarith
  have hRsq : R ^ 2 = x := Real.sq_sqrt hx0
  let M : ℕ := ⌊R⌋₊
  have hM1 : 1 ≤ M := Nat.floor_pos.mpr hR1
  have hMR : (M : ℝ) ≤ R := Nat.floor_le hR0
  have hRM1 : R < (M : ℝ) + 1 := Nat.lt_floor_add_one R
  let f : ℝ → ℝ := fun t => Real.sqrt (x - t ^ 2)
  have hf_even : ∀ t : ℝ, f (-t) = f t := fun t => by simp [f]
  have hf_slice := gaussCircleCount_eq_sum_slice hx0
  dsimp only at hf_slice
  change gaussCircleCount x =
    ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * (⌊f (a : ℝ)⌋₊ : ℝ) + 1) at hf_slice
  have hfloor_err :
      |gaussCircleCount x - ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * f (a : ℝ))| ≤
        2 * (M : ℝ) + 1 := by
    rw [hf_slice, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm :
        ∀ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          |2 * (⌊f (a : ℝ)⌋₊ : ℝ) + 1 - 2 * f (a : ℝ)| ≤ (1 : ℝ) := by
      intro a _
      have hf0 : 0 ≤ f (a : ℝ) := Real.sqrt_nonneg _
      have hlo : f (a : ℝ) - 1 < (⌊f (a : ℝ)⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (f (a : ℝ))]
      have hhi : (⌊f (a : ℝ)⌋₊ : ℝ) ≤ f (a : ℝ) := Nat.floor_le hf0
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    have hcard : ((M : ℤ) + 1 - (-(M : ℤ))).toNat = 2 * M + 1 := by omega
    rw [hcard]
    push_cast
    exact le_rfl
  have hf_anti : AntitoneOn f (Set.Icc 0 R) := by
    intro t1 ht1 t2 ht2 h12
    refine Real.sqrt_le_sqrt ?_
    nlinarith [ht1.1, ht2.1]
  have hf_cont : ContinuousOn f (Set.Icc 0 R) := by
    refine ContinuousOn.sqrt ?_
    fun_prop
  have hadj_full :
      ∫ t in (0 : ℝ)..(M : ℝ), f t =
        ∑ k ∈ Finset.range M, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t := by
    symm
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (f := f) fun k hk => by
      refine (hf_cont.mono ?_).intervalIntegrable
      have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ R := (Nat.cast_le.mpr hk).trans hMR
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      exact ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans hk1⟩
    simpa using h
  have hsum_shift :
      ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) = ∑ k ∈ Finset.range M, f ((k + 1 : ℕ) : ℝ) := by
    symm
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, hk⟩
    · intro k1 _ k2 _ h; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro _ _; rfl
  have hsum_le_int :
      ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) ≤ ∫ t in (0 : ℝ)..(M : ℝ), f t := by
    rw [hadj_full, hsum_shift]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkM : k + 1 ≤ M := Finset.mem_range.mp hk
    have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have hi : IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
      (hf_cont.mono (by
        intro t ht
        rw [Set.uIcc_of_le hle] at ht
        exact ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans ((Nat.cast_le.mpr hkM).trans hMR)⟩)).intervalIntegrable
    have hc : IntervalIntegrable (fun _ : ℝ => f ((k + 1 : ℕ) : ℝ)) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
      intervalIntegrable_const
    have hconst := intervalIntegral.integral_const (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
      (c := f ((k + 1 : ℕ) : ℝ))
    have hmono := intervalIntegral.integral_mono_on hle hc hi
      (fun t ht => hf_anti ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans ((Nat.cast_le.mpr hkM).trans hMR)⟩
        ⟨Nat.cast_nonneg _, (Nat.cast_le.mpr hkM).trans hMR⟩ ht.2)
    have hone : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
    rw [hconst, hone, smul_eq_mul, one_mul] at hmono
    exact hmono
  have hint_le_sum :
      ∫ t in (0 : ℝ)..(M : ℝ), f t ≤ f 0 + ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) - f (M : ℝ) := by
    rw [hadj_full]
    have hupper :
        ∑ k ∈ Finset.range M, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t ≤
          ∑ k ∈ Finset.range M, f (k : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hkM : k + 1 ≤ M := Finset.mem_range.mp hk
      have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      have hi : IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
        (hf_cont.mono (by
          intro t ht
          rw [Set.uIcc_of_le hle] at ht
          exact ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans ((Nat.cast_le.mpr hkM).trans hMR)⟩)).intervalIntegrable
      have hc : IntervalIntegrable (fun _ : ℝ => f (k : ℝ)) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
        intervalIntegrable_const
      have hconst := intervalIntegral.integral_const (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
        (c := f (k : ℝ))
      have hmono := intervalIntegral.integral_mono_on hle hi hc
        (fun t ht => hf_anti ⟨Nat.cast_nonneg k, (Nat.cast_le.mpr (Nat.le_of_lt hkM)).trans hMR⟩
          ⟨(Nat.cast_nonneg k).trans ht.1, ht.2.trans ((Nat.cast_le.mpr hkM).trans hMR)⟩ ht.1)
      have hone : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
      rw [hconst, hone, smul_eq_mul, one_mul] at hmono
      exact hmono
    refine hupper.trans_eq ?_
    have h1 : ∑ k ∈ Finset.range (M + 1), f (k : ℝ) =
        f (M : ℝ) + ∑ k ∈ Finset.range M, f (k : ℝ) := by
      rw [Finset.sum_range_succ, add_comm]
    have h2 : ∑ k ∈ Finset.range (M + 1), f (k : ℝ) =
        f 0 + ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) := by
      rw [Finset.sum_range_succ', hsum_shift]
      simp only [Nat.cast_zero, add_comm]
    linarith
  have htail_nonneg : 0 ≤ ∫ t in (M : ℝ)..R, f t :=
    intervalIntegral.integral_nonneg hMR fun t _ => Real.sqrt_nonneg _
  have htail_le : ∫ t in (M : ℝ)..R, f t ≤ f (M : ℝ) := by
    have hi : IntervalIntegrable f volume (M : ℝ) R :=
      (hf_cont.mono (by
        intro t ht
        rw [Set.uIcc_of_le hMR] at ht
        exact ⟨(Nat.cast_nonneg M).trans ht.1, ht.2⟩)).intervalIntegrable
    have hc : IntervalIntegrable (fun _ : ℝ => f (M : ℝ)) volume (M : ℝ) R :=
      intervalIntegrable_const
    have hconst := intervalIntegral.integral_const (a := (M : ℝ)) (b := R) (c := f (M : ℝ))
    have hmono := intervalIntegral.integral_mono_on hMR hi hc
      (fun t ht => hf_anti ⟨Nat.cast_nonneg M, hMR⟩ ⟨(Nat.cast_nonneg M).trans ht.1, ht.2⟩ ht.1)
    rw [hconst, smul_eq_mul] at hmono
    have hlen : (R - (M : ℝ)) * f (M : ℝ) ≤ 1 * f (M : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    linarith
  have hi_0M : IntervalIntegrable f volume 0 (M : ℝ) :=
    (hf_cont.mono (by
      intro t ht
      rw [Set.uIcc_of_le (Nat.cast_nonneg M)] at ht
      exact ⟨ht.1, ht.2.trans hMR⟩)).intervalIntegrable
  have hi_MR : IntervalIntegrable f volume (M : ℝ) R :=
    (hf_cont.mono (by
      intro t ht
      rw [Set.uIcc_of_le hMR] at ht
      exact ⟨(Nat.cast_nonneg M).trans ht.1, ht.2⟩)).intervalIntegrable
  have hint_split : ∫ t in (0 : ℝ)..R, f t =
      (∫ t in (0 : ℝ)..(M : ℝ), f t) + (∫ t in (M : ℝ)..R, f t) :=
    (intervalIntegral.integral_add_adjacent_intervals hi_0M hi_MR).symm
  have hint_eval : 4 * ∫ t in (0 : ℝ)..R, f t = Real.pi * x := by
    have h1 : ∫ t in (0 : ℝ)..R, f t = Real.pi * R ^ 2 / 4 := by
      simpa [f, hRsq] using integral_sqrt_sq_sub_sq hR0
    rw [h1, hRsq]
    ring
  have hf0 : f 0 = R := by simp [f, R]
  have heven_sum :
      ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * f (a : ℝ)) =
        2 * f 0 + 4 * ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) := by
    have hs := sum_Icc_neg_self_even M (fun t => 2 * f t) (fun t => by rw [hf_even])
    rw [hs]
    simp_rw [← Finset.mul_sum]
    ring
  have hint_err :
      |∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * f (a : ℝ)) - Real.pi * x| ≤ 2 * R := by
    rw [← hint_eval, hint_split, heven_sum]
    have hlo : 4 * ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) ≤
        4 * ((∫ t in (0 : ℝ)..(M : ℝ), f t) + ∫ t in (M : ℝ)..R, f t) := by linarith
    have hhi : 4 * ((∫ t in (0 : ℝ)..(M : ℝ), f t) + ∫ t in (M : ℝ)..R, f t) ≤
        4 * f 0 + 4 * ∑ k ∈ Finset.Icc 1 M, f (k : ℝ) := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htri :
      |gaussCircleError x| ≤
        |gaussCircleCount x - ∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * f (a : ℝ))| +
          |∑ a ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (2 * f (a : ℝ)) - Real.pi * x| := by
    rw [gaussCircleError]
    exact abs_sub_le _ _ _
  have hM_le : 2 * (M : ℝ) + 1 ≤ 3 * R := by linarith
  linarith

/-- Uniform Gauss circle error bound valid for all `0 ≤ x`: `|R₂(x) - π x| ≤ 5 √x + 1`. -/
theorem abs_gaussCircleError_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |gaussCircleError x| ≤ 5 * Real.sqrt x + 1 := by
  by_cases hx1 : 1 ≤ x
  · exact (abs_gaussCircleError_le hx1).trans (by linarith)
  · push Not at hx1
    have hfloor0 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    have hcnt : gaussCircleCount x = 1 := by
      rw [gaussCircleCount_eq_one_add_sum_repTwoSquares hx, hfloor0]
      simp
    rw [gaussCircleError, hcnt]
    have hpi_le : Real.pi ≤ 4 := Real.pi_le_four
    have hpi_pos : 0 ≤ Real.pi := Real.pi_nonneg
    have hx_le_sqrt : x ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
    have h1 : 1 - Real.pi * x ≤ 5 * Real.sqrt x + 1 := by
      have : 0 ≤ Real.pi * x := mul_nonneg hpi_pos hx
      have : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      linarith
    have h2 : -(5 * Real.sqrt x + 1) ≤ 1 - Real.pi * x := by
      have hpx : Real.pi * x ≤ 4 * x := mul_le_mul_of_nonneg_right hpi_le hx
      linarith
    exact abs_le.mpr ⟨h2, h1⟩

/-- Asymptotic Gauss circle error bound `P(x) = O(√x)` as `x → ∞`. -/
theorem gaussCircleError_isBigO_sqrt :
    gaussCircleError =O[atTop] Real.sqrt := by
  refine Asymptotics.IsBigO.of_bound 5 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] using abs_gaussCircleError_le hx

end GaussCircleElementary

end AnalyticNumberTheory.DivisorProblems
