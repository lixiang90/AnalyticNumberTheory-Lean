import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import AnalyticNumberTheory.DivisorProblems.GaussCircle

/-!
# Jacobi's two-square formula

For positive `n`, the four rotations of each first-quadrant representative account
for all ordered, signed solutions of `a² + b² = n`. Unique factorization in the
Gaussian integers gives the first-quadrant counts on prime powers and proves
multiplicativity for coprime arguments. Comparing with the divisor sum of the
nontrivial character modulo four gives Jacobi's formula. Summing in `n` then
expresses the number of lattice points in a disk as a finite difference of floor sums.
-/

open scoped BigOperators
open Filter Topology MeasureTheory

namespace AnalyticNumberTheory.DivisorProblems

section JacobiTwoSquares

/-- First-quadrant pairs `(a, b) ∈ ℕ × ℕ` with `1 ≤ a` and `a ^ 2 + b ^ 2 = n`. -/
def posSqFinset (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 0 n).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = n)

/-- First-quadrant representation count `r₂⁺(n) = #{(a, b) ∈ ℕ × ℕ : 1 ≤ a, a ^ 2 + b ^ 2 = n}`. -/
def r2Pos (n : ℕ) : ℕ := (posSqFinset n).card

private theorem mem_posSqFinset {n : ℕ} {p : ℕ × ℕ} :
    p ∈ posSqFinset n ↔ 1 ≤ p.1 ∧ p.1 ^ 2 + p.2 ^ 2 = n := by
  unfold posSqFinset
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, hp⟩
    exact ⟨h1, hp⟩
  · rintro ⟨h1, hp⟩
    have ha_le : p.1 ≤ n := by
      have : p.1 ≤ p.1 * p.1 := Nat.le_mul_self p.1
      nlinarith [sq p.1, sq p.2]
    have hb_le : p.2 ≤ n := by
      have : p.2 ≤ p.2 * p.2 := Nat.le_mul_self p.2
      nlinarith [sq p.1, sq p.2]
    exact ⟨⟨⟨h1, ha_le⟩, ⟨Nat.zero_le _, hb_le⟩⟩, hp⟩

private theorem r2Pos_one : r2Pos 1 = 1 := by
  rw [r2Pos, Finset.card_eq_one]
  refine ⟨(1, 0), Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_posSqFinset.mpr ⟨le_rfl, by norm_num⟩, ?_⟩⟩
  rintro ⟨a, b⟩ hp
  rw [mem_posSqFinset] at hp
  rcases hp with ⟨ha1, hab⟩
  have hb0 : b = 0 := by nlinarith
  subst hb0
  have ha_eq : a = 1 := by nlinarith
  subst ha_eq
  rfl

/-- Unit rotation symmetry: `r₂(n) = 4 * r₂⁺(n)` for every `1 ≤ n`. -/
theorem repTwoSquares_eq_four_mul_r2Pos {n : ℕ} (hn : 1 ≤ n) :
    repTwoSquares n = 4 * r2Pos n := by
  rw [← repTwoSquaresFinset_card, r2Pos]
  let φ : Fin 4 × (ℕ × ℕ) → ℤ × ℤ := fun ⟨k, a, b⟩ =>
    match k with
    | 0 => ((a : ℤ), (b : ℤ))
    | 1 => (-(b : ℤ), (a : ℤ))
    | 2 => (-(a : ℤ), -(b : ℤ))
    | 3 => ((b : ℤ), -(a : ℤ))
  have hbij : Finset.card ((Finset.univ : Finset (Fin 4)) ×ˢ posSqFinset n) =
      Finset.card (repTwoSquaresFinset n) := by
    refine Finset.card_bij (fun x _ => φ x) ?_ ?_ ?_
    · rintro ⟨k, a, b⟩ hx
      rw [Finset.mem_product, mem_posSqFinset] at hx
      rcases hx.2 with ⟨_, hab⟩
      rw [mem_repTwoSquaresFinset]
      fin_cases k <;> simp only [φ] <;> zify at hab <;> nlinarith
    · rintro ⟨k1, a1, b1⟩ h1 ⟨k2, a2, b2⟩ h2 heq
      rw [Finset.mem_product, mem_posSqFinset] at h1 h2
      rcases h1 with ⟨_, ha1, _⟩
      rcases h2 with ⟨_, ha2, _⟩
      dsimp only at ha1 ha2
      fin_cases k1 <;> fin_cases k2 <;> dsimp only [φ] at heq <;> rw [Prod.ext_iff] at heq <;>
        rcases heq with ⟨e1, e2⟩
      · exact Prod.ext rfl (Prod.ext (by dsimp; omega) (by dsimp; omega))
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact Prod.ext rfl (Prod.ext (by dsimp; omega) (by dsimp; omega))
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact Prod.ext rfl (Prod.ext (by dsimp; omega) (by dsimp; omega))
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact Prod.ext rfl (Prod.ext (by dsimp; omega) (by dsimp; omega))
    · intro ⟨x, y⟩ hxy
      rw [mem_repTwoSquaresFinset] at hxy
      have hsq : x.natAbs ^ 2 + y.natAbs ^ 2 = n := by
        zify
        simpa [Int.natAbs_sq] using hxy
      have hsq_comm : y.natAbs ^ 2 + x.natAbs ^ 2 = n := by
        rw [add_comm]; exact hsq
      have hne : x ≠ 0 ∨ y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        simp [hcon.1, hcon.2] at hsq
        omega
      rcases lt_trichotomy x 0 with hxlt | rfl | hxgt
      · rcases le_or_gt y 0 with hyle | hygt
        · refine ⟨(2, x.natAbs, y.natAbs), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hxlt.ne, hsq⟩⟩, ?_⟩
          have hxabs : -(x.natAbs : ℤ) = x := by
            have := Int.natCast_natAbs x; rw [abs_of_neg hxlt] at this; omega
          have hyabs : -(y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_nonpos hyle] at this; omega
          exact Prod.ext hxabs hyabs
        · refine ⟨(1, y.natAbs, x.natAbs), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hygt.ne', hsq_comm⟩⟩, ?_⟩
          have hxabs : -(x.natAbs : ℤ) = x := by
            have := Int.natCast_natAbs x; rw [abs_of_neg hxlt] at this; omega
          have hyabs : (y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_pos hygt] at this; exact this
          exact Prod.ext hxabs hyabs
      · rcases lt_trichotomy y 0 with hylt | rfl | hygt
        · refine ⟨(3, y.natAbs, 0), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hylt.ne, by simpa using hsq_comm⟩⟩, ?_⟩
          have hyabs : -(y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_neg hylt] at this; omega
          exact Prod.ext rfl hyabs
        · exact (hne.elim (fun h => h rfl) (fun h => h rfl)).elim
        · refine ⟨(1, y.natAbs, 0), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hygt.ne', by simpa using hsq_comm⟩⟩, ?_⟩
          have hyabs : (y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_pos hygt] at this; exact this
          exact Prod.ext (by simp [φ]) hyabs
      · rcases lt_or_ge y 0 with hylt | hyge
        · refine ⟨(3, y.natAbs, x.natAbs), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hylt.ne, hsq_comm⟩⟩, ?_⟩
          have hxabs : (x.natAbs : ℤ) = x := by
            have := Int.natCast_natAbs x; rw [abs_of_pos hxgt] at this; exact this
          have hyabs : -(y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_neg hylt] at this; omega
          exact Prod.ext hxabs hyabs
        · refine ⟨(0, x.natAbs, y.natAbs), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, mem_posSqFinset.mpr ⟨Int.natAbs_pos.mpr hxgt.ne', hsq⟩⟩, ?_⟩
          have hxabs : (x.natAbs : ℤ) = x := by
            have := Int.natCast_natAbs x; rw [abs_of_pos hxgt] at this; exact this
          have hyabs : (y.natAbs : ℤ) = y := by
            have := Int.natCast_natAbs y; rw [abs_of_nonneg hyge] at this; exact this
          exact Prod.ext hxabs hyabs
  simpa [Finset.card_product, Fintype.card_fin, eq_comm] using hbij

/-- First-quadrant predicate on `GaussianInt`: `0 < z.re` and `0 ≤ z.im`. -/
private def inFirstQuad (z : GaussianInt) : Prop := 0 < z.re ∧ 0 ≤ z.im

private theorem norm_eq_sq_add_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm, sq]

private theorem norm_pow_gi (z : GaussianInt) (k : ℕ) : (z ^ k).norm = z.norm ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

private theorem mul_star_eq_norm (z : GaussianInt) : z * star z = (z.norm : GaussianInt) := by
  ext <;> simp [Zsqrtd.norm]
  ring

private theorem natCast_norm_eq (n : ℕ) : (n : GaussianInt).norm = (n : ℤ) ^ 2 := by
  simp [norm_eq_sq_add_sq]

private theorem natCast_re_gi (n : ℕ) : ((n : GaussianInt).re : ℤ) = n := rfl

private theorem associated_mul_left_cancel {a b c : GaussianInt} (ha : a ≠ 0)
    (h : Associated (a * b) (a * c)) : Associated b c := by
  rcases h with ⟨u, hu⟩
  exact ⟨u, mul_left_cancel₀ ha (by simpa [mul_assoc] using hu)⟩

private theorem associated_mul_right_cancel {a b c : GaussianInt} (hc : c ≠ 0)
    (h : Associated (a * c) (b * c)) : Associated a b := by
  rw [mul_comm a c, mul_comm b c] at h
  exact associated_mul_left_cancel hc h

private theorem isCoprime_natCast_gi {m n : ℕ} (hcop : m.Coprime n) :
    IsCoprime (m : GaussianInt) (n : GaussianInt) := by
  refine ⟨(Nat.gcdA m n : GaussianInt), (Nat.gcdB m n : GaussianInt), ?_⟩
  have hg := Nat.gcd_eq_gcd_ab m n
  rw [hcop, mul_comm (m : ℤ) (Nat.gcdA m n), mul_comm (n : ℤ) (Nat.gcdB m n)] at hg
  exact_mod_cast hg.symm

private theorem isUnit_iff_norm_eq_one (u : GaussianInt) : IsUnit u ↔ u.norm = 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    have hv : (v : GaussianInt) * v.inv = 1 := v.val_inv
    have hnorm := congr_arg Zsqrtd.norm hv
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_one] at hnorm
    have hn0 : 0 ≤ (v : GaussianInt).norm := GaussianInt.norm_nonneg _
    have hn1 : 0 ≤ v.inv.norm := GaussianInt.norm_nonneg _
    have hne : v.inv.norm ≠ 0 := fun h => by rw [h, mul_zero] at hnorm; omega
    have hge1 : 1 ≤ v.inv.norm := by omega
    nlinarith
  · intro h
    refine isUnit_iff_exists_inv.mpr ⟨star u, ?_⟩
    rw [mul_star_eq_norm, h]
    rfl

private theorem isUnit_cases {u : GaussianInt} (hu : IsUnit u) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  rw [isUnit_iff_norm_eq_one, norm_eq_sq_add_sq] at hu
  have h1 : u.re ^ 2 ≤ 1 := by linarith [sq_nonneg u.im]
  have h2 : u.im ^ 2 ≤ 1 := by linarith [sq_nonneg u.re]
  have hr_bd : -1 ≤ u.re ∧ u.re ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hi_bd : -1 ≤ u.im ∧ u.im ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hr : u.re = -1 ∨ u.re = 0 ∨ u.re = 1 := by omega
  have hi : u.im = -1 ∨ u.im = 0 ∨ u.im = 1 := by omega
  rcases hr with hr | hr | hr <;> rcases hi with hi | hi | hi
  · exfalso; rw [hr, hi] at hu; norm_num at hu
  · right; left; ext <;> simp [hr, hi]
  · exfalso; rw [hr, hi] at hu; norm_num at hu
  · right; right; right; ext <;> simp [hr, hi]
  · exfalso; rw [hr, hi] at hu; norm_num at hu
  · right; right; left; ext <;> simp [hr, hi]
  · exfalso; rw [hr, hi] at hu; norm_num at hu
  · left; ext <;> simp [hr, hi]
  · exfalso; rw [hr, hi] at hu; norm_num at hu

private theorem eq_of_associated_of_inFirstQuad {z₁ z₂ : GaussianInt}
    (h1 : inFirstQuad z₁) (h2 : inFirstQuad z₂) (hass : Associated z₁ z₂) : z₁ = z₂ := by
  rcases hass with ⟨u, rfl⟩
  have hu := isUnit_cases u.isUnit
  rcases hu with h | h | h | h
  · rw [h, mul_one]
  · rw [h] at h2
    simp only [inFirstQuad, Zsqrtd.re_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_one,
      Zsqrtd.im_one] at h2
    linarith [h1.1, h2.1]
  · rw [h] at h2
    simp only [inFirstQuad] at h2
    have hre : (z₁ * ⟨0, 1⟩).re = -z₁.im := by simp
    linarith [h1.2, h2.1]
  · rw [h] at h2
    simp only [inFirstQuad] at h2
    have him : (z₁ * ⟨0, -1⟩).im = -z₁.re := by simp
    linarith [h1.1, h2.2]

/-- Canonical first-quadrant representative in the associate class of a nonzero `z : GaussianInt`. -/
private noncomputable def canonQuad (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then ⟨0, -1⟩ * z
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else ⟨0, 1⟩ * z

private theorem canonQuad_inFirstQuad {z : GaussianInt} (hz : z ≠ 0) :
    inFirstQuad (canonQuad z) := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (Zsqrtd.ext h.1 h.2)
  unfold canonQuad inFirstQuad
  split_ifs with h1 h2 h3
  · exact h1
  · simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    omega
  · simp only [Zsqrtd.re_neg, Zsqrtd.im_neg]
    omega
  · simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    omega

private theorem associated_unit_mul (u z : GaussianInt) (hu : IsUnit u) :
    Associated (u * z) z := by
  rcases hu with ⟨u, rfl⟩
  exact ⟨u⁻¹, by rw [mul_comm (u : GaussianInt) z, mul_assoc, Units.mul_inv, mul_one]⟩

private theorem canonQuad_associated {z : GaussianInt} : Associated (canonQuad z) z := by
  unfold canonQuad
  split_ifs
  · exact Associated.refl _
  · refine associated_unit_mul ⟨0, -1⟩ z ?_
    rw [isUnit_iff_norm_eq_one, norm_eq_sq_add_sq]
    norm_num
  · rw [← neg_one_mul z]
    exact associated_unit_mul (-1) z isUnit_one.neg
  · refine associated_unit_mul ⟨0, 1⟩ z ?_
    rw [isUnit_iff_norm_eq_one, norm_eq_sq_add_sq]
    norm_num

private theorem canonQuad_eq_self {z : GaussianInt} (hz : inFirstQuad z) : canonQuad z = z := by
  unfold canonQuad
  simp [hz.1, hz.2]

private theorem canonQuad_norm_natAbs {z : GaussianInt} :
    (canonQuad z).norm.natAbs = z.norm.natAbs := by
  rcases canonQuad_associated (z := z) with ⟨u, hu⟩
  have hn := congr_arg Zsqrtd.norm hu
  rw [Zsqrtd.norm_mul] at hn
  have hun : (u : GaussianInt).norm = 1 := (isUnit_iff_norm_eq_one _).mp u.isUnit
  rw [hun, mul_one] at hn
  rw [hn]

private theorem canonQuad_eq_iff {z₁ z₂ : GaussianInt} (h1 : z₁ ≠ 0) (h2 : z₂ ≠ 0) :
    canonQuad z₁ = canonQuad z₂ ↔ Associated z₁ z₂ := by
  constructor
  · intro heq
    exact canonQuad_associated.symm.trans (heq ▸ canonQuad_associated)
  · intro hass
    exact eq_of_associated_of_inFirstQuad (canonQuad_inFirstQuad h1) (canonQuad_inFirstQuad h2)
      (canonQuad_associated.trans (hass.trans canonQuad_associated.symm))

private theorem canonQuad_ne_zero {z : GaussianInt} (hz : z ≠ 0) : canonQuad z ≠ 0 := by
  have hq := canonQuad_inFirstQuad hz
  intro h0
  rw [h0] at hq
  simp [inFirstQuad] at hq

private def posQuadEmb : (ℕ × ℕ) ↪ GaussianInt :=
  ⟨fun p => ⟨(p.1 : ℤ), (p.2 : ℤ)⟩, fun _ _ h => by
    simp only [Zsqrtd.ext_iff] at h
    ext
    · exact Int.ofNat.inj h.1
    · exact Int.ofNat.inj h.2⟩

@[simp]
private theorem posQuadEmb_apply (p : ℕ × ℕ) : posQuadEmb p = ⟨(p.1 : ℤ), (p.2 : ℤ)⟩ := rfl

private noncomputable def posQuadFinset (n : ℕ) : Finset GaussianInt :=
  (posSqFinset n).map posQuadEmb

private theorem card_posQuadFinset (n : ℕ) : (posQuadFinset n).card = r2Pos n := by
  rw [posQuadFinset, Finset.card_map, r2Pos]

private theorem mem_posQuadFinset {n : ℕ} {z : GaussianInt} :
    z ∈ posQuadFinset n ↔ inFirstQuad z ∧ z.norm = (n : ℤ) := by
  rw [posQuadFinset, Finset.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [mem_posSqFinset] at hab
    change 1 ≤ a ∧ a ^ 2 + b ^ 2 = n at hab
    refine ⟨⟨Int.natCast_pos.mpr hab.1, Int.natCast_nonneg b⟩, ?_⟩
    rw [norm_eq_sq_add_sq]
    change (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (n : ℤ)
    exact_mod_cast hab.2
  · rintro ⟨⟨hre, him⟩, hnorm⟩
    refine ⟨(z.re.natAbs, z.im.natAbs), mem_posSqFinset.mpr ⟨by omega, ?_⟩, ?_⟩
    · rw [norm_eq_sq_add_sq] at hnorm
      zify
      simpa [Int.natAbs_sq] using hnorm
    · simp only [posQuadEmb_apply]
      ext
      · change ((z.re.natAbs : ℕ) : ℤ) = z.re
        rw [Int.natCast_natAbs, abs_of_pos hre]
      · change ((z.im.natAbs : ℕ) : ℤ) = z.im
        rw [Int.natCast_natAbs, abs_of_nonneg him]

private theorem natCast_dvd_norm_eq {z : GaussianInt} :
    (z.norm.natAbs : GaussianInt) = z * star z := by
  rw [mul_star_eq_norm, ← Int.cast_natCast, GaussianInt.abs_natCast_norm]

/-- Exact norm property of `gcd z m` for `z.norm = m * n` with `m.Coprime n`. -/
private theorem gcd_norm_eq_of_coprime {z : GaussianInt} {m n : ℕ}
    (hm : 1 ≤ m) (_hn : 1 ≤ n) (hcop : m.Coprime n) (hzn : z.norm.natAbs = m * n) :
    (EuclideanDomain.gcd z (m : GaussianInt)).norm.natAbs = m := by
  let d : GaussianInt := EuclideanDomain.gcd z (m : GaussianInt)
  have hdz : d ∣ z := EuclideanDomain.gcd_dvd_left z (m : GaussianInt)
  have hdm : d ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right z (m : GaussianInt)
  have hd_ne : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hdm
    have hm0 : ((m : GaussianInt).re : ℤ) = 0 := by rw [hdm]; rfl
    rw [natCast_re_gi] at hm0
    omega
  have hd_dvd_mul : d.norm.natAbs ∣ m * n := by
    rcases hdz with ⟨z', hz'⟩
    have hnorm := congr_arg Zsqrtd.norm hz'
    rw [Zsqrtd.norm_mul] at hnorm
    have hna : (z.norm.natAbs : ℤ) = ((d.norm.natAbs * z'.norm.natAbs : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, pow_one] using hnorm
    have hna_nat : z.norm.natAbs = d.norm.natAbs * z'.norm.natAbs := Int.ofNat.inj hna
    rw [hna_nat] at hzn
    exact ⟨z'.norm.natAbs, hzn.symm⟩
  have hd_dvd_msq : d.norm.natAbs ∣ m ^ 2 := by
    rcases hdm with ⟨m', hm'⟩
    have hnorm := congr_arg Zsqrtd.norm hm'
    rw [Zsqrtd.norm_mul, natCast_norm_eq] at hnorm
    have hna : ((m ^ 2 : ℕ) : ℤ) = ((d.norm.natAbs * m'.norm.natAbs : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, pow_one] using hnorm
    exact ⟨m'.norm.natAbs, Int.ofNat.inj hna⟩
  have hcop_dn : d.norm.natAbs.Coprime n := (hcop.pow_left 2).coprime_dvd_left hd_dvd_msq
  have hd_dvd_m : d.norm.natAbs ∣ m := hcop_dn.dvd_of_dvd_mul_right hd_dvd_mul
  rcases hd_dvd_m with ⟨a, ha⟩
  by_contra hne
  have ha_pos : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    rw [ha0, mul_zero] at ha
    omega
  have ha_gt : 1 < a := by
    by_contra hle
    have ha1 : a = 1 := by omega
    rw [ha1, mul_one] at ha
    exact hne ha.symm
  rcases hdz with ⟨z', hz'⟩
  rcases hdm with ⟨m', hm'⟩
  have hmul_eq : d * m' = d * (star d * (a : GaussianInt)) := by
    rw [← hm', ← mul_assoc, mul_star_eq_norm]
    have hca : (d.norm : GaussianInt) * (a : GaussianInt) = (m : GaussianInt) := by
      rw [← GaussianInt.abs_natCast_norm d]
      exact_mod_cast ha.symm
    exact hca.symm
  have hm'_eq : m' = star d * (a : GaussianInt) := mul_left_cancel₀ hd_ne hmul_eq
  have ha_dvd_m' : (a : GaussianInt) ∣ m' := ⟨star d, by rw [hm'_eq, mul_comm]⟩
  have hz'_norm : z'.norm.natAbs = a * n := by
    have hnorm := congr_arg Zsqrtd.norm hz'
    rw [Zsqrtd.norm_mul] at hnorm
    have hna_z : (z.norm.natAbs : ℤ) = ((d.norm.natAbs * z'.norm.natAbs : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, pow_one] using hnorm
    have hna : z.norm.natAbs = d.norm.natAbs * z'.norm.natAbs := Int.ofNat.inj hna_z
    have hd_pos : 0 < d.norm.natAbs := Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hd_ne)
    rw [hzn, ha, mul_assoc] at hna
    exact (Nat.eq_of_mul_eq_mul_left hd_pos hna).symm
  let p : ℕ := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpa : p ∣ a := Nat.minFac_dvd a
  have hp_ne : (p : GaussianInt) ≠ 0 := by
    intro h0
    have hm0 : ((p : GaussianInt).re : ℤ) = 0 := by rw [h0]; rfl
    rw [natCast_re_gi] at hm0
    exact hp.ne_zero (by omega)
  have hp_nu : ¬IsUnit (p : GaussianInt) := by
    rw [isUnit_iff_norm_eq_one, natCast_norm_eq]
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  obtain ⟨π, hπ_irr, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hp_nu hp_ne
  have hπ_prime : Prime π := irreducible_iff_prime.mp hπ_irr
  have hpa' : (p : GaussianInt) ∣ (a : GaussianInt) := (Nat.castRingHom GaussianInt).map_dvd hpa
  have hπ_dvd_a : π ∣ (a : GaussianInt) := hπ_dvd.trans hpa'
  have hπ_dvd_m' : π ∣ m' := hπ_dvd_a.trans ha_dvd_m'
  have hstar_dvd_p : star π ∣ (p : GaussianInt) := by
    rcases hπ_dvd with ⟨q, hq⟩
    refine ⟨star q, ?_⟩
    have hsq := congr_arg star hq
    simpa [star_mul, star_natCast, mul_comm] using hsq
  have hstar_dvd_m' : star π ∣ m' :=
    (hstar_dvd_p.trans hpa').trans ha_dvd_m'
  have hstar_nu : ¬IsUnit (star π) := by
    intro hu
    apply hπ_irr.1
    rw [isUnit_iff_norm_eq_one] at hu ⊢
    simpa [Zsqrtd.norm_conj] using hu
  have hp_dvd_z' : (p : GaussianInt) ∣ z' * star z' := by
    rw [← natCast_dvd_norm_eq]
    exact (Nat.castRingHom GaussianInt).map_dvd (hpa.trans ⟨n, hz'_norm⟩)
  have hπ_dvd_prod : π ∣ z' * star z' := hπ_dvd.trans hp_dvd_z'
  have hcop_zm : IsUnit (EuclideanDomain.gcd z' m') := by
    have hbez : 1 = z' * EuclideanDomain.gcdA z (m : GaussianInt) +
        m' * EuclideanDomain.gcdB z (m : GaussianInt) := by
      apply mul_left_cancel₀ hd_ne
      calc d * 1 = d := mul_one _
        _ = z * EuclideanDomain.gcdA z (m : GaussianInt) +
            (m : GaussianInt) * EuclideanDomain.gcdB z (m : GaussianInt) :=
              EuclideanDomain.gcd_eq_gcd_ab _ _
        _ = _ := by simp only [mul_add, ← mul_assoc, ← hz', ← hm']
    apply isUnit_of_dvd_one
    rw [hbez]
    exact dvd_add ((EuclideanDomain.gcd_dvd_left z' m').mul_right _)
      ((EuclideanDomain.gcd_dvd_right z' m').mul_right _)
  rcases hπ_prime.dvd_or_dvd hπ_dvd_prod with hπz' | hπsz'
  · exact hπ_irr.1 (isUnit_of_dvd_unit (EuclideanDomain.dvd_gcd hπz' hπ_dvd_m') hcop_zm)
  · have hstar_dvd_z' : star π ∣ z' := by
      rcases hπsz' with ⟨q, hq⟩
      exact ⟨star q, by simpa [star_mul, star_star, mul_comm] using congr_arg star hq⟩
    exact hstar_nu (isUnit_of_dvd_unit (EuclideanDomain.dvd_gcd hstar_dvd_z' hstar_dvd_m') hcop_zm)

/-- Multiplicativity of `r₂⁺` on coprime positive integers. -/
theorem r2Pos_mul_of_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : m.Coprime n) :
    r2Pos (m * n) = r2Pos m * r2Pos n := by
  rw [← card_posQuadFinset (m * n), ← card_posQuadFinset m, ← card_posQuadFinset n]
  have hbij :
      Finset.card (posQuadFinset m ×ˢ posQuadFinset n) = Finset.card (posQuadFinset (m * n)) := by
    refine Finset.card_bij (fun p _ => canonQuad (p.1 * p.2)) ?_ ?_ ?_
    · rintro ⟨z₁, z₂⟩ hp
      rw [Finset.mem_product, mem_posQuadFinset, mem_posQuadFinset] at hp
      rcases hp with ⟨⟨hq1, hn1⟩, ⟨hq2, hn2⟩⟩
      have h10 : z₁ ≠ 0 := fun h0 => by rw [h0] at hq1; simp [inFirstQuad] at hq1
      have h20 : z₂ ≠ 0 := fun h0 => by rw [h0] at hq2; simp [inFirstQuad] at hq2
      have hmul_ne : z₁ * z₂ ≠ 0 := mul_ne_zero h10 h20
      rw [mem_posQuadFinset]
      refine ⟨canonQuad_inFirstQuad hmul_ne, ?_⟩
      have hnorm : (z₁ * z₂).norm = ((m * n : ℕ) : ℤ) := by
        rw [Zsqrtd.norm_mul, hn1, hn2]; push_cast; ring
      have hnat : (canonQuad (z₁ * z₂)).norm.natAbs = m * n := by
        rw [canonQuad_norm_natAbs]
        simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hnorm
      rw [← GaussianInt.abs_natCast_norm, hnat]
    · rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
      rw [Finset.mem_product, mem_posQuadFinset, mem_posQuadFinset] at h1 h2
      rcases h1 with ⟨⟨ha1q, ha1n⟩, ⟨hb1q, hb1n⟩⟩
      rcases h2 with ⟨⟨ha2q, ha2n⟩, ⟨hb2q, hb2n⟩⟩
      have ha1_ne : a₁ ≠ 0 := fun h => by rw [h] at ha1q; simp [inFirstQuad] at ha1q
      have hb1_ne : b₁ ≠ 0 := fun h => by rw [h] at hb1q; simp [inFirstQuad] at hb1q
      have ha2_ne : a₂ ≠ 0 := fun h => by rw [h] at ha2q; simp [inFirstQuad] at ha2q
      have hb2_ne : b₂ ≠ 0 := fun h => by rw [h] at hb2q; simp [inFirstQuad] at hb2q
      rw [canonQuad_eq_iff (mul_ne_zero ha1_ne hb1_ne) (mul_ne_zero ha2_ne hb2_ne)] at heq
      have hcop_mn : IsCoprime (m : GaussianInt) (n : GaussianInt) := isCoprime_natCast_gi hcop
      have ha1_dvd_m : a₁ ∣ (m : GaussianInt) := ⟨star a₁, by
        have h := mul_star_eq_norm a₁
        rw [ha1n] at h
        exact h.symm⟩
      have hb2_dvd_n : b₂ ∣ (n : GaussianInt) := ⟨star b₂, by
        have h := mul_star_eq_norm b₂
        rw [hb2n] at h
        exact h.symm⟩
      have ha2_dvd_m : a₂ ∣ (m : GaussianInt) := ⟨star a₂, by
        have h := mul_star_eq_norm a₂
        rw [ha2n] at h
        exact h.symm⟩
      have hb1_dvd_n : b₁ ∣ (n : GaussianInt) := ⟨star b₁, by
        have h := mul_star_eq_norm b₁
        rw [hb1n] at h
        exact h.symm⟩
      have hcop12 : IsCoprime a₁ b₂ :=
        (hcop_mn.of_isCoprime_of_dvd_left ha1_dvd_m).of_isCoprime_of_dvd_right hb2_dvd_n
      have hcop21 : IsCoprime a₂ b₁ :=
        (hcop_mn.of_isCoprime_of_dvd_left ha2_dvd_m).of_isCoprime_of_dvd_right hb1_dvd_n
      have hd12 : a₁ ∣ a₂ := by
        rcases heq with ⟨u, hu⟩
        have hd : a₁ ∣ a₂ * b₂ := ⟨b₁ * (u : GaussianInt), by rw [← hu]; ring⟩
        exact hcop12.dvd_of_dvd_mul_right hd
      have hd21 : a₂ ∣ a₁ := by
        rcases heq.symm with ⟨u, hu⟩
        have hd : a₂ ∣ a₁ * b₁ := ⟨b₂ * (u : GaussianInt), by rw [← hu]; ring⟩
        exact hcop21.dvd_of_dvd_mul_right hd
      have ha_eq : a₁ = a₂ :=
        eq_of_associated_of_inFirstQuad ha1q ha2q (associated_of_dvd_dvd hd12 hd21)
      subst ha_eq
      have hb_ass : Associated b₁ b₂ := associated_mul_left_cancel ha1_ne heq
      have hb_eq : b₁ = b₂ := eq_of_associated_of_inFirstQuad hb1q hb2q hb_ass
      exact Prod.ext rfl hb_eq
    · intro z hz
      rw [mem_posQuadFinset] at hz
      rcases hz with ⟨hzq, hzn⟩
      have hz_ne : z ≠ 0 := fun h => by rw [h] at hzq; simp [inFirstQuad] at hzq
      have hzna : z.norm.natAbs = m * n :=
        by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hzn
      let d := EuclideanDomain.gcd z (m : GaussianInt)
      let e := EuclideanDomain.gcd z (n : GaussianInt)
      have hd_norm : d.norm.natAbs = m := gcd_norm_eq_of_coprime hm hn hcop hzna
      have he_norm : e.norm.natAbs = n :=
        gcd_norm_eq_of_coprime hn hm hcop.symm (by simpa [mul_comm] using hzna)
      have hd_ne : d ≠ 0 := by
        intro h0
        have : (0 : ℕ) = m := by simpa [d, h0] using hd_norm
        omega
      have he_ne : e ≠ 0 := by
        intro h0
        have : (0 : ℕ) = n := by simpa [e, h0] using he_norm
        omega
      let a := canonQuad d
      let b := canonQuad e
      have ha_mem : a ∈ posQuadFinset m := by
        rw [mem_posQuadFinset]
        refine ⟨canonQuad_inFirstQuad hd_ne, ?_⟩
        rw [← GaussianInt.abs_natCast_norm]
        exact_mod_cast (by simpa [canonQuad_norm_natAbs] using hd_norm :
          (canonQuad d).norm.natAbs = m)
      have hb_mem : b ∈ posQuadFinset n := by
        rw [mem_posQuadFinset]
        refine ⟨canonQuad_inFirstQuad he_ne, ?_⟩
        rw [← GaussianInt.abs_natCast_norm]
        exact_mod_cast (by simpa [canonQuad_norm_natAbs] using he_norm :
          (canonQuad e).norm.natAbs = n)
      refine ⟨(a, b), Finset.mem_product.mpr ⟨ha_mem, hb_mem⟩, ?_⟩
      have hcop_mn : IsCoprime (m : GaussianInt) (n : GaussianInt) := isCoprime_natCast_gi hcop
      have hcop_de : IsCoprime d e :=
        (hcop_mn.of_isCoprime_of_dvd_left (EuclideanDomain.gcd_dvd_right z _)).of_isCoprime_of_dvd_right
          (EuclideanDomain.gcd_dvd_right z _)
      have hde_dvd_z : d * e ∣ z :=
        hcop_de.mul_dvd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
      rcases hde_dvd_z with ⟨w, hw⟩
      have hw_norm : w.norm.natAbs = 1 := by
        have hnorm := congr_arg Zsqrtd.norm hw
        rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul] at hnorm
        have hna : (z.norm.natAbs : ℤ) = ((d.norm.natAbs * e.norm.natAbs * w.norm.natAbs : ℕ) : ℤ) := by
          simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, zero_add, pow_one] using hnorm
        have hnat := Int.ofNat.inj hna
        rw [hzna, hd_norm, he_norm] at hnat
        have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
        nlinarith
      have hwu : IsUnit w := by
        rw [isUnit_iff_norm_eq_one, ← GaussianInt.abs_natCast_norm]
        exact_mod_cast hw_norm
      rcases hwu with ⟨u, rfl⟩
      have hass_de : Associated (d * e) z := ⟨u, hw.symm⟩
      have hass_ab : Associated (a * b) z :=
        (Associated.mul_mul canonQuad_associated canonQuad_associated).trans hass_de
      have hself := canonQuad_eq_self hzq
      rw [← hself]
      exact (canonQuad_eq_iff (mul_ne_zero (canonQuad_ne_zero hd_ne) (canonQuad_ne_zero he_ne))
        hz_ne).mpr hass_ab
  simpa [Finset.card_product, eq_comm] using hbij

/-- Prime-power value for `p = 2`: `r₂⁺(2 ^ k) = 1`. -/
theorem r2Pos_two_pow (k : ℕ) : r2Pos (2 ^ k) = 1 := by
  let π₂ : GaussianInt := ⟨1, 1⟩
  have hπ₂_norm : π₂.norm = 2 := by simp [π₂, norm_eq_sq_add_sq]
  have hπ₂_irr : Irreducible π₂ := by
    refine ⟨?_, fun a b hab => ?_⟩
    · rw [isUnit_iff_norm_eq_one, hπ₂_norm]; norm_num
    · have hn := congr_arg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul, hπ₂_norm] at hn
      have ha0 : 0 ≤ a.norm := GaussianInt.norm_nonneg a
      have hb0 : 0 ≤ b.norm := GaussianInt.norm_nonneg b
      have hne0 : b.norm ≠ 0 := fun h0 => by rw [h0, mul_zero] at hn; omega
      have hne1 : a.norm ≠ 0 := fun h0 => by rw [h0, zero_mul] at hn; omega
      have ha1_ge : 1 ≤ a.norm := by omega
      have hb1_ge : 1 ≤ b.norm := by omega
      have ha_le : a.norm ≤ 2 := by nlinarith
      have hb_le : b.norm ≤ 2 := by nlinarith
      have hcases : a.norm = 1 ∨ b.norm = 1 := by
        rcases (show a.norm = 1 ∨ a.norm = 2 by omega) with ha1 | ha2
        · left; exact ha1
        · right; rw [ha2] at hn; omega
      rcases hcases with ha1 | hb1
      · left; exact (isUnit_iff_norm_eq_one _).mpr ha1
      · right; exact (isUnit_iff_norm_eq_one _).mpr hb1
  have hπ₂_prime : Prime π₂ := irreducible_iff_prime.mp hπ₂_irr
  have hπ_dvd_star : π₂ ∣ star π₂ := ⟨⟨0, -1⟩, by ext <;> simp [π₂]⟩
  have hex_unique : ∀ (m : ℕ) (z : GaussianInt), z.norm = (2 ^ m : ℕ) → Associated z (π₂ ^ m) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      simp only [pow_zero, Nat.cast_one] at hz ⊢
      exact associated_one_iff_isUnit.mpr ((isUnit_iff_norm_eq_one z).mpr hz)
    | succ m ih =>
      intro z hz
      have h2dvd : (2 : GaussianInt) ∣ z * star z := by
        rw [mul_star_eq_norm, hz]
        refine ⟨(2 ^ m : GaussianInt), ?_⟩
        push_cast; ring
      have hπ_dvd_two : π₂ ∣ (2 : GaussianInt) := ⟨star π₂, by rw [mul_star_eq_norm, hπ₂_norm]; rfl⟩
      have hπ_dvd_prod : π₂ ∣ z * star z := hπ_dvd_two.trans h2dvd
      have hπ_dvd_z : π₂ ∣ z := by
        rcases hπ₂_prime.dvd_or_dvd hπ_dvd_prod with hz_dvd | hsz_dvd
        · exact hz_dvd
        · have hstar_dvd : star π₂ ∣ z := by
            rcases hsz_dvd with ⟨q, hq⟩
            exact ⟨star q, by simpa [star_mul, star_star, mul_comm] using congr_arg star hq⟩
          exact hπ_dvd_star.trans hstar_dvd
      rcases hπ_dvd_z with ⟨w, rfl⟩
      have hw_norm : w.norm = (2 ^ m : ℕ) := by
        have hnorm := Zsqrtd.norm_mul π₂ w
        rw [hz, hπ₂_norm] at hnorm
        have hpow : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 * (2 ^ m : ℕ) := by push_cast; ring
        rw [hpow] at hnorm
        linarith
      have hass : Associated w (π₂ ^ m) := ih w hw_norm
      simpa [pow_succ'] using Associated.mul_mul (Associated.refl π₂) hass
  rw [← card_posQuadFinset, Finset.card_eq_one]
  have hπ₂_ne : π₂ ≠ 0 := fun h => by rw [Zsqrtd.ext_iff] at h; norm_num [π₂] at h
  have hpk_ne : π₂ ^ k ≠ 0 := pow_ne_zero k hπ₂_ne
  refine ⟨canonQuad (π₂ ^ k), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩⟩
  · rw [mem_posQuadFinset]
    refine ⟨canonQuad_inFirstQuad hpk_ne, ?_⟩
    have hnorm : (π₂ ^ k).norm = (2 ^ k : ℕ) := by
      rw [norm_pow_gi, hπ₂_norm]; norm_cast
    have hna : (canonQuad (π₂ ^ k)).norm.natAbs = 2 ^ k := by
      rw [canonQuad_norm_natAbs]
      simpa using congrArg Int.natAbs hnorm
    rw [← GaussianInt.abs_natCast_norm, hna]
  · rw [mem_posQuadFinset] at hz
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simpa [inFirstQuad] using hz.1
    have hself := canonQuad_eq_self hz.1
    rw [← hself]
    exact (canonQuad_eq_iff hz_ne hpk_ne).mpr (hex_unique k z hz.2)

/-- Prime-power value for `p ≡ 3 (mod 4)`: `r₂⁺(p ^ k) = 1` if `Even k`, else `0`. -/
theorem r2Pos_prime_pow_three_mod_four {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    r2Pos (p ^ k) = if Even k then 1 else 0 := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have hp_prime_gi : Prime (p : GaussianInt) :=
    GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp3
  have hall : ∀ (m : ℕ) (z : GaussianInt), z.norm = (p ^ m : ℕ) →
      Even m ∧ Associated z ((p : GaussianInt) ^ (m / 2)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro z hz
      rcases m with _ | _ | m
      · exact ⟨Even.zero, associated_one_iff_isUnit.mpr ((isUnit_iff_norm_eq_one z).mpr (by simpa using hz))⟩
      · exfalso
        have hp_dvd_prod : (p : GaussianInt) ∣ z * star z := by
          rw [mul_star_eq_norm, hz]; simp
        have hp_dvd_z : (p : GaussianInt) ∣ z := by
          rcases hp_prime_gi.dvd_or_dvd hp_dvd_prod with hz_dvd | hsz_dvd
          · exact hz_dvd
          · rcases hsz_dvd with ⟨q, hq⟩
            exact ⟨star q, by simpa [star_mul, star_natCast, star_star, mul_comm] using congr_arg star hq⟩
        rcases hp_dvd_z with ⟨w, rfl⟩
        have hnorm := Zsqrtd.norm_mul (p : GaussianInt) w
        rw [hz, natCast_norm_eq] at hnorm
        have hna : (p : ℤ) = ((p ^ 2 * w.norm.natAbs : ℕ) : ℤ) := by
          simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, zero_add, pow_one] using hnorm
        have hnat := Int.ofNat.inj hna
        have hp2 : 2 ≤ p := hp.two_le
        have hw1 : w.norm.natAbs ≠ 0 := fun h0 => by rw [h0, mul_zero] at hnat; exact hp.ne_zero hnat
        nlinarith [Nat.pos_of_ne_zero hw1]
      · have hp_dvd_prod : (p : GaussianInt) ∣ z * star z := by
          rw [mul_star_eq_norm, hz]
          refine ⟨(p ^ (m + 1) : GaussianInt), ?_⟩
          push_cast; ring
        have hp_dvd_z : (p : GaussianInt) ∣ z := by
          rcases hp_prime_gi.dvd_or_dvd hp_dvd_prod with hz_dvd | hsz_dvd
          · exact hz_dvd
          · rcases hsz_dvd with ⟨q, hq⟩
            exact ⟨star q, by simpa [star_mul, star_natCast, star_star, mul_comm] using congr_arg star hq⟩
        rcases hp_dvd_z with ⟨w, rfl⟩
        have hnorm := Zsqrtd.norm_mul (p : GaussianInt) w
        rw [hz, natCast_norm_eq] at hnorm
        have hw_norm : w.norm = (p ^ m : ℕ) := by
          have hp2 : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
          have hpow : ((p ^ (m + 2) : ℕ) : ℤ) = (p : ℤ) ^ 2 * (p ^ m : ℕ) := by
            push_cast; ring
          rw [hpow] at hnorm
          exact mul_left_cancel₀ hp2 hnorm.symm
        obtain ⟨hm_even, hw_ass⟩ := ih m (by omega) w hw_norm
        refine ⟨by rw [Nat.even_add]; simp [hm_even], ?_⟩
        have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
        rw [hdiv, pow_succ']
        exact Associated.mul_mul (Associated.refl (p : GaussianInt)) hw_ass
  rw [← card_posQuadFinset]
  split_ifs with hk
  · rw [Finset.card_eq_one]
    have hp_ne : (p : GaussianInt) ≠ 0 := by
      intro h0
      have hm0 : ((p : GaussianInt).re : ℤ) = 0 := by rw [h0]; rfl
      rw [natCast_re_gi] at hm0
      exact hp.ne_zero (by omega)
    have hpk_ne : (p : GaussianInt) ^ (k / 2) ≠ 0 := pow_ne_zero _ hp_ne
    refine ⟨canonQuad ((p : GaussianInt) ^ (k / 2)), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩⟩
    · rw [mem_posQuadFinset]
      refine ⟨canonQuad_inFirstQuad hpk_ne, ?_⟩
      have hnorm : ((p : GaussianInt) ^ (k / 2)).norm = (p ^ k : ℕ) := by
        rw [norm_pow_gi, natCast_norm_eq]
        push_cast
        rw [← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp hk)]
      have hna : (canonQuad ((p : GaussianInt) ^ (k / 2))).norm.natAbs = p ^ k := by
        rw [canonQuad_norm_natAbs]
        simpa using congrArg Int.natAbs hnorm
      rw [← GaussianInt.abs_natCast_norm, hna]
    · rw [mem_posQuadFinset] at hz
      have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simpa [inFirstQuad] using hz.1
      have hself := canonQuad_eq_self hz.1
      rw [← hself]
      exact (canonQuad_eq_iff hz_ne hpk_ne).mpr (hall k z hz.2).2
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_posQuadFinset] at hz
    exact hk (hall k z hz.2).1

/-- Prime-power value for `p ≡ 1 (mod 4)`: `r₂⁺(p ^ k) = k + 1`. -/
theorem r2Pos_prime_pow_one_mod_four {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    r2Pos (p ^ k) = k + 1 := by
  have hex : ∃ a b : ℕ, p = a ^ 2 + b ^ 2 := by
    rw [Nat.eq_sq_add_sq_iff]
    intro q hq _
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).mp
        (Nat.dvd_of_mem_primeFactors hq)
    omega
  rcases hex with ⟨a, b, hab⟩
  let π : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  have hπ_norm : π.norm = (p : ℤ) := by
    rw [norm_eq_sq_add_sq]
    zify at hab
    exact hab.symm
  have hπ_irr : Irreducible π := by
    refine ⟨?_, fun u v huv => ?_⟩
    · rw [isUnit_iff_norm_eq_one, hπ_norm]; exact_mod_cast hp.ne_one
    · have hn := congr_arg Zsqrtd.norm huv
      rw [Zsqrtd.norm_mul, hπ_norm] at hn
      have hna : (p : ℤ) = ((u.norm.natAbs * v.norm.natAbs : ℕ) : ℤ) := by
        simpa only [Nat.cast_mul, Nat.cast_pow, GaussianInt.abs_natCast_norm, pow_one] using hn
      have hnat := Int.ofNat.inj hna
      rcases hp.eq_one_or_self_of_dvd u.norm.natAbs ⟨v.norm.natAbs, hnat⟩ with hu1 | hup
      · left; rw [isUnit_iff_norm_eq_one, ← GaussianInt.abs_natCast_norm]; exact_mod_cast hu1
      · right; rw [isUnit_iff_norm_eq_one, ← GaussianInt.abs_natCast_norm]
        have hv1 : v.norm.natAbs = 1 := by nlinarith [hp.two_le]
        exact_mod_cast hv1
  have hπ_prime : Prime π := irreducible_iff_prime.mp hπ_irr
  have hnot_ass : ¬Associated π (star π) := by
    rintro ⟨u, hu⟩
    have hcases := isUnit_cases u.isUnit
    rcases hcases with h | h | h | h
    · have him := congr_arg Zsqrtd.im hu
      rw [h, mul_one] at him
      change (b : ℤ) = -(b : ℤ) at him
      have hb0 : b = 0 := by omega
      rw [hb0, zero_pow two_ne_zero, add_zero] at hab
      have ha_dvd : a ∣ p := ⟨a, by rw [hab, sq]⟩
      rcases hp.eq_one_or_self_of_dvd a ha_dvd with ha1 | hap
      · rw [ha1] at hab; norm_num at hab; exact hp.ne_one hab
      · rw [hap] at hab; nlinarith [hp.two_le]
    · have hre := congr_arg Zsqrtd.re hu
      rw [h] at hre
      change (a : ℤ) * (-1) + (-1) * (b : ℤ) * 0 = (a : ℤ) at hre
      have ha0 : a = 0 := by omega
      rw [ha0, zero_pow two_ne_zero, zero_add] at hab
      have hb_dvd : b ∣ p := ⟨b, by rw [hab, sq]⟩
      rcases hp.eq_one_or_self_of_dvd b hb_dvd with hb1 | hbp
      · rw [hb1] at hab; norm_num at hab; exact hp.ne_one hab
      · rw [hbp] at hab; nlinarith [hp.two_le]
    · have him := congr_arg Zsqrtd.im hu
      rw [h] at him
      change (a : ℤ) * 1 + (b : ℤ) * 0 = -(b : ℤ) at him
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      rw [ha0, hb0] at hab
      simp at hab
      exact hp.ne_zero hab
    · have hre := congr_arg Zsqrtd.re hu
      rw [h] at hre
      change (a : ℤ) * 0 + (-1) * (b : ℤ) * (-1) = (a : ℤ) at hre
      have hab_eq : a = b := by omega
      rw [hab_eq] at hab
      have heven : p = 2 * (b ^ 2) := by rw [hab]; ring
      have hp2 : p % 2 = 0 := by rw [heven]; omega
      omega
  have hnot_dvd : ¬(π ∣ star π) := by
    intro hdvd
    rcases hdvd with ⟨w, hw⟩
    have hn := congr_arg Zsqrtd.norm hw
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hπ_norm] at hn
    have hnat : p = p * w.norm.natAbs := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hn
    have hw1 : w.norm.natAbs = 1 := by nlinarith [hp.two_le]
    have hwu : IsUnit w := by
      rw [isUnit_iff_norm_eq_one, ← GaussianInt.abs_natCast_norm]
      exact_mod_cast hw1
    rcases hwu with ⟨u, rfl⟩
    exact hnot_ass ⟨u, hw.symm⟩
  have hπ_ne : π ≠ 0 := fun h0 => by rw [h0, Zsqrtd.norm_zero] at hπ_norm; omega
  have hstar_ne : star π ≠ 0 := fun h0 => hπ_ne (by simpa using congr_arg star h0)
  have hex : ∀ (m : ℕ) (z : GaussianInt), z.norm = (p ^ m : ℕ) →
      ∃ j ∈ Finset.range (m + 1), Associated z (π ^ j * star π ^ (m - j)) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [pow_zero, tsub_zero, mul_one]
      exact associated_one_iff_isUnit.mpr ((isUnit_iff_norm_eq_one z).mpr (by simpa using hz))
    | succ m ih =>
      intro z hz
      have hp_dvd_prod : (p : GaussianInt) ∣ z * star z := by
        rw [mul_star_eq_norm, hz]
        refine ⟨(p ^ m : GaussianInt), ?_⟩
        push_cast; ring
      have hπ_dvd_p : π ∣ (p : GaussianInt) := ⟨star π, by rw [mul_star_eq_norm, hπ_norm]; rfl⟩
      rcases hπ_prime.dvd_or_dvd (hπ_dvd_p.trans hp_dvd_prod) with hπz | hπsz
      · rcases hπz with ⟨w, rfl⟩
        have hw_norm : w.norm = (p ^ m : ℕ) := by
          have hnorm := Zsqrtd.norm_mul π w
          rw [hz, hπ_norm] at hnorm
          push_cast at hnorm
          rw [pow_succ'] at hnorm
          have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
          exact mul_left_cancel₀ hp0 hnorm.symm
        obtain ⟨j, hj, hw_ass⟩ := ih w hw_norm
        have hj_lt : j < m + 1 := Finset.mem_range.mp hj
        refine ⟨j + 1, Finset.mem_range.mpr (by omega), ?_⟩
        have hsub : m + 1 - (j + 1) = m - j := by omega
        rw [hsub]
        have hrw := Associated.mul_mul (Associated.refl π) hw_ass
        have hcomm : π * (π ^ j * star π ^ (m - j)) = π ^ (j + 1) * star π ^ (m - j) := by
          rw [pow_succ', mul_assoc]
        rwa [hcomm] at hrw
      · have hstar_dvd_z : star π ∣ z := by
          rcases hπsz with ⟨q, hq⟩
          exact ⟨star q, by simpa [star_mul, star_star, mul_comm] using congr_arg star hq⟩
        rcases hstar_dvd_z with ⟨w, rfl⟩
        have hw_norm : w.norm = (p ^ m : ℕ) := by
          have hnorm := Zsqrtd.norm_mul (star π) w
          rw [hz, Zsqrtd.norm_conj, hπ_norm] at hnorm
          push_cast at hnorm
          rw [pow_succ'] at hnorm
          have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
          exact mul_left_cancel₀ hp0 hnorm.symm
        obtain ⟨j, hj, hw_ass⟩ := ih w hw_norm
        have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
        have hsub : m + 1 - j = (m - j) + 1 := by omega
        rw [hsub, pow_succ]
        have hrw : Associated (star π * w) (star π * (π ^ j * star π ^ (m - j))) :=
          Associated.mul_mul (Associated.refl (star π)) hw_ass
        have hcomm : star π * (π ^ j * star π ^ (m - j)) = π ^ j * (star π ^ (m - j) * star π) := by
          ring
        rwa [hcomm] at hrw
  have hunq : ∀ j₁ j₂, j₁ ≤ k → j₂ ≤ k →
      Associated (π ^ j₁ * star π ^ (k - j₁)) (π ^ j₂ * star π ^ (k - j₂)) → j₁ = j₂ := by
    suffices hlt : ∀ a b, a < b → a ≤ k → b ≤ k →
        ¬Associated (π ^ a * star π ^ (k - a)) (π ^ b * star π ^ (k - b)) by
      intro j₁ j₂ h1 h2 hass
      rcases lt_trichotomy j₁ j₂ with h | rfl | h
      · exact (hlt j₁ j₂ h h1 h2 hass).elim
      · rfl
      · exact (hlt j₂ j₁ h h2 h1 hass.symm).elim
    intro a b hab hak hbk hass
    have hsplit1 : k - a = (k - b) + (b - a) := by omega
    have hsplit2 : b = a + (b - a) := by omega
    have hsplit3 : k - (a + (b - a)) = k - b := by omega
    rw [hsplit1, pow_add] at hass
    conv_rhs at hass => rw [hsplit2, pow_add, hsplit3]
    have hass1 : Associated (π ^ a * star π ^ (k - b) * star π ^ (b - a))
        (π ^ a * star π ^ (k - b) * π ^ (b - a)) := by
      convert hass using 1 <;> ring
    have hne : π ^ a * star π ^ (k - b) ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ_ne) (pow_ne_zero _ hstar_ne)
    have hass2 := associated_mul_left_cancel hne hass1
    have hdvd : π ^ (b - a) ∣ star π ^ (b - a) := hass2.symm.dvd
    have h1 : π ∣ star π ^ (b - a) := (dvd_pow_self π (Nat.sub_ne_zero_of_lt hab)).trans hdvd
    exact hnot_dvd (hπ_prime.dvd_of_dvd_pow h1)
  rw [← card_posQuadFinset]
  have hbij : Finset.card (Finset.range (k + 1)) = Finset.card (posQuadFinset (p ^ k)) := by
    refine Finset.card_bij (fun j _ => canonQuad (π ^ j * star π ^ (k - j))) ?_ ?_ ?_
    · intro j hj
      have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hne : π ^ j * star π ^ (k - j) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_ne) (pow_ne_zero _ hstar_ne)
      rw [mem_posQuadFinset]
      refine ⟨canonQuad_inFirstQuad hne, ?_⟩
      have hnorm : (π ^ j * star π ^ (k - j)).norm = (p ^ k : ℕ) := by
        rw [Zsqrtd.norm_mul, norm_pow_gi, norm_pow_gi, Zsqrtd.norm_conj, hπ_norm]
        push_cast
        rw [← pow_add, Nat.add_sub_of_le hj_le]
      have hna : (canonQuad (π ^ j * star π ^ (k - j))).norm.natAbs = p ^ k := by
        rw [canonQuad_norm_natAbs]
        simpa using congrArg Int.natAbs hnorm
      rw [← GaussianInt.abs_natCast_norm, hna]
    · intro j₁ h1 j₂ h2 heq
      have hj1 : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp h1)
      have hj2 : j₂ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp h2)
      have hne1 : π ^ j₁ * star π ^ (k - j₁) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_ne) (pow_ne_zero _ hstar_ne)
      have hne2 : π ^ j₂ * star π ^ (k - j₂) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_ne) (pow_ne_zero _ hstar_ne)
      rw [canonQuad_eq_iff hne1 hne2] at heq
      exact hunq j₁ j₂ hj1 hj2 heq
    · intro z hz
      rw [mem_posQuadFinset] at hz
      have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simpa [inFirstQuad] using hz.1
      obtain ⟨j, hj, hass⟩ := hex k z hz.2
      have hne : π ^ j * star π ^ (k - j) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_ne) (pow_ne_zero _ hstar_ne)
      refine ⟨j, hj, ?_⟩
      have hself := canonQuad_eq_self hz.1
      rw [← hself]
      exact (canonQuad_eq_iff hne hz_ne).mpr hass.symm
  rw [← hbij, Finset.card_range]

private theorem sum_divisors_chi4_mul_of_coprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, ZMod.χ₄ (d : ℕ) =
      (∑ a ∈ m.divisors, ZMod.χ₄ (a : ℕ)) * (∑ b ∈ n.divisors, ZMod.χ₄ (b : ℕ)) := by
  trans ∑ p ∈ m.divisors ×ˢ n.divisors, ZMod.χ₄ (p.1 : ℕ) * ZMod.χ₄ (p.2 : ℕ)
  · symm
    refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
      exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hp.1.1 hp.2.1, Nat.mul_ne_zero (by omega) (by omega)⟩
    · rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
      rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at h1 h2
      dsimp only at heq
      have ha1_cop_b2 : a₁.Coprime b₂ := (hcop.coprime_dvd_left h1.1.1).coprime_dvd_right h2.2.1
      have ha2_cop_b1 : a₂.Coprime b₁ := (hcop.coprime_dvd_left h2.1.1).coprime_dvd_right h1.2.1
      have ha12 : a₁ ∣ a₂ := ha1_cop_b2.dvd_of_dvd_mul_right ⟨b₁, heq.symm⟩
      have ha21 : a₂ ∣ a₁ := ha2_cop_b1.dvd_of_dvd_mul_right ⟨b₂, heq⟩
      have ha_eq : a₁ = a₂ := Nat.dvd_antisymm ha12 ha21
      subst ha_eq
      have ha1_pos : 0 < a₁ := Nat.pos_of_dvd_of_pos h1.1.1 hm
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left ha1_pos heq)
    · intro d hd
      rw [Nat.mem_divisors] at hd
      have hgcd := hcop.gcd_mul d
      have hd_eq : d = Nat.gcd m d * Nat.gcd n d := by
        rw [Nat.gcd_comm m d, Nat.gcd_comm n d]
        simpa [Nat.gcd_eq_left hd.1] using hgcd
      refine ⟨(Nat.gcd m d, Nat.gcd n d), Finset.mem_product.mpr ⟨?_, ?_⟩, hd_eq.symm⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by omega⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by omega⟩
    · rintro ⟨a, b⟩ _
      push_cast
      exact (ZMod.χ₄.map_mul _ _).symm
  · rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Jacobi's first-quadrant divisor formula:
`r₂⁺(n) = ∑ d ∣ n, χ₄(d)` for every `1 ≤ n`. -/
theorem r2Pos_eq_sum_chi4 {n : ℕ} (hn : 1 ≤ n) :
    (r2Pos n : ℤ) = ∑ d ∈ n.divisors, ZMod.χ₄ (d : ℕ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases eq_or_lt_of_le hn with rfl | hn1
    · rw [r2Pos_one]
      norm_num
    let p : ℕ := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    let k : ℕ := n.factorization p
    have hk_pos : 1 ≤ k := (hp.dvd_iff_one_le_factorization (by omega)).mp (Nat.minFac_dvd n)
    let m : ℕ := n / p ^ k
    have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
    have hn_eq : n = p ^ k * m := (Nat.mul_div_cancel' hpk_dvd).symm
    have hm_pos : 1 ≤ m := by
      have hm0 : m ≠ 0 := by
        intro h0
        have : n = 0 := by rw [hn_eq, h0, mul_zero]
        omega
      exact Nat.pos_of_ne_zero hm0
    have hcop : (p ^ k).Coprime m := by
      refine Nat.Coprime.pow_left k ?_
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      have hpow_dvd : p ^ (k + 1) ∣ n := by
        rw [hn_eq, pow_succ]
        exact Nat.mul_dvd_mul_left (p ^ k) hpm
      have hk1 : k + 1 ≤ n.factorization p :=
        (hp.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
      omega
    have hr2_pk : (r2Pos (p ^ k) : ℤ) = ∑ d ∈ (p ^ k).divisors, ZMod.χ₄ (d : ℕ) := by
      rw [Nat.divisors_prime_pow hp k, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, map_pow]
      have hp4 : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
        rcases hp.eq_two_or_odd with hp2 | hodd
        · left; exact hp2
        · right; omega
      rcases hp4 with hp2 | hp1 | hp3
      · rw [hp2]
        rw [r2Pos_two_pow k]
        simp [Finset.sum_range_succ']
      · rw [r2Pos_prime_pow_one_mod_four hp hp1 k, ZMod.χ₄_nat_one_mod_four hp1]
        simp [Finset.sum_const, Finset.card_range]
      · rw [r2Pos_prime_pow_three_mod_four hp hp3 k, ZMod.χ₄_nat_three_mod_four hp3]
        clear ih hn_eq hpk_dvd hcop
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Finset.sum_range_succ, ← ihk]
          by_cases hk_even : Even k
          · have hk1_odd : ¬Even (k + 1) := by simpa [Nat.even_add_one] using hk_even
            have hpow : (-1 : ℤ) ^ (k + 1) = -1 :=
              (Nat.not_even_iff_odd.mp hk1_odd).neg_one_pow
            simp [hk_even, hk1_odd, hpow]
          · have hk1_even : Even (k + 1) := by simpa [Nat.even_add_one] using hk_even
            have hpow : (-1 : ℤ) ^ (k + 1) = 1 := hk1_even.neg_one_pow
            simp [hk_even, hk1_even, hpow]
    rcases eq_or_lt_of_le hm_pos with hm1 | hm1
    · have hn_eq' : n = p ^ k := by rw [hn_eq, ← hm1, mul_one]
      rw [hn_eq']
      exact hr2_pk
    · have hm_lt : m < n := by
        have hpk_ge : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        nlinarith [hn_eq]
      have ih_m := ih m hm_lt hm_pos
      have hpk_pos : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
      rw [hn_eq, r2Pos_mul_of_coprime hpk_pos hm_pos hcop, Nat.cast_mul, hr2_pk, ih_m,
        sum_divisors_chi4_mul_of_coprime hpk_pos hm_pos hcop]

/-- Jacobi's two-square formula:
`r₂(n) = 4 * ∑ d ∣ n, χ₄(d)` for every `1 ≤ n`. -/
theorem repTwoSquares_eq_four_mul_sum_chi4 {n : ℕ} (hn : 1 ≤ n) :
    (repTwoSquares n : ℤ) = 4 * ∑ d ∈ n.divisors, ZMod.χ₄ (d : ℕ) := by
  rw [repTwoSquares_eq_four_mul_r2Pos hn, Nat.cast_mul, r2Pos_eq_sum_chi4 hn]
  norm_num

/-- Lattice point count via Jacobi's formula:
`R₂(x) = 1 + 4 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∣ n, χ₄(d)` for `0 ≤ x`. -/
theorem gaussCircleCount_eq_one_add_four_sum_chi4 {x : ℝ} (hx : 0 ≤ x) :
    gaussCircleCount x =
      1 + 4 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ℕ) : ℝ) := by
  rw [gaussCircleCount_eq_one_add_sum_repTwoSquares hx, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact_mod_cast repTwoSquares_eq_four_mul_sum_chi4 hn1

/-- Classical Dirichlet/Jacobi floor-sum formula for lattice points in the disk:
`R₂(x) = 1 + 4 * ∑ k ∈ Finset.range (⌊x⌋₊ + 1), (⌊x / (4 k + 1)⌋₊ - ⌊x / (4 k + 3)⌋₊)`
for every `0 ≤ x`. -/
theorem gaussCircleCount_eq_one_add_four_sum_floor_sub {x : ℝ} (hx : 0 ≤ x) :
    gaussCircleCount x =
      1 + 4 * ∑ k ∈ Finset.range (⌊x⌋₊ + 1),
        ((⌊x / (4 * (k : ℝ) + 1)⌋₊ : ℝ) - (⌊x / (4 * (k : ℝ) + 3)⌋₊ : ℝ)) := by
  rw [gaussCircleCount_eq_one_add_four_sum_chi4 hx]
  congr 2
  have hconv :
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
    have hsum := sum_Icc_convolution_eq_sum_sum_div (fun d => (ZMod.χ₄ (d : ℕ) : ℝ))
      (fun _ => (1 : ℝ)) ⌊x⌋₊
    calc
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ℕ) : ℝ)
          = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              LSeries.convolution (fun d => (ZMod.χ₄ (d : ℕ) : ℝ)) (fun _ => (1 : ℝ)) n := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [LSeries.convolution_def]
            symm
            simpa [mul_one] using Nat.sum_divisorsAntidiagonal
              (f := fun d _ => (ZMod.χ₄ (d : ℕ) : ℝ) * (1 : ℝ)) (n := n)
      _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) *
            ∑ _m ∈ Finset.Icc 1 (⌊x⌋₊ / d), (1 : ℝ) := hsum
      _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
            refine Finset.sum_congr rfl fun d hd => ?_
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            rw [← nat_floor_div_nat hx hd1]
            simp
  rw [hconv]
  let N : ℕ := ⌊x⌋₊ + 1
  have hle_ext : ⌊x⌋₊ ≤ 4 * N := by omega
  have hext :
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) =
        ∑ d ∈ Finset.Icc 1 (4 * N), (ZMod.χ₄ (d : ℕ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hle_ext) fun d hd hnd => ?_
    rw [Finset.mem_Icc] at hd hnd
    push Not at hnd
    have hgt : ⌊x⌋₊ < d := hnd hd.1
    have hx_lt : x < (d : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ d := by exact_mod_cast hgt
      linarith [Nat.lt_floor_add_one x]
    have hd_pos_nat : 0 < d := by omega
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos_nat
    have hdiv_lt : x / (d : ℝ) < 1 := (div_lt_one hd_pos).mpr hx_lt
    simp [Nat.floor_eq_zero.mpr hdiv_lt]
  rw [hext]
  have hbij :
      ∑ d ∈ Finset.Icc 1 (4 * N), (ZMod.χ₄ (d : ℕ) : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) =
        ∑ p ∈ Finset.range N ×ˢ Finset.range 4,
          (ZMod.χ₄ ((4 * p.1 + p.2 + 1 : ℕ) : ℕ) : ℝ) *
            (⌊x / ((4 * p.1 + p.2 + 1 : ℕ) : ℝ)⌋₊ : ℝ) := by
    symm
    refine Finset.sum_bij (fun p _ => 4 * p.1 + p.2 + 1) ?_ ?_ ?_ ?_
    · rintro ⟨k, r⟩ hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    · rintro ⟨k1, r1⟩ h1 ⟨k2, r2⟩ h2 heq
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h1 h2
      ext <;> omega
    · intro d hd
      rw [Finset.mem_Icc] at hd
      refine ⟨((d - 1) / 4, (d - 1) % 4), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [Finset.mem_range]; omega
      · rw [Finset.mem_range]; omega
      · dsimp only; omega
    · intro _ _; rfl
  rw [hbij, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : ZMod.χ₄ ((4 * k + 0 + 1 : ℕ) : ℕ) = 1 :=
    ZMod.χ₄_nat_one_mod_four (by omega)
  have h1 : ZMod.χ₄ ((4 * k + 1 + 1 : ℕ) : ℕ) = 0 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (4 * k + 1 + 1) % 2 = 0 by omega]
  have h2 : ZMod.χ₄ ((4 * k + 2 + 1 : ℕ) : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by omega)
  have h3 : ZMod.χ₄ ((4 * k + 3 + 1 : ℕ) : ℕ) = 0 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (4 * k + 3 + 1) % 2 = 0 by omega]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3]
  push_cast
  ring_nf

end JacobiTwoSquares

end AnalyticNumberTheory.DivisorProblems
