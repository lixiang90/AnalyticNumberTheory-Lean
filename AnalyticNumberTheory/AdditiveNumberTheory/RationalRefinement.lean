import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod

/-! # Refining a rational approximation to a linear frequency -/

noncomputable section

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- An approximation of accuracy `1/q²` outside the width `2/x` can be
replaced by a reduced fraction inside that width. The new denominator is
strictly larger than `q/2` and at most `x/q`. -/
theorem exists_narrow_rational_approximation {α x : ℝ} {q : ℕ} {a : ℤ}
    (hx : 0 < x) (hq : 1 ≤ q) (ha : a.natAbs.Coprime q)
    (hclose : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (hwide : 2 < x * |α - (a : ℝ) / q|) :
    ∃ (b : ℤ) (r : ℕ), 1 ≤ r ∧ b.natAbs.Coprime r ∧
      (q : ℝ) / 2 < r ∧ (r : ℝ) ≤ x / q ∧ x * |α - (b : ℝ) / r| < 2 := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ := zero_lt_one.trans_le hq₁
  have hsize : 2 * (q : ℝ) ^ 2 < x := by
    have h₁ := mul_lt_mul_of_pos_right hwide (sq_pos_of_pos hq₀)
    have h₂ := mul_le_mul_of_nonneg_left ((le_div_iff₀ (sq_pos_of_pos hq₀)).mp hclose) hx.le
    nlinarith only [h₁, h₂]
  have hQ : 1 ≤ x / q := (le_div_iff₀ hq₀).mpr (by
    nlinarith only [hsize, mul_nonneg hq₀.le (sub_nonneg.mpr hq₁), hq₀.le])
  obtain ⟨b, r, hr, hrQ, hb, happ⟩ := dirichlet_rational_approx_lt α hQ
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hr
  rw [show 1 / ((r : ℝ) * (x / q)) = (q : ℝ) / ((r : ℝ) * x) by field_simp] at happ
  have hprod := (lt_div_iff₀ (mul_pos hr₀ hx)).mp happ
  have hne : (q, a) ≠ (r, b) := by
    intro h
    cases h
    have hu : x * |α - (a : ℝ) / q| < 1 := (mul_lt_mul_iff_of_pos_right hq₀).mp (by
      nlinarith only [hprod])
    linarith
  have hhalf : (q : ℝ) / ((r : ℝ) * x) < 1 / (2 * (q : ℝ) * r) := by
    apply (div_lt_div_iff₀ (mul_pos hr₀ hx) (by positivity)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hsize hr₀]
  have htri : |(a : ℝ)/q - (b : ℝ)/r| ≤ |α - (a : ℝ)/q| + |α - (b : ℝ)/r| := by
    simpa only [abs_sub_comm ((a : ℝ)/q) α] using (abs_sub_le ((a : ℝ)/q) α ((b : ℝ)/r))
  have hgap := ((farey_gap_of_ne hq hr ha hb hne).trans htri).trans_lt
    (add_lt_add_of_le_of_lt hclose (happ.trans hhalf))
  let scale := 2 * (q : ℝ) ^ 2 * r
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hcompare : 2 * (q : ℝ) < 2 * (r : ℝ) + q := by
    calc
      _ = (1 / ((q : ℝ) * r)) * scale := by dsimp [scale]; field_simp
      _ < (1 / (q : ℝ) ^ 2 + 1 / (2 * (q : ℝ) * r)) * scale :=
        mul_lt_mul_of_pos_right hgap hscale
      _ = _ := by dsimp [scale]; field_simp
  refine ⟨b, r, hr, hb, by linarith, hrQ, (mul_lt_mul_iff_of_pos_right hr₀).mp ?_⟩
  nlinarith only [hprod, hcompare]

end AnalyticNumberTheory.AdditiveNumberTheory
