import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Logarithmic derivatives in zero-free rectangles

A local Borel–Carathéodory argument bounds the logarithmic derivative on
a smaller rectangle. Its parameters can be used for either Page or
Siegel–Walfisz estimates.
-/

noncomputable section

open Complex AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

/-- Explicit coefficient in the rectangle bound, for a zero-free width
parameter `w`, logarithmic modulus bound `B u` and right-hand bound `Z`. -/
def characterRectangleConstant (w B Z : ℝ) : ℝ :=
  max (4/w+Z) (12/w*(Real.log (816*(1+4/w))+2*(B+1)+1))

/-- A zero-free rectangle at height `exp u + 1` gives an explicit logarithmic
derivative bound at height `exp u` for the same character. -/
theorem logDeriv_LFunction_of_zeroFree_rectangle {B w Cz : ℝ}
    (hw : 0<w) (hw4 : w≤1/4) (hCz : 0<Cz)
    {u : ℝ} (hu : 1≤u) {q : ℕ} [NeZero q] (hqu : Real.log q≤B*u)
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1)
    (hright : ∀ s : ℂ,1<s.re → s.re≤2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖≤1/(s.re-1)+Cz)
    (hstrip : ∀ {z : ℂ},1-w/u≤z.re → |z.im|≤Real.exp u+1 →
      DirichletCharacter.LFunction χ z≠0)
    {s : ℂ} (hre : 1-(w/4)/u≤s.re) (hs2 : s.re≤2) (ht : |s.im|≤Real.exp u) :
    DirichletCharacter.LFunction χ s≠0 ∧
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖≤characterRectangleConstant w B Cz*u^2 := by
  let c₀ := 816 * (1 + 4 / w)
  let c₁ := Real.log c₀ + 2 * (B + 1) + 1
  have hc₀ : 1 ≤ c₀ := by
    dsimp only [c₀]
    have := div_pos (by norm_num : (0 : ℝ) < 4) hw
    linarith
  have hu0 : 0 < u := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  let η := w / (4 * u)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηu : 4 * η * u = w := by dsimp only [η]; field_simp [hu0.ne']
  have hη1 : 4 * η ≤ 1 / 4 := by nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 4*η)]
  have hsre : 1 - η ≤ s.re := by
    simpa only [η, div_div] using hre
  have hwide : 1 - w / u ≤ 1 - η := by rw [show w / u = 4 * η by dsimp only [η]; field_simp [hu0.ne']]; linarith
  refine ⟨hstrip (hwide.trans hsre) (by linarith), ?_⟩
  by_cases hσ : 1 + η ≤ s.re
  · have h1 : 1 < s.re := by linarith
    have hinv : 1 / (s.re - 1) ≤ 1 / η :=
      one_div_le_one_div_of_le hη (by linarith)
    apply (hright s h1 hs2).trans
    calc
      _ ≤ 1 / η + Cz := by linarith
      _ ≤ (4 / w + Cz) * u ^ 2 := by
        rw [show 1 / η = 4 / w * u by dsimp only [η]; field_simp [hu0.ne', hw.ne']]
        have hsq : u ≤ u ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 / w),
          mul_le_mul_of_nonneg_left (by nlinarith : 1 ≤ u ^ 2) hCz.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (s.im : ℂ) * I
    have hzre : z₀.re = 1 + η := by simp [z₀]
    have hzim : z₀.im = s.im := by simp [z₀]
    have hgeo {z : ℂ} (hz : z ∈ Metric.ball z₀ (4 * η)) :
        1 - w / u ≤ z.re ∧ |z.im| ≤ Real.exp u + 1 := by
      have hdist := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at hdist
      have hreal := (Complex.abs_re_le_norm (z-z₀)).trans_lt hdist
      have him := (Complex.abs_im_le_norm (z-z₀)).trans_lt hdist
      rw [Complex.sub_re, hzre] at hreal
      rw [Complex.sub_im, hzim] at him
      constructor
      · rw [show w / u = 4*η by dsimp only [η]; field_simp [hu0.ne']]
        linarith [(abs_lt.mp hreal).1]
      · have htri := abs_add_le (z.im - s.im) s.im
        rw [sub_add_cancel] at htri
        linarith
    have hne : ∀ z ∈ Metric.ball z₀ (4 * η), DirichletCharacter.LFunction χ z ≠ 0 :=
      fun z hz => hstrip (hgeo hz).1 (hgeo hz).2
    have hinv : ‖(DirichletCharacter.LFunction χ z₀)⁻¹‖ ≤ (1 + 4 / w) * u := by
      have h := norm_inv_LFunction_le_one_add_inv χ (show 1 < z₀.re by linarith)
      rw [hzre, add_sub_cancel_left] at h
      rw [show 1 / η = 4 / w * u by dsimp only [η]; field_simp [hu0.ne', hw.ne']] at h
      linarith
    let M := c₀ * ((q : ℝ) * Real.exp u)^2 * u
    have hball : ∀ z ∈ Metric.ball z₀ (4*η),
        ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ z₀‖ ≤ M := by
      intro z hz
      obtain ⟨hzre, hzt⟩ := hgeo hz
      rw [show w / u = 4*η by dsimp only [η]; field_simp [hu0.ne']] at hzre
      have hf := norm_LFunction_re_ge_half_le hχ (show 1/2 ≤ z.re by linarith)
      rw [div_eq_mul_inv, norm_mul]
      have hqfactor : (q : ℝ) + 48 * q^2 + 2 ≤ 51 * q^2 := by nlinarith
      have htfactor : |z.im| + 2 ≤ 4 * Real.exp u := by linarith [Real.one_le_exp hu0.le]
      calc
        _ ≤ ((51 * q^2) * (4 * Real.exp u)^2) * ((1 + 4 / w) * u) := by
          apply mul_le_mul _ hinv (norm_nonneg _) (by positivity)
          exact hf.trans (mul_le_mul hqfactor (pow_le_pow_left₀ (by positivity) htfactor 2)
            (sq_nonneg _) (by positivity))
        _ = M := by dsimp only [M, c₀]; ring
    have hsball : s ∈ Metric.closedBall z₀ (2*η) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have heq : s - z₀ = ((s.re - (1 + η) : ℝ) : ℂ) := by apply Complex.ext <;> simp [z₀]
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hlog : Real.log M ≤ c₁ * u := by
      dsimp only [M]
      rw [Real.log_mul (by positivity : c₀ * ((q:ℝ)*Real.exp u)^2 ≠ 0) hu0.ne',
        Real.log_mul (by linarith : c₀ ≠ 0) (by positivity), Real.log_pow,
        Real.log_mul hq0.ne' (Real.exp_pos _).ne', Real.log_exp]
      dsimp only [c₁]
      norm_num only [Nat.cast_ofNat]
      have hc := mul_le_mul_of_nonneg_right hu (Real.log_nonneg hc₀)
      nlinarith only [hqu, Real.log_le_self hu0.le, hc]
    have hbc := landau_logDeriv_le_of_ne_zero (by positivity : 0 ≤ 2*η)
      (by linarith : 2*η < 4*η) (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
      hne hball hsball
    rw [show 2 * (4*η + 2*η) / (4*η - 2*η)^2 = 12/w*u by dsimp only [η]; field_simp [hu0.ne', hw.ne']; ring] at hbc
    apply hbc.trans
    calc
      _ ≤ (12 / w * u) * (c₁ * u) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (12/w*c₁) * u^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end AnalyticNumberTheory.PrimeDistribution
