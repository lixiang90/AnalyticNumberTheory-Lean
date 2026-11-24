import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-!
# Zero-free rectangles for polylogarithmic moduli

For height `exp u` and modulus at most `u^B`, the classical zero-free region and
Siegel's bound for a possible real exceptional zero give a common zero-free strip
of width proportional to `1/u`. A logarithmic-derivative estimate on a slightly
smaller strip then applies uniformly to all nonprincipal characters.
-/

noncomputable section

open Complex Filter
open scoped Topology
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.PrimeDistribution

private theorem conductor_height_log_le {B u : ℝ} (hB : 0 ≤ B) (hu : 1 ≤ u)
    {q : ℕ} (hq : 0 < q) (hqu : (q : ℝ) ≤ u ^ B)
    {t : ℝ} (ht : |t| ≤ Real.exp u + 1) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤ (B + 4) * u := by
  have hu0 : 0 < u := by linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log q ≤ B * u := by
    have h := Real.log_le_log hqpos hqu
    rw [Real.log_rpow hu0] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hu0.le) hB)
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
  have hlogt : Real.log (|t| + 2) ≤ 4 * u := by
    calc
      _ ≤ Real.log (4 * Real.exp u) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 4 + u := by rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [Real.log_mul hqpos.ne' (by positivity)]
  linarith

/-- A common zero-free strip for all nonprincipal characters of modulus at most `u^B`
up to height `exp u + 1`. The constant may depend ineffectively on `B`. -/
theorem siegelWalfisz_zeroFree_strip {B : ℝ} (hB : 0 ≤ B) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∀ {u : ℝ}, 1 ≤ u → ∀ {q : ℕ} [NeZero q],
      (q : ℝ) ≤ u ^ B → ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ {s : ℂ}, 1 - d / u ≤ s.re → |s.im| ≤ Real.exp u + 1 →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨a, ha, hzfr⟩ := zeroFreeRegion
  let ε := 1 / (B + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨b, hb, hsiegel⟩ := siegel_zero_bound ε hε
  let d := min (a / (B + 4)) (min (b / 2) (1 / 4))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hda : d ≤ a / (B + 4) := min_le_left _ _
  have hdb : d ≤ b / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd4 : d ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d, hd, hd4, ?_⟩
  intro u hu q _ hqu χ hχ s hre ht hzero
  have hu0 : 0 < u := by linarith
  have hqnat := NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqnat
  have hq2 : 2 ≤ q := by
    by_contra! h
    have heq : q = 1 := by omega
    subst q
    exact hχ (Subsingleton.elim _ _)
  have hlog := conductor_height_log_le hB hu hqnat hqu ht
  have hlogpos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by
      calc
        (1 : ℝ) < |s.im| + 2 := by linarith [abs_nonneg s.im]
        _ ≤ (q : ℝ) * (|s.im| + 2) := le_mul_of_one_le_left (by positivity) hq1)
  have hwidth : d / u ≤ a / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    rw [div_le_div_iff₀ hu0 hlogpos]
    calc
      _ ≤ d * ((B + 4) * u) := mul_le_mul_of_nonneg_left hlog hd.le
      _ = (d * (B + 4)) * u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_div_iff₀ (by positivity)).mp hda) hu0.le
  obtain ⟨hr, _, him, _, _, _⟩ := hzfr χ s (.inl hχ) ((sub_le_sub_left hwidth 1).trans hre) hzero
  have hsreal : (s.re : ℂ) = s := Complex.ext rfl (by simpa using him.symm)
  have hzeror : DirichletCharacter.LFunction χ (s.re : ℂ) = 0 := by rw [hsreal]; exact hzero
  have hβ := hsiegel hq2 hr hχ s.re hzeror
  have hpow : (q : ℝ) ^ ε ≤ u := by
    calc
      _ ≤ (u ^ B) ^ ε := Real.rpow_le_rpow (Nat.cast_nonneg _) hqu hε.le
      _ = u ^ (B * ε) := (Real.rpow_mul hu0.le _ _).symm
      _ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (by
        dsimp only [ε]; rw [mul_one_div, div_le_one (by linarith)]; linarith)
      _ = _ := Real.rpow_one _
  have hsep : d / u < b * (q : ℝ) ^ (-ε) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
    exact (div_lt_div_of_pos_right (by linarith : d < b) hu0).trans_le
      (div_le_div_of_nonneg_left hb.le (Real.rpow_pos_of_pos hqpos _) hpow)
  linarith only [hβ, hre, hsep]

/-- Quantitative nonvanishing and a logarithmic-derivative bound up to height `exp u`.
The proof centers a zero-free disk just to the right of one, including at small heights
where a real character can have an exceptional zero outside the larger strip. -/
theorem siegelWalfisz_logDeriv_strip {B : ℝ} (hB : 0 ≤ B) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∃ K > 0, ∀ {u : ℝ}, 1 ≤ u → ∀ {q : ℕ} [NeZero q],
      (q : ℝ) ≤ u ^ B → ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ {s : ℂ}, 1 - d / u ≤ s.re → s.re ≤ 2 → |s.im| ≤ Real.exp u →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ K * u ^ 2 := by
  obtain ⟨w, hw, hw4, hstrip⟩ := siegelWalfisz_zeroFree_strip hB
  obtain ⟨Cz, hCz, hright⟩ := norm_logDeriv_LFunction_re_gt_one_le
  let c₀ := 816 * (1 + 4 / w)
  let c₁ := Real.log c₀ + 2 * (B + 1) + 1
  have hc₀ : 1 ≤ c₀ := by
    dsimp only [c₀]
    have := div_pos (by norm_num : (0 : ℝ) < 4) hw
    linarith
  have hc₁ : 0 < c₁ := by dsimp only [c₁]; linarith [Real.log_nonneg hc₀]
  refine ⟨w / 4, by positivity, by linarith, max (4 / w + Cz) (12 / w * c₁), ?_, ?_⟩
  · exact (mul_pos (by positivity : 0 < 12 / w) hc₁).trans_le (le_max_right _ _)
  intro u hu q _ hqu χ hχ s hre hs2 ht
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
  refine ⟨hstrip hu hqu hχ (hwide.trans hsre) (by linarith), ?_⟩
  by_cases hσ : 1 + η ≤ s.re
  · have h1 : 1 < s.re := by linarith
    have hinv : 1 / (s.re - 1) ≤ 1 / η :=
      one_div_le_one_div_of_le hη (by linarith)
    apply (hright χ s h1 hs2).trans
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
      fun z hz => hstrip hu hqu hχ (hgeo hz).1 (hgeo hz).2
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
    have hlogq := Real.log_le_log hq0 hqu
    rw [Real.log_rpow hu0] at hlogq
    have hlog : Real.log M ≤ c₁ * u := by
      dsimp only [M]
      rw [Real.log_mul (by positivity : c₀ * ((q:ℝ)*Real.exp u)^2 ≠ 0) hu0.ne',
        Real.log_mul (by linarith : c₀ ≠ 0) (by positivity), Real.log_pow,
        Real.log_mul hq0.ne' (Real.exp_pos _).ne', Real.log_exp]
      have hlq := hlogq.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hu0.le) hB)
      dsimp only [c₁]
      norm_num only [Nat.cast_ofNat]
      have hc := mul_le_mul_of_nonneg_right hu (Real.log_nonneg hc₀)
      nlinarith only [hlq, Real.log_le_self hu0.le, hc]
    have hbc := landau_logDeriv_le_of_ne_zero (by positivity : 0 ≤ 2*η)
      (by linarith : 2*η < 4*η) (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
      hne hball hsball
    rw [show 2 * (4*η + 2*η) / (4*η - 2*η)^2 = 12/w*u by dsimp only [η]; field_simp [hu0.ne', hw.ne']; ring] at hbc
    apply hbc.trans
    calc
      _ ≤ (12 / w * u) * (c₁ * u) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (12/w*c₁) * u^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

/-- Siegel–Walfisz rectangle with height `exp (sqrt (log x))`. The same constants
serve all nonprincipal characters with modulus at most `(log x)^A`. -/
theorem siegelWalfisz_logDeriv_rectangle {A : ℝ} (hA : 0 ≤ A) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ ∃ K > 0, ∀ {x : ℝ}, 1 ≤ Real.log x →
      ∀ {q : ℕ} [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
      ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 → ∀ {s : ℂ},
      1 - d / Real.sqrt (Real.log x) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ Real.exp (Real.sqrt (Real.log x)) →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ K * Real.log x := by
  obtain ⟨d, hd, hd4, K, hK, hstrip⟩ := siegelWalfisz_logDeriv_strip (show 0 ≤ 2 * A by positivity)
  refine ⟨d, hd, hd4, K, hK, ?_⟩
  intro x hx q _ hq χ hχ s hs hs₂ ht
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log x)
  have hpow : Real.sqrt (Real.log x) ^ (2 * A) = Real.log x ^ A := by
    rw [Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, hsq]
  have h := hstrip (Real.one_le_sqrt.mpr hx) (hpow ▸ hq) hχ hs hs₂ ht
  rwa [hsq] at h

end AnalyticNumberTheory.PrimeDistribution
