import AnalyticNumberTheory.PrimeDistribution.CharacterLogDerivRectangle

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
  have hpos : 0<characterRectangleConstant w B Cz :=
    (by positivity : 0<4/w+Cz).trans_le (le_max_left ..)
  refine ⟨w/4,by positivity,by linarith,_,hpos,?_⟩
  intro u hu q _ hqu χ hχ s hre hs₂ ht
  have hlogq := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) hqu
  rw [Real.log_rpow (by linarith)] at hlogq
  exact logDeriv_LFunction_of_zeroFree_rectangle hw hw4 hCz hu
    (hlogq.trans (mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hB)) hχ
    (hright χ) (fun hz him => hstrip hu hqu hχ hz him) hre hs₂ ht

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
