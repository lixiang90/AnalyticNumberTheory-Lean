import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.PrimeDistribution.SiegelWalfiszRegion

/-!
# Uniform distribution of primes in arithmetic progressions

A logarithmic zero-free rectangle and a bound on the logarithmic derivative
give a uniform Chebyshev estimate for nonprincipal Dirichlet characters.
-/

noncomputable section

open Complex Filter Set
open scoped Topology ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.PrimeDistribution

/-- On the rectangle of height `exp (sqrt (log x))`, a logarithmic bound for
the logarithmic derivative gives a uniform exponentially decreasing relative
error for a nonprincipal character at half-integer cutoffs. -/
theorem norm_psiChar_halfInteger_le_of_logDeriv_rectangle {d D : ℝ} (hd : 0 < d) (hD : 0 < D) :
    ∃ C > 0, ∃ γ > 0, ∀ (N q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      let x : ℝ := N + 1 / 2
      let y := Real.sqrt (Real.log x)
      Real.exp 16 ≤ x →
      (∀ s : ℂ, 1 - d / y ≤ s.re → s.re ≤ 2 → |s.im| ≤ Real.exp y →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
          ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ D * Real.log x) →
      ‖psiChar x χ‖ ≤ C * x * Real.exp (-γ * y) := by
  let b := min d (1 / 8)
  have hb : 0 < b := lt_min hd (by norm_num)
  obtain ⟨C, hC, herr⟩ := perron_rectangle_error_le_exp hb (min_le_right ..) hD
  refine ⟨C, hC, b / 16, by positivity, fun N q _ χ hχ => ?_⟩
  intro x y hx hreg
  let T := Real.exp y
  let L := Real.log (T + 3)
  let σ := 1 - b / L
  let c := 1 + 1 / Real.log x
  let B := D * L ^ 2
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : 16 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hy2 : y ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hy : 1 ≤ y := by nlinarith [Real.sqrt_nonneg (Real.log x)]
  have hT : 2 ≤ T := by
    have := Real.exp_le_exp.mpr hy
    linarith [Real.exp_one_gt_d9]
  have hyL : y ≤ L := by
    calc y = Real.log T := (Real.log_exp y).symm
         _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have hσ0 : 0 < σ := by
    have hh := (div_le_self hb.le (hy.trans hyL)).trans (min_le_right d (1 / 8))
    dsimp [σ]; linarith
  have hσ1 : σ ≤ 1 := sub_le_self _ (div_nonneg hb.le (by linarith))
  have hc : 1 < c := lt_add_of_pos_right _ (one_div_pos.mpr (by linarith))
  have hc2 : c ≤ 2 := by
    have := div_le_one_of_le₀ (by linarith : 1 ≤ Real.log x) (by linarith)
    dsimp [c]; linarith
  have hleft : 1 - d / y ≤ σ := by
    apply sub_le_sub_left
    exact div_le_div₀ hd.le (min_le_left ..) (by linarith) hyL
  have hB : D * Real.log x ≤ B := by
    rw [← hy2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hyL 2) hD.le
  have hedge (u t : ℝ) (hu : σ ≤ u) (hu' : u ≤ c) (ht : |t| ≤ T) :
      ‖-deriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((u : ℂ) + (t : ℂ) * I)‖ ≤ B := by
    have h := (hreg ((u : ℂ) + (t : ℂ) * I) (by simpa using hleft.trans hu)
      (by simpa using hu'.trans hc2) (by simpa using ht)).2
    simpa [logDeriv, neg_div] using h.trans hB
  have hN : 2 ≤ N := by
    by_contra! h
    have hsmall : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
    have hlarge := Real.add_one_le_exp (16 : ℝ)
    dsimp [x] at hx
    linarith
  have h := norm_psiChar_le_of_rect_zeroFree_sharp hχ hN hσ0 (hσ1.trans hc.le) hc hc2 hT
    (by dsimp [B]; positivity) (by dsimp [B]; positivity)
    (fun s hs => (hreg s (hleft.trans hs.1.1) (hs.1.2.trans hc2) (abs_le.mpr hs.2)).1)
    (fun t ht => hedge σ t le_rfl (hσ1.trans hc.le) (abs_le.mpr ht))
    (fun u hu => hedge u T hu.1 hu.2 (by rw [abs_of_nonneg (by linarith)]))
    (fun u hu => hedge u (-T) hu.1 hu.2 (by rw [abs_neg, abs_of_nonneg (by linarith)]))
  exact h.trans (herr x hx)

/-- Eventual, uniform bounds at half integers suffice for the full real-variable
character estimate. Rounding only affects the allowed logarithmic power
and the constants. -/
private theorem uniform_psiChar_of_halfInteger_bounds
    (hhalf : ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ γ > 0, ∀ᶠ N : ℕ in atTop,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
      let y : ℝ := N + 1 / 2
      (q : ℝ) ≤ Real.log y ^ A → χ ≠ 1 →
      ‖psiChar y χ‖ ≤ C * y * Real.exp (-γ * Real.sqrt (Real.log y))) :
    ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ γ > 0, ∀ (x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → χ ≠ 1 →
      ‖psiChar x χ‖ ≤ C * x * Real.exp (-γ * Real.sqrt (Real.log x)) := by
  intro A hA
  obtain ⟨C, hC, γ, hγ, N₀, hhalf⟩ := (show ∃ C > 0, ∃ γ > 0, ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
    let y : ℝ := N + 1 / 2
    (q : ℝ) ≤ Real.log y ^ (2 * A) → χ ≠ 1 →
    ‖psiChar y χ‖ ≤ C * y * Real.exp (-γ * Real.sqrt (Real.log y)) from by
      obtain ⟨C, hC, γ, hγ, h⟩ := hhalf (2 * A) (by positivity)
      exact ⟨C, hC, γ, hγ, eventually_atTop.mp h⟩)
  let X := max ((N₀ : ℝ) + 1) (Real.exp 4 + 2)
  let D := (Real.log 4 + 4) * Real.exp (γ / 2 * Real.sqrt (Real.log X))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨max (2 * C) D, lt_of_lt_of_le hD (le_max_right ..), γ / 2, by positivity,
    fun x q χ hx hq hqx hχ => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hlarge : X ≤ x
  · let N := ⌊x⌋₊
    let y : ℝ := N + 1 / 2
    have hfloor := Nat.floor_le hx0.le
    have hceil := Nat.lt_floor_add_one x
    change (N : ℝ) ≤ x at hfloor
    change x < (N : ℝ) + 1 at hceil
    have hN : N₀ ≤ N := Nat.le_floor (by linarith [(le_max_left ((N₀ : ℝ) + 1) (Real.exp 4 + 2)).trans hlarge])
    have hy0 : 0 < y := by dsimp [y]; positivity
    have hy4 : 4 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr (by
      dsimp [y]; linarith [(le_max_right ((N₀ : ℝ) + 1) (Real.exp 4 + 2)).trans hlarge])
    have hxy : x ≤ 2 * y := by dsimp [y]; linarith [Nat.cast_nonneg (α := ℝ) N]
    have hyx : y ≤ 2 * x := by dsimp [y]; linarith
    have hlog : Real.log x ≤ 2 * Real.log y := by
      calc _ ≤ Real.log (2 * y) := Real.log_le_log hx0 hxy
           _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
           _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmod : (q : ℝ) ≤ Real.log y ^ (2 * A) := by
      apply hqx.trans
      rw [Real.rpow_mul (by linarith : 0 ≤ Real.log y)]
      exact Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (by
        rw [Real.rpow_two]; nlinarith) hA
    have hroot : Real.sqrt (Real.log x) ≤ 2 * Real.sqrt (Real.log y) := by
      nlinarith [Real.sq_sqrt (Real.log_nonneg (by linarith : 1 ≤ x)),
        Real.sq_sqrt (by linarith : 0 ≤ Real.log y), Real.sqrt_nonneg (Real.log x),
        Real.sqrt_nonneg (Real.log y)]
    have hfloor_y : ⌊y⌋₊ = N := (Nat.floor_eq_iff hy0.le).mpr (by dsimp [y]; constructor <;> linarith)
    have heq : psiChar x χ = psiChar y χ := by simp only [psiChar, hfloor_y, N]
    rw [heq]
    apply (hhalf N hN q χ hq hmod hχ).trans
    have hfac : C * y ≤ max (2 * C) D * x := by
      calc _ ≤ C * (2 * x) := by gcongr
           _ = (2 * C) * x := by ring
           _ ≤ _ := by gcongr; exact le_max_left ..
    exact mul_le_mul hfac (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hroot hγ.le]))
      (Real.exp_pos _).le (by positivity)
  · have hroot := Real.sqrt_le_sqrt (Real.log_le_log hx0 (le_of_not_ge hlarge))
    have hprod : 1 ≤ Real.exp (γ / 2 * Real.sqrt (Real.log X)) *
        Real.exp (-(γ / 2) * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [mul_le_mul_of_nonneg_left hroot hγ.le]
    apply (norm_psiChar_le_const_mul_self hx0.le χ).trans
    calc (Real.log 4 + 4) * x ≤ (Real.log 4 + 4) * x *
            (Real.exp (γ / 2 * Real.sqrt (Real.log X)) * Real.exp (-(γ / 2) * Real.sqrt (Real.log x))) :=
            le_mul_of_one_le_right (by positivity) hprod
         _ = D * x * Real.exp (-(γ / 2) * Real.sqrt (Real.log x)) := by dsimp [D]; ring
         _ ≤ _ := by gcongr; exact le_max_right ..


/-- Uniform Siegel–Walfisz cancellation for nonprincipal Dirichlet characters of
polylogarithmic modulus. -/
theorem norm_psiChar_siegelWalfisz :
    ∀ A : ℝ, 0 ≤ A → ∃ C > 0, ∃ γ > 0, ∀ (x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → χ ≠ 1 →
      ‖psiChar x χ‖ ≤ C * x * Real.exp (-γ * Real.sqrt (Real.log x)) := by
  apply uniform_psiChar_of_halfInteger_bounds
  intro A hA
  obtain ⟨d, hd, _, D, hD, hreg⟩ := siegelWalfisz_logDeriv_rectangle hA
  obtain ⟨C, hC, γ, hγ, hhalf⟩ := norm_psiChar_halfInteger_le_of_logDeriv_rectangle hd hD
  refine ⟨C, hC, γ, hγ, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 16)] with N hN
  intro q χ hq y hqx hχ
  have : NeZero q := ⟨by omega⟩
  have hy : Real.exp 16 ≤ y := by dsimp [y]; linarith
  have hlog : 16 ≤ Real.log y := (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hy)).mpr hy
  exact hhalf N q χ hχ hy (fun s hs hs' ht => hreg (by linarith) hqx hχ hs hs' ht)

/-- **The Siegel–Walfisz theorem.** The estimate is uniform in all reduced
residue classes modulo `q ≤ (log x)^A` for every fixed real `A ≥ 0`. -/
theorem siegelWalfisz : SiegelWalfiszBound :=
  siegelWalfisz_of_character_bounds abs_psi_sub_id_le_exp norm_psiChar_siegelWalfisz

end AnalyticNumberTheory.PrimeDistribution
