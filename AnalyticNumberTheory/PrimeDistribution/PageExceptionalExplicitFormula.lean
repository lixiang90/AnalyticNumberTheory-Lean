import AnalyticNumberTheory.PrimeDistribution.CharacterSqrtLogRectangle

/-! # A Page-family explicit formula retaining the possible exceptional real zero -/

noncomputable section

open Real Complex AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- For every x ≥ 2 one primitive inducing pair suffices throughout the range
q ≤ exp(κ sqrt(log x)). Every nonprincipal character has an exponentially
small partial sum at all endpoints up to x, apart from the possible explicit
term −(y^β−1)/β of a simple real zero of a character with that inducing pair. -/
theorem page_psi_exceptional_explicit :
    ∃ κ C : ℝ, 0 < κ ∧ κ ≤ 1/4 ∧ 0 < C ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∃ e : Σ m : ℕ, DirichletCharacter ℂ m,
        ∀ {q : ℕ} [NeZero q], (q : ℝ) ≤ Real.exp (κ*Real.sqrt (Real.log x)) →
        ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
          (∀ {y : ℝ}, 1 ≤ y → y ≤ x →
            ‖psiChar y χ‖ ≤ C*x*Real.exp (-(κ/2)*Real.sqrt (Real.log x))) ∨
          ((⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = e ∧
            ∃ β : ℝ, 1/2 ≤ β ∧ β < 1 ∧ IsReal χ ∧ χ.LFunction (β : ℂ) = 0 ∧
              characterZeroMultiplicity χ (β : ℂ) = 1 ∧
              ∀ {y : ℝ}, 1 ≤ y → y ≤ x →
                ‖psiChar y χ + (((y^β-1)/β : ℝ) : ℂ)‖ ≤
                  C*x*Real.exp (-(κ/2)*Real.sqrt (Real.log x))) := by
  obtain ⟨a, ha, H⟩ := nonprincipalDensityFinset_zeroFree_cases
  obtain ⟨b, hb, _, P⟩ := page_nonprincipalDensityFinset_empty
  let κ := min (1/4) (min (a/16) (b/16))
  have hκ : 0 < κ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hκ4 : κ ≤ 1/4 := min_le_left ..
  have hκ1 : κ ≤ 1 := by linarith only [hκ4]
  have hκa : 16*κ ≤ a := by
    have h : κ ≤ a/16 := (min_le_right ..).trans (min_le_left ..)
    linarith only [h]
  have hκb : 16*κ ≤ b := by
    have h : κ ≤ b/16 := (min_le_right ..).trans (min_le_right ..)
    linarith only [h]
  obtain ⟨C, hC, hsum⟩ := nonprincipal_psi_sqrtLog_explicit hκ (by linarith only [hκ4])
  refine ⟨κ, C, hκ, hκ4, hC, ?_⟩
  intro x hx
  let u := Real.sqrt (Real.log x)
  let T := Real.exp (κ*u)
  let σ := 1-2*κ/u
  by_cases hx' : Real.exp 1 ≤ x
  · have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le (by linarith)).mpr hx'
    have hu : 1 ≤ u := Real.one_le_sqrt.mpr hl
    have hu₀ := zero_lt_one.trans_le hu
    have hT₀ : 0 < T := Real.exp_pos _
    obtain ⟨e, _, he⟩ := P (show 2 ≤ T+2 by linarith only [hT₀])
    refine ⟨e, ?_⟩
    intro q _ hq χ hχ
    have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hbnd : 1 - a/Real.log ((q : ℝ)*(T+2)) ≤ σ :=
      sqrtLog_zeroFreeThreshold hκ hκ1 hκa hu hq₁ (hq.trans (by linarith : T ≤ T+4))
    have hpage : 1 - b/Real.log ((T+2+2)*(T+2)) ≤ σ :=
      sqrtLog_zeroFreeThreshold hκ hκ1 hκb hu (by linarith : 1 ≤ T+2+2) (by linarith : T+2+2 ≤ T+4)
    rcases H hχ hT₀.le hbnd with hz | ⟨β, hβ, hσ, hβ1, hr, hz, hm, hset⟩
    · left
      intro y hy hyx
      have h := hsum hx' hq hχ hy hyx
      change ‖psiChar y χ + rightmostPerronZeroSum χ y σ T‖ ≤ _ at h
      simpa only [rightmostPerronZeroSum, hz, Finset.sum_empty, add_zero] using h
    · right
      have hpair : (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = e := by
        by_contra hne
        have hnil := he (hq.trans (by linarith : T ≤ T+2)) hne hpage
        simpa only [hset, Finset.singleton_ne_empty] using hnil
      have hhalf : 1/2 ≤ σ := by
        dsimp only [σ]
        have h := (div_le_iff₀ hu₀).mpr (by linarith only [hκ4,hu] : 2*κ ≤ (1/2)*u)
        linarith only [h]
      refine ⟨hpair, β, hhalf.trans hσ, hβ1, hr, hz, hm, ?_⟩
      intro y hy hyx
      have h := hsum hx' hq hχ hy hyx
      change ‖psiChar y χ + rightmostPerronZeroSum χ y σ T‖ ≤ _ at h
      rwa [rightmostPerronZeroSum_of_singleton hβ hset hm (zero_lt_one.trans_le hy)] at h
  · refine ⟨⟨0, 1⟩, ?_⟩
    intro q _ hq χ hχ
    have h₁ : u ≤ 1 := Real.sqrt_le_one.mpr ((Real.log_le_iff_le_exp (by linarith)).mpr (le_of_not_ge hx'))
    have ht : κ*u ≤ 1 := (mul_le_mul_of_nonneg_left h₁ hκ.le).trans (by simpa using hκ1)
    have hq' : (3:ℝ) ≤ q := by exact_mod_cast three_le_level_of_ne_one hχ
    have h := hq.trans (Real.exp_le_exp.mpr ht)
    linarith only [hq', h, Real.exp_one_lt_d9]

end AnalyticNumberTheory.PrimeDistribution
