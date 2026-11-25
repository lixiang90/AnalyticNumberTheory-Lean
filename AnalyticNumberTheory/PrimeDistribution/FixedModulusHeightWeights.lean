import AnalyticNumberTheory.PrimeDistribution.FixedModulusPowerWeights

/-! # Reciprocal ordinates in a fixed-modulus zero sum -/

noncomputable section

open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- The reciprocal-ordinate weight removes the height from the three powers in
the fixed-modulus density estimate, at the cost of a factor `1 + log (T + 1)`. -/
theorem fixed_modulus_zero_reciprocal_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x T : ℝ}, 2 ≤ x → 1 ≤ T →
      modulusZeroWeight q T (fun z => x ^ z.re / (1 + |z.im|)) ≤
        C * (Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x) *
          (1 + Real.log x) * (1 + Real.log ((q : ℝ) * (2 * (T + 1)))) ^ 8 *
          (1 + Real.log (T + 1)) := by
  obtain ⟨C, hC, H⟩ := fixed_modulus_zero_power_sum
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ x T hx hT
  let S := modulusZeros q T
  let w (p : Σ _ : DirichletCharacter ℂ q, ℂ) :=
    (characterZeroMultiplicity p.1 p.2 : ℝ) * x ^ p.2.re
  let v (p : Σ _ : DirichletCharacter ℂ q, ℂ) := |p.2.im|
  let M := Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x
  let L := 1 + Real.log ((q : ℝ) * (2 * (T + 1)))
  let A := C * M * (1 + Real.log x) * L ^ 8
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hx₀ : 0 < x := by linarith
  have hxlog := Real.log_nonneg (by linarith : 1 ≤ x)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hw (p) : 0 ≤ w p := by dsimp only [w]; positivity
  have hv (p) (hp : p ∈ S) : 0 ≤ v p ∧ v p ≤ T := by
    obtain ⟨_, _, h₁, h₂, _⟩ := (mem_characterStripZeros p.1).mp (mem_sigma.mp hp).2
    exact ⟨abs_nonneg _, abs_le.mpr ⟨h₁, h₂⟩⟩
  have cumulative (u : ℝ) (hu : 2 ≤ u) (huT : u ≤ 2 * (T + 1)) :
      (∑ p ∈ S with v p ≤ u, w p) ≤ A * u + 0 * Real.sqrt u := by
    have hsub : (S.filter fun p => v p ≤ u) ⊆ modulusZeros q u := by
      intro p hp
      obtain ⟨hp, ht⟩ := mem_filter.mp hp
      obtain ⟨hχ, hz⟩ := mem_sigma.mp hp
      obtain ⟨h₁, h₂, _, _, he⟩ := (mem_characterStripZeros p.1).mp hz
      exact mem_sigma.mpr ⟨hχ, (mem_characterStripZeros p.1).mpr
        ⟨h₁, h₂, (abs_le.mp ht).1, (abs_le.mp ht).2, he⟩⟩
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hw p)).trans ((H hx hu).trans ?_)
    have hu₁ : 1 ≤ u := by linarith
    have hu₀ := zero_lt_one.trans_le hu₁
    have hlogu := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hu₁)
    have hlogs : 1 + Real.log ((q : ℝ) * u) ≤ L :=
      add_le_add_right (Real.log_le_log (mul_pos hq₀ hu₀)
        (mul_le_mul_of_nonneg_left huT hq₀.le)) _
    have hpow : ((q : ℝ) * u) ^ (3/5 : ℝ) ≤ (q : ℝ) ^ (3/5 : ℝ) * u := by
      rw [Real.mul_rpow hq₀.le hu₀.le]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hq₀.le _)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hu₁ (by norm_num : (3/5 : ℝ) ≤ 1)
    have hterms : Real.sqrt x * ((q : ℝ) * u) + x ^ (4/5 : ℝ) * ((q : ℝ) * u) ^ (3/5 : ℝ) + x
        ≤ M * u := by
      dsimp only [M]
      nlinarith only [mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx₀.le (4/5)),
        le_mul_of_one_le_right hx₀.le hu₁]
    have hscale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hterms hC.le)
      (add_nonneg zero_le_one hxlog)
    apply (mul_le_mul hscale (pow_le_pow_left₀ (by linarith) hlogs 8)
      (by positivity) (by positivity)).trans_eq
    dsimp only [A]
    ring
  have hh := reciprocal_height_sum_le S v w hA (le_refl 0) hT hv (fun p _ => hw p) cumulative
  change (∑ p ∈ S, (characterZeroMultiplicity p.1 p.2 : ℝ) * (x ^ p.2.re / (1 + |p.2.im|))) ≤ _
  simp only [← mul_div_assoc]
  exact hh.trans_eq (by dsimp only [A, M, L]; ring)

/-- At height `√x`, every logarithm can be expressed in terms of `x` alone
for moduli up to `x`. Real zeros are included with their full multiplicity. -/
theorem fixed_modulus_zero_weight_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x : ℝ}, 4 ≤ x → (q : ℝ) ≤ x →
      modulusZeroWeight q (Real.sqrt x) (fun z => x ^ z.re / (1 + |z.im|)) ≤
        C * (Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x) *
          (1 + Real.log x) ^ 10 := by
  obtain ⟨C, hC, H⟩ := fixed_modulus_zero_reciprocal_height
  refine ⟨C * 3 ^ 8, by positivity, ?_⟩
  intro q _ x hx hqx
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hs := Real.one_le_sqrt.mpr hx₁
  have hsmall : Real.sqrt x + 1 ≤ x := by
    have he : Real.sqrt x ≤ x/2 := Real.sqrt_le_iff.mpr ⟨by linarith,
      by nlinarith only [mul_nonneg hx₀.le (sub_nonneg.mpr hx)]⟩
    linarith
  have hlog := Real.log_nonneg hx₁
  let L := 1 + Real.log x
  let M := Real.sqrt x * q + x ^ (4/5 : ℝ) * (q : ℝ) ^ (3/5 : ℝ) + x
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hprod : (q : ℝ) * (2 * (Real.sqrt x + 1)) ≤ x ^ 3 := by
    calc
      _ ≤ x * (2 * x) := mul_le_mul hqx (by linarith) (by positivity) hx₀.le
      _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg x) (show 0 ≤ x-2 by linarith)]
  have hbase := one_le_mul_of_one_le_of_one_le hq (show 1 ≤ 2 * (Real.sqrt x + 1) by linarith)
  have hlogprod := Real.log_le_log (zero_lt_one.trans_le hbase) hprod
  rw [Real.log_pow] at hlogprod
  norm_num at hlogprod
  have hlogs : 1 + Real.log ((q : ℝ) * (2 * (Real.sqrt x + 1))) ≤ 3 * L := by
    dsimp only [L]
    linarith
  have hlogsmall : 1 + Real.log (Real.sqrt x + 1) ≤ L :=
    add_le_add_right (Real.log_le_log (by positivity) hsmall) _
  have he := H (q := q) (by linarith : 2 ≤ x) hs
  apply he.trans
  have hp := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg hbase)) hlogs 8
  have hn := add_nonneg zero_le_one (Real.log_nonneg (by linarith : 1 ≤ Real.sqrt x + 1))
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ C * M * L))
    hlogsmall hn (by positivity)).trans_eq
  dsimp only [L, M]
  ring

end AnalyticNumberTheory.PrimeDistribution
