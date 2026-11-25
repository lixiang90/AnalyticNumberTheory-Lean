import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeCharacterMean
import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeCharacterTransfer
import AnalyticNumberTheory.AdditiveNumberTheory.PageExceptionalWeights

/-! # A contour bound for smoothed prime sums at reduced rational frequencies -/

noncomputable section
open Complex Finset Real
open scoped Classical
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- The full character mean, including modulus one. The principal character
is covered by the integrated Chebyshev bound. -/
theorem logSmoothedPsiChar_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {x : ℝ}, (q : ℝ) ≤ x →
      (∑ χ : DirichletCharacter ℂ q, ‖logSmoothedPsiChar χ x‖) ≤
        C * (x*(1+Real.log x)^4 + (x*q)^(3/4 : ℝ)*(1+Real.log x)^3) := by
  obtain ⟨K,hK,H⟩ := logSmoothedPsiChar_nonprincipal_mean
  let c := Real.log 4 + 4
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨K+c, by positivity, ?_⟩
  intro q _ x hqx
  have hq := NeZero.pos q
  have hx : 1 ≤ x := (show (1 : ℝ) ≤ q by exact_mod_cast hq).trans hqx
  have hx₀ := zero_le_one.trans hx
  let L := 1+Real.log x
  let M := x*L^4 + (x*q)^(3/4 : ℝ)*L^3
  have hL : 1 ≤ L := by dsimp [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  have hxM : x ≤ M := (le_mul_of_one_le_right hx₀ (one_le_pow₀ hL (n := 4))).trans
    (le_add_of_nonneg_right (show 0 ≤ (x*q)^(3/4 : ℝ)*L^3 by positivity))
  have hprincipal : ‖logSmoothedPsiChar (1 : DirichletCharacter ℂ q) x‖ ≤ c*M :=
    (norm_logSmoothedPsiChar_le _ hx).trans (mul_le_mul_of_nonneg_left (by linarith only [hxM]) hc.le)
  have hrest : (∑ χ : DirichletCharacter ℂ q with χ ≠ 1, ‖logSmoothedPsiChar χ x‖) ≤ K*M := by
    by_cases h : 2 ≤ q
    · exact H h hqx
    · obtain rfl : q = 1 := by omega
      have he (χ : DirichletCharacter ℂ 1) : χ = 1 := Subsingleton.elim ..
      simpa only [he, ne_self_iff_false, filter_false, sum_empty] using
        (show 0 ≤ K*M from mul_nonneg hK.le (hx₀.trans hxM))
  rw [filter_ne'] at hrest
  rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ q))]
  exact (add_le_add hrest hprincipal).trans_eq (by change K*M+c*M=(K+c)*M; ring)

/-- The contour estimate retaining the exact ratio q/φ(q) in front of the
two terms. This keeps the arithmetic dependence separate from the logarithms
introduced by the analytic estimates. -/
theorem logSmoothedPrimeExpSum_rational_totient :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x : ℝ},
      a.natAbs.Coprime q → (q : ℝ) ≤ x →
      ‖logSmoothedPrimeExpSum x ((a : ℝ)/q)‖ ≤
        C*((q : ℝ)/q.totient)*((x/Real.sqrt q)*(1+Real.log x)^4 + x^(3/4 : ℝ)*(q : ℝ)^(1/4 : ℝ)*(1+Real.log x)^3) := by
  obtain ⟨K,hK,mean⟩ := logSmoothedPsiChar_mean
  let D := 1/Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D+K, by positivity, ?_⟩
  intro q _ a x ha hqx
  let L := 1+Real.log x
  let U := x/Real.sqrt q
  let V := x^(3/4 : ℝ)*(q : ℝ)^(1/4 : ℝ)
  let T := U*L^4 + V*L^3
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq₁
  have hx := hq₁.trans hqx
  have hx₀ := zero_lt_one.trans_le hx
  have hroot := Real.sqrt_pos.mpr hq₀
  have hlog := Real.log_le_log hq₀ hqx
  have hlogx := Real.log_nonneg hx
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hlogx]
  have hL₀ := zero_le_one.trans hL
  have hU : 1 ≤ U := (one_le_div hroot).mpr ((Real.sqrt_le_iff.mpr ⟨hq₀.le, by nlinarith only [mul_nonneg hq₀.le (sub_nonneg.mpr hq₁)]⟩).trans hqx)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfirst : L^3 ≤ T := (pow_le_pow_right₀ hL (by decide : 3 ≤ 4)).trans
    ((le_mul_of_one_le_left (pow_nonneg hL₀ 4) hU).trans (le_add_of_nonneg_right (by positivity : 0 ≤ V*L^3)))
  have herr : (Real.log q/Real.log 2)*(Real.log x)^2/2 ≤ D*T := by
    have hp : Real.log q*(Real.log x)^2 ≤ L*L^2 :=
      mul_le_mul (by dsimp [L]; linarith only [hlog]) (pow_le_pow_left₀ hlogx (by dsimp [L]; linarith) 2)
        (sq_nonneg _) hL₀
    have hp' : Real.log q*(Real.log x)^2 ≤ T := hp.trans ((show L*L^2 = L^3 by ring) ▸ hfirst)
    have hpos := mul_nonneg hD.le (mul_nonneg (Real.log_nonneg hq₁) (sq_nonneg (Real.log x)))
    calc
      _ = D*(Real.log q*(Real.log x)^2)/2 := by dsimp only [D]; ring
      _ ≤ D*(Real.log q*(Real.log x)^2) := half_le_self hpos
      _ ≤ _ := mul_le_mul_of_nonneg_left hp' hD.le
  have hpow : (x*q)^(3/4 : ℝ) = Real.sqrt q * V := by
    dsimp only [V]
    rw [Real.mul_rpow hx₀.le hq₀.le, Real.sqrt_eq_rpow]
    have hz : (q : ℝ)^(3/4 : ℝ) = (q : ℝ)^(1/2 : ℝ) * (q : ℝ)^(1/4 : ℝ) := by
      rw [← Real.rpow_add hq₀]
      norm_num
    rw [hz]
    ring
  have hscale : x*L^4 + (x*q)^(3/4 : ℝ)*L^3 = Real.sqrt q * (U*L^4 + V*L^3) := by
    have hUeq : Real.sqrt q * U = x := mul_div_cancel₀ _ hroot.ne'
    calc
      _ = (Real.sqrt q*U)*L^4 + (Real.sqrt q*V)*L^3 := by rw [hUeq,hpow]
      _ = _ := by ring
  let R := (q : ℝ)/q.totient
  have hφ : (0 : ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hR : 1 ≤ R := (one_le_div hφ).mpr (Nat.cast_le.mpr (Nat.totient_le q))
  have hT := (pow_nonneg hL₀ 3).trans hfirst
  have herr' : (Real.log q/Real.log 2)*(Real.log x)^2/2 ≤ D*R*T := by
    apply herr.trans
    exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hT hR) hD.le).trans_eq (by ring)
  have hsum := mean hqx
  change _ ≤ K*(x*L^4 + (x*q)^(3/4 : ℝ)*L^3) at hsum
  rw [hscale] at hsum
  have hm : (Real.sqrt q/q.totient)*(∑ χ : DirichletCharacter ℂ q, ‖logSmoothedPsiChar χ x‖) ≤ K*R*T := by
    apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ Real.sqrt q/q.totient)).trans_eq
    calc
      _ = ((q : ℝ)/q.totient)*(K*(U*L^4 + V*L^3)) := by
        simp only [div_eq_mul_inv]
        linear_combination (q.totient : ℝ)⁻¹*K*(U*L^4 + V*L^3) * Real.sq_sqrt hq₀.le
      _ = K*R*T := by dsimp only [R,T]; ring
  exact (norm_logSmoothedPrimeExpSum_le_character_mean ha hx).trans
    ((add_le_add herr' hm).trans_eq (by change D*R*T+K*R*T=(D+K)*R*T; ring))

/-- At any reduced rational phase a/q, logarithmic smoothing gives the two
terms x/sqrt(q) times (1+log x)⁵ and x^(3/4) q^(1/4) times (1+log x)⁴.
The absolute constant is uniform for every positive modulus q ≤ x. -/
theorem logSmoothedPrimeExpSum_rational_contour :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x : ℝ},
      a.natAbs.Coprime q → (q : ℝ) ≤ x →
      ‖logSmoothedPrimeExpSum x ((a : ℝ)/q)‖ ≤
        C * ((x/Real.sqrt q)*(1+Real.log x)^5 + x^(3/4 : ℝ)*(q : ℝ)^(1/4 : ℝ)*(1+Real.log x)^4) := by
  obtain ⟨K,hK,H⟩ := logSmoothedPrimeExpSum_rational_totient
  refine ⟨6*K, by positivity,?_⟩
  intro q _ a x ha hqx
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx := hq₁.trans hqx
  have hx₀ := zero_lt_one.trans_le hx
  let L := 1+Real.log x
  let U := x/Real.sqrt q
  let V := x^(3/4 : ℝ)*(q : ℝ)^(1/4 : ℝ)
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hr : (q : ℝ)/q.totient ≤ 6*L := (div_totient_le_six_mul_log (NeZero.pos q)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hq₁) hqx) 1) (by norm_num))
  apply (H ha hqx).trans
  change K*_* (U*L^4+V*L^3) ≤ (6*K)*(U*L^5+V*L^4)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hK.le) (by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.ExponentialSums
