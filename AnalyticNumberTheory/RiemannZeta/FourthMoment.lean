import AnalyticNumberTheory.RiemannZeta.FourthMomentApproximation
import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.AnalyticTools.DyadicIntegrals

/-!
# An unconditional fourth-moment estimate for the Riemann zeta function

The smoothed approximate functional equation represents the square of
zeta by two divisor polynomials of length `T^(1+η)`, up to a bounded
error. Their mean-square inequality gives the fourth-moment bound
`O(T^(1+ε))` for every positive `ε`.
-/

open Complex Real Filter MeasureTheory Set
open scoped Topology Asymptotics
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.RiemannZeta

/-- The fourth moment on `[T,2T]` is bounded by `C(ε) T^(1+ε)` for every `T ≥ 2`. -/
theorem fourthMoment_riemannZeta_dyadic_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 2 ≤ T →
      (∫ t in T..(2*T), ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤ C*T^(1+ε) := by
  let η := ε/3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B,hB,herr⟩ := norm_zeta_sq_sub_fourthMomentPieces_le hη
  obtain ⟨D,hD,hpoly⟩ := fourthMomentPiece_mean_sq hη
  refine ⟨3*(B^2+2*D), by positivity,?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith
  have hab : T ≤ 2*T := by linarith
  let N := ⌈T^(1+η)⌉₊
  let P := fourthMomentPiece η N false
  let Q := fourthMomentPiece η N true
  let Z (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)
  have hN : (N:ℝ) ≤ 2*T^(1+η) := by
    have hp : 1 ≤ T^(1+η) := Real.one_le_rpow hT1 (by linarith)
    have hceil : (N:ℝ) < T^(1+η)+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hZ : Continuous Z := continuous_riemannZeta_half
  obtain ⟨hP,hp⟩ := hpoly hT hN false
  obtain ⟨hQ,hq⟩ := hpoly hT hN true
  change (∫ t in T..(2*T), ‖P t‖^2) ≤ _ at hp
  change (∫ t in T..(2*T), ‖Q t‖^2) ≤ _ at hq
  have hpoint (t : ℝ) (ht : t ∈ Icc T (2*T)) : ‖Z t‖^4 ≤ 3*(B^2+‖P t‖^2+‖Q t‖^2) := by
    have H := herr hT ht
    change ‖Z t^2-(P t+Q t)‖ ≤ B at H
    have h := norm_sub_norm_le (Z t^2) (P t+Q t)
    rw [norm_pow] at h
    have hbd : ‖Z t‖^2 ≤ B+‖P t‖+‖Q t‖ := by linarith [norm_add_le (P t) (Q t)]
    nlinarith [pow_le_pow_left₀ (sq_nonneg _) hbd 2, sq_nonneg (B-‖P t‖),sq_nonneg (B-‖Q t‖),sq_nonneg (‖P t‖-‖Q t‖)]
  have hi : IntervalIntegrable (fun t => B^2+‖P t‖^2+‖Q t‖^2) volume T (2*T) := (intervalIntegrable_const.add hP).add hQ
  have h := intervalIntegral.integral_mono_on hab ((hZ.norm.pow 4).intervalIntegrable ..) (hi.const_mul 3) hpoint
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (intervalIntegrable_const.add hP) hQ,
    intervalIntegral.integral_add intervalIntegrable_const hP,intervalIntegral.integral_const] at h
  have hTpow : T ≤ T^(1+ε) := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1:ℝ) ≤ 1+ε)
  have hηeq : 1+3*η = 1+ε := by dsimp [η]; ring
  rw [hηeq] at hp hq
  change (∫ t in T..(2*T), ‖Z t‖^4) ≤ _
  apply h.trans
  change 3*((2*T-T)*B^2+(∫ t in T..(2*T), ‖P t‖^2)+(∫ t in T..(2*T), ‖Q t‖^2)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hTpow (sq_nonneg B)]

/-- Global fourth-moment bound with an arbitrarily small exponent loss. -/
theorem fourthMoment_riemannZeta_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤ C*T^(1+ε) := by
  obtain ⟨C,hC,h⟩ := fourthMoment_riemannZeta_dyadic_le hε
  exact integral_from_one_of_dyadic (continuous_riemannZeta_half.norm.pow 4) (fun t => pow_nonneg (norm_nonneg _) 4)
    (by linarith) hC.le (fun _ ht => h ht)

/-- The critical-line fourth moment of the Riemann zeta function is `Oε(T^(1+ε))`. -/
theorem fourthMoment_riemannZeta_isBigO {ε : ℝ} (hε : 0 < ε) :
    (fun T : ℝ => ∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) =O[atTop] (fun T : ℝ => T^(1+ε)) := by
  obtain ⟨C,hC,h⟩ := fourthMoment_riemannZeta_le hε
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg hT (fun t _ => by positivity)),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact h T hT

end AnalyticNumberTheory.RiemannZeta
