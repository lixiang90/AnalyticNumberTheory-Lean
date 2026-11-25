import AnalyticNumberTheory.RiemannZeta.FourthMomentSharpPolynomial
import AnalyticNumberTheory.RiemannZeta.FourthMomentCriticalIdentity
import AnalyticNumberTheory.AnalyticTools.DyadicLogMoment

/-!
# The cubic logarithmic remainder in the fourth zeta moment

After accounting for the direct and reflected short polynomials and their
squared error, the remaining analytic input is a single cross integral.
Its estimate gives the dyadic fourth moment and then the global moment
with the same leading coefficient and logarithmic error.
-/

noncomputable section
open Real Complex Filter MeasureTheory
open scoped Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- At cutoff T/(4π), the squared approximation error has a cubic
logarithmic bound on each dyadic interval. -/
theorem fourthMomentError_dyadic_mean_sq :
    ∃ K : ℝ,0<K ∧ ∀ {T : ℝ}, 8*π≤T →
      (∫t in T..2*T,‖fourthMomentError ⌊T/(4*π)⌋₊ ((1/2:ℂ)+t*I)‖^2) ≤ K*T*(1+Real.log T)^3 := by
  let δ := 1/(4*π)
  have hd : 0<δ := by dsimp [δ];positivity
  have hd1 : δ≤1 := by dsimp [δ];apply (div_le_one (by positivity)).mpr;linarith [Real.pi_gt_three]
  obtain ⟨K,hK,HK⟩ := zeta_sq_sub_short_mainTerms_mean_sq hd hd1
  refine ⟨K,hK,?_⟩
  intro T hT
  have hδ : δ*T=T/(4*π) := by dsimp [δ];ring
  have h := HK (show 2≤T by linarith [Real.pi_gt_three]) (show 2≤δ*T by
    rw [hδ];exact (le_div_iff₀ (by positivity)).mpr (by linarith))
  simpa only [hδ,fourthMomentError_critical_eq] using h

/-- The dyadic Ingham formula with a cubic logarithmic error follows from
the estimate of the analytic cross integral at the reflected cutoff. -/
theorem fourthMoment_dyadic_sharp_of_crossTerm
    (H : ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      ‖∫t in T..2*T,fourthMomentCrossTerm ⌊T/(4*π)⌋₊ ((1/2:ℂ)+t*I)‖≤C*T*(1+Real.log T)^3) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      |(∫t in T..2*T,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)-
        (1/(2*π^2))*T*(Real.log T)^4|≤C*T*(1+Real.log T)^3 := by
  obtain ⟨D,hD,HD⟩ := H
  obtain ⟨A,hA,HA⟩ := fourthMoment_mainTerms_dyadic_sharp
  obtain ⟨B,hB,HB⟩ := fourthMomentError_dyadic_mean_sq
  refine ⟨A+B+4*D,by positivity,?_⟩
  filter_upwards [HD,eventually_ge_atTop (8*π)] with T hx ht
  let N := ⌊T/(4*π)⌋₊
  let P := ∫t in T..2*T,‖fourthMomentMainTerm N false t+fourthMomentMainTerm N true t‖^2
  let R := ∫t in T..2*T,‖fourthMomentError N ((1/2:ℂ)+t*I)‖^2
  let X := ∫t in T..2*T,fourthMomentCrossTerm N ((1/2:ℂ)+t*I)
  let L := (1+Real.log T)^3
  let M := (1/(2*π^2))*T*(Real.log T)^4
  have hx' : |X.re|≤D*T*L := (Complex.abs_re_le_norm X).trans hx
  have hp : |P-M|≤A*T*L := HA ht
  have hr : R≤B*T*L := HB ht
  have hr₀ : 0≤R := intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun _ _ => sq_nonneg _)
  rw [fourthMoment_integral_energy_identity N T (2*T)]
  change |P+R+4*X.re-M|≤(A+B+4*D)*T*L
  rw [abs_le] at hp hx' ⊢
  have hb₀ : 0≤B*T*L := hr₀.trans hr
  constructor <;> linarith only [hp.1,hp.2,hx'.1,hx'.2,hr₀,hr,hb₀]

/-- The global fourth moment on [0,T] with cubic logarithmic error,
conditional only on the reflected mixed integral estimate. -/
theorem fourthMoment_sharp_of_crossTerm
    (H : ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
      ‖∫t in T..2*T,fourthMomentCrossTerm ⌊T/(4*π)⌋₊ ((1/2:ℂ)+t*I)‖≤C*T*(1+Real.log T)^3) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 2≤T →
      |(∫t in (0:ℝ)..T,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)-
        (1/(2*π^2))*T*(Real.log T)^4|≤C*T*(Real.log T)^3 :=
  fourth_log_moment_of_dyadic (continuous_riemannZeta_half.norm.pow 4) _ (fourthMoment_dyadic_sharp_of_crossTerm H)

end AnalyticNumberTheory.RiemannZeta
