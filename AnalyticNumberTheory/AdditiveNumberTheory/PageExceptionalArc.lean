import AnalyticNumberTheory.AdditiveNumberTheory.PageCharacterExpansion
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachExceptionalMean

/-! # The integral on a major arc of exceptional denominator

The two retained character polynomials have a logarithm-free absolute cubic
moment on the actual arc width. Their Gauss coefficients retain the conductor
saving after the numerators of the reduced fractions are summed.
-/

noncomputable section

open Finset Real MeasureTheory AnalyticNumberTheory.PrimeDistribution AnalyticNumberTheory.DirichletLFunctions
open scoped ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Uniform pointwise error after extracting the two character polynomials
from every arc with denominator at most `M`. -/
def pageArcRemainder (N M : ℕ) (R E : ℝ) : ℝ :=
  (log M/log 2*log N+M*E)*(1+2*Real.pi*N/R)

private theorem three_cubes {u v w : ℝ} (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    (u+v+w)^3≤27*(u^3+v^3+w^3) := by
  let m := max u (max v w)
  have h₁ : u≤m := le_max_left ..
  have h₂ : v≤m := (le_max_left ..).trans (le_max_right ..)
  have h₃ : w≤m := (le_max_right ..).trans (le_max_right ..)
  have h : m^3≤u^3+v^3+w^3 := by
    dsimp [m]
    rcases max_choice u (max v w) with he|he
    · rw [he]; linarith [pow_nonneg hv 3,pow_nonneg hw 3]
    · rw [he]; rcases max_choice v w with h'|h' <;> rw [h'] <;>
        linarith [pow_nonneg hu 3,pow_nonneg hv 3,pow_nonneg hw 3]
  calc _ ≤ (3*m)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
       _ ≤ _ := by nlinarith only [h]

set_option maxHeartbeats 700000 in
/-- Finite, effective upper bound for the absolute integral on one arc whose
denominator is a multiple of the primitive exceptional conductor `d`. -/
theorem page_exceptional_arc_integral {N M q d : ℕ} {K R E : ℝ} (hN : 1≤N)
    (hq : 0<q) (hqM : q≤M) (hMK : (M:ℝ)≤K) (hR : 1≤R) (hNR : (N:ℝ)≤R^2)
    (hd : 0<d) (hdq : d∣q) {ψ : DirichletCharacter ℂ d} (hp : ψ.IsPrimitive)
    (hψ : ψ≠1) (hdata : PagePartialBound N K E ⟨d,ψ⟩) (hE : 0≤E)
    {a : ℕ} (ha : a.Coprime q) :
    ‖∫ α in majorArc q (a:ℤ) R,primeExpSum N α^3*e (-α*N)‖≤
      66150*Real.pi^3*N^2*(sqrt d)^3/(q.totient:ℝ)^3+
        54*(1/(q*R))*(pageArcRemainder N M R E)^3 := by
  let : NeZero q := ⟨hq.ne'⟩
  let χ := ψ.changeLevel hdq
  let χ₁ := (1 : DirichletCharacter ℂ q)
  let S := fun t : ℝ => primeExpSum N ((a:ℝ)/q+t)
  let F := fun ξ : DirichletCharacter ℂ q => characterPrimeSum ξ N
  let g := fun ξ : DirichletCharacter ℂ q => rationalCharacterCoefficient ξ a
  let T := 1/((q:ℝ)*R)
  let W := sqrt d/(q.totient:ℝ)
  let D := pageArcRemainder N M R E
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have hqMr : (q:ℝ)≤M := by exact_mod_cast hqM
  have hqR : R≤q*R := le_mul_of_one_le_left (by linarith) hqr
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1 := (div_le_one (by positivity)).2 (hR.trans hqR)
  have hNT : (N:ℝ)≤(1/T)^2 := by
    rw [show 1/T=q*R by dsimp [T]; simp]
    exact hNR.trans (pow_le_pow_left₀ (by linarith) hqR 2)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hW : 0≤W := by dsimp [W]; positivity
  have hlog : 0≤log N := log_nonneg (by exact_mod_cast hN)
  have hMlog : 0≤log M := log_nonneg (hqr.trans hqMr)
  have hD : 0≤D := by dsimp [D,pageArcRemainder]; positivity
  have hgχ : ‖g χ‖≤W := by
    have h := norm_rationalCharacterCoefficient_le_conductor χ ha
    rwa [show χ.conductor=d from conductor_changeLevel_of_isPrimitive hdq hp] at h
  have hg₁ : ‖g χ₁‖≤W := by
    apply (norm_rationalCharacterCoefficient_le_conductor χ₁ ha).trans
    apply div_le_div_of_nonneg_right _ hφ.le
    dsimp only [χ₁]
    rw [DirichletCharacter.conductor_one,Nat.cast_one,sqrt_one]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have happrox (t : ℝ) (ht : |t|≤T) :
      ‖S t-g χ₁*F χ₁ t-g χ*F χ t‖≤D := by
    apply (norm_page_shift_sub_two_characters hN (hqMr.trans hMK) hdq hψ hdata hE a t).trans
    have hqlog := Real.log_le_log (by linarith : 0<(q:ℝ)) hqMr
    have hqφ : (q.totient:ℝ)≤M := by exact_mod_cast (Nat.totient_le q).trans hqM
    have htR := ht.trans (one_div_le_one_div_of_le (by linarith : 0<R) hqR)
    dsimp only [D,pageArcRemainder]
    apply mul_le_mul (add_le_add (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hqlog (by positivity)) hlog) (mul_le_mul_of_nonneg_right hqφ hE))
      _ (by positivity) (by positivity)
    rw [div_eq_mul_one_div (2*Real.pi*N)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htR (by positivity))
  have hpoint (t : ℝ) (ht : |t|≤T) :
      ‖S t‖^3≤27*(W^3*(‖F χ₁ t‖^3+‖F χ t‖^3)+D^3) := by
    have hh : ‖S t‖≤W*‖F χ₁ t‖+W*‖F χ t‖+D := by
      have he : S t=(g χ₁*F χ₁ t+g χ*F χ t)+(S t-g χ₁*F χ₁ t-g χ*F χ t) := by ring
      calc ‖S t‖ = ‖(g χ₁*F χ₁ t+g χ*F χ t)+(S t-g χ₁*F χ₁ t-g χ*F χ t)‖ := congrArg norm he
           _ ≤ ‖g χ₁*F χ₁ t+g χ*F χ t‖+‖S t-g χ₁*F χ₁ t-g χ*F χ t‖ := norm_add_le _ _
           _ ≤ _ := add_le_add ((norm_add_le _ _).trans (by
               rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hg₁ (norm_nonneg _))
                 (mul_le_mul_of_nonneg_right hgχ (norm_nonneg _)))) (happrox t ht)
    apply (pow_le_pow_left₀ (norm_nonneg _) hh 3).trans
    apply (three_cubes (by positivity) (by positivity) hD).trans_eq
    ring
  have hC (ξ : DirichletCharacter ℂ q) : Continuous (fun t => ‖F ξ t‖^3) :=
    (continuous_characterPrimeSum ξ N).norm.pow 3
  have hM (ξ : DirichletCharacter ℂ q) : (∫ t in (-T)..T, ‖F ξ t‖^3) ≤ 1225*Real.pi^3*N^2 :=
    vonMangoldt_shortArc_mean_cube hT hT1 hNT _ (fun n _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (ξ.norm_le_one _))
  have hlim : -T≤T := by linarith
  have hSC : Continuous S := (continuous_primeExpSum N).comp (continuous_const.add continuous_id)
  rw [setIntegral_majorArc_eq _ hq _ (by linarith : 0<R)]
  push_cast
  apply (intervalIntegral.norm_integral_le_integral_norm hlim).trans
  simp only [norm_mul,norm_e,mul_one,norm_pow]
  change (∫t in (-T)..T,‖S t‖^3)≤_
  calc _ ≤ ∫t in (-T)..T,27*(W^3*(‖F χ₁ t‖^3+‖F χ t‖^3)+D^3) :=
            intervalIntegral.integral_mono_on hlim ((hSC.norm.pow 3).intervalIntegrable ..)
              ((continuous_const.mul ((continuous_const.mul ((hC χ₁).add (hC χ))).add continuous_const)).intervalIntegrable ..)
              (fun t ht => hpoint t (abs_le.mpr ht))
       _ = 27*(W^3*((∫t in (-T)..T,‖F χ₁ t‖^3)+(∫t in (-T)..T,‖F χ t‖^3))+2*T*D^3) := by
            rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
              (f:=fun t => W^3*(‖F χ₁ t‖^3+‖F χ t‖^3)) (g:=fun _ => D^3)
              ((continuous_const.mul ((hC χ₁).add (hC χ))).intervalIntegrable ..) intervalIntegrable_const,
              intervalIntegral.integral_const_mul,intervalIntegral.integral_add ((hC χ₁).intervalIntegrable ..)
              ((hC χ).intervalIntegrable ..),intervalIntegral.integral_const]
            simp only [smul_eq_mul]; ring
       _ ≤ 27*(W^3*(1225*Real.pi^3*N^2+1225*Real.pi^3*N^2)+2*T*D^3) := by gcongr <;> exact hM _
       _ = _ := by dsimp [W,T,D]; ring

end AnalyticNumberTheory.AdditiveNumberTheory
