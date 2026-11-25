import AnalyticNumberTheory.DirichletLFunctions.ExplicitFormulaHorizontal
import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronContourBound
import AnalyticNumberTheory.PrimeDistribution.PrimitivePerronSignedShifts

/-!
# Uniform finite Perron estimate for primitive characters

The completed L-function carries the zero residues, while the archimedean
factor is moved only to the critical line. The cutoff is common to both
horizontal sides of the contour.
-/

noncomputable section

open Complex Set
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

set_option maxHeartbeats 600000 in
/-- The complex Perron approximation retains the signed sum over the zeros. -/
theorem primitiveSignedPerronContourBound : PrimitiveSignedPerronContourBound := by
  obtain ⟨E,hE,HE⟩ := exists_completed_horizontal_logDeriv_bound
  obtain ⟨D,hD,HD⟩ := norm_completed_logDeriv_left_edge
  obtain ⟨G,hG,HG⟩ := norm_characterGammaLogCorrection_le
  obtain ⟨B,hB,HB⟩ := norm_logDeriv_LFunction_re_gt_one_le
  let C := 12*D+4*E+14*G+6*(1+B)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun {q} hq χ hχ {N c A} hN hc hc' hA => ?_⟩
  let _ : NeZero q := ⟨by omega⟩
  let x := (N:ℝ)+1/2
  let L := 1+Real.log ((q:ℝ)*(A+3))
  let X := (1+1/(c-1))*L
  let Y := Real.sqrt x*L^2
  have hx : 1≤x := by dsimp [x]; linarith [show (2:ℝ)≤N by exact_mod_cast hN]
  have hxp : 0<x := by linarith
  have hq1 : (1:ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hq0 : (0:ℝ)<q := by linarith
  have hL : 1≤L := by
    dsimp [L]
    exact le_add_of_nonneg_right (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 (by linarith)))
  have hLp : 0<L := by linarith
  have hLs : L≤L^2 := by nlinarith [mul_nonneg hLp.le (sub_nonneg.mpr hL)]
  obtain ⟨T,hT,H⟩ := HE hχ hq hA
  refine ⟨T,hT,?_⟩
  let Z := (x^c+1)/T*L^2
  have ht : 0<T := by linarith [hT.1]
  have hl : 0≤Real.log (1+T) := Real.log_nonneg (by linarith)
  have hlog {u : ℝ} (hu : |u|≤T) : 1+Real.log ((q:ℝ)*(|u|+2))≤L := by
    dsimp [L]
    apply add_le_add_right
    exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith only [hu,hT.2] : |u|+2≤A+3) hq0.le)
  have hlog' {u : ℝ} (hu : |u|≤T) : 1+Real.log (|u|+2)≤L := by
    apply le_trans _ (hlog hu)
    apply add_le_add_right
    exact Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hq1)
  have hlogT : Real.log (1+T)≤L := by
    have h1 := hlog' (u:=T) (abs_of_pos ht).le
    have h2 := Real.log_le_log (by linarith : 0<1+T) (by linarith : 1+T≤T+2)
    rw [abs_of_pos ht] at h1
    linarith
  have hDl : 0≤D*L := by positivity
  have hEl : 0≤E*L^2 := by positivity
  have hGl : 0≤G*L := by positivity
  have Hc := completed_perron_signed_shift_bound hχ hq hx hc hc' ht hDl hEl
    (fun t ht' => (HD hχ hq t).trans (mul_le_mul_of_nonneg_left (hlog (abs_le.mpr ht')) hD.le))
    (fun s hl hu hh => H s hl (hu.trans hc') hh)
  have Hγ := archimedean_perron_shift_bound (χ:=χ) hx hc hc' ht hGl
    (fun s hl hu hh => (HG χ hl (hu.trans hc')).trans (mul_le_mul_of_nonneg_left (hlog' hh) hG.le))
  have hrec : 0≤1/(c-1) := by positivity
  have HU := norm_perronVertical_div (F:=logDeriv χ.LFunction) ht.le
      (σ:=c) (by rw [abs_of_pos (by linarith)]; linarith) (show 0≤1/(c-1)+B by positivity)
      (fun t _ => by simpa using HB χ ((c:ℂ)+t*I) (by simpa using hc) (by simp; linarith))
  have HR := norm_twistedPerron_add_le_completed_and_corrections (isPrimitive_ne_one hχ hq) hq hxp hc
    (T:=T) (characterPerronZeroSum χ x T)
  let R := (x^c+1)/T
  have hR : 0≤R := by dsimp [R]; positivity
  have hsx := Real.one_le_sqrt.mpr hx
  have hX : 0≤X := by dsimp [X]; positivity
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have H₁ : 12*(D*L)*Real.log (1+T) ≤ 12*D*Y := by
    dsimp [Y]
    have ha := mul_le_mul_of_nonneg_left hlogT (show 0≤12*(D*L) by positivity)
    nlinarith only [ha,mul_le_mul_of_nonneg_left hsx (show 0≤12*D*L^2 by positivity)]
  have H₂ : 12*Real.sqrt x*(G*L)*Real.log (1+T)≤12*G*Y := by
    dsimp [Y]
    nlinarith only [mul_le_mul_of_nonneg_left hlogT (show 0≤12*Real.sqrt x*(G*L) by positivity)]
  have H₃ : 2*R*(G*L)≤2*G*Z := by
    change 2*R*(G*L)≤2*G*(R*L^2)
    nlinarith only [mul_le_mul_of_nonneg_left hLs (mul_nonneg hR hG.le)]
  have H₄ : 6*(1/(c-1)+B)*Real.log (1+T)≤6*(1+B)*X := by
    dsimp [X]
    have ha := mul_le_mul_of_nonneg_left hlogT (show 0≤6*(1/(c-1)+B) by positivity)
    nlinarith only [ha,hLp.le,mul_nonneg (mul_nonneg hB.le hrec) hLp.le]
  change _≤C*(X+Y+Z)
  have hc₁ : ‖perronVertical (fun s => perronDifferenceWeight x s*logDeriv (DirichletCharacter.completedLFunction χ) s) c T-(2*Real.pi:ℂ)*characterPerronZeroSum χ x T‖
      ≤(12*D)*Y+(4*E)*Z := by
    change _≤12*(D*L)*Real.log (1+T)+4*R*(E*L^2) at Hc
    change _≤(12*D)*Y+(4*E)*(R*L^2)
    linarith only [Hc,H₁]
  have hc₂ : ‖perronVertical (fun s => perronDifferenceWeight x s*characterGammaLogCorrection χ s) c T‖≤
      12*G*Y+2*G*Z := by
    change _≤12*Real.sqrt x*(G*L)*Real.log (1+T)+2*R*(G*L) at Hγ
    linarith only [Hγ,H₂,H₃]
  have htot : _≤6*(1+B)*X+((12*D)+(12*G))*Y+((4*E)+(2*G))*Z :=
    HR.trans (by linarith only [hc₁,hc₂,HU.trans H₄])
  apply htot.trans
  rw [mul_add C (X+Y) Z,mul_add C X Y]
  apply add_le_add (add_le_add (mul_le_mul_of_nonneg_right _ hX)
    (mul_le_mul_of_nonneg_right _ hY)) (mul_le_mul_of_nonneg_right _ hZ)
  all_goals dsimp [C]; linarith only [hB,hD,hG,hE]

/-- Absolute majorant for the regularized zero sum, uniform even in the
presence of a small real zero of a primitive character. -/
theorem norm_characterPerronZeroSum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) {x : ℝ} (hx : 1≤x) (T : ℝ) :
    ‖characterPerronZeroSum χ x T‖ ≤ 32*characterZeroWeight χ T (fun z => x^z.re/(1+|z.im|)) := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mul,Complex.norm_natCast]
  simpa [characterZeroWeight,characterStripZeros,characterZeroMultiplicity,NeZero.ne q] using
    sum_norm_perronDifferenceWeight_le hχ hq hx (-T) T

/-- Uniform half-integer form of the truncated explicit inequality. -/
theorem primitivePerronContourBound : PrimitivePerronContourBound := by
  obtain ⟨C,hC,H⟩ := primitiveSignedPerronContourBound
  refine ⟨C+32,by positivity,fun {q} hq χ hχ {N c A} hN hc hc' hA => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  let x : ℝ := N+1/2
  have hx : 1≤x := by dsimp [x];linarith [show (2:ℝ)≤N by exact_mod_cast hN]
  obtain ⟨T,hT,h⟩ := H hq χ hχ hN hc hc' hA
  refine ⟨T,hT,?_⟩
  let J := dirichletContourIntegral (fun n : ℕ => χ n*(Λ n:ℂ)) x c T
  let z := characterPerronZeroSum χ x T
  let w := characterZeroWeight χ T (fun s => x^s.re/(1+|s.im|))
  let ℓ := 1+Real.log ((q:ℝ)*(A+3))
  let e := (1+1/(c-1))*ℓ+Real.sqrt x*ℓ^2+(x^c+1)/T*ℓ^2
  change ‖J+z‖≤C*e at h
  change ‖J‖≤(C+32)*(e+w)
  have ht : 0<T := by linarith [hT.1]
  have hl : 0≤ℓ := by
    dsimp [ℓ];positivity [Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast (show 1≤q by omega) : (1:ℝ)≤q) (by linarith : 1≤A+3))]
  have he : 0≤e := by dsimp [e];positivity [show 0<x by linarith]
  have hw : 0≤w := Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hz : ‖z‖≤32*w := norm_characterPerronZeroSum_le hχ hq hx T
  have HJ : ‖J‖≤‖J+z‖+‖z‖ := by simpa using norm_sub_le (J+z) z
  nlinarith only [HJ,h,hz,he,mul_nonneg hC.le hw]

end AnalyticNumberTheory.PrimeDistribution
