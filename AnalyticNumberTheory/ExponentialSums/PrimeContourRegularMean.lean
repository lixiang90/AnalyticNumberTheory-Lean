import AnalyticNumberTheory.ExponentialSums.PrimeContourCriticalNumerator
import AnalyticNumberTheory.DirichletSeries.LogPerronFamilyBounds

/-! # The integrated mean of the regular prime contour on the critical line -/

noncomputable section
open Complex Real Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.ExponentialSums

/-- The regular contour contributes at most an absolute constant times
√x √q (√q + A) (1+log x)³ when q and A² do not exceed x. -/
theorem primeContourRegular_integral_mean :
    ∃ C : ℝ, 0<C ∧ ∀ {q A : ℕ} [NeZero q], 2≤q → 1≤A → ∀ {x : ℝ}, (q : ℝ)≤x →
      ((A*A : ℕ) : ℝ)≤x →
      (∑ χ : DirichletCharacter ℂ q with χ≠1, ‖logPerronIntegral (primeContourRegularPart χ A A) (1/2) x‖) ≤
        C*Real.sqrt x*Real.sqrt q*(Real.sqrt q+A)*(1+Real.log x)^3 := by
  obtain ⟨K,hK,HK⟩ := nonprincipal_critical_perron_means
  refine ⟨4+2*K, by positivity, ?_⟩
  intro q A _ hq hA x hqx hAx
  let s (t : ℝ) := (1/2 : ℂ)+t*I
  let w (t : ℝ) := (‖s t‖^2)⁻¹
  let V (t : ℝ) := nonprincipalCriticalNorm (q := q) (fun χ => χ.LFunction) t / ‖s t‖^2
  let D (t : ℝ) := nonprincipalCriticalNorm (q := q) (fun χ => deriv χ.LFunction) t / ‖s t‖^2
  let L := 1+Real.log x
  let R := Real.sqrt q + A
  let Z := R*Real.sqrt q*L^3
  let S := (univ : Finset (DirichletCharacter ℂ q)).filter (·≠1)
  have hq₁ : (1 : ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hx := hq₁.trans hqx
  have hx₀ := zero_lt_one.trans_le hx
  have hL : 1≤L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  have hR : 0≤R := by dsimp [R]; positivity
  have hlog : 1+Real.log q≤L := add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hq₁) hqx) _
  have hφ : Real.sqrt q.totient ≤ Real.sqrt q := Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.totient_le q))
  have HH := HK (q := q) hq
  have hV : (∫ t : ℝ, V t) ≤ K*Real.sqrt q*L := HH.2.2.1.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hφ hK.le) hlog (by positivity) (by positivity))
  have hD : (∫ t : ℝ, D t) ≤ K*Real.sqrt q*L^2 := HH.2.2.2.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hφ hK.le) (pow_le_pow_left₀ (by positivity) hlog 2) (sq_nonneg _) (by positivity))
  have half : ((1/2 : ℝ) : ℂ)=1/2 := by norm_num
  have hw := vertical_inv_norm_sq_mass (by norm_num : (0 : ℝ)<1/2)
  rw [half] at hw
  have hwv : (∫ t : ℝ, w t) = 2*Real.pi := hw.2.trans (by ring)
  let c := (4*R*L)*Real.sqrt q
  have i₀ : Integrable (fun t => c*w t) := hw.1.const_mul c
  have i₁ : Integrable (fun t => (R*L)*D t) := HH.2.1.const_mul _
  have i₂ : Integrable (fun t => (R*L^2)*V t) := HH.1.const_mul _
  let B (t : ℝ) := c*w t + (R*L)*D t + (R*L^2)*V t
  have hi (χ : DirichletCharacter ℂ q) (hm : χ ∈ S) :
      Integrable (logPerronTrace (primeContourRegularPart χ A A) (1/2) x) :=
    (logSmoothedPsiChar_two_contours hq (mem_filter.mp hm).2 (U := A) hA hx₀).1
  have H := sum_norm_logPerronIntegral_le S (fun χ => primeContourRegularPart χ A A) (1/2) x hi B
    ((i₀.add i₁).add i₂) (fun t => by
      rw [half]
      apply (div_le_div_of_nonneg_right (primeContourRegular_pointwise (q := q) hA hAx t) (sq_nonneg _)).trans_eq
      dsimp only [B,c,w,D,V,s,R,L]
      ring)
  have hInt : (∫ t : ℝ, B t) = c*(2*Real.pi)+(R*L)*(∫ t : ℝ, D t)+(R*L^2)*(∫ t : ℝ, V t) := by
    calc
      _ = (∫ t : ℝ, c*w t + (R*L)*D t)+(∫ t : ℝ, (R*L^2)*V t) := integral_add (i₀.add i₁) i₂
      _ = _ := by rw [integral_add i₀ i₁]; simp only [integral_const_mul, hwv]
  have hc : c ≤ 4*Z := by
    have h3 : L≤L^3 := by
      calc L = L*1 := (mul_one _).symm
           _ ≤ L*L^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) hL₀
           _ = _ := by ring
    calc c = (4*R*Real.sqrt q)*L := by dsimp only [c]; ring
         _ ≤ (4*R*Real.sqrt q)*L^3 := mul_le_mul_of_nonneg_left h3 (by positivity)
         _ = 4*Z := by dsimp only [Z]; ring
  have hp : 1≤2*Real.pi := by linarith only [Real.pi_gt_three]
  have hmass : (∫ t : ℝ, B t) ≤ (2*Real.pi)*(4+2*K)*Z := by
    rw [hInt]
    calc
      _ ≤ (4*Z)*(2*Real.pi)+(R*L)*(K*Real.sqrt q*L^2)+(R*L^2)*(K*Real.sqrt q*L) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc (by positivity)) (mul_le_mul_of_nonneg_left hD (by positivity)))
          (mul_le_mul_of_nonneg_left hV (by positivity))
      _ = (4*Z)*(2*Real.pi)+2*K*Z := by dsimp only [Z]; ring
      _ ≤ (4*Z)*(2*Real.pi)+(2*K*Z)*(2*Real.pi) :=
        add_le_add le_rfl (le_mul_of_one_le_right (by dsimp only [Z]; positivity) hp)
      _ = _ := by ring
  have hexp : Real.exp (1/2*Real.log x) = Real.sqrt x := by
    rw [mul_comm, ← Real.rpow_def_of_pos hx₀, ← Real.sqrt_eq_rpow]
  rw [hexp] at H
  apply H.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*Real.pi)).mpr
  exact (mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg x)).trans_eq (by dsimp only [Z,R,L]; ring)

end AnalyticNumberTheory.ExponentialSums
