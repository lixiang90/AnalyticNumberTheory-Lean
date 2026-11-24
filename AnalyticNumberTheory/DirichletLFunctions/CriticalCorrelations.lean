import AnalyticNumberTheory.DirichletLFunctions.CriticalMeanSquare

/-!
# Mixed second moments of periodic Dirichlet series

The mixed second moment recovers the average of the two coefficient
sequences over one period. For distinct characters of a fixed modulus
the coefficient orthogonality relation makes the leading term vanish.
-/

open Complex Real Filter MeasureTheory Finset
open scoped Topology

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem LFunction_scale {q : ℕ} [NeZero q] (c : ℂ) (Φ : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun r => c*Φ r) s = c*ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction,mul_assoc,← Finset.mul_sum]
  ring

private theorem LFunction_linear {q : ℕ} [NeZero q] (c : ℂ) (Φ Ψ : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun r => Φ r+c*Ψ r) s = ZMod.LFunction Φ s+c*ZMod.LFunction Ψ s := by
  simp only [ZMod.LFunction,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,mul_add]
  ring

/-- Every complex periodic sequence has a critical-line mean square
whose leading coefficient is its mean square over one period. -/
theorem mean_sq_periodicLFunction {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖^2)/(T*Real.log T))
      atTop (𝓝 (periodicNormMean Φ)) := by
  let A : ℝ := 1+∑ r, ‖Φ r‖
  have hA : 0 < A := by dsimp [A]; positivity
  let Ψ := fun r => ((A:ℂ)⁻¹)*Φ r
  have hΨ (r) : ‖Ψ r‖ ≤ 1 := by
    have hr : ‖Φ r‖ ≤ ∑ j, ‖Φ j‖ := single_le_sum (fun j _ => norm_nonneg (Φ j)) (mem_univ r)
    simp only [Ψ,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le]
    rw [← div_eq_inv_mul,div_le_one hA]
    dsimp [A]; linarith
  have he : Φ = fun r => (A:ℂ)*Ψ r := funext fun r => by
    simp [Ψ,← mul_assoc,Complex.ofReal_ne_zero.mpr hA.ne']
  have h := (mean_sq_periodicLFunction_half Ψ hΨ).const_mul (A^2)
  conv in periodicNormMean Φ => rw [he]
  conv in ZMod.LFunction Φ _ => rw [he]
  simpa only [LFunction_scale,periodicNormMean,norm_mul,Complex.norm_real,Real.norm_of_nonneg hA.le,
    mul_pow,intervalIntegral.integral_const_mul,← Finset.mul_sum,mul_div_assoc] using h

private def fourthRoot (j : Fin 4) : ℂ := ![1,-1,I,-I] j

private theorem polarize (z w : ℂ) :
    (∑ j, fourthRoot j * ((‖z+fourthRoot j*w‖^2 : ℝ):ℂ))/4 = z*star w := by
  have hn (v : ℂ) : ((‖v‖^2:ℝ):ℂ) = v*star v := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp_rw [hn]
  simp [Fin.sum_univ_four,fourthRoot]
  ring_nf
  simp [Complex.I_sq] <;> ring
/-- Mixed critical-line moments recover the complex inner product of the
coefficient sequences over a period, with conjugation in the second factor. -/
theorem mixed_mean_periodicLFunctions {q : ℕ} [NeZero q] (Φ Ψ : ZMod q → ℂ) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T,
      ZMod.LFunction Φ ((1/2:ℂ)+t*I)*star (ZMod.LFunction Ψ ((1/2:ℂ)+t*I)))/
      ((T*Real.log T:ℝ):ℂ)) atTop (𝓝 ((∑ r, Φ r*star (Ψ r))/(q:ℂ))) := by
  let A (j : Fin 4) (r : ZMod q) := Φ r + fourthRoot j * Ψ r
  let V (j : Fin 4) (t : ℝ) : ℂ := ((‖ZMod.LFunction (A j) ((1/2:ℂ)+t*I)‖^2:ℝ):ℂ)
  have hc (j : Fin 4) : Continuous (V j) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : (1/2:ℂ)+(t:ℂ)*I ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num at hh
    have hL := (ZMod.differentiableAt_LFunction (A j) _ (Or.inl hs)).continuousAt.comp
      (f := fun t : ℝ => (1/2:ℂ)+t*I) (by fun_prop)
    exact Complex.continuous_ofReal.continuousAt.comp (hL.norm.pow 2)
  have H (j : Fin 4) : Tendsto (fun T : ℝ => fourthRoot j*((∫ t in (1:ℝ)..T,V j t)/((T*Real.log T:ℝ):ℂ)))
      atTop (𝓝 (fourthRoot j*(periodicNormMean (A j):ℂ))) := by
    apply Filter.Tendsto.const_mul
    simpa only [V,intervalIntegral.integral_ofReal,← Complex.ofReal_div,Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp (mean_sq_periodicLFunction (A j))
  have h := (tendsto_finsetSum univ fun j _ => H j).div_const (4:ℂ)
  have havg : (∑ j, fourthRoot j*(periodicNormMean (A j):ℂ))/4 =
      (∑ r, Φ r*star (Ψ r))/(q:ℂ) := by
    simp only [periodicNormMean, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast,
      ← mul_div_assoc, ← Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm,div_right_comm,Finset.sum_div]
    congr 1
    exact sum_congr rfl fun r _ => polarize (Φ r) (Ψ r)
  rw [havg] at h
  refine h.congr fun T => ?_
  simp only [← mul_div_assoc,← Finset.sum_div]
  rw [div_right_comm]
  congr 1
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (s := univ) (f := fun j t => fourthRoot j*V j t) (fun j _ => (continuous_const.mul (hc j)).intervalIntegrable ..),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [V,A,LFunction_linear] using
    polarize (ZMod.LFunction Φ ((1/2:ℂ)+t*I)) (ZMod.LFunction Ψ ((1/2:ℂ)+t*I))

/-- Distinct Dirichlet characters of the same modulus have vanishing
normalized mixed second moment. -/
theorem mixed_mean_LFunctions_of_ne {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q} (h : χ≠ψ) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T,
      χ.LFunction ((1/2:ℂ)+t*I)*star (ψ.LFunction ((1/2:ℂ)+t*I)))/((T*Real.log T:ℝ):ℂ))
      atTop (𝓝 0) := by
  simpa only [DirichletCharacter.LFunction,sum_zmod_mul_conj_eq,if_neg h,zero_div] using
    mixed_mean_periodicLFunctions (χ : ZMod q → ℂ) ψ

end AnalyticNumberTheory.DirichletLFunctions
