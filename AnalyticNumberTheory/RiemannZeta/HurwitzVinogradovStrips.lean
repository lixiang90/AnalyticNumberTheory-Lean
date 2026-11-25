import AnalyticNumberTheory.RiemannZeta.HurwitzVinogradov

/-!
# Near-one strips for Hurwitz zeta

In a strip of width `R/(log T)^(2/3)` the regular part of Hurwitz zeta
grows at most as `(log T)^(2/3)`, uniformly in the shift. An additional
factor `(log log T)^(2/3)` in the width increases the exponent of the
logarithm by an absolute constant times `R^(3/2)`.
-/

open Complex Real
namespace AnalyticNumberTheory.RiemannZeta

private theorem scaled_strip_exponent {σ R X L : ℝ} (hR : 0≤R) (hX : 0≤X) (hL : 0<L)
    (hσ : 1-R*X^(2/3:ℝ)/L^(2/3:ℝ)≤σ) :
    (max (1-σ) 0)^(3/2:ℝ)*L≤R^(3/2:ℝ)*X := by
  have hη : max (1-σ) 0≤R*X^(2/3:ℝ)/L^(2/3:ℝ) := max_le (by linarith only [hσ]) (by positivity)
  apply (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (le_max_right ..) hη (by norm_num : 0≤(3/2:ℝ))) hL.le).trans_eq
  rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow hR (by positivity),
    ←Real.rpow_mul hX,←Real.rpow_mul hL.le]
  norm_num
  field_simp

/-- Two-thirds logarithmic growth in each strip of width
`R/(log |Im s|)^(2/3)`, uniformly for shifts in `(0,1]`. -/
theorem hurwitzZeta_sub_initial_near_one {R : ℝ} (hR : 0≤R) :
    ∃ D : ℝ,0<D ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 0<s.re →
      2≤|s.im| → 1-R/(Real.log |s.im|)^(2/3:ℝ)≤s.re →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        D*(Real.log |s.im|)^(2/3:ℝ) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  refine ⟨D*Real.exp (K*R^(3/2:ℝ)),by positivity,?_⟩
  intro a s ha hσ ht hstrip
  have hL := Real.log_pos (by linarith : 1 < |s.im|)
  have h := scaled_strip_exponent (X:=1) hR zero_le_one hL (by simpa using hstrip)
  simp only [mul_one] at h
  apply (H ha hσ ht).trans
  rw [mul_assoc K]
  calc _ ≤ (D*(Real.log |s.im|)^(2/3:ℝ))*Real.exp (K*R^(3/2:ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hK.le)) (by positivity)
       _ = _ := by ring

/-- In strips wider by `(log log |Im s|)^(2/3)`, the exponent of the
logarithm increases by at most `K*R^(3/2)`, with absolute `K` and `D`. -/
theorem hurwitzZeta_sub_initial_loglog_strip :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {R a : ℝ} {s : ℂ},0≤R →
      a∈Set.Ioc (0:ℝ) 1 → 0<s.re → Real.exp 1≤|s.im| →
      1-R*(Real.log (Real.log |s.im|))^(2/3:ℝ)/(Real.log |s.im|)^(2/3:ℝ)≤s.re →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        D*(Real.log |s.im|)^(2/3+K*R^(3/2:ℝ):ℝ) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  refine ⟨K,hK,D,hD,?_⟩
  intro R a s hR ha hσ ht hstrip
  let L := Real.log |s.im|
  have hL : 1≤L := (Real.log_exp 1).symm.le.trans (Real.log_le_log (Real.exp_pos _) ht)
  have hL₀ := zero_lt_one.trans_le hL
  have he := scaled_strip_exponent hR (Real.log_nonneg hL) hL₀ hstrip
  apply (H ha hσ ((show (2:ℝ)≤Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]).trans ht)).trans
  change D*L^(2/3:ℝ)*Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*L) ≤ D*L^(2/3+K*R^(3/2:ℝ):ℝ)
  rw [Real.rpow_add hL₀,←mul_assoc,Real.rpow_def_of_pos hL₀ (K*_)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  calc _ = K*((max (1-s.re) 0)^(3/2:ℝ)*L) := by ring
       _ ≤ K*(R^(3/2:ℝ)*Real.log L) := mul_le_mul_of_nonneg_left he hK.le
       _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
