import AnalyticNumberTheory.AnalyticTools.Gamma.GaussianRatios

/-!
# A gamma-factor ratio uniform up to the imaginary axis

The quotient in a reflected Dirichlet functional equation remains uniformly
bounded on compact height intervals even at a pole of the denominator.
At large heights Stirling's formula gives the exact exponent.
-/
open Set Real Complex
namespace AnalyticNumberTheory.AnalyticTools.Gamma

private theorem compact_reflection (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀z : ℂ, z.re≤0 → ‖z‖≤3 →
      ‖Gammaℝ (1-z+k)‖/‖Gammaℝ (z+k)‖≤C := by
  let S := Metric.closedBall (0:ℂ) 3 ∩ {z : ℂ | z.re≤0}
  let f (z:ℂ) := ‖Gammaℝ (1-z+k)*(Gammaℝ (z+k))⁻¹‖
  have hS : IsCompact S := (isCompact_closedBall ..).inter_right (isClosed_le Complex.continuous_re continuous_const)
  have hne : (0:ℂ)∈S := by simp [S]
  have hc : ContinuousOn f S := by
    intro z hz
    have hpos : 0<(1-z+k).re := by
      rw [add_re,sub_re,one_re,natCast_re]
      have := hz.2
      change z.re≤0 at this
      linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hd := (differentiableAt_GammaReal hpos).continuousAt.comp (f:=fun s : ℂ => 1-s+k) (by fun_prop)
    have hi := (Complex.differentiable_Gammaℝ_inv (z+k)).continuousAt.comp (f:=fun s : ℂ => s+k) (by fun_prop)
    exact (hd.mul hi).norm.continuousWithinAt
  obtain ⟨v,hv,H⟩ := hS.exists_isMaxOn ⟨0,hne⟩ hc
  refine ⟨1+f v,by dsimp [f];positivity,?_⟩
  intro z hz hnorm
  have h := H (show z∈S from ⟨by simpa using hnorm,hz⟩)
  change f z≤f v at h
  calc _ = f z := by dsimp only [f];rw [norm_mul,norm_inv,div_eq_mul_inv]
       _ ≤ f v := h
       _ ≤ _ := by linarith

private theorem norm_gammaReal_factor (z : ℂ) :
    ‖Gammaℝ z‖=π^(-z.re/2)*‖Complex.Gamma (z/2)‖ := by
  rw [Gammaℝ_def,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos];simp

/-- Uniform reflected ratio for both parities, including δ=0. -/
theorem gammaReal_reflected_strip_ratio :
    ∃ C : ℝ,0<C ∧ ∀{δ : ℝ},δ∈Icc (0:ℝ) (1/4) → ∀k : ℕ,k≤1 → ∀t : ℝ,
      ‖Gammaℝ (1+(δ:ℂ)-(t:ℂ)*I+k)‖/‖Gammaℝ (-(δ:ℂ)+(t:ℂ)*I+k)‖≤
        C*(|t|+2)^(1/2+δ) := by
  obtain ⟨A,hA,HA⟩ := compact_reflection 0
  obtain ⟨B,hB,HB⟩ := compact_reflection 1
  obtain ⟨c,C,hc,hcC,H⟩ := norm_complex_gamma_strip_bounds (-1/2) 2
  have hC := hc.trans_le hcC
  let D := max (max A B) (C/c)
  have hD : 0<D := hA.trans_le ((le_max_left ..).trans (le_max_left ..))
  refine ⟨D,hD,?_⟩
  intro δ hδ k hk t
  let z : ℂ := -(δ:ℂ)+(t:ℂ)*I
  have hzr : z.re= -δ := by simp [z]
  have hden : -(δ:ℂ)+(t:ℂ)*I+k=z+k := rfl
  have hnum : 1+(δ:ℂ)-(t:ℂ)*I+k=1-z+k := by dsimp [z];ring
  rw [hnum,hden]
  have hk' : (k:ℝ)≤1 := by exact_mod_cast hk
  have hk0 := Nat.cast_nonneg (α:=ℝ) k
  have hex : 0≤1/2+δ := by linarith [hδ.1]
  by_cases ht : |t|≤2
  · have hz : ‖z‖≤3 := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      simpa only [z,Complex.add_re,Complex.neg_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,
        neg_zero,add_zero,abs_neg,Complex.add_im,Complex.neg_im,Complex.mul_I_im,zero_add,abs_of_nonneg hδ.1]
        using (h.trans (by simp [z,abs_of_nonneg hδ.1];linarith [hδ.2] : |z.re|+|z.im|≤3))
    have hb : ‖Gammaℝ (1-z+k)‖/‖Gammaℝ (z+k)‖≤D := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
      · exact (HA z (by linarith [hδ.1]) hz).trans ((le_max_left ..).trans (le_max_left ..))
      · exact (HB z (by linarith [hδ.1]) hz).trans ((le_max_right ..).trans (le_max_left ..))
    exact hb.trans (le_mul_of_one_le_right hD.le (Real.one_le_rpow (by linarith [abs_nonneg t]) hex))
  · let x := (1+δ+(k:ℝ))/2
    let y := (-δ+(k:ℝ))/2
    let v := t/2
    have hx : x∈Icc (-1/2:ℝ) 2 := by dsimp [x];constructor <;> linarith [hδ.1,hδ.2]
    have hy : y∈Icc (-1/2:ℝ) 2 := by dsimp [y];constructor <;> linarith [hδ.1,hδ.2]
    have hv : 1≤|v| := by dsimp [v];rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)];linarith
    have hv₀ : 0 < |v| := by linarith
    have h₁ := (H (t:=-v) hx (by simpa using hv)).2
    rw [abs_neg] at h₁
    have h₂ := (H (t:=v) hy hv).1
    have he₁ : (1-z+k)/2=(x:ℂ)+((-v:ℝ):ℂ)*I := by dsimp [x,z,v];push_cast;ring
    have he₂ : (z+k)/2=(y:ℂ)+(v:ℂ)*I := by dsimp [y,z,v];push_cast;ring
    let E := Real.exp (-(π/2)*|v|)
    have hE : 0<E := Real.exp_pos _
    have hr : ‖Complex.Gamma ((1-z+k)/2)‖/‖Complex.Gamma ((z+k)/2)‖≤
        (C/c)*|v|^(1/2+δ) := by
      rw [he₁,he₂]
      apply (div_le_div₀ (by positivity) h₁ (by positivity) h₂).trans_eq
      change (C*E*|v|^(x-1/2))/(c*E*|v|^(y-1/2))=_
      rw [mul_div_mul_comm,mul_div_mul_right _ _ hE.ne',←Real.rpow_sub hv₀,
        show x-1/2-(y-1/2)=1/2+δ by dsimp [x,y];ring]
    rw [norm_gammaReal_factor,norm_gammaReal_factor,mul_div_mul_comm,←Real.rpow_sub Real.pi_pos]
    have hπ : π^(-(1-z+k).re/2- -(z+k).re/2)≤1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi])
      simp only [add_re,sub_re,one_re,natCast_re,hzr];linarith [hδ.1]
    apply (mul_le_mul hπ hr (by positivity) zero_le_one).trans
    rw [one_mul]
    apply mul_le_mul (le_max_right ..) _ (by positivity) hD.le
    apply Real.rpow_le_rpow (abs_nonneg _) _ hex
    dsimp only [v];rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)];linarith [abs_nonneg t]

end AnalyticNumberTheory.AnalyticTools.Gamma
