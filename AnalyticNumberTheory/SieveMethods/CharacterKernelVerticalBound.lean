import AnalyticNumberTheory.DirichletLFunctions.ConductorLeftEdge
import AnalyticNumberTheory.AnalyticTools.Gamma.SmoothingKernel

/-!
# The left vertical integral of a smoothed character correlation

A logarithmic displacement to the left of zero converts the conductor
bound into its square root times one logarithm.
-/
open Real Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Uniform bound for the vertical integral after shifting by a distance δ. -/
theorem characterKernel_vertical_bound :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : s.re∈Icc (0:ℝ) 2) {δ X : ℝ}, 0<δ → δ≤1/4 → 0<X →
      ‖gammaSmoothingIntegral (fun w => χ.LFunction (s-3+w)) X (3-s.re-δ)‖ ≤
        C*(1+1/δ)*((q:ℝ)*(|s.im|+2))^(1/2+δ)*X^(3-s.re-δ) := by
  obtain ⟨A,hA,HA⟩ := norm_LFunction_conductor_left_edge
  obtain ⟨B,hB,HB⟩ := norm_Gamma_positive_strip_weight (a:=(3/4:ℝ)) (b:=3)
    (by norm_num) (by norm_num) 3
  refine ⟨A*B,by positivity,?_⟩
  intro q _ χ s hs δ X hδ hδ' hX
  let l := 3-s.re-δ
  let H := (q:ℝ)*(|s.im|+2)
  let D := A*(1+1/δ)*H^(1/2+δ)*B*X^l
  have hH : 0<H := mul_pos (Nat.cast_pos.mpr (NeZero.pos q)) (by linarith [abs_nonneg s.im])
  have hD : 0≤D := by dsimp [D];positivity
  have hl : l∈Icc (3/4:ℝ) 3 := by dsimp [l]; constructor <;> linarith [hs.1,hs.2]
  let w (t:ℝ) : ℂ := (l:ℂ)+(t:ℂ)*I
  have hbound (t:ℝ) :
      ‖χ.LFunction (s-3+w t)*Complex.Gamma (w t)*(X:ℂ)^(w t)‖≤ D*(1+t^2)⁻¹ := by
    have hwr : (w t).re=l := by simp [w]
    have hwi : (w t).im=t := by simp [w]
    have hs' : s-3+w t= -(δ:ℂ)+((s.im+t:ℝ):ℂ)*I := by
      apply Complex.ext <;> simp [w,l] <;> ring
    have he : 0≤1/2+δ := by linarith
    have he' : 1/2+δ≤1 := by linarith
    have hcond : (q:ℝ)*(|s.im+t|+2) ≤ H*(1+|t|) := by
      dsimp [H];rw [mul_assoc];gcongr
      nlinarith [abs_add_le s.im t,abs_nonneg t,mul_nonneg (abs_nonneg s.im) (abs_nonneg t)]
    have hpow := Real.rpow_le_rpow (by positivity : 0≤(q:ℝ)*(|s.im+t|+2)) hcond he
    rw [Real.mul_rpow hH.le (by positivity)] at hpow
    have hpow' : (1+|t|)^(1/2+δ)≤1+|t| := (Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg t] : 1≤1+|t|) he').trans_eq (Real.rpow_one _)
    have hL := HA hδ hδ' χ (s.im+t)
    rw [←hs'] at hL
    have hg := HB (w t) (hwr ▸ hl)
    rw [hwi] at hg
    have hden : 1+t^2≤(1+|t|)^2 := by nlinarith [abs_nonneg t,sq_abs t]
    have hx : ‖(X:ℂ)^(w t)‖=X^l := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hX,hwr]
    have hL' : ‖χ.LFunction (s-3+w t)‖≤ A*(1+1/δ)*(H^(1/2+δ)*(1+|t|)) :=
      hL.trans (mul_le_mul_of_nonneg_left (hpow.trans (mul_le_mul_of_nonneg_left hpow' (by positivity))) (by positivity))
    rw [norm_mul,norm_mul,hx,←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    calc _ ≤ A*(1+1/δ)*(H^(1/2+δ)*(1+|t|))*‖Complex.Gamma (w t)‖*X^l*(1+|t|)^2 := by gcongr
         _ = A*(1+1/δ)*H^(1/2+δ)*((1+|t|)^3*‖Complex.Gamma (w t)‖)*X^l := by ring
         _ ≤ D := by dsimp [D];gcongr
  have hi := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul D) (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hi
  unfold gammaSmoothingIntegral
  rw [norm_mul,norm_inv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  norm_num only [Complex.norm_ofNat]
  change _*‖∫ t : ℝ, χ.LFunction (s-3+w t)*Complex.Gamma (w t)*(X:ℂ)^(w t)‖ ≤ _
  calc _ ≤ (2*π)⁻¹*(D*π) := by gcongr
       _ = D/2 := by field_simp [Real.pi_ne_zero]
       _ ≤ D := by linarith
       _ = _ := by dsimp [D,H,l];ring

/-- The logarithmically shifted line gives square-root conductor growth. -/
theorem characterKernel_logarithmic_vertical_decay :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : s.re∈Icc (0:ℝ) 2) {X : ℝ},1≤X →
      let H := (q:ℝ)*(|s.im|+2)
      let δ := 1/(4+Real.log H)
      X^(s.re-3)*‖gammaSmoothingIntegral (fun w => χ.LFunction (s-3+w)) X (3-s.re-δ)‖ ≤
        C*Real.sqrt H*(1+Real.log H)*X^(-δ) := by
  obtain ⟨A,hA,HA⟩ := characterKernel_vertical_bound
  refine ⟨5*A*Real.exp 1,by positivity,?_⟩
  intro q _ χ s hs X hX
  dsimp only
  let H := (q:ℝ)*(|s.im|+2)
  let δ := 1/(4+Real.log H)
  have hq : 1≤(q:ℝ) := by exact_mod_cast (NeZero.one_le : 1≤q)
  have hH : 1≤H := by dsimp [H];nlinarith [abs_nonneg s.im,mul_nonneg (by linarith : 0≤(q:ℝ)-1) (by linarith [abs_nonneg s.im] : 0≤|s.im|+2)]
  have hlog := Real.log_nonneg hH
  have hd : 0<δ := by dsimp [δ];positivity
  have hd' : δ≤1/4 := by dsimp [δ];apply one_div_le_one_div_of_le (by norm_num);linarith
  have h := HA χ hs hd hd' (zero_lt_one.trans_le hX)
  have hx : X^(s.re-3)*X^(3-s.re-δ)=X^(-δ) := by
    rw [←Real.rpow_add (zero_lt_one.trans_le hX)];congr 1;ring
  have hdelta : H^δ≤Real.exp 1 := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hH)]
    apply Real.exp_le_exp.mpr
    dsimp [δ];rw [mul_one_div,div_le_one (by positivity)];linarith
  have hsmall : 1+1/δ≤5*(1+Real.log H) := by simp only [δ,one_div,inv_inv];linarith
  rw [Real.rpow_add (zero_lt_one.trans_le hH),←Real.sqrt_eq_rpow] at h
  change X^(s.re-3)*_ ≤ _*Real.sqrt H*(1+Real.log H)*X^(-δ)
  calc _ ≤ X^(s.re-3)*(A*(1+1/δ)*(Real.sqrt H*H^δ)*X^(3-s.re-δ)) := by gcongr
       _ = A*(1+1/δ)*Real.sqrt H*H^δ*(X^(s.re-3)*X^(3-s.re-δ)) := by ring
       _ ≤ A*(5*(1+Real.log H))*Real.sqrt H*Real.exp 1*X^(-δ) := by rw [hx];gcongr
       _ = _ := by ring

/-- The logarithmically shifted line gives square-root conductor growth. -/
theorem characterKernel_logarithmic_vertical_bound :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : s.re∈Icc (0:ℝ) 2) {X : ℝ},1≤X →
      let H := (q:ℝ)*(|s.im|+2)
      let δ := 1/(4+Real.log H)
      X^(s.re-3)*‖gammaSmoothingIntegral (fun w => χ.LFunction (s-3+w)) X (3-s.re-δ)‖ ≤
        C*Real.sqrt H*(1+Real.log H) := by

  obtain ⟨C,hC,HC⟩ := characterKernel_logarithmic_vertical_decay
  refine ⟨C,hC,?_⟩;intro q _ χ s hs X hX
  let H := (q:ℝ)*(|s.im|+2)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast (NeZero.one_le : 1≤q))
    (by linarith [abs_nonneg s.im])
  have hl := Real.log_nonneg hH
  apply (HC χ hs hX).trans
  apply mul_le_of_le_one_right (by change 0≤C*Real.sqrt H*(1+Real.log H);positivity)
  exact (Real.rpow_le_rpow_of_exponent_le hX (show -(1/(4+Real.log H))≤0 from neg_nonpos.mpr (by positivity))).trans_eq (Real.rpow_zero _)

end AnalyticNumberTheory.SieveMethods
