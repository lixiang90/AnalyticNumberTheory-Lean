import AnalyticNumberTheory.DirichletLFunctions.GaussianPolynomialShift

/-!
# Balanced polynomial reduction for the critical line of a character

At the critical line the two completed Gaussian integrals have equal norms.
Moving an arbitrary initial polynomial to the quarter line leaves a tail
on the line of real part three halves.
-/
noncomputable section
open Real Complex Set Finset MeasureTheory Filter
open scoped ComplexConjugate
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem gamma_star_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    (star χ).gammaFactor (conj z)=conj (χ.gammaFactor z) := by
  rw [gammaFactor_eq_Gammaℝ,gammaFactor_eq_Gammaℝ,parityExp_star,←Complex.Gammaℝ_conj]
  congr 1;simp

private theorem gaussian_mean_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (c t : ℝ) :
    characterGaussianMean (star χ) (-t) c (star χ).LFunction=
      conj (characterGaussianMean χ t c χ.LFunction) := by
  let s := (1/2:ℂ)+t*I
  let w (v : ℝ) := (c:ℂ)+v*I
  have hs : (1/2:ℂ)+(-t:ℝ)*I=conj s := by simp [s,Complex.conj_ofNat]
  have hw (v : ℝ) : (c:ℂ)+(-v:ℝ)*I=conj (w v) := by simp [w]
  have hc (v : ℝ) : conductorWeight q (conj (w v))=conj (conductorWeight q (w v)) := by
    unfold conductorWeight
    rw [show conj (w v)/2=conj (w v/2) by simp [Complex.conj_ofNat],Complex.cpow_conj _ _ (by rw [←Complex.ofReal_natCast,Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)];exact Real.pi_ne_zero.symm)]
    simp
  unfold characterGaussianMean
  rw [←integral_conj]
  conv_lhs => rw [←integral_neg_eq_self]
  apply integral_congr_ae;filter_upwards with v
  dsimp only [characterGaussianKernel]
  rw [hs,hw,←map_add,LFunction_star_conj hχ,gamma_star_conj,gamma_star_conj,hc]
  change _=conj ((χ.gammaFactor (s+w v)/χ.gammaFactor s*Complex.exp (w v^2)/w v)*conductorWeight q (w v)*χ.LFunction (s+w v))
  simp only [map_mul,map_div₀,←map_pow,Complex.exp_conj]

/-- On the critical line one normalized right-hand Gaussian integral
controls the L-function of a primitive character of conductor at least two. -/
theorem norm_primitive_L_le_gaussian {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2≤q) (t : ℝ) {c : ℝ} (hc : 0<c) :
    ‖χ.LFunction ((1/2:ℂ)+t*I)‖≤‖characterGaussianMean χ t c χ.LFunction‖ := by
  let s := (1/2:ℂ)+t*I
  let s' := (1/2:ℂ)+(-t:ℝ)*I
  have hconj : s'=conj s := by simp [s',s,Complex.conj_ofNat]
  have hs : 1-s=s' := by dsimp [s,s'];push_cast;ring
  have hG : 0<‖χ.gammaFactor s‖ := norm_pos_iff.mpr (by rw [gammaFactor_eq_Gammaℝ];apply Complex.Gammaℝ_ne_zero_of_re_pos;simp [s];positivity)
  have hG' : ‖(star χ).gammaFactor s'‖=‖χ.gammaFactor s‖ := by rw [hconj,gamma_star_conj,Complex.norm_conj]
  have hi := congrArg norm (completedLGaussianIntegral_div_eq χ t (c:=c) (by linarith))
  have hi' := congrArg norm (completedLGaussianIntegral_div_eq (star χ) (-t) (c:=c) (by linarith))
  change ‖completedLGaussianIntegral χ s c/χ.gammaFactor s‖=_ at hi
  change ‖completedLGaussianIntegral (star χ) s' c/(star χ).gammaFactor s'‖=_ at hi'
  rw [norm_div] at hi hi'
  rw [hG',gaussian_mean_conj (isPrimitive_ne_one hχ hq),Complex.norm_conj] at hi'
  have h₁ := (div_eq_iff hG.ne').mp hi
  have h₂ := (div_eq_iff hG.ne').mp hi'
  have hfe := completedL_gaussian_functional_equation hχ hq s hc
  rw [hs] at hfe
  have H := norm_add_le (completedLGaussianIntegral χ s c)
    (((q:ℂ)^(1/2-s)*χ.rootNumber)*completedLGaussianIntegral (star χ) s' c)
  rw [hfe,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos (NeZero.pos q),norm_rootNumber_primitive hχ,
    show ((1/2:ℂ)-s).re=0 by simp [s,Complex.conj_ofNat],Real.rpow_zero,one_mul,one_mul] at H
  rw [completedLFunction_eq_mul_gammaFactor χ (s:=s) (Or.inr (by omega)) (norm_pos_iff.mp hG)] at H
  rw [norm_mul,h₁,h₂] at H
  apply le_of_mul_le_mul_right (a:=‖χ.gammaFactor s‖) _ hG
  nlinarith only [H,mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : 1≤π) (mul_nonneg (norm_nonneg (χ.LFunction s)) hG.le)]

/-- The common Gaussian weight for the estimates of the two displaced
polynomials. -/
def characterMomentGaussian (v : ℝ) := Real.exp (-v^2/2)

theorem integrable_characterMomentGaussian : Integrable characterMomentGaussian := by
  convert integrable_exp_neg_mul_sq (by norm_num : 0<(1/2:ℝ)) using 1
  ext v;dsimp [characterMomentGaussian];congr 1;ring

private theorem gaussian_abs_majorant {c : ℝ} (hc : -(1/2:ℝ)<c) (hc' : c≠0) :
    ∃ K : ℝ,0<K ∧ ∀{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (f : ℂ→ℂ)
      {M : ℝ},(∀v : ℝ,‖f (((1/2+c:ℝ):ℂ)+(t+v:ℝ)*I)‖≤M) →
      Continuous (fun v : ℝ => f (((1/2+c:ℝ):ℂ)+(t+v:ℝ)*I)) →
      ‖characterGaussianMean χ t c f‖≤K*(conductorLength q t)^c*
        ∫v,characterMomentGaussian v*‖f (((1/2+c:ℝ):ℂ)+(t+v:ℝ)*I)‖ := by
  obtain ⟨K,hK,H⟩ := norm_characterGaussianKernel_le hc hc'
  refine ⟨K,hK,?_⟩;intro q _ χ t f M hM hf
  let a := K*(conductorLength q t)^c
  have hi : Integrable (fun v : ℝ => characterMomentGaussian v*‖f (((1/2+c:ℝ):ℂ)+(t+v:ℝ)*I)‖) := by
    have hw : Continuous characterMomentGaussian := by change Continuous (fun v : ℝ=>Real.exp (-v^2/2));fun_prop
    apply (integrable_characterMomentGaussian.mul_const M).mono' (hw.mul hf.norm).aestronglyMeasurable
    filter_upwards with v
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (show 0≤characterMomentGaussian v from (Real.exp_pos _).le) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hM v) (Real.exp_pos _).le
  rw [←integral_const_mul];apply (norm_integral_le_integral_norm ..).trans
  apply integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _)) (hi.const_mul a)
  filter_upwards with v
  rw [norm_mul,show (1/2:ℂ)+t*I+((c:ℂ)+v*I)=(((1/2+c:ℝ):ℂ)+(t+v:ℝ)*I) by push_cast;ring]
  exact (mul_le_mul_of_nonneg_right (H χ t v) (norm_nonneg _)).trans_eq (by dsimp [a,characterMomentGaussian];ring)

set_option maxHeartbeats 1400000 in
/-- A common pair of Gaussian convolutions, with arbitrary cutoff, bounds
every primitive L-function on the critical line. -/
theorem primitive_L_critical_gaussian_polynomials :
    ∃ C : ℝ,0<C ∧ ∀{q N : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
      χ.IsPrimitive → 2≤q → 1≤N → ∀t : ℝ,
      let P := dirichletPoly (fun n : ℕ=>χ n) N
      let z := fun (σ u : ℝ)=>(σ:ℂ)+u*I
      let X := conductorLength q t
      ‖χ.LFunction (z (1/2) t)‖≤2*π*‖P (z (1/2) t)‖+
        C*X^(-(1/4):ℝ)*(∫v,characterMomentGaussian v*‖P (z (1/4) (t+v))‖)+
        C*X*(∫v,characterMomentGaussian v*‖χ.LFunction (z (3/2) (t+v))-P (z (3/2) (t+v))‖) := by
  obtain ⟨U,hU,HU⟩ := gaussian_abs_majorant (c:=1) (by norm_num) (by norm_num)
  obtain ⟨V,hV,HV⟩ := gaussian_abs_majorant (c:=-(1/4)) (by norm_num) (by norm_num)
  let C := max U V
  refine ⟨C,hU.trans_le (le_max_left ..),?_⟩
  intro q N _ χ hχ hq hN t P z X
  let R (s : ℂ) := χ.LFunction s-P s
  let line (c v : ℝ) := (1/2:ℂ)+t*I+((c:ℂ)+v*I)
  have he (c v : ℝ) : line c v=z (1/2+c) (t+v) := by dsimp [line,z];push_cast;ring
  have hzhalf : z (1/2) t=(1/2:ℂ)+t*I := by simp [z]
  have hr (σ u : ℝ) : (z σ u).re=σ := by simp [z]
  have hc (σ : ℝ) : Continuous (fun v : ℝ => z σ (t+v)) := by dsimp [z];fun_prop
  have hp : Continuous P := (differentiable_dirichletPoly _ _).continuous
  have hL : Continuous (fun v : ℝ => χ.LFunction (z (3/2) (t+v))) :=
    (differentiable_LFunction_of_ne_one (isPrimitive_ne_one hχ hq)).continuous.comp (hc _)
  have hP (σ u : ℝ) (hσ : 0≤σ) : ‖P (z σ u)‖≤N := by
    apply (norm_characterPolynomial_le_power_sum χ N _).trans
    calc _ ≤ ∑_n∈Finset.Icc 1 N,(1:ℝ) := by
                apply sum_le_sum;intro n hn
                exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (mem_Icc.mp hn).1) (by rw [hr];linarith)
         _ = _ := by simp
  have hR (u : ℝ) : ‖R (z (3/2) u)‖≤(N:ℝ)^(-(1/2):ℝ)*2 := by
    have H := norm_LFunction_sub_polynomial_absolute χ hN (s:=z (3/2) u) (by rw [hr];norm_num)
    rw [hr] at H;convert H using 1 <;>norm_num <;>ring
  have hp₁ : ∀v, ‖P (line 1 v)‖≤N := fun v=>by rw [he];exact hP _ _ (by norm_num)
  have hr₁ : ∀v, ‖R (line 1 v)‖≤(N:ℝ)^(-(1/2):ℝ)*2 := fun v=>by rw [he,show (1/2:ℝ)+1=3/2 by norm_num];exact hR _
  have hcont₁ : Continuous (fun v=>P (line 1 v)) := hp.comp (by dsimp [line];fun_prop)
  have hcont₂ : Continuous (fun v=>R (line 1 v)) := by
    simp_rw [he,show (1/2:ℝ)+1=3/2 by norm_num];exact hL.sub (hp.comp (hc _))
  have hiR := integrable_characterGaussianMean χ t (c:=1) (by norm_num) (by norm_num) R (by positivity) hcont₂ hr₁
  have hiP := integrable_characterGaussianMean χ t (c:=1) (by norm_num) (by norm_num) P (Nat.cast_nonneg N) hcont₁ hp₁
  have hsum : characterGaussianMean χ t 1 χ.LFunction=characterGaussianMean χ t 1 R+characterGaussianMean χ t 1 P := by
    unfold characterGaussianMean;rw [←integral_add hiR hiP]
    apply integral_congr_ae;filter_upwards with v;dsimp [R];ring
  have hshift := characterGaussianMean_polynomial_shift_to χ N t (c:=1) (by norm_num) (by norm_num)
  change characterGaussianMean χ t 1 P-characterGaussianMean χ t (-(1/4)) P=2*π*P ((1/2:ℂ)+t*I) at hshift
  rw [←hzhalf] at hshift
  have hgauss := norm_primitive_L_le_gaussian hχ hq t (c:=1) (by norm_num)
  rw [←hzhalf] at hgauss
  apply hgauss.trans
  rw [hsum,show characterGaussianMean χ t 1 P=2*π*P (z (1/2) t)+characterGaussianMean χ t (-(1/4)) P by linear_combination hshift]
  have hneg := HV χ t P (M:=N) (by norm_num only [show (1/2:ℝ)+-(1/4)=1/4 by norm_num];exact fun v=>hP _ _ (by norm_num))
    (by norm_num only [show (1/2:ℝ)+-(1/4)=1/4 by norm_num];exact hp.comp (hc _))
  have hpos := HU χ t R (M:=(N:ℝ)^(-(1/2):ℝ)*2) (by norm_num only [show (1/2:ℝ)+1=3/2 by norm_num];exact fun v=>hR _)
    (by norm_num only [show (1/2:ℝ)+1=3/2 by norm_num];exact hL.sub (hp.comp (hc _)))
  norm_num only [show (1/2:ℝ)+-(1/4)=1/4 by norm_num,show (1/2:ℝ)+1=3/2 by norm_num,Real.rpow_one] at hneg hpos
  let J := ∫v,characterMomentGaussian v*‖P (z (1/4) (t+v))‖
  let K := ∫v,characterMomentGaussian v*‖R (z (3/2) (t+v))‖
  change ‖characterGaussianMean χ t (-(1/4)) P‖≤V*X^(-(1/4):ℝ)*J at hneg
  change ‖characterGaussianMean χ t 1 R‖≤U*X*K at hpos
  have hJ : 0≤J := integral_nonneg (fun v=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hK : 0≤K := integral_nonneg (fun v=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hX : 0≤X := Real.sqrt_nonneg _
  change _≤2*π*‖P (z (1/2) t)‖+C*X^(-(1/4):ℝ)*J+C*X*K
  let Z := (2*π:ℂ)*P (z (1/2) t)
  let G := characterGaussianMean χ t (-(1/4)) P
  let H := characterGaussianMean χ t 1 R
  have hz : ‖Z+G‖≤‖Z‖+V*X^(-(1/4):ℝ)*J := (norm_add_le Z G).trans (add_le_add (le_refl _) hneg)
  have hall : ‖H+(Z+G)‖≤U*X*K+(‖Z‖+V*X^(-(1/4):ℝ)*J) := (norm_add_le H (Z+G)).trans (add_le_add hpos hz)
  apply hall.trans
  dsimp only [Z,C]
  rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left U V) hX) hK,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right U V) (Real.rpow_nonneg hX (-(1/4):ℝ))) hJ]

end AnalyticNumberTheory.DirichletLFunctions
