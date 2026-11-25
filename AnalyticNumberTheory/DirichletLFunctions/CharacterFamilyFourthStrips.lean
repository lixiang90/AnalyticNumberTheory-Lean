import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.FamilyVerticalFourthMeans
import AnalyticNumberTheory.DirichletLFunctions.NarrowLogarithmicStrips
import AnalyticNumberTheory.DirichletLFunctions.Characters

/-!
# Transferring character-family fourth moments to a strip

A single joint critical-line estimate for a finite set of characters
controls its fourth means off the line. The scale in the interpolation
is the product of the modulus and height, independently of the size of
the rectangle. The principal character is allowed.
-/

open Complex Real Set Finset MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A normalized critical-line fourth moment for a finite set of characters at a fixed modulus. -/
def CharacterFamilyCriticalFourthBound {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)) (D : ℝ) : Prop :=
  ∀ {T : ℝ},1≤T → (∑ χ∈S,∫ t in -T..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤D*q.totient*T*(1+Real.log (q*T))^4

/-- Analyticity of all characters to the left of the principal pole. -/
theorem analyticAt_LFunction_re_lt_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : z.re<1) :
    AnalyticAt ℂ χ.LFunction z := by
  apply DifferentiableOn.analyticOnNhd (s:={(1:ℂ)}ᶜ) _ isOpen_compl_singleton z (show z≠1 by intro he;simp [he] at hz)
  exact fun s hs => (χ.differentiableAt_LFunction s (.inl hs)).differentiableWithinAt

private theorem LFunction_quarter_rectangle_bound :
    ∃ K : ℝ,0<K ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {s : ℂ},1≤T →
      |s.re-1/2|≤1/4 → |s.im|≤2*T → ‖χ.LFunction s‖≤K*((q:ℝ)*T)^2 := by
  obtain ⟨A,hA,H⟩ := LFunction_derivative_strips_all_heights
  refine ⟨1+16*(A+64),by positivity,?_⟩
  intro q _ χ T s hT hs ht
  have hq : (1:ℝ)≤q := by exact_mod_cast (NeZero.pos q)
  have hr := abs_le.mp hs
  have hσ : 0≤s.re := by linarith [hr.1]
  have hσ' : s.re≤3/4 := by linarith [hr.2]
  have hne : s≠1 := fun he => by norm_num [he] at hσ'
  let V := 2+|s.im|
  have hV : 1≤V := by dsimp [V];linarith [abs_nonneg s.im]
  have hVT : V≤4*T := by dsimp [V];linarith
  have h := H χ (k:=2) (by norm_num) hσ (by norm_num;linarith only [hσ]) hne
  change ‖χ.LFunction s‖≤_+_*(A*V^_*(1+Real.log V)+16*V^_/_) at h
  have hp : (∑n∈Icc 1 q,(n:ℝ)^(-s.re))≤q := by
    calc _ ≤ ∑n∈Icc 1 q,(1:ℝ) := Finset.sum_le_sum (fun n hn => Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast (mem_Icc.mp hn).1) (by linarith))
         _ = _ := by simp [Nat.card_Icc]
  have hqpow := Real.rpow_le_rpow_of_exponent_le hq (by linarith : 1-s.re≤1)
  have hpow := Real.rpow_le_rpow_of_exponent_le hV (by norm_num : 1/((2:ℝ)^2-2)≤1)
  have hpow' := Real.rpow_le_rpow_of_exponent_le hV (by linarith : 1-s.re≤1)
  rw [Real.rpow_one] at hqpow hpow hpow'
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hV)
  have hden : 1/4≤|1-s.re|+|s.im| := by linarith [le_abs_self (1-s.re),abs_nonneg s.im]
  have hPole : 16*V^(1-s.re)/(|1-s.re|+|s.im|)≤64*V := (div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [hpow',mul_le_mul_of_nonneg_right hden (by linarith : 0≤V)])
  have hReg := mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) (by linarith only [hlog] : 1+Real.log V≤V)
    (show 0≤1+Real.log V by linarith [Real.log_nonneg hV]) (by positivity : 0≤A*V)
  have hRest : A*V^(1/((2:ℝ)^2-2))*(1+Real.log V)+16*V^(1-s.re)/(|1-s.re|+|s.im|)≤(A+64)*V^2 := by
    nlinarith only [hReg,hPole,mul_le_mul_of_nonneg_right hV (by linarith : 0≤V)]
  apply h.trans
  apply (add_le_add hp (mul_le_mul hqpow hRest (by positivity [Real.log_nonneg hV]) (Nat.cast_nonneg q))).trans
  have hV2 := pow_le_pow_left₀ (by linarith : 0≤V) hVT 2
  have hq2 : (q:ℝ)≤q^2 := by nlinarith only [mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg q)]
  have hT2 : 1≤T^2 := one_le_pow₀ hT
  have hqT : (q:ℝ)≤((q:ℝ)*T)^2 := by rw [mul_pow];exact hq2.trans (le_mul_of_one_le_right (sq_nonneg _) hT2)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_right hq2 (by positivity : 0≤A+64)) hV2 (sq_nonneg _) (by positivity)
  nlinarith only [hqT,hh]

/-- Coarse fourth-mean growth throughout the quarter strip, with the exact
exponential dependence on the distance to the critical line. -/
theorem character_family_fourth_interpolated {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T σ : ℝ}, 1≤T → |σ-1/2|≤1/4 →
      (∑χ∈S,∫ t in -T..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(1+Real.log (q*T))^4*Real.exp (64*|σ-1/2| *Real.log (q*T)) := by
  obtain ⟨K,hK,H⟩ := LFunction_quarter_rectangle_bound
  let B := 32*D+K^4
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨2*B,by positivity,?_⟩
  intro q _ S hS T σ hT hσ
  let X := (q:ℝ)*T
  let Y := (q.totient:ℝ)*T*(1+Real.log X)^4
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le hq hT
  have hx := zero_lt_one.trans_le hX
  have hlog := Real.log_nonneg hX
  have hY : 0≤Y := by dsimp [Y];positivity
  have hL : 1≤(1+Real.log X)^4 := one_le_pow₀ (by linarith)
  have hlog₂ : 1+Real.log ((q:ℝ)*(2*T))≤2*(1+Real.log X) := by
    rw [show (q:ℝ)*(2*T)=2*X by dsimp [X];ring,Real.log_mul (by norm_num) hx.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog₂' := pow_le_pow_left₀ (by linarith [Real.log_nonneg (by change 1≤(q:ℝ)*(2*T);nlinarith only [show (1:ℝ)≤q*T from hX])] : 0≤1+Real.log ((q:ℝ)*(2*T))) hlog₂ 4
  rw [mul_pow] at hlog₂'
  have hc := (hS (T:=2*T) (by linarith)).trans (mul_le_mul_of_nonneg_left hlog₂' (by positivity))
  have hcenter : (∑χ∈S,∫ t in -(2*T)..2*T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤B*Y :=
    hc.trans (by dsimp [B,Y];nlinarith only [mul_nonneg (pow_nonneg hK.le 4) hY])
  have hcard : (S.card:ℝ)≤q.totient := by
    exact_mod_cast (Finset.card_le_univ S).trans_eq (card_dirichletCharacter_eq_totient (q:=q))
  have hqY : (S.card:ℝ)*T≤Y := (mul_le_mul_of_nonneg_right hcard (by linarith)).trans (le_mul_of_one_le_right (by positivity) hL)
  have hscale : (S.card:ℝ)*T*(K*X^2)^4≤B*Y*X^8 := by
    rw [mul_pow,←pow_mul]
    have hh := mul_le_mul (by dsimp [B];linarith : K^4≤B) hqY (by positivity) hB.le
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith only [hh] : S.card*T*K^4≤B*Y) (pow_nonneg hx.le 8)
  have hh := family_fourthMoment_interpolation (ι:=DirichletCharacter ℂ q) (f:=fun χ => χ.LFunction) S (l:=0) (u:=1) (σ:=σ) (c:=1/2) (w:=1/4)
    (T:=T) (X:=X) (K:=K*X^2) (M:=B*Y) 8 (by norm_num) (by linarith) hX (by positivity) (by positivity)
    (by norm_num : (0:ℝ)<1/2-1/4) (by norm_num : (1/2:ℝ)+1/4<1)
    (fun χ _ z hz => analyticAt_LFunction_re_lt_one χ hz.2)
    (by simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hcenter)
    (fun χ _ z hz ht => H χ hT hz ht) hscale hσ
  apply hh.trans_eq
  dsimp [Y,X];norm_num;ring

/-- The family fourth moment on a doubled symmetric height window, in the strip
of width `1/(200 log(qT))`. Both endpoints in height are included. -/
theorem character_family_fourth_narrow_window {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ∈S,∫ t in -(2*T)..2*T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨A,hA,H⟩ := character_family_fourth_interpolated hD
  refine ⟨512*A*Real.exp 1,by positivity,?_⟩
  intro q _ S hS T σ hT hs
  let X := (q:ℝ)*T
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hX : 2≤X := hT.trans (by dsimp [X];simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith))
  have hx : 0<X := by linarith
  have hlog : 1/2≤Real.log X := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hX)
  have hpos : 0<Real.log X := by linarith
  have hline : |σ-1/2|≤1/4 := hs.trans ((div_le_iff₀ (by change 0<200*Real.log X;positivity)).mpr (by change 1≤1/4*(200*Real.log X);linarith))
  have hh := H S hS (T:=2*T) (by linarith) hline
  have hid : (q:ℝ)*(2*T)=2*X := by dsimp [X];ring
  rw [hid] at hh
  have h₂log : Real.log (2*X)≤2*Real.log X := by
    rw [Real.log_mul (by norm_num) hx.ne'];linarith [Real.log_le_log (by norm_num) hX]
  have hl := pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1≤2*X by linarith)] : 0≤1+Real.log (2*X))
    (by linarith : 1+Real.log (2*X)≤4*Real.log X) 4
  rw [mul_pow] at hl
  have hgap := (le_div_iff₀ (by positivity : 0<200*Real.log X)).mp (show |σ-1/2|≤1/(200*Real.log X) from hs)
  have hExp := Real.exp_le_exp.mpr (show 64*|σ-1/2| *Real.log (2*X)≤1 by
    nlinarith only [mul_le_mul_of_nonneg_left h₂log (abs_nonneg (σ-1/2)),hgap])
  apply hh.trans
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity : 0≤A*q.totient*(2*T))) hExp (Real.exp_pos _).le (by positivity)).trans_eq (by dsimp [X];ring)

/-- Uniform fourth moment on the positive height interval for every family
satisfying the critical-line hypothesis. -/
theorem character_family_fourth_narrow_strip {D : ℝ} (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)),
      CharacterFamilyCriticalFourthBound S D → ∀ {T σ : ℝ},2≤T → |σ-1/2|≤1/(200*Real.log (q*T)) →
      (∑χ∈S,∫ t in (0:ℝ)..T,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q.totient*T*(Real.log (q*T))^4 := by
  obtain ⟨C,hC,H⟩ := character_family_fourth_narrow_window hD
  refine ⟨C,hC,?_⟩
  intro q _ S hS T σ hT hs
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hX : 2≤(q:ℝ)*T := hT.trans (by simpa using mul_le_mul_of_nonneg_right hq (show 0≤T by linarith))
  have hlog : 1/2≤Real.log ((q:ℝ)*T) := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hX)
  have hh : 1/(200*Real.log ((q:ℝ)*T))≤1/4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hσ : σ<1 := by linarith [(abs_le.mp hs).2]
  apply (Finset.sum_le_sum (fun χ hi => ?_)).trans (H S hS hT hs)
  have hc : Continuous (fun t : ℝ => χ.LFunction ((σ:ℂ)+t*I)) :=
    continuous_iff_continuousAt.mpr fun t => (analyticAt_LFunction_re_lt_one χ (z:=(σ:ℂ)+t*I) (by simpa using hσ)).continuousAt.comp
      (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)
  exact intervalIntegral.integral_mono_interval (by linarith : -(2*T)≤0) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun t => pow_nonneg (norm_nonneg _) _) ((hc.norm.pow 4).intervalIntegrable ..)

end AnalyticNumberTheory.DirichletLFunctions
