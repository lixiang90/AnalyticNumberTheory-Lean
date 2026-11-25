import AnalyticNumberTheory.DivisorProblems.DivisorExponentBalance
import AnalyticNumberTheory.DivisorProblems.SawtoothBlockBounds

/-!
# Van der Corput's exponent 27/82 in the divisor problem

A third-derivative test controls short reciprocal sums. A reciprocal
B-process and a fifth-derivative test control the longer blocks. The
Fourier cutoff and the dyadic decomposition each contribute one logarithm.
-/

open Real Finset
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DivisorProblems

/-- The `27/82` estimate on each dyadic block below the square-root cutoff. -/
theorem reciprocal_sawtooth_divisor_exponent :
    ∃ C≥1, ∀ {x : ℝ} {D a b : ℕ},1≤x → 1≤D → (D:ℝ)^2≤x → D≤a → a≤b → b≤2*D →
    |∑ n∈Ioc a b,sawtooth (x/n)|≤C*x^(27/82:ℝ)*(1+Real.log x) := by
  obtain ⟨C,hC,H⟩ := reciprocal_frequency_divisor_exponent
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
  refine ⟨2+C*(2+2*Real.log 3),by nlinarith only [hC,h3,mul_nonneg (show 0≤C by linarith) h3],?_⟩
  intro x D a b hx hD hDx ha hab hb
  let Y := x^(27/82:ℝ)
  have hY : 1≤Y := Real.one_le_rpow hx (by norm_num)
  have hY' : 0<Y := by linarith
  have hx' : 0<x := by linarith
  have hD' : 0<(D:ℝ) := by exact_mod_cast hD
  have hlog := Real.log_nonneg hx
  have hlen : ((Ioc a b).card:ℝ)≤D := by rw [Nat.card_Ioc]; exact_mod_cast (show b-a≤D by omega)
  have hprod : Y≤Y*(1+Real.log x) := le_mul_of_one_le_right hY'.le (by linarith)
  by_cases hs : (D:ℝ)≤Y
  · calc
      _ ≤ ∑ _n∈Ioc a b,(1/2:ℝ) := (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => sawtooth_abs_le _)
      _ ≤ Y := by rw [sum_const,nsmul_eq_mul]; linarith only [hlen,hs,hY]
      _ ≤ _ := by
        change Y≤(2+C*(2+2*Real.log 3))*Y*(1+Real.log x)
        nlinarith only [hprod,mul_nonneg (show 0≤1+C*(2+2*Real.log 3) by positivity) (mul_nonneg hY'.le (show 0≤1+Real.log x by linarith))]
  let K := ⌈2*(D:ℝ)/Y⌉₊
  have hKlow : 2*(D:ℝ)≤K*Y := (div_le_iff₀ hY').mp (Nat.le_ceil _)
  have hK : 2≤K := by
    apply (Nat.add_one_le_ceil_iff (n:=1)).mpr
    rw [lt_div_iff₀ hY']; push_cast; linarith
  have hKpos : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hKh : (K:ℝ)≤3*D/Y := by
    apply (le_div_iff₀ hY').mpr
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (by positivity : 0≤2*(D:ℝ)/Y)) hY'
    rw [add_mul,div_mul_cancel₀ _ hY'.ne',one_mul] at h
    dsimp [K]; linarith
  have HH := sawtooth_sum_le_of_frequency_bound (Ioc a b) (fun n : ℕ => x/n) hK
    (show 0≤C*Y by positivity) (by
      intro n hn
      obtain ⟨hn₁,hn₂⟩ := mem_Icc.mp hn
      simpa only [←mul_div_assoc] using H (a:=a) (b:=b) (h:=(n:ℝ)) hx (by exact_mod_cast hD)
        hDx (by exact_mod_cast ha) hab (by exact_mod_cast hb) (by exact_mod_cast (show 1≤K by omega))
        hKh (by exact_mod_cast hn₁) (by exact_mod_cast hn₂))
  have hfrac : 2*((Ioc a b).card:ℝ)/K≤Y := (div_le_iff₀ hKpos).mpr (by linarith only [hlen,hKlow])
  have hKD : (K:ℝ)≤3*D := hKh.trans (div_le_self (by positivity) hY)
  have hKL := Real.log_le_log hKpos hKD
  rw [Real.log_mul (by norm_num) hD'.ne'] at hKL
  have hDL := Real.log_le_log (sq_pos_of_pos hD') hDx
  rw [Real.log_pow,Nat.cast_ofNat] at hDL
  have hl : 1+2*Real.log K≤(2+2*Real.log 3)*(1+Real.log x) := by
    nlinarith only [hKL,hDL,hlog,mul_nonneg h3 hlog]
  apply HH.trans
  change _≤(2+C*(2+2*Real.log 3))*Y*(1+Real.log x)
  nlinarith only [hfrac,hprod,mul_le_mul_of_nonneg_left hl (show 0≤C*Y by positivity),
    mul_nonneg hY'.le (show 0≤1+Real.log x by linarith)]

/-- Van der Corput's divisor-problem estimate, uniform for every real `x ≥ 2`. -/
theorem abs_divisorError_le_vanDerCorput_exponent :
    ∃ C>0, ∀ {x : ℝ},2≤x → |divisorError x|≤C*x^(27/82:ℝ)*(Real.log x)^2 := by
  obtain ⟨C,hC,H⟩ := reciprocal_sawtooth_divisor_exponent
  have h2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  let B := 1+(Real.log 2)⁻¹
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨9/(Real.log 2)^2+4*C*B/Real.log 2,by positivity,?_⟩
  intro x hx
  have hx1 : 1≤x := by linarith
  have hx' : 0<x := by linarith
  let Y := x^(27/82:ℝ)
  have hY : 1≤Y := Real.one_le_rpow hx1 (by norm_num)
  have hY' : 0<Y := by linarith
  let N := ⌊Real.sqrt x⌋₊
  have hN : 1≤N := Nat.floor_pos.mpr (Real.one_le_sqrt.mpr hx1)
  have hNx : (N:ℝ)≤Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
  let J := N.log2+1
  have hlogx := Real.log_nonneg hx1
  have HE := abs_divisorError_le_dyadic_sawtooth hx1 (K:=J) Nat.lt_log2_self.le
  have hblock (j : ℕ) : |∑ n∈dyadicBlock N j,sawtooth (x/n)|≤C*Y*(1+Real.log x) := by
    let D : ℕ := 2^j
    let b := min N (2^(j+1))
    change |∑ n∈Ioc D b,sawtooth (x/n)|≤_
    by_cases h : D≤b
    · have hD := (Nat.cast_le.mpr (h.trans (min_le_left ..))).trans hNx
      apply H hx1 (by dsimp [D]; exact one_le_pow₀ (by decide) (n:=j)) ((pow_le_pow_left₀ (Nat.cast_nonneg _) hD 2).trans_eq (Real.sq_sqrt hx'.le)) le_rfl h
      simpa only [b,D,pow_succ,Nat.mul_comm] using min_le_right N (2^(j+1))
    · rw [Ioc_eq_empty_of_le (not_le.mp h).le,sum_empty,abs_zero]; positivity
  have hh := sum_le_sum (s:=range J) (fun j _ => hblock j)
  rw [sum_const,card_range,nsmul_eq_mul] at hh
  have hz := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
  have hxlog : 0<Real.log x := h2.trans_le hz
  have hJ : (J:ℝ)≤2*Real.log x/Real.log 2 := by
    have hp : (2:ℝ)^N.log2≤(N:ℝ) := by exact_mod_cast Nat.log2_self_le (n:=N) (by omega)
    have hs : Real.sqrt x≤x := by
      nlinarith only [Real.sq_sqrt hx'.le,Real.one_le_sqrt.mpr hx1,
        mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr (Real.one_le_sqrt.mpr hx1))]
    have h := Real.log_le_log (by positivity) (hp.trans (hNx.trans hs))
    rw [Real.log_pow] at h
    apply (le_div_iff₀ h2).mpr
    dsimp [J]; push_cast; linarith
  have hL : 1+Real.log x≤B*Real.log x := by
    dsimp [B]; rw [add_mul,one_mul,inv_mul_eq_div]
    linarith only [(one_le_div h2).mpr hz]
  have h9 : 9≤9/(Real.log 2)^2*Y*(Real.log x)^2 := by
    have H' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2.le hz 2) (show 0≤Y by linarith)
    have H'' := le_mul_of_one_le_left (sq_nonneg (Real.log 2)) hY
    have H''' := H''.trans H'
    field_simp [h2.ne']; nlinarith only [H''']
  calc
    _ ≤ 9+2*((J:ℝ)*(C*Y*(1+Real.log x))) := HE.trans (by gcongr)
    _ ≤ 9+2*((2*Real.log x/Real.log 2)*(C*Y*(B*Real.log x))) := by gcongr
    _ ≤ _ := by
      change _≤(9/(Real.log 2)^2+4*C*B/Real.log 2)*Y*(Real.log x)^2
      calc
        _ ≤ 9/(Real.log 2)^2*Y*(Real.log x)^2+2*((2*Real.log x/Real.log 2)*(C*Y*(B*Real.log x))) := add_le_add h9 le_rfl
        _ = _ := by ring

/-- Asymptotic form of the `27/82` divisor estimate. -/
theorem divisorError_isBigO_vanDerCorput_exponent :
    divisorError =O[Filter.atTop] (fun x : ℝ => x^(27/82:ℝ)*(Real.log x)^2) := by
  obtain ⟨C,_,H⟩ := abs_divisorError_le_vanDerCorput_exponent
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (sq_nonneg _))]
  simpa only [mul_assoc] using H hx

/-- In particular the divisor error is little-o of the cube root. -/
theorem divisorError_isLittleO_cubeRoot :
    divisorError =o[Filter.atTop] (fun x : ℝ => x^(1/3:ℝ)) := by
  apply divisorError_isBigO_vanDerCorput_exponent.trans_isLittleO
  have h := isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/3-27/82)
  have hh := (Asymptotics.isBigO_refl (fun x : ℝ => x^(27/82:ℝ)) Filter.atTop).mul_isLittleO h
  apply hh.congr'
  · filter_upwards with x
    simp only [Real.rpow_two]
  · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with x hx
    simp only [←Real.rpow_add hx]
    norm_num

end AnalyticNumberTheory.DivisorProblems
