import AnalyticNumberTheory.DivisorProblems.ReciprocalDivisorBlocks

/-!
# Balancing the divisor-problem exponent pairs

The two families overlap at block length `x^(2/5)`. Smoothing at
frequency comparable to `D/x^(27/82)` gives the same power throughout.
-/

open Real Finset
open AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

private theorem rescale_frequency {h x K g : ℝ} (hh : 0<h) (hx : 0<x) (hK : 0<K)
    (hg : 0≤g) (hg' : g≤1) :
    (h*x)^g≤(K*x)^g*max 1 (h/K) := by
  let m := max 1 (h/K)
  have hm : 1≤m := le_max_left ..
  have hm0 : 0≤m := by linarith
  have hhm : h≤m*K := (div_le_iff₀ hK).mp (le_max_right ..)
  have hp := Real.rpow_le_rpow (mul_pos hh hx).le (mul_le_mul_of_nonneg_right hhm hx.le) hg
  apply hp.trans
  rw [mul_assoc,Real.mul_rpow hm0 (mul_pos hK hx).le,mul_comm]
  exact mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hm hg').trans_eq (Real.rpow_one m)) (by positivity)

private theorem reciprocal_transform_remainder {x D A : ℝ} (hx : 1≤x) (hD : 1≤D)
    (hDx : D^2≤x) (ha : x≤A) (hax : A≤9*x^2) :
    249*(1+Real.sqrt ((2*D)^3/A))*(1+Real.log (6+4*A/D^2)) ≤
      249*4*(1+Real.log 42+40)*x^(27/82:ℝ) := by
  have hx' : 0<x := by linarith
  have hD' : 0<D := by linarith
  have hA : 0<A := hx'.trans_le ha
  have hDlog := Real.log_le_log (sq_pos_of_pos hD') hDx
  rw [Real.log_pow,Nat.cast_ofNat] at hDlog
  have hAlog := Real.log_le_log hx' ha
  have hG : Real.sqrt ((2*D)^3/A)≤3*x^(1/4:ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_sqrt,Real.log_div,Real.log_pow,Real.log_mul,Real.log_rpow]
    have h23 : 3*Real.log 2≤2*Real.log 3 := by
      have h := Real.log_le_log (by norm_num : 0<(2:ℝ)^3) (by norm_num : (2:ℝ)^3≤3^2)
      simpa only [Real.log_pow,Nat.cast_ofNat] using h
    norm_num only [Nat.cast_ofNat] at *
    linarith only [hDlog,hAlog,h23]
  have hlog : Real.log (6+4*A/D^2)≤Real.log 42+2*Real.log x := by
    have he := Real.log_le_log (by positivity : 0<6+4*A/D^2)
      (show 6+4*A/D^2≤42*x^2 by
        have hd := div_le_self (by positivity : 0≤4*A) (one_le_pow₀ hD (n:=2))
        nlinarith only [hax,hd,one_le_pow₀ hx (n:=2)])
    simpa only [Real.log_mul (by norm_num : (42:ℝ)≠0) (pow_ne_zero 2 hx'.ne'),Real.log_pow,Nat.cast_ofNat] using he
  have hnon := Real.log_nonneg (by linarith [show 0≤4*A/D^2 by positivity] : 1≤6+4*A/D^2)
  have hp := Real.log_le_rpow_div hx'.le (by norm_num : (0:ℝ)<1/20)
  have hp' := Real.one_le_rpow hx (by norm_num : (0:ℝ)≤1/20)
  have hq := Real.one_le_rpow hx (by norm_num : (0:ℝ)≤1/4)
  have h42 := Real.log_nonneg (by norm_num : (1:ℝ)≤42)
  have hlog' : 1+Real.log (6+4*A/D^2)≤(1+Real.log 42+40)*x^(1/20:ℝ) := by
    nlinarith only [hlog,hp,hp',mul_nonneg h42 (sub_nonneg.mpr hp')]
  have hmaj := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1:ℝ)/4+1/20≤27/82)
  rw [Real.rpow_add hx'] at hmaj
  calc
    _ ≤ 249*(4*x^(1/4:ℝ))*((1+Real.log 42+40)*x^(1/20:ℝ)) := by gcongr <;> linarith
    _ = 249*4*(1+Real.log 42+40)*(x^(1/4:ℝ)*x^(1/20:ℝ)) := by ring
    _ ≤ _ := by gcongr

/-- The reciprocal sum on any subinterval of `[D,2D]` up to frequency
`K²`, where `K≤3D/x^(27/82)`. High frequencies may cost a factor `h/K`. -/
theorem reciprocal_frequency_divisor_exponent :
    ∃ C≥1, ∀ {x D h K : ℝ} {a b : ℕ},1≤x → 1≤D → D^2≤x → D≤a → a≤b →
      (b:ℝ)≤2*D → 1≤K → K≤3*D/x^(27/82:ℝ) → 1≤h → h≤K^2 →
      ‖∑ n∈Ioc a b,e (h*x/n)‖≤C*x^(27/82:ℝ)*max 1 (h/K) := by
  obtain ⟨B,hB,H₁⟩ := reciprocal_third_derivative_block
  obtain ⟨C,hC,H₂⟩ := reciprocal_transformed_derivative_block
  let V := 249*4*(1+Real.log 42+40)
  have hV : 0≤V := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤42); dsimp [V]; positivity
  refine ⟨6*B+6*C+V,by linarith,?_⟩
  intro x D h K a b hx hD hDx ha hab hb hK hK' hh hh'
  let Y := x^(27/82:ℝ)
  let m := max 1 (h/K)
  have hp : 0<x := by linarith
  have hd : 0<D := by linarith
  have hk : 0<K := by linarith
  have hh0 : 0<h := by linarith
  have hY : 1≤Y := Real.one_le_rpow hx (by norm_num)
  have hm : 1≤m := le_max_left ..
  have hY0 : 0≤Y := by linarith
  have hm0 : 0≤m := by linarith
  have hlogD := Real.log_le_log (sq_pos_of_pos hd) hDx
  rw [Real.log_pow,Nat.cast_ofNat] at hlogD
  have hlogK := Real.log_le_log hk hK'
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow] at hlogK
  have hxlog := Real.log_nonneg hx
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
  have hscale {g v : ℝ} (hg : 0≤g) (hg' : g≤1)
      (he : g*(Real.log K+Real.log x)+v*Real.log D≤Real.log 3+(27/82)*Real.log x) :
      (h*x)^g*D^v≤3*Y*m := by
    have hbase : (K*x)^g*D^v≤3*Y := by
      apply (Real.log_le_log_iff (by positivity) (mul_pos (by norm_num : (0:ℝ)<3) (by dsimp [Y]; positivity))).mp
      dsimp [Y]
      simpa (disch := positivity) only [Real.log_mul,Real.log_rpow] using he
    calc _ ≤ ((K*x)^g*m)*D^v := mul_le_mul_of_nonneg_right (rescale_frequency hh0 hp hk hg hg') (by positivity)
         _ = ((K*x)^g*D^v)*m := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hbase hm0
  by_cases hs : D≤x^(2/5:ℝ)
  · have hs' := Real.log_le_log hd hs
    rw [Real.log_rpow hp] at hs'
    have h₁ := hscale (v:=1/3) (by norm_num : (0:ℝ)≤1/6) (by norm_num) (by linarith)
    have h₂ : (h*x)^(-(1/6):ℝ)*D^(7/6:ℝ)≤Y := by
      apply (Real.log_le_log_iff (by positivity) (by dsimp [Y]; positivity)).mp
      dsimp [Y]
      simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
      linarith only [hs',hxlog,Real.log_nonneg hh]
    have hS := H₁ (a:=a) (b:=b) (mul_pos hh0 hp) hD ha hb
    apply hS.trans
    change _≤(6*B+6*C+V)*Y*m
    nlinarith only [mul_le_mul_of_nonneg_left h₁ (by linarith : 0≤B),
      mul_le_mul_of_nonneg_left (h₂.trans (le_mul_of_one_le_right hY0 hm)) (by linarith : 0≤B),
      mul_nonneg (show 0≤(2*B+6*C+V) by linarith) (mul_nonneg hY0 hm0)]
  · have hs' := Real.log_le_log (Real.rpow_pos_of_pos hp _) (not_le.mp hs).le
    rw [Real.log_rpow hp] at hs'
    have h₁ := hscale (v:=-(1/5)) (by norm_num : (0:ℝ)≤11/30) (by norm_num) (by linarith)
    have h₂ := hscale (v:=-(11/20)) (by norm_num : (0:ℝ)≤61/120) (by norm_num) (by linarith)
    have hax : x≤h*x := le_mul_of_one_le_left hp.le hh
    have hK3 : K≤3*D := hK'.trans (div_le_self (by positivity) hY)
    have hA : h*x≤9*x^2 := by
      calc _ ≤ (3*D)^2*x := mul_le_mul_of_nonneg_right (hh'.trans (pow_le_pow_left₀ hk.le hK3 2)) hp.le
           _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hDx hp.le]
    have hE := reciprocal_transform_remainder hx hD hDx hax hA
    have hS := H₂ hD (hDx.trans hax) ha hab hb
    apply hS.trans
    change _≤(6*B+6*C+V)*Y*m
    change _≤V*Y at hE
    nlinarith only [mul_le_mul_of_nonneg_left h₁ (by linarith : 0≤C),
      mul_le_mul_of_nonneg_left h₂ (by linarith : 0≤C),
      hE.trans (le_mul_of_one_le_right (mul_nonneg hV hY0) hm),
      mul_nonneg (show 0≤6*B by linarith) (mul_nonneg hY0 hm0)]

end AnalyticNumberTheory.DivisorProblems
