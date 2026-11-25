import AnalyticNumberTheory.ExponentialSums.VinogradovLinearKernels
import AnalyticNumberTheory.ExponentialSums.VinogradovLogTaylor
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cancellation in the logarithmic Taylor coefficients

For `N^(2l) ≤ t ≤ N^(2l+2)`, all degrees between `3l` and `4l` give
a saving in their respective frequency boxes. The estimates are uniform
in the polynomial degree and in the moment parameter.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem logCoefficient_window {X T l m D V : ℝ} (hX : 100≤X) (hl : 8≤l)
    (hT : 2*l*X≤T) (hT' : T≤(2*l+2)*X) (hm : 3*l≤m) (hm' : m≤4*l)
    (hD : m*X-T≤D) (hD' : D≤7+2*m+m*X-T) (hV : m*X/3≤V) :
    T/10≤V ∧ T/10≤D ∧ D≤2*V-T/10 ∧ D+1≤4*T := by
  have h1 := mul_le_mul_of_nonneg_right hm (by linarith : 0≤X)
  have h2 := mul_le_mul_of_nonneg_right hm' (by linarith : 0≤X)
  have h3 := mul_le_mul_of_nonneg_right hl (by linarith : 0≤X)
  have h4 := mul_le_mul_of_nonneg_right hX (by linarith : 0≤l)
  constructor
  · nlinarith only [hT',hV,h1,h3,hX]
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hT',hD,h1,h3,hX]
  · nlinarith only [hD',hV,hT,h2,hm',h4,hl]
  · nlinarith only [hD',hT,h2,hm',h4,hl]

private theorem logTaylor_reciprocal {r : ℕ} (j : Fin r) {t n : ℝ} (ht : 0<t) (hn : 0<n) :
    let m := j.val+1
    0 < |logTaylorCoefficients r t n j| ∧
    Real.log (1/|logTaylorCoefficients r t n j|) =
      Real.log (2*Real.pi) + Real.log (m:ℝ) + m*Real.log n - Real.log t := by
  intro m
  have hm : 0<(m:ℝ) := by dsimp [m]; positivity
  have hp : 0<2*Real.pi := by positivity
  have hA : |logTaylorCoefficients r t n j| = t/(2*Real.pi)*(1/n)^m/m := by
    simp [logTaylorCoefficients,abs_div,abs_mul,abs_pow,abs_of_pos ht,abs_of_pos hn,
      abs_of_pos hp,m, abs_of_nonneg (by positivity : 0≤(j.val:ℝ)+1)]
  rw [hA]
  refine ⟨by positivity,?_⟩
  rw [Real.log_div one_ne_zero (by positivity),Real.log_one,
    Real.log_div (by positivity) hm.ne',Real.log_mul (by positivity) (by positivity),
    Real.log_div ht.ne' hp.ne',Real.log_pow,Real.log_div one_ne_zero hn.ne',Real.log_one]
  ring

/-- Throughout a block `N≤n≤2N`, each degree `3l≤j+1≤4l` saves a fixed power
of `t` in the symmetric linear kernel. -/
theorem logTaylor_kernel_window {r s a : ℕ} (j : Fin r) {N n t l : ℝ}
    (hN : 0<N) (hX : 100≤Real.log N) (hn : N≤n) (hn' : n≤2*N)
    (ht : 0<t) (hl : 8≤l) (hlT : 2*l*Real.log N≤Real.log t)
    (hTl : Real.log t ≤(2*l+2)*Real.log N)
    (hm : 3*l≤(j.val+1:ℕ)) (hm' : ((j.val+1:ℕ):ℝ)≤4*l)
    (hs : 1≤s) (ha : 0<a) (haN : Real.log N/3 ≤ Real.log (a:ℝ)) :
    vinogradovLinearKernel (s*a^(j.val+1)) (logTaylorCoefficients r t n j) ≤
      5840*(2*(s*a^(j.val+1):ℕ)+1:ℝ)^2 * t^(-(1/20):ℝ) := by
  let m := j.val+1
  let R := s*a^m
  let L := (2*R+1:ℝ)
  let θ := logTaylorCoefficients r t n j
  let D := Real.log (1/|θ|)
  have hnr := hN.trans_le hn
  have hm0 : 0<(m:ℝ) := by dsimp [m]; positivity
  have hm1 : (1:ℝ)≤m := by dsimp [m]; simp
  have hL0 : 0<L := by dsimp [L]; positivity
  have hA0 : 0<(a:ℝ) := by exact_mod_cast ha
  obtain ⟨hθ,hD⟩ := logTaylor_reciprocal j ht hnr
  change 0 < |θ| at hθ
  change D = Real.log (2*Real.pi)+Real.log (m:ℝ)+m*Real.log n-Real.log t at hD
  have h2pi : 1≤2*Real.pi := by linarith only [Real.pi_gt_three]
  have h2log : Real.log (2:ℝ) ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hnlog : Real.log n ≤ Real.log N+1 := by
    have H := Real.log_le_log hnr hn'
    rw [Real.log_mul (by norm_num) hN.ne'] at H; linarith
  have hlogpi := Real.log_le_sub_one_of_pos (show 0<2*Real.pi by positivity)
  have hV : (m:ℝ)*Real.log N/3 ≤ Real.log L := by
    have hR : (a:ℝ)^m ≤ L := by
      have ha' : a^m≤R := Nat.le_mul_of_pos_left _ (by omega)
      change _ ≤ 2*(R:ℝ)+1
      have hh : (a:ℝ)^m ≤ (R:ℝ) := by exact_mod_cast ha'
      linarith only [hh,Nat.cast_nonneg (α:=ℝ) R]
    have H := Real.log_le_log (pow_pos hA0 m) hR
    rw [Real.log_pow] at H
    linarith only [H,mul_le_mul_of_nonneg_left haN hm0.le]
  obtain ⟨hv,hd,hd',hlog⟩ := logCoefficient_window hX hl hlT hTl hm hm'
    (show (m:ℝ)*Real.log N-Real.log t≤D by
      linarith only [hD,Real.log_nonneg h2pi,Real.log_nonneg hm1,
        mul_le_mul_of_nonneg_left (Real.log_le_log hN hn) hm0.le])
    (show D≤7+2*(m:ℝ)+m*Real.log N-Real.log t by
      nlinarith only [hD,hlogpi,Real.pi_lt_four,Real.log_le_sub_one_of_pos hm0,
        mul_le_mul_of_nonneg_left hnlog hm0.le]) hV
  have hT : 1≤Real.log t := by nlinarith only [hlT,mul_le_mul hX hl (by norm_num) (by linarith)]
  let U := t^(1/10:ℝ)
  have hU0 : 0<U := Real.rpow_pos_of_pos ht _
  have hUlog : Real.log U=Real.log t/10 := by rw [Real.log_rpow ht]; ring
  have hU : 1≤U := (Real.log_le_log_iff one_pos hU0).mp (by rw [Real.log_one,hUlog]; linarith)
  have hz : 0<1/|θ| := by positivity
  have hls : U≤L := (Real.log_le_log_iff hU0 hL0).mp (by rwa [hUlog])
  have huθ : U ≤ 1/|θ| := (Real.log_le_log_iff hU0 hz).mp (by rwa [hUlog])
  have hsmall : |θ|≤1/U := (le_div_iff₀ hU0).mpr (by simpa [mul_comm] using (le_div_iff₀ hθ).mp huθ)
  have hlarge : 1/|θ|≤L^2/U := by
    apply (Real.log_le_log_iff hz (by positivity)).mp
    rw [Real.log_div (by positivity) hU0.ne',Real.log_pow,hUlog]
    exact_mod_cast hd'
  have hlogH : Real.log (2/|θ|) ≤ 4*Real.log t := by
    rw [show 2/|θ|=2*(1/|θ|) by ring,Real.log_mul (by norm_num) hz.ne']
    change Real.log 2+D≤_; linarith only [hlog,h2log]
  have H := vinogradovLinearKernel_saving R hθ hU (by linarith : 1≤4*Real.log t) hls hsmall hlarge hlogH
  have hx := Real.log_le_rpow_div ht.le (by norm_num : (0:ℝ)<1/20)
  change _ ≤ 5840*L^2*t^(-(1/20):ℝ)
  apply H.trans
  change 73*(4*Real.log t)*(L^2/t^(1/10:ℝ)) ≤ _
  rw [show (1/10:ℝ)=1/20+1/20 by norm_num,Real.rpow_add ht,Real.rpow_neg ht.le]
  have hp := Real.rpow_pos_of_pos ht (1/20)
  field_simp
  nlinarith only [hx]

end AnalyticNumberTheory.ExponentialSums
