import AnalyticNumberTheory.RiemannZeta.DivisorPowerTails
import AnalyticNumberTheory.RiemannZeta.FourthMomentMainTerms

/-!
# The two factors on the right boundary of the fourth-moment contour

At real part two the direct tail of zeta squared has reciprocal-square
mean decay. The reflected finite divisor polynomial has a fourth-power
mean bound. On the contour's dyadic segment their product therefore has
integral of order T(1+log T)^3.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

private theorem cutoff_bounds {T : ℝ} (ht : 16*Real.pi≤T) :
    let N := ⌊T/(4*Real.pi)⌋₊
    1≤N ∧ (N:ℝ)≤T ∧ T≤8*Real.pi*N := by
  intro N
  have hp : 0<4*Real.pi := by positivity
  have hT : 0<T := (by positivity : 0<16*Real.pi).trans_le ht
  have hmin : 4≤T/(4*Real.pi) := (le_div_iff₀ hp).mpr (by linarith)
  refine ⟨(Nat.le_floor_iff (by positivity)).mpr (by norm_num;linarith),
    (Nat.floor_le (by positivity)).trans (div_le_self hT.le (by linarith [Real.pi_gt_three])),?_⟩
  have h := (div_lt_iff₀ hp).mp (Nat.lt_floor_add_one (T/(4*Real.pi)))
  change T≤8*Real.pi*⌊T/(4*Real.pi)⌋₊
  have hf : 1≤⌊T/(4*Real.pi)⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by norm_num;linarith)
  have hg : (1:ℝ)≤⌊T/(4*Real.pi)⌋₊ := by exact_mod_cast hf
  nlinarith only [h,mul_le_mul_of_nonneg_left hg Real.pi_pos.le]

private theorem reflected_norm (N : ℕ) (t : ℝ) :
    ‖divisorPolynomial N (1-((2:ℂ)+t*I))‖=‖divisorPolynomial N ((-1:ℂ)+t*I)‖ := by
  rw [show 1-((2:ℂ)+t*I)=conj ((-1:ℂ)+t*I) by simp;ring,divisorPolynomial_conj,Complex.norm_conj]

private theorem reflected_point {N : ℕ} (hN : 1≤N) (t : ℝ) :
    ‖divisorPolynomial N (1-((2:ℂ)+t*I))‖≤2*(N:ℝ)^2*(1+Real.log N) := by
  rw [reflected_norm,divisorPolynomial,dirichletPoly]
  apply (norm_sum_le ..).trans
  apply le_trans (b:=(N:ℝ)*∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ))
  · rw [mul_sum];apply sum_le_sum;intro n hn
    rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos (Finset.mem_Icc.mp hn).1]
    have hσ : (-((-1:ℂ)+t*I)).re=1 := by simp
    rw [hσ,Real.rpow_one,mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by positivity)
  · apply (mul_le_mul_of_nonneg_left (sum_divisors_card_le_log hN) (Nat.cast_nonneg _)).trans_eq;ring

private theorem reflected_mean {N : ℕ} (hN : 1≤N) {T : ℝ} (hT : 0≤T) :
    (∫t in T..(2*T),‖divisorPolynomial N (1-((2:ℂ)+t*I))‖^2)≤
      (T+2*Real.pi*N)*(N:ℝ)^3*(1+Real.log N)^3 := by
  simp_rw [reflected_norm]
  let a := fun n : ℕ => (n.divisors.card:ℂ)
  have H := dirichletPoly_mean_sq_asymp a N (-1) (t₀:=T) (t₁:=2*T) (by linarith)
  rw [Real.norm_eq_abs,show 2*T-T=T by ring] at H
  have he (n : ℕ) : ‖a n‖^2*(n:ℝ)^(-2*(-1:ℝ))=(n.divisors.card:ℝ)^2*(n:ℝ)^2 := by
    simp [a]
  simp_rw [he] at H
  have hdiag : (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2*(n:ℝ)^2)≤(N:ℝ)^3*(1+Real.log N)^3 := by
    apply le_trans (b:=(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)*(N:ℝ)^2)
    · rw [sum_mul];apply sum_le_sum;intro n hn
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (Finset.mem_Icc.mp hn).2) 2) (sq_nonneg _)
    · have h := sum_Icc_card_divisors_sq_le N
      rw [max_eq_left hN] at h
      apply (mul_le_mul_of_nonneg_right h (sq_nonneg (N:ℝ))).trans_eq;ring
  have h := mul_le_mul_of_nonneg_left hdiag (show 0≤T+2*Real.pi*N by positivity)
  change (∫t in T..(2*T),‖dirichletPoly a N ((-1:ℂ)+t*I)‖^2)≤_
  norm_num at H
  linarith only [(abs_le.mp H).2,h]

/-- Uniform pointwise estimates for the two factors at the right boundary.
The ordinate is unrestricted. -/
theorem fourthMoment_right_boundary_pointwise : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},16*Real.pi≤T → ∀ t : ℝ,
    let N := ⌊T/(4*Real.pi)⌋₊
    ‖divisorPolynomial N (1-((2:ℂ)+t*I))‖≤C*T^2*(1+Real.log T) ∧
    ‖riemannZeta ((2:ℂ)+t*I)^2-divisorPolynomial N ((2:ℂ)+t*I)‖≤C/T*(1+Real.log T) := by
  obtain ⟨B,hB,H⟩ := zeta_square_tail_pointwise
  let C := 2+8*Real.pi*B
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro T ht t N
  obtain ⟨hN,hn,hTn⟩ := cutoff_bounds ht
  change (N:ℝ)≤T at hn
  change T≤8*Real.pi*N at hTn
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hTp := hp.trans_le hn
  have hlog : 1+Real.log N≤1+Real.log T := add_le_add_right (Real.log_le_log hp hn) 1
  have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
  constructor
  · apply (reflected_point hN t).trans
    have hC : 2≤C := by dsimp [C];linarith only [mul_nonneg (show 0≤8*Real.pi by positivity) hB.le]
    exact mul_le_mul (mul_le_mul hC (pow_le_pow_left₀ hp.le hn 2) (sq_nonneg _) (by dsimp [C];positivity)) hlog hL (by dsimp [C];positivity)
  · apply (H hN t).trans
    have hcoef : B/N≤C/T := by
      rw [div_le_div_iff₀ hp hTp];dsimp only [C]
      nlinarith only [mul_le_mul_of_nonneg_left hTn hB.le,hp.le]
    exact mul_le_mul hcoef hlog hL (by dsimp [C];positivity)

/-- Dyadic second-moment estimates for the reflected polynomial and the
infinite tail, with a common absolute constant and cubic logarithmic loss. -/
theorem fourthMoment_right_boundary_means : ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},16*Real.pi≤T →
    let N := ⌊T/(4*Real.pi)⌋₊
    (∫t in T..(2*T),‖divisorPolynomial N (1-((2:ℂ)+t*I))‖^2)≤C*T^4*(1+Real.log T)^3 ∧
    (∫t in T..(2*T),‖riemannZeta ((2:ℂ)+t*I)^2-divisorPolynomial N ((2:ℂ)+t*I)‖^2)≤
      C*T^(-(2:ℤ))*(1+Real.log T)^3 := by
  obtain ⟨B,hB,H⟩ := zeta_square_tail_mean
  let D := 8*Real.pi+4*weightedHilbertConstant
  let K := 8*Real.pi
  let C := 1+2*Real.pi+D*B*K^2
  have hD : 0<D := by dsimp [D];positivity [weightedHilbertConstant_pos]
  have hK : 0<K := by dsimp [K];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro T ht N
  obtain ⟨hN,hn,hTn⟩ := cutoff_bounds ht
  change (N:ℝ)≤T at hn
  change T≤K*N at hTn
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hTp := hp.trans_le hn
  have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
  have hlogs := pow_le_pow_left₀ hL (add_le_add_right (Real.log_le_log hp hn) 1) 3
  constructor
  · apply (reflected_mean hN hTp.le).trans
    have hsize : T+2*Real.pi*N≤(1+2*Real.pi)*T := by
      linarith only [mul_le_mul_of_nonneg_left hn (show 0≤2*Real.pi by positivity)]
    have hscale : (T+2*Real.pi*N)*(N:ℝ)^3≤C*T^4 := by
      apply (mul_le_mul hsize (pow_le_pow_left₀ hp.le hn 3) (by positivity) (by positivity)).trans
      dsimp [C];nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hD.le hB.le) (sq_nonneg K)) (pow_nonneg hTp.le 4)]
    exact mul_le_mul hscale hlogs (pow_nonneg hL _) (by positivity)
  · apply (H hN hTp.le).trans
    have hcoef : T/(N:ℝ)+4*weightedHilbertConstant≤D := by
      dsimp [D];have h := (div_le_iff₀ hp).mpr hTn;dsimp [K] at h;linarith
    have hinv : B/(N:ℝ)^2≤B*K^2/T^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hTp.le hTn 2) hB.le]
    have hC' : D*(B*K^2/T^2)≤C*T^(-(2:ℤ)) := by
      norm_num only [zpow_neg,zpow_ofNat,←div_eq_mul_inv]
      rw [←mul_div_assoc]
      exact div_le_div_of_nonneg_right (by dsimp [C];nlinarith only [Real.pi_pos] : D*(B*K^2)≤C) (sq_nonneg T)
    rw [←mul_assoc]
    exact mul_le_mul ((mul_le_mul hcoef hinv (by positivity) hD.le).trans hC') hlogs (pow_nonneg hL _) (by positivity)

end AnalyticNumberTheory.RiemannZeta
