import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity
import AnalyticNumberTheory.DivisorProblems.DivisorCubeRoot

/-!
# A finite Möbius zero detector for the Riemann zeta function

At heights between `N` and `2N`, a zero forces the product of the length-`N`
zeta and Möbius polynomials to be small. Möbius inversion cancels every
coefficient up to `N` except the constant term. Consequently the tail
`N < n ≤ N²` has absolute value at least one half.
-/

noncomputable section

open Finset Complex Filter
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Coefficient of the product of the two length-`N` truncated polynomials. -/
def zetaDetectorCoeff (N n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, if d ≤ N ∧ n/d ≤ N then (μ d : ℂ) else 0

lemma norm_moebius_complex_le (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))

/-- The divisor function dominates the detector coefficients. -/
theorem norm_zetaDetectorCoeff_le (N n : ℕ) : ‖zetaDetectorCoeff N n‖ ≤ n.divisors.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ n.divisors, (1:ℝ) := by
      refine sum_le_sum fun d _ => ?_
      split_ifs
      · exact norm_moebius_complex_le _
      · simp
    _ = _ := by simp

/-- Initial cancellation by Möbius inversion. -/
theorem zetaDetectorCoeff_of_le {N n : ℕ} (hn : n ≤ N) :
    zetaDetectorCoeff N n = if n=1 then 1 else 0 := by
  unfold zetaDetectorCoeff
  calc
    _ = ∑ d ∈ n.divisors, (μ d:ℂ) := by
      refine sum_congr rfl fun d hd => ite_eq_left ⟨?_, (Nat.div_le_self ..).trans hn⟩
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1).trans hn
    _ = (1 : ArithmeticFunction ℂ) n := by
      have h := congrArg (fun f : ArithmeticFunction ℂ => f n) ArithmeticFunction.coe_moebius_mul_coe_zeta
      simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] using h
    _ = _ := ArithmeticFunction.one_apply

private lemma detector_fiber {N n : ℕ} (hn : 0 < n) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1*p.2=n)) =
      n.divisorsAntidiagonal.filter (fun p => p.1 ≤ N ∧ p.2 ≤ N) := by
  ext ⟨i,j⟩
  simp only [mem_filter,mem_product,mem_Icc,Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨hi,hi'⟩,⟨hj,hj'⟩⟩,h⟩; exact ⟨⟨h,hn.ne'⟩,hi',hj'⟩
  · rintro ⟨⟨h,_⟩,hi,hj⟩
    have hij : 0 < i*j := h ▸ hn
    exact ⟨⟨⟨Nat.pos_of_mul_pos_right hij,hi⟩,Nat.pos_of_mul_pos_left hij,hj⟩,h⟩

/-- Exact multiplication rule after twisting both polynomials by a completely multiplicative weight. -/
theorem zetaDetector_product_twist (g : ℕ → ℂ) (hg : ∀ m n, g (m*n) = g m * g n)
    (N : ℕ) (s : ℂ) :
    dirichletPoly (fun n => (μ n:ℂ)*g n) N s * dirichletPoly g N s =
      dirichletPoly (fun n => zetaDetectorCoeff N n * g n) (N^2) s := by
  unfold dirichletPoly
  simp only [sum_mul, mul_sum]
  rw [sum_comm, ← sum_product (f := fun p : ℕ × ℕ => (μ p.1:ℂ)*g p.1*(p.1:ℂ)^(-s)*(g p.2*(p.2:ℂ)^(-s)))]
  let D := Icc 1 N ×ˢ Icc 1 N
  have hmap (p : ℕ × ℕ) (hp : p ∈ D) : p.1*p.2 ∈ Icc 1 (N^2) := by
    have h := mem_product.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp h.1).1 (mem_Icc.mp h.2).1,
      by simpa only [sq] using Nat.mul_le_mul (mem_Icc.mp h.1).2 (mem_Icc.mp h.2).2⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun n hn => ?_
  rw [show D.filter (fun p : ℕ × ℕ => p.1*p.2=n) =
      n.divisorsAntidiagonal.filter (fun p => p.1 ≤ N ∧ p.2 ≤ N) from detector_fiber (mem_Icc.mp hn).1]
  have hterm (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) :
      (μ p.1:ℂ)*g p.1*(p.1:ℂ)^(-s)*(g p.2*(p.2:ℂ)^(-s)) = (μ p.1:ℂ)*(g n * (n:ℂ)^(-s)) := by
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    rw [← he, hg, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.1 ≤ N ∧ p.2 ≤ N), (μ p.1:ℂ)*(g n * (n:ℂ)^(-s)) :=
      sum_congr rfl fun p hp => hterm p (mem_filter.mp hp).1
    _ = _ := by
      rw [← sum_mul, sum_filter, Nat.sum_divisorsAntidiagonal (fun d k => if d ≤ N ∧ k ≤ N then (μ d:ℂ) else 0)]
      change zetaDetectorCoeff N n * (g n * _) = _
      ring

/-- Exact multiplication rule for the finite zero detector. -/
theorem zetaDetector_product (N : ℕ) (s : ℂ) :
    dirichletPoly (fun n => (μ n:ℂ)) N s * dirichletPoly (fun _ => 1) N s =
      dirichletPoly (zetaDetectorCoeff N) (N^2) s := by
  simpa only [mul_one] using zetaDetector_product_twist (fun _ => 1) (by simp) N s

/-- The product consists of one constant and its high-frequency tail. -/
theorem zetaDetector_product_eq_one_add {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    dirichletPoly (fun n => (μ n:ℂ)) N s * dirichletPoly (fun _ => 1) N s =
      1 + ∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n * (n:ℂ)^(-s) := by
  rw [zetaDetector_product, dirichletPoly, ← sum_filter_add_sum_filter_not (Icc 1 (N^2)) (fun n => n ≤ N)]
  have hNN : N ≤ N^2 := by nlinarith
  have hs : (Icc 1 (N^2)).filter (· ≤ N) = Icc 1 N := by ext n; simp only [mem_filter,mem_Icc]; omega
  have ht : (Icc 1 (N^2)).filter (fun n => ¬n ≤ N) = Ioc N (N^2) := by ext n; simp only [mem_filter,mem_Icc,mem_Ioc]; omega
  rw [hs,ht]
  congr 1
  rw [sum_eq_single 1]
  · simp [zetaDetectorCoeff_of_le hN]
  · intro n hn hn'
    simp [zetaDetectorCoeff_of_le (mem_Icc.mp hn).2, hn']
  · simp [hN]

private lemma norm_moebiusPoly_le {N : ℕ} {s : ℂ} (hs : 1/2 ≤ s.re) :
    ‖dirichletPoly (fun n => (μ n:ℂ)) N s‖ ≤ 2*Real.sqrt N := by
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum _).trans (DivisorProblems.sum_Icc_inv_sqrt_le N)
  intro n hn
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn).1, neg_re]
  apply (mul_le_mul_of_nonneg_right (norm_moebius_complex_le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
  rw [one_mul, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le hnr (by linarith)

/-- The tail detects every sufficiently high zeta zero on or to the right of
`Re(s) = 3/4` in the height band `N ≤ |Im(s)| ≤ 2N`. -/
theorem zetaDetector_large_at_zero :
    ∀ᶠ N : ℕ in atTop, ∀ {s : ℂ}, 3/4 ≤ s.re → (N:ℝ) ≤ |s.im| → |s.im| ≤ 2*N →
      riemannZeta s = 0 →
      1/2 ≤ ‖∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n * (n:ℂ)^(-s)‖ := by
  obtain ⟨C,hC,happrox⟩ := riemannZeta_approx_dirichletPoly_sub_bound (c:=2)
    (by norm_num) (by linarith [Real.pi_gt_three])
  have hg : Tendsto (fun N : ℕ => (N:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually_ge_atTop (4*(1+C)), eventually_ge_atTop (1:ℕ)] with N hlarge hN
  intro s hs hlow hhigh hz
  have hnr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have ht := happrox (N:=N) hN (σ:=s.re) (t:=s.im) (by linarith) (hnr.trans hlow) hhigh
  rw [Complex.re_add_im, hz, zero_sub, norm_neg] at ht
  have hpoly : ‖dirichletPoly (fun _ => 1) N s‖ ≤ (1+C)*(N:ℝ)^(-(3/4:ℝ)) := by
    have h1 : (N:ℝ)^(1-s.re)/|s.im| ≤ (N:ℝ)^(-s.re) := by
      apply (div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) hn0 hlow).trans_eq
      rw [← Real.rpow_sub_one hn0.ne']
      congr 1; ring
    have hpow := Real.rpow_le_rpow_of_exponent_le hnr (by linarith : -s.re ≤ -(3/4:ℝ))
    apply ht.trans
    calc
      _ ≤ (1+C)*(N:ℝ)^(-s.re) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by linarith)
  have hm := norm_moebiusPoly_le (N:=N) (s:=s) (by linarith)
  have hbd : 2*Real.sqrt N*((1+C)*(N:ℝ)^(-(3/4:ℝ))) ≤ 1/2 := by
    rw [Real.sqrt_eq_rpow, show 2*(N:ℝ)^(1/2:ℝ)*((1+C)*(N:ℝ)^(-(3/4:ℝ))) =
      2*(1+C)*((N:ℝ)^(1/2:ℝ)*(N:ℝ)^(-(3/4:ℝ))) by ring, ← Real.rpow_add hn0]
    norm_num
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have hprod := (mul_le_mul hm hpoly (norm_nonneg _) (by positivity)).trans hbd
  rw [← norm_mul, zetaDetector_product_eq_one_add hN] at hprod
  have htri := norm_sub_norm_le (1 : ℂ) (-(∑ n ∈ Ioc N (N^2), zetaDetectorCoeff N n*(n:ℂ)^(-s)))
  rw [norm_one, norm_neg, sub_neg_eq_add] at htri
  linarith

end AnalyticNumberTheory.PrimeDistribution
