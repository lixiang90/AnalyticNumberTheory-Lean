import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import AnalyticNumberTheory.AnalyticTools.GaussianMeans

/-!
# Mean values of shifted divisor polynomials

The divisor bound makes the square diagonal of the divisor polynomial
summable on every line strictly to the right of the critical line.
The finite mean-value inequality then holds uniformly in the ordinate.
-/

open Complex Real Finset Filter MeasureTheory
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.ExponentialSums
open scoped Topology

namespace AnalyticNumberTheory.RiemannZeta

/-- The polynomial formed from the positive divisor counts. -/
noncomputable def divisorPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  dirichletPoly (fun n => (n.divisors.card:ℂ)) N s

private theorem divisor_diagonal_bounded {η : ℝ} (hη : 0 < η) :
    ∃ B > 0, ∀ N : ℕ,
      ∑ n ∈ Icc 1 N, ‖(n.divisors.card:ℂ)‖^2*(n:ℝ)^(-2*(1/2+η)) ≤ B := by
  obtain ⟨K,hK,H⟩ := card_divisors_le_rpow (half_pos hη)
  let f := fun n : ℕ => K^2*(n:ℝ)^(-1-η)
  have hs : Summable f := (Real.summable_nat_rpow.mpr (by linarith : -1-η < -1)).mul_left (K^2)
  refine ⟨1+∑' n, f n,?_,fun N => ?_⟩
  · have : 0 ≤ ∑' n, f n := tsum_nonneg fun n => by dsimp [f]; positivity
    linarith
  have hb : ∑ n ∈ Icc 1 N, ‖(n.divisors.card:ℂ)‖^2*(n:ℝ)^(-2*(1/2+η)) ≤ ∑ n ∈ Icc 1 N, f n := by
    refine sum_le_sum fun n hn => ?_
    have h1 := (mem_Icc.mp hn).1
    have hp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    simp only [Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (H n h1) 2)
      (Real.rpow_nonneg hp.le _)).trans_eq
    rw [mul_pow,← Real.rpow_mul_natCast hp.le,mul_assoc,← Real.rpow_add hp]
    dsimp [f]
    congr 2; ring
  exact hb.trans ((hs.sum_le_tsum _ (fun n _ => by dsimp [f]; positivity)).trans (by linarith))

/-- A bound independent of the ordinate for the mean square on an arbitrary
interval of length `b-a` on a fixed line `1/2+η`. -/
theorem divisorPolynomial_vertical_mean_bound {η : ℝ} (hη : 0 < η) :
    ∃ B > 0, ∀ (N : ℕ) {a b : ℝ}, a ≤ b →
      (∫ t in a..b, ‖divisorPolynomial N (((1/2+η:ℝ):ℂ)+t*I)‖^2) ≤
        B*((b-a)+2*π*N) := by
  obtain ⟨B,hB,H⟩ := divisor_diagonal_bounded hη
  refine ⟨B,hB,fun N a b hab => ?_⟩
  have hm := dirichletPoly_mean_sq_asymp (fun n => (n.divisors.card:ℂ)) N (1/2+η) hab
  rw [Real.norm_eq_abs] at hm
  have hp : 0 ≤ b-a+2*π*N := by positivity
  have hs := mul_le_mul_of_nonneg_left (H N) hp
  unfold divisorPolynomial
  linarith only [(abs_le.mp hm).2,hs]

/-- Continuity of the divisor polynomial on a vertical line. -/
theorem divisorPolynomial_continuous (N : ℕ) (σ : ℝ) :
    Continuous (fun u : ℝ => divisorPolynomial N ((σ:ℂ)+u*I)) := by
  unfold divisorPolynomial dirichletPoly
  apply continuous_finsetSum
  intro n hn
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hn).1; omega)
  simp only [Complex.cpow_def_of_ne_zero hn']
  fun_prop

/-- For each finite cutoff the polynomial is bounded on each vertical line. -/
theorem divisorPolynomial_vertical_bounded (N : ℕ) (σ : ℝ) :
    ∃ M : ℝ, ∀ u : ℝ, ‖divisorPolynomial N ((σ:ℂ)+u*I)‖ ≤ M := by
  refine ⟨∑ n ∈ Icc 1 N, (n.divisors.card:ℝ)*(n:ℝ)^(-σ),fun u => ?_⟩
  unfold divisorPolynomial dirichletPoly
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro n hn
  have hn' : 0 < n := (mem_Icc.mp hn).1
  simp only [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos hn']
  simp

/-- Gaussian convolution of a divisor polynomial on either the positive or
negative dyadic interval. The majorant of the kernel may depend on `t`. -/
theorem divisorPolynomial_gaussian_dyadic {η : ℝ} (hη : 0 < η) :
    ∃ D > 0, ∀ {T K : ℝ} {N : ℕ}, 1 ≤ T → 0 ≤ K → (N:ℝ) ≤ 2*T^(1+η) →
      ∀ (negative : Bool) (F : ℝ → ℝ → ℂ),
      (∀ t ∈ Set.Ioc T (2*T), ∀ v, ‖F t v‖ ≤ K*T^η*Real.exp (-(1/2:ℝ)*v^2)) →
      (∫ t in T..2*T, ‖∫ v, F t v*divisorPolynomial N
        (((1/2+η:ℝ):ℂ)+((if negative then v-t else v+t):ℝ)*I)‖^2) ≤
          D*K^2*T^(1+3*η) := by
  obtain ⟨B,hB,hm⟩ := divisorPolynomial_vertical_mean_bound hη
  refine ⟨2*π*B*(1+4*π),by positivity,?_⟩
  intro T K N hT hK hN negative F hF
  let p := fun u : ℝ => divisorPolynomial N (((1/2+η:ℝ):ℂ)+u*I)
  let P := fun t v : ℝ => p (if negative then v-t else v+t)
  have hp : Continuous p := divisorPolynomial_continuous ..
  have hc : Continuous (Function.uncurry P) := by
    cases negative <;> apply hp.comp <;> first | exact continuous_snd.add continuous_fst | exact continuous_snd.sub continuous_fst
  obtain ⟨M,hM⟩ := divisorPolynomial_vertical_bounded N (1/2+η)
  have he (v : ℝ) : (∫ t in T..2*T, ‖P t v‖^2) ≤ B*(T+2*π*N) := by
    cases negative
    · change (∫ t in T..2*T, (fun u => ‖p u‖^2) (v+t)) ≤ _
      rw [intervalIntegral.integral_comp_add_left (fun u : ℝ => ‖p u‖^2) v]
      simpa only [show v+2*T-(v+T)=T by ring] using
        hm N (a := v+T) (b := v+2*T) (by linarith)
    · change (∫ t in T..2*T, (fun u => ‖p u‖^2) (v-t)) ≤ _
      rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => ‖p u‖^2) v]
      simpa only [show v-T-(v-2*T)=T by ring] using
        hm N (a := v-2*T) (b := v-T) (by linarith)
  have hT' : 0 < T := by linarith
  have h := gaussian_weighted_mean_bound (show T ≤ 2*T by linarith) (mul_nonneg hK (Real.rpow_nonneg hT'.le η))
    F P hc ⟨M,fun t v => hM _⟩ hF he
  apply h.trans
  have hpow : T ≤ T^(1+η) := by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hT (show (1:ℝ)≤1+η by linarith))
  have hc' : T+2*π*N ≤ (1+4*π)*T^(1+η) := by
    nlinarith only [hpow,mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
  calc _ ≤ 2*π*(K*T^η)^2*(B*((1+4*π)*T^(1+η))) := by gcongr
       _ = _ := by
         have ht : (T^η)^2*T^(1+η) = T^(1+3*η) := by
           rw [← Real.rpow_mul_natCast hT'.le,← Real.rpow_add hT']
           congr 1; push_cast; ring
         rw [← ht]
         ring

end AnalyticNumberTheory.RiemannZeta
