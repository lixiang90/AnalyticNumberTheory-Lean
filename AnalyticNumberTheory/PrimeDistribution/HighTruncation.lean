import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula
import AnalyticNumberTheory.RiemannZeta.TrivialZeroBounds

/-!
# Uniform truncation at large heights

At heights above a fixed power of x, expanding Perron rectangles on the line
of real part two make all three auxiliary edges bounded. The ordinary Perron
estimate costs only O(log x), also at prime powers and zero ordinates.
-/

noncomputable section

open Filter Finset Complex
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

private theorem finite_trivial_bound {x : ℝ} (hx : 0 < x) (hL : 1 ≤ Real.log x) (N : ℕ) :
    ‖∑ n ∈ range N, (x:ℂ)^(trivialZetaZero n)/trivialZetaZero n‖ ≤ 1 := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_right (1/2)
  calc
    _ ≤ ∑ n ∈ range N, (1/2:ℝ)^n*(1/2) := by
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro n _
      rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx,Real.rpow_def_of_pos hx,mul_comm (Real.log x)]
      exact (div_le_self (Real.exp_pos _).le (one_le_norm_trivialZetaZero n)).trans
        ((exp_re_trivialZetaZero_le_half_pow n hL).trans_eq (pow_succ ..))
    _ ≤ ∑' n : ℕ, (1/2:ℝ)^n*(1/2) := hg.summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = _ := hg.tsum_eq.trans (by norm_num)

private theorem perron_high_bound {x U : ℝ} (hx : 2 ≤ x) (hL : 1 ≤ Real.log x) (hU : x^3 ≤ U) :
    ‖dirichletContourIntegral (fun n => (Λ n : ℂ)) x 2 U-(Chebyshev.psi x:ℂ)‖ ≤
      (4/(Real.pi*Real.log 2)+384/Real.pi+48)*Real.log x := by
  have hx₀ : 0 < x := by linarith
  have hU₀ : 0 < U := (pow_pos hx₀ 3).trans_le hU
  have H := perron_truncated_vonMangoldt_of_abscissa hx (by norm_num : (1:ℝ)<2) hU₀
  norm_num only [Real.rpow_two,sub_self,show (2:ℝ)-1 = 1 by norm_num,one_pow,mul_one,
    show (2:ℝ)^2 = 4 by norm_num,show (12:ℝ)*4 = 48 by norm_num] at H
  have h₁ : x^2/U ≤ 1 := (div_le_one hU₀).mpr ((pow_le_pow_right₀ (by linarith : 1 ≤ x) (by decide : 2≤3)).trans hU)
  have h₂ : 4*x*(Real.log x)^2/U ≤ 4 := by
    apply (div_le_iff₀ hU₀).mpr
    have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log x) (Real.log_le_self hx₀.le) 2
    nlinarith only [mul_le_mul_of_nonneg_left hsq hx₀.le,hU]
  have hlog2 := Real.log_pos one_lt_two
  calc
    _ ≤ _ := H
    _ ≤ 4/(Real.pi*Real.log 2)*1+(96/Real.pi)*4+48*Real.log x := by gcongr
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 4/(Real.pi*Real.log 2)+384/Real.pi)
      calc
        _ = (4/(Real.pi*Real.log 2)+384/Real.pi)*1+48*Real.log x := by ring
        _ ≤ (4/(Real.pi*Real.log 2)+384/Real.pi)*Real.log x+48*Real.log x := add_le_add h le_rfl
        _ = _ := by ring

/-- At every height T ≥ x⁸ the sharp explicit formula has unconditional error
O(log x), uniformly for all sufficiently large x. The exponent eight is a
convenient overlap range for the smoothed formula. -/
theorem sharp_explicit_formula_high_truncation :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ {T : ℝ}, x^8 ≤ T →
      ‖(Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T‖ ≤ K*Real.log x := by
  obtain ⟨U,C,hC,HU⟩ := exists_expandingPerron_heights
  obtain ⟨B,hB,HB⟩ := sharpZetaZeroSum_unit_variation
  let c := Complex.log (2*(Real.pi:ℂ))
  let A := 4/(Real.pi*Real.log 2)+384/Real.pi+48
  have hA : 0 < A := by dsimp only [A]; positivity [Real.log_pos one_lt_two]
  refine ⟨A+(‖c‖+1+16*C+2*B),by positivity,?_⟩
  have hrate : ∀ᶠ R : ℝ in atTop, (Real.log R)^2 ≤ Real.sqrt R := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).bound one_pos] with R h
    simpa only [Real.rpow_two,←Real.sqrt_eq_rpow,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log R)),
      abs_of_nonneg (Real.sqrt_nonneg _),one_mul] using h
  have hneg := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))
  obtain ⟨R₀,hgood⟩ := eventually_atTop.mp (HU.and (hrate.and hneg))
  filter_upwards [eventually_ge_atTop R₀,eventually_ge_atTop (3:ℝ),eventually_ge_atTop (Real.exp 1)] with x hx hx₃ hxE
  intro T hT
  let R := Real.sqrt T
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hL : 1 ≤ Real.log x := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hxE
  have hR₄ : x^4 ≤ R := Real.le_sqrt_of_sq_le (by simpa only [←pow_mul] using hT)
  have hxR : x ≤ R := (by simpa only [pow_one] using pow_le_pow_right₀ hx₁ (by decide : 1≤4) : x ≤ x^4).trans hR₄
  have hR₃ := hx₃.trans hxR
  have hR₀ : 0 < R := hx₀.trans_le hxR
  have hT₀ : 0 < T := (pow_pos hx₀ 8).trans_le hT
  have hRT : R^2 = T := Real.sq_sqrt hT₀.le
  obtain ⟨hh,hr,hv⟩ := hgood R (hx.trans hxR)
  obtain ⟨hlo,hhi,hoff,hhor,hvert⟩ := hh
  have hTU := hRT ▸ hlo
  have hU₀ : 0 < U R := hT₀.trans hTU
  have hscaled : x^2*(Real.log R)^2 ≤ R := by
    have hx₂ : x^2 ≤ Real.sqrt R := Real.le_sqrt_of_sq_le (by simpa only [←pow_mul] using hR₄)
    exact (mul_le_mul hx₂ hr (sq_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hR₀.le)
  have hside (t : ℝ) (ht : |t|=U R) : ‖zetaPerronHorizontal x R t‖ ≤ 6*C := by
    apply (norm_zetaPerronHorizontal_le (by linarith) hR₃ hlo ht hC (fun σ hσ => hhor σ hσ t ht)).trans
    rw [←mul_div_assoc,div_le_iff₀ hR₀]
    nlinarith only [mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ 6*C)]
  have hleft : ‖zetaPerronLeft x R (U R)‖ ≤ 4*C := by
    apply (norm_zetaPerronLeft_le (by linarith) hR₃ hU₀ hhi hC hvert).trans
    have hsmall : R^3*Real.exp (-(R*Real.log x)) ≤ 1 := calc
      _ ≤ R^3*Real.exp (-R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_right hR₀.le hL))
      _ ≤ _ := hv.le
    exact mul_le_of_le_one_right (by positivity) hsmall
  let edge := (zetaPerronHorizontal x R (U R)-zetaPerronHorizontal x R (-U R)+I*zetaPerronLeft x R (U R))/
    (2*Real.pi*I)
  have he : ‖edge‖ ≤ 16*C := by
    have hden : 1 ≤ ‖(2*(Real.pi:ℂ)*I)‖ := by
      simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one]
      linarith [Real.pi_gt_three]
    dsimp only [edge]
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hden).trans
    apply (norm_add_le ..).trans
    rw [norm_mul,Complex.norm_I,one_mul]
    apply (add_le_add (norm_sub_le ..) le_rfl).trans
    linarith [hside (U R) (abs_of_pos hU₀),hside (-U R) (by rw [abs_neg,abs_of_pos hU₀]),hleft]
  have hT₂ : 2 ≤ T := by nlinarith only [hRT,hR₃,sq_nonneg (R-1)]
  have hvar : ‖sharpZetaZeroSum x T-sharpZetaZeroSum x (U R)‖ ≤ 2*B := by
    rw [norm_sub_rev]
    apply (HB hx₁ hT₂ hTU.le (by simpa only [hRT] using hhi.le)).trans
    have hlogT : Real.log T ≤ 2*R := by rw [←hRT,Real.log_pow]; push_cast; linarith [Real.log_le_self hR₀.le]
    rw [←mul_div_assoc,div_le_iff₀ hT₀]
    have H : x*Real.log T ≤ 2*T := by
      nlinarith only [mul_le_mul_of_nonneg_left hlogT hx₀.le,mul_le_mul_of_nonneg_right hxR hR₀.le,hRT]
    nlinarith only [mul_le_mul_of_nonneg_left H hB.le]
  have hU₃ : x^3 ≤ U R := (pow_le_pow_right₀ hx₁ (by decide : 3≤8)).trans (hT.trans hTU.le)
  let P := dirichletContourIntegral (fun n => (Λ n:ℂ)) x 2 (U R)
  let J := ∑ n ∈ range ⌈R⌉₊, (x:ℂ)^(trivialZetaZero n)/trivialZetaZero n
  have hP : ‖(Chebyshev.psi x:ℂ)-P‖ ≤ A*Real.log x := by
    rw [norm_sub_rev]; exact perron_high_bound (by linarith) hL hU₃
  have hJ : ‖J‖ ≤ 1 := finite_trivial_bound hx₀ hL _
  have hid : (Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T =
      ((Chebyshev.psi x:ℂ)-P)-c-J+edge+(sharpZetaZeroSum x T-sharpZetaZeroSum x (U R)) := by
    rw [sharpZetaZeroSum_eq_contour hx₀ hU₀ R hoff]
    dsimp only [P,c,J,edge]
    ring
  rw [hid]
  calc
    _ ≤ (((‖(Chebyshev.psi x:ℂ)-P‖+‖c‖)+‖J‖)+‖edge‖)+‖sharpZetaZeroSum x T-sharpZetaZeroSum x (U R)‖ := by
      apply (norm_add_le ..).trans
      gcongr
      apply (norm_add_le ..).trans
      gcongr
      apply (norm_sub_le ..).trans
      gcongr
      exact norm_sub_le ..
    _ ≤ (((A*Real.log x+‖c‖)+1)+16*C)+2*B := by gcongr
    _ ≤ _ := by
      have H := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ ‖c‖+1+16*C+2*B)
      linarith only [H]

end AnalyticNumberTheory.PrimeDistribution
