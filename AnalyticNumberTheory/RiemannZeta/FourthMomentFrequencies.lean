import AnalyticNumberTheory.RiemannZeta.HardyGammaPhase
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialDiagonals
import AnalyticNumberTheory.RiemannZeta.FourthMomentMainTerms

/-!
# Nonstationary terms in the fourth zeta moment

With a divisor polynomial shorter than `T/(4π)`, the phase of every frequency pair
has derivative separated from zero on the entire integration interval.
-/

open Complex Real MeasureTheory Finset Filter
open scoped ComplexConjugate
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.DirichletSeries
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.RiemannZeta

private noncomputable def freq (n m : ℕ) (t : ℝ) :=
  Complex.exp (((4*hardyPhase t - t*(Real.log n+Real.log m):ℝ):ℂ)*I)

/-- Uniform oscillatory integral estimate below the stationary range of the mixed term. -/
theorem norm_integral_four_hardyPhase_sub_logs {n m : ℕ} {T : ℝ} (hT : 0 < T)
    (hn : 0 < n) (hm : 0 < m) (h₁ : (n:ℝ) ≤ T/(4*π)) (h₂ : (m:ℝ) ≤ T/(4*π)) :
    ‖∫ t in T..2*T, Complex.exp (((4*hardyPhase t-t*(Real.log n+Real.log m):ℝ):ℂ)*I)‖ ≤ 2/Real.log 2 := by
  let L := Real.log n+Real.log m
  let F (t : ℝ) := 4*hardyPhase t-t*L
  let D (t : ℝ) := 2*(Real.log t-Real.log (2*π))-L
  have hd {t : ℝ} (ht : 0 < t) : HasDerivAt F (D t) t := by
    have hh := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
      ((hasDerivAt_id t).const_mul (Real.log (2*π)+1))
    have h := ((((hh.div_const 2).sub_const (π/8)).const_mul 4)).sub ((hasDerivAt_id t).mul_const L)
    convert h using 1
    · rfl
    · dsimp [D]; field_simp; ring
  have hD {t : ℝ} (ht : 0 < t) : HasDerivAt D (2/t) t := by
    have h := (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2*π))).const_mul 2).sub_const L
    convert h using 1
    · rfl
  have hπ : 0 < 4*π := by positivity
  have hl₁ := Real.log_le_log (by exact_mod_cast hn : (0:ℝ) < n) h₁
  have hl₂ := Real.log_le_log (by exact_mod_cast hm : (0:ℝ) < m) h₂
  have hlog : Real.log (T/(4*π)) = Real.log T-Real.log (2*π)-Real.log 2 := by
    rw [Real.log_div hT.ne' hπ.ne',show 4*π = (2*π)*2 by ring,Real.log_mul (by positivity) (by norm_num)]
    ring
  rw [hlog] at hl₁ hl₂
  have hh := vanDerCorput_integral_first_deriv (F := F) (F' := D) (F'' := fun t => 2/t)
    (show T ≤ 2*T by linarith) (m := 2*Real.log 2) (by positivity)
    (fun t ht => hd (hT.trans_le ht.1)) (fun t ht => hD (hT.trans_le ht.1))
    (continuousOn_const.div continuousOn_id (fun t ht => (hT.trans_le ht.1).ne'))
    (Or.inl (fun t ht => div_nonneg (by norm_num) (hT.trans_le ht.1).le)) (fun t ht => by
      apply le_trans _ (le_abs_self _)
      dsimp [D,L]; linarith [Real.log_le_log hT ht.1])
  exact hh.trans_eq (by ring)

private noncomputable def coeff (n : ℕ) := (n.divisors.card:ℝ)*(√(n:ℝ))⁻¹

private theorem sum_coeff_sq {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, coeff n)^2 ≤ 4*(N:ℝ)*(1+Real.log N)^3 := by
  let f (n : ℕ) := (n.divisors.card:ℝ)^2*(√(n:ℝ))⁻¹
  let g (n : ℕ) := (√(n:ℝ))⁻¹
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 N) (r := coeff) (f := f) (g := g)
    (fun _ _ => by dsimp [f]; positivity) (fun _ _ => by dsimp [g]; positivity)
    (fun n _ => by dsimp [coeff,f,g]; exact le_of_eq (by ring))
  have hf : ∑ n ∈ Icc 1 N, f n ≤ 2*√N*(1+Real.log N)^3 := by
    simpa only [f,Real.rpow_neg (Nat.cast_nonneg _) _,← Real.sqrt_eq_rpow] using divisor_diagonal_quarter hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  apply h.trans
  apply (mul_le_mul hf (sum_Icc_inv_sqrt_le N) (sum_nonneg fun n _ => by positivity) (by positivity)).trans_eq
  calc 2*√(N:ℝ)*(1+Real.log N)^3*(2*√N) = 4*(√(N:ℝ))^2*(1+Real.log N)^3 := by ring
       _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

private theorem critical_power (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n:ℂ)^(-(1/2+(t:ℂ)*I)) = ((√(n:ℝ))⁻¹:ℝ)*Complex.exp (((-t*Real.log n:ℝ):ℂ)*I) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hnc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc : (((√(n:ℝ))⁻¹:ℝ):ℂ) = (n:ℂ)^(-(1/2:ℂ)) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_inv,Complex.ofReal_cpow hnr.le,Complex.cpow_neg]
    push_cast
    rfl
  rw [hc,Complex.cpow_def_of_ne_zero hnc,Complex.cpow_def_of_ne_zero hnc,← Complex.exp_add,
    ← Complex.ofReal_natCast,← Complex.ofReal_log hnr.le]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 700000 in
/-- Bound for the oscillatory square of the short divisor polynomial with the leading
Stirling phase. The implied constant is independent of its length. -/
theorem norm_integral_exp_four_phase_mul_divisorPolynomial_sq {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hNT : (N:ℝ) ≤ T/(4*π)) :
    ‖∫ t in T..2*T, Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I) *
      divisorPolynomial N ((1/2:ℂ)+t*I)^2‖ ≤ (8/Real.log 2)*N*(1+Real.log N)^3 := by
  let S := Icc 1 N
  let a (n m : ℕ) := coeff n*coeff m
  let G (n m : ℕ) (t : ℝ) := (a n m:ℂ)*freq n m t
  have hrepr (t : ℝ) : Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I)*divisorPolynomial N ((1/2:ℂ)+t*I)^2 =
      ∑ n ∈ S, ∑ m ∈ S, G n m t := by
    rw [divisorPolynomial,dirichletPoly,pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [critical_power n (mem_Icc.mp hn).1,critical_power m (mem_Icc.mp hm).1]
    have he : Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I) *
        Complex.exp (((-t*Real.log n:ℝ):ℂ)*I) * Complex.exp (((-t*Real.log m:ℝ):ℂ)*I) = freq n m t := by
      dsimp only [freq]
      rw [← Complex.exp_add,← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [G,a,coeff]
    rw [← he]
    push_cast
    ring
  have hcont (n m : ℕ) : ContinuousOn (G n m) (Set.Icc T (2*T)) := by
    have hlog : ContinuousOn Real.log (Set.Icc T (2*T)) := fun t ht =>
      (Real.continuousAt_log (hT.trans_le ht.1).ne').continuousWithinAt
    dsimp [G,freq,hardyPhase]
    fun_prop
  have hi (n m : ℕ) := (hcont n m).intervalIntegrable_of_Icc (μ := volume) (by linarith : T ≤ 2*T)
  have ha (n m : ℕ) : 0 ≤ a n m := by dsimp [a,coeff]; positivity
  have H (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S) :
      ‖∫ t in T..2*T, G n m t‖ ≤ (a n m)*(2/Real.log 2) := by
    have hh := norm_integral_four_hardyPhase_sub_logs hT (mem_Icc.mp hn).1 (mem_Icc.mp hm).1
      (le_trans (Nat.cast_le.mpr (mem_Icc.mp hn).2) hNT) (le_trans (Nat.cast_le.mpr (mem_Icc.mp hm).2) hNT)
    dsimp only [G]
    rw [intervalIntegral.integral_const_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha n m)]
    exact mul_le_mul_of_nonneg_left hh (ha n m)
  simp_rw [hrepr]
  have hrow (n : ℕ) : IntervalIntegrable (fun t => ∑ m ∈ S, G n m t) volume T (2*T) := by
    exact (continuousOn_finsetSum S (fun m _ => hcont n m)).intervalIntegrable_of_Icc (by linarith)
  rw [intervalIntegral.integral_finsetSum (s := S) (f := fun n t => ∑ m ∈ S, G n m t) (fun n _ => hrow n)]
  have hI (n : ℕ) := intervalIntegral.integral_finsetSum (s := S) (f := G n) (fun m _ => hi n m)
  simp_rw [hI]
  apply (norm_sum_le _ _).trans
  apply le_trans (Finset.sum_le_sum fun n hn => (norm_sum_le _ _).trans (Finset.sum_le_sum (H n hn)))
  simp only [a,← Finset.sum_mul,← Finset.mul_sum]
  calc _ = (∑ n ∈ S, coeff n)^2*(2/Real.log 2) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_right (sum_coeff_sq hN) (by positivity : (0:ℝ) ≤ 2/Real.log 2)).trans_eq (by ring)

private theorem half_conj (t : ℝ) : (1/2:ℂ)+(-t:ℝ)*I = conj ((1/2:ℂ)+t*I) := by
  rw [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_one,map_ofNat,Complex.ofReal_neg]; ring

/-- The phase in the product of the original main term and the conjugate reflected one
is the fourth power of Hardy's gamma phase. -/
theorem fourthMomentMainTerm_mul_conj (N : ℕ) (t : ℝ) :
    fourthMomentMainTerm N false t * conj (fourthMomentMainTerm N true t) =
      hardyGammaUnit t^4 * divisorPolynomial N ((1/2:ℂ)+t*I)^2 := by
  let s := (1/2:ℂ)+t*I
  let G := Gammaℝ s
  let q := (1/2:ℂ)*s*(s-1)
  have hG : G ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [s])
  have hq : q ≠ 0 := by
    have h0 : s ≠ 0 := by intro h; have hh := congrArg Complex.re h; norm_num [s] at hh
    have h1 : s ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num [s] at hh
    exact mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1)
  have hqC : conj q = q := by
    dsimp only [q,s]; simp only [map_mul,map_add,map_sub,map_one,map_div₀,map_ofNat,Complex.conj_I,Complex.conj_ofReal]; ring
  have hA : xiCompletionFactor s = q*G := rfl
  have hnorm : ((‖G‖:ℝ):ℂ)^2 = G*conj G := by simpa using (Complex.mul_conj' G).symm
  have hu : hardyGammaUnit t^2 = G/conj G := by
    change (G/(‖G‖:ℂ))^2 = _
    rw [div_pow,hnorm,pow_two,mul_div_mul_left _ _ hG]
  have hphase : xiCompletionFactor s^2/conj (xiCompletionFactor s)^2 = hardyGammaUnit t^4 := by
    rw [show hardyGammaUnit t^4=(hardyGammaUnit t^2)^2 by ring,hu,hA,map_mul,hqC,← div_pow,mul_div_mul_left _ _ hq]
  change (xiCompletionFactor s^2/xiCompletionFactor s^2*divisorPolynomial N s) *
    conj (xiCompletionFactor ((1/2:ℂ)+(-t:ℝ)*I)^2/xiCompletionFactor s^2*
      divisorPolynomial N ((1/2:ℂ)+(-t:ℝ)*I)) = _
  rw [div_self (pow_ne_zero 2 (hA ▸ mul_ne_zero hq hG)),one_mul,half_conj]
  change divisorPolynomial N s * conj (xiCompletionFactor (conj s)^2/xiCompletionFactor s^2 * divisorPolynomial N (conj s)) = _
  rw [xiCompletionFactor_conj,divisorPolynomial_conj,map_mul,map_div₀,map_pow,map_pow,starRingEnd_self_apply,starRingEnd_self_apply,hphase]
  ring

private theorem norm_critical_square_le {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖divisorPolynomial N ((1/2:ℂ)+t*I)‖^2 ≤ 4*(N:ℝ)*(1+Real.log N)^3 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) _ 2).trans (sum_coeff_sq hN)
  unfold divisorPolynomial dirichletPoly
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [critical_power n (mem_Icc.mp hn).1,norm_mul,norm_mul,Complex.norm_natCast,
    Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact le_rfl

private theorem norm_gamma_four_sub_le {t : ℝ} (ht : 2 ≤ t) :
    ‖hardyGammaUnit t^4 - Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I)‖ ≤ 16/t := by
  let a := hardyGammaUnit t
  let b := Complex.exp ((hardyPhase t:ℂ)*I)
  have ha : ‖a‖ = 1 := norm_hardyGammaUnit t
  have hb : ‖b‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hab : ‖a-b‖ ≤ 4/t := norm_hardyGammaUnit_sub_exp_le ht
  have he : Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I) = b^4 := by
    dsimp only [b]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  change ‖a^4-b^4‖ ≤ _
  rw [show a^4-b^4 = (a-b)*((a+b)*(a^2+b^2)) by ring,norm_mul,norm_mul]
  have h₁ := norm_add_le a b
  have h₂ := norm_add_le (a^2) (b^2)
  rw [ha,hb] at h₁
  simp only [norm_pow,ha,hb,one_pow] at h₂
  apply (mul_le_mul hab (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)) (by positivity) (by positivity)).trans_eq
  ring

/-- Uniform bound for the mixed integral of the two short fourth-moment polynomials. -/
theorem norm_integral_fourthMomentMainTerm_mul_conj_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 2 ≤ T) (hNT : (N:ℝ) ≤ T/(4*π)) :
    ‖∫ t in T..2*T, fourthMomentMainTerm N false t * conj (fourthMomentMainTerm N true t)‖ ≤
      (64+8/Real.log 2)*N*(1+Real.log N)^3 := by
  let X (t : ℝ) := fourthMomentMainTerm N false t*conj (fourthMomentMainTerm N true t)
  let D (t : ℝ) := divisorPolynomial N ((1/2:ℂ)+t*I)
  let P (t : ℝ) := Complex.exp (((4*hardyPhase t:ℝ):ℂ)*I)
  let Y (t : ℝ) := P t*(D t)^2
  let L := (N:ℝ)*(1+Real.log N)^3
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2*T := by linarith
  have hL : 0 ≤ L := by dsimp [L]; have hh := Real.log_nonneg (by exact_mod_cast hN : 1≤(N:ℝ)); positivity
  have hp (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) : ‖X t-Y t‖ ≤ (16/T)*(4*L) := by
    dsimp only [X,Y]
    rw [fourthMomentMainTerm_mul_conj]
    change ‖hardyGammaUnit t^4*(D t)^2 - P t*(D t)^2‖ ≤ _
    rw [← sub_mul,norm_mul,norm_pow]
    apply mul_le_mul ((norm_gamma_four_sub_le (hT.trans ht.1)).trans (by gcongr; exact ht.1))
      ((norm_critical_square_le hN t).trans_eq (by dsimp [L]; ring)) (sq_nonneg _) (by positivity)
  have hiX : IntervalIntegrable X volume T (2*T) := ((continuous_fourthMomentMainTerm N false).mul
    (Complex.continuous_conj.comp (continuous_fourthMomentMainTerm N true))).intervalIntegrable ..
  have hlog : ContinuousOn Real.log (Set.Icc T (2*T)) := fun t ht => (Real.continuousAt_log (hT0.trans_le ht.1).ne').continuousWithinAt
  have hD : Continuous D := by simpa only [D,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using divisorPolynomial_continuous N (1/2)
  have hP : ContinuousOn P (Set.Icc T (2*T)) := by dsimp [P,hardyPhase]; fun_prop
  have hiY : IntervalIntegrable Y volume T (2*T) := (hP.mul (hD.continuousOn.pow 2)).intervalIntegrable_of_Icc hab
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2*T) (f := fun t => X t-Y t) (C := (16/T)*(4*L))
    (fun t ht => hp t (Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le hab] using ht)))
  rw [intervalIntegral.integral_sub hiX hiY,abs_of_nonneg (by linarith)] at hh
  have h₁ := norm_sub_norm_le (∫ t in T..2*T, X t) (∫ t in T..2*T, Y t)
  have h₂ := norm_integral_exp_four_phase_mul_divisorPolynomial_sq hN hT0 hNT
  change ‖∫ t in T..2*T, Y t‖ ≤ _ at h₂
  have hval : (16/T)*(4*L)*(2*T-T) = 64*L := by field_simp; ring
  change ‖∫ t in T..2*T, X t‖ ≤ _
  dsimp only [L] at hval
  linarith

end AnalyticNumberTheory.RiemannZeta
