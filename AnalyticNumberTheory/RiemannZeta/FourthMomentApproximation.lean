import AnalyticNumberTheory.RiemannZeta.GaussianWeightShift
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialMoments

/-!
# Truncating the smoothed functional equation for the fourth moment

A far right line bounds the tail of the divisor series pointwise. Each
retained weight can be moved back towards the critical line before
applying a mean-value theorem to the resulting finite polynomial.
-/

open Complex Real MeasureTheory Set Finset Filter
open scoped Topology
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

set_option maxHeartbeats 800000

private noncomputable def S (t : ℝ) : ℂ := 1/2+(t:ℂ)*I
private def d (n : ℕ) : ℂ := n.divisors.card
private noncomputable def w (c v : ℝ) : ℂ := c+(v:ℂ)*I
private noncomputable def den (t : ℝ) : ℂ := 2*π*xiCompletionFactor (S t)^2
private noncomputable def G (t u c v : ℝ) : ℂ := xiGaussianKernel (S u) 2 (w c v)/den t
private noncomputable def coeff (t u c : ℝ) (n : ℕ) : ℂ :=
  LSeries.term d (S u) n * xiDirichletWeight (S u) 2 c n / den t

/-- One half of the truncated smoothed expansion of zeta squared. The Boolean selects
the reflected critical ordinate in the dual Dirichlet polynomial. -/
noncomputable def fourthMomentPiece (c : ℝ) (N : ℕ) (negative : Bool) (t : ℝ) : ℂ :=
  let u := if negative then -t else t
  ∫ v : ℝ, G t u c v * divisorPolynomial N (((1/2+c:ℝ):ℂ)+((if negative then v-t else v+t):ℝ)*I)

private theorem G_continuous {c : ℝ} (hc : 0 < c) (negative : Bool) :
    Continuous (fun p : ℝ × ℝ => G p.1 (if negative then -p.1 else p.1) c p.2) := by
  let u (p : ℝ × ℝ) := if negative then -p.1 else p.1
  have hu : Continuous u := by cases negative <;> first | exact continuous_fst | exact continuous_fst.neg
  have hS : Continuous S := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw : Continuous (w c) := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnr (t : ℝ) : (S t).re = 1/2 := by simp [S]
  have hgA {P : ℝ × ℝ → ℂ} (hP : Continuous P) (hp : ∀ p, 0 < (P p).re) :
      Continuous (fun p => xiCompletionFactor (P p)) := continuous_iff_continuousAt.mpr fun p =>
    ContinuousAt.comp (f := P) (differentiableAt_xiCompletionFactor (hp p)).continuousAt hP.continuousAt
  have hhw (r : ℝ) : w c r ≠ 0 := by intro hh; have H := congrArg Complex.re hh; simp [w] at H; linarith
  have hden (t : ℝ) : den t ≠ 0 := by
    have h₀ : S t ≠ 0 := by intro H; have hh := congrArg Complex.re H; norm_num [S] at hh
    have h₁ : S t ≠ 1 := by intro H; have hh := congrArg Complex.re H; norm_num [S] at hh
    have hG := Gammaℝ_ne_zero_of_re_pos (show 0 < (S t).re by rw [hnr]; norm_num)
    have hφ : xiCompletionFactor (S t) ≠ 0 := mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num : (1/2:ℂ) ≠ 0) h₀) (sub_ne_zero.mpr h₁)) hG
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (pow_ne_zero _ hφ)
  have H₁ := hgA ((hS.comp hu).add (hw.comp continuous_snd)) (fun p => by simp [hnr,w]; linarith)
  have H₂ := hgA (hS.comp continuous_fst) (fun p => by change 0 < (S p.1).re; rw [hnr]; norm_num)
  dsimp only [G,xiGaussianKernel,den]
  exact ((H₁.pow 2 |>.mul (Complex.continuous_exp.comp ((hw.comp continuous_snd).pow 2))).div
    (hw.comp continuous_snd) (fun p => hhw p.2)).div (continuous_const.mul (H₂.pow 2)) (fun p => hden p.1)

private theorem gaussianIntegrable : Integrable (fun v : ℝ => Real.exp (-v^2/2)) := by
  simpa only [show ∀ v : ℝ, -(1/2:ℝ)*v^2 = -v^2/2 by intro v; ring] using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)

private theorem norm_coeff_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t : ℝ}, 2 ≤ T → t ∈ Icc T (2*T) → ∀ u : ℝ, |u|=t →
      ∀ {n : ℕ}, 0 < n → ‖coeff t u c n‖ ≤ C*T^c*((d n).re/(n:ℝ)^(1/2+c)) := by
  obtain ⟨K,hK,hbound⟩ := norm_normalized_xiGaussianKernel_sq_le hc
  let m : ℝ := ∫ v : ℝ, Real.exp (-v^2/2)
  have hm : 0 ≤ m := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨K*(m+1), by positivity,?_⟩
  intro T t hT ht u hu n hn
  have hT0 : 0 < T := by linarith
  have hG (v : ℝ) := hbound hT ht u v hu
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hdR : 0 ≤ (d n).re := by simp [d]
  have hz : ‖LSeries.term d (S u) n‖ = (d n).re/(n:ℝ)^(1/2:ℝ) := by rw [LSeries.norm_term_eq,ite_eq_right hn.ne']; simp [S,d]
  have hpow (v : ℝ) : ‖(n:ℂ)^(w c v)‖ = (n:ℝ)^c := by rw [Complex.norm_natCast_cpow_of_pos hn]; simp [w]
  have hdiv : ‖xiDirichletWeight (S u) 2 c n / den t‖ ≤ K*T^c*m/(n:ℝ)^c := by
    rw [xiDirichletWeight,← integral_div]
    let g (v : ℝ) := K*T^c*Real.exp (-v^2/2)/(n:ℝ)^c
    have hg : Integrable g := (gaussianIntegrable.const_mul (K*T^c)).div_const _
    have hb (v : ℝ) : ‖xiGaussianKernel (S u) 2 (w c v)/(n:ℂ)^(w c v)/den t‖ ≤ g v := by
      rw [div_right_comm,norm_div,hpow]
      exact div_le_div_of_nonneg_right (hG v) (by positivity)
    exact (norm_integral_le_of_norm_le hg (Eventually.of_forall hb)).trans_eq (by dsimp [g,m]; rw [integral_div,integral_const_mul])
  rw [coeff,mul_div_assoc,norm_mul,hz]
  calc _ ≤ ((d n).re/(n:ℝ)^(1/2:ℝ))*(K*T^c*m/(n:ℝ)^c) := mul_le_mul_of_nonneg_left hdiv (by positivity)
       _ = K*m*T^c*((d n).re/(n:ℝ)^(1/2+c)) := by rw [Real.rpow_add hnR]; ring
       _ ≤ _ := by gcongr; linarith

private theorem summable_divisor_over_sq : Summable (fun n : ℕ => (d n).re/(n:ℝ)^2) := by
  have ha := (LSeriesSummable_sigma_zero_iff (s := (2:ℂ))).mpr (by norm_num)
  convert ha.norm using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [d]
  · simp [d,ArithmeticFunction.sigma_zero_apply,hn]

private theorem tail_coeff_le {η : ℝ} (hη : 0 < η) :
    ∃ c C : ℝ, 1 < c ∧ 0 < C ∧ ∀ {T t : ℝ}, 2 ≤ T → t ∈ Icc T (2*T) →
      ∀ u : ℝ, |u|=t → ∀ {n : ℕ}, ⌈T^(1+η)⌉₊ < n → ‖coeff t u c n‖ ≤ C*((d n).re/(n:ℝ)^2) := by
  let c := 2+2/η
  have hpos : 0 < 2/η := by positivity
  have hc : 1 < c := by dsimp [c]; linarith
  have hβ : 0 < c-3/2 := by dsimp [c]; linarith
  obtain ⟨C,hC,h⟩ := norm_coeff_le (c := c) (by linarith)
  refine ⟨c,C,hc,hC,?_⟩
  intro T t hT ht u hu n hn
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hN : T^(1+η) ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn.le)
  have hpow : T^c ≤ (n:ℝ)^(c-3/2) := by
    calc T^c ≤ T^((1+η)*(c-3/2)) := Real.rpow_le_rpow_of_exponent_le hT1 (by dsimp [c]; field_simp; nlinarith)
         _ = (T^(1+η))^(c-3/2) := Real.rpow_mul hT0.le _ _
         _ ≤ _ := Real.rpow_le_rpow (by positivity) hN hβ.le
  apply (h hT ht u hu hn0).trans
  have hd : 0 ≤ (d n).re := by simp [d]
  calc _ ≤ C*(n:ℝ)^(c-3/2)*((d n).re/(n:ℝ)^(1/2+c)) := by gcongr
       _ = _ := by
         rw [show (1/2:ℝ)+c = (c-3/2)+2 by ring,Real.rpow_add hnr, Real.rpow_two]
         field_simp


private theorem integral_mul_term (F W : ℝ → ℂ) (b a x s : ℂ) (hx : x ≠ 0) :
    (∫ v : ℝ, (F v / b) * (a / x^(s+W v))) =
      (a / x^s) * (∫ v : ℝ, F v / x^(W v)) / b := by
  calc
    _ = ∫ v : ℝ, ((a / x^s) * (F v / x^(W v))) / b := by
      apply integral_congr_ae
      filter_upwards with v
      rw [Complex.cpow_add _ _ hx]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [integral_div, integral_const_mul]

private theorem piece_eq_sum {c T t : ℝ} (hc : 0 < c) (hT : 2 ≤ T) (ht : t ∈ Icc T (2*T))
    (N : ℕ) (neg : Bool) :
    fourthMomentPiece c N neg t = ∑ n ∈ Finset.Icc 1 N, coeff t (if neg then -t else t) c n := by
  let u := if neg then -t else t
  let z (v : ℝ) := S u+w c v
  have ht0 : 0 < t := by linarith [ht.1]
  have hu : |u|=t := by cases neg <;> simp [u,abs_of_pos ht0]
  have hS : Continuous z := continuous_const.add (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  obtain ⟨K,hK,h⟩ := norm_normalized_xiGaussianKernel_sq_le hc
  have hGc : Continuous (G t u c) := by
    have hh := (G_continuous hc neg).comp (continuous_const.prodMk continuous_id : Continuous (fun v : ℝ => (t,v)))
    exact hh
  have hGi : Integrable (G t u c) := by
    apply (gaussianIntegrable.const_mul (K*T^c)).mono' hGc.aestronglyMeasurable
    exact Eventually.of_forall fun v => h hT ht u v hu
  have hrepr (v : ℝ) : divisorPolynomial N (((1/2+c:ℝ):ℂ)+((if neg then v-t else v+t):ℝ)*I) =
      ∑ n ∈ Finset.Icc 1 N, LSeries.term d (z v) n := by
    have hz : (((1/2+c:ℝ):ℂ)+((if neg then v-t else v+t):ℝ)*I) = z v := by
      cases neg <;> dsimp [z,u,S,w] <;> push_cast <;> ring
    rw [hz,divisorPolynomial,dirichletPoly]
    apply Finset.sum_congr rfl
    intro n hn
    have hpos := (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero (by omega : n ≠ 0),Complex.cpow_neg,div_eq_mul_inv]
    rfl
  have hi (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Integrable (fun v : ℝ => G t u c v*LSeries.term d (z v) n) := by
    have hnpos : n ≠ 0 := by have hp := (Finset.mem_Icc.mp hn).1; omega
    have hnc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos
    have hterm : Continuous (fun v => LSeries.term d (z v) n) := by
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      simp_rw [LSeries.term_of_ne_zero hn0,Complex.cpow_def_of_ne_zero hnc]
      exact continuous_const.div (Complex.continuous_exp.comp (continuous_const.mul hS)) (fun _ => Complex.exp_ne_zero _)
    apply (hGi.norm.mul_const ‖LSeries.term d (((1/2+c:ℝ):ℂ)) n‖).mono' ((hGc.mul hterm).aestronglyMeasurable)
    filter_upwards with v
    change ‖G t u c v * LSeries.term d (z v) n‖ ≤ _
    rw [norm_mul]
    simp only [LSeries.norm_term_eq]
    simp [z,S,w]
  change (∫ v : ℝ, G t u c v * divisorPolynomial N (((1/2+c:ℝ):ℂ)+((if neg then v-t else v+t):ℝ)*I)) = _
  simp_rw [hrepr,Finset.mul_sum]
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [coeff,LSeries.term_of_ne_zero hn0]
  simp only [LSeries.term_of_ne_zero hn0]
  exact integral_mul_term (fun v => xiGaussianKernel (S u) 2 (w c v))
    (w c) (den t) (d n) n (S u) hnc

/-- On every high dyadic interval, polynomials of length `⌈T^(1+η)⌉` approximate
`ζ(1/2+it)^2` with a bounded error, after Gaussian smoothing in both directions. -/
theorem norm_zeta_sq_sub_fourthMomentPieces_le {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {T t : ℝ}, 2 ≤ T → t ∈ Icc T (2*T) →
      ‖riemannZeta ((1/2:ℂ)+t*I)^2 -
        (fourthMomentPiece η ⌈T^(1+η)⌉₊ false t + fourthMomentPiece η ⌈T^(1+η)⌉₊ true t)‖ ≤ B := by
  obtain ⟨c,C,hc,hC,htail⟩ := tail_coeff_le hη
  let b (n : ℕ) := 2*C*((d n).re/(n:ℝ)^2)
  have hsb : Summable b := summable_divisor_over_sq.mul_left _
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b,d]; positivity
  refine ⟨∑' n, b n,tsum_nonneg hb,?_⟩
  intro T t hT ht
  let N := ⌈T^(1+η)⌉₊
  let A := Finset.Icc 1 N
  let f (n : ℕ) := coeff t t c n + coeff t (-t) c n
  have hs : 0 < (S t).re := by simp [S]
  have hs1 : (S t).re < 1 := by norm_num [S]
  have hcm : 1-S t=S (-t) := by dsimp [S]; push_cast; ring
  have h := riemannZeta_sq_smoothed_functional_equation hs hs1 (c := c) (by simp [S]; linarith) (by simp [S]; linarith)
  rw [hcm] at h
  have hf : HasSum f (riemannZeta (S t)^2) := by
    apply h.congr_fun
    intro n
    dsimp only [f,coeff]
    rw [← add_div]
    rfl
  have ht0 : 0 < t := by linarith [ht.1]
  have hp (neg : Bool) : fourthMomentPiece η N neg t = ∑ n ∈ A, coeff t (if neg then -t else t) c n := by
    rw [piece_eq_sum hη hT ht]
    apply Finset.sum_congr rfl
    intro n hn
    rw [coeff,xiDirichletWeight_eq_of_pos _ (by simp [S]) 2 n (Finset.mem_Icc.mp hn).1 hη (by linarith : 0 < c)]
    rfl
  change ‖riemannZeta (S t)^2 - (fourthMomentPiece η N false t+fourthMomentPiece η N true t)‖ ≤ _
  rw [hp false,hp true,← Finset.sum_add_distrib]
  change ‖riemannZeta (S t)^2 - ∑ n ∈ A, f n‖ ≤ _
  rw [← hf.tsum_eq,← hf.summable.sum_add_tsum_compl (s := A),add_sub_cancel_left]
  have hcomp (n : ↥(A:Set ℕ)ᶜ) : ‖f n‖ ≤ b n := by
    have hnot : (n:ℕ) ∉ A := n.2
    by_cases hn : (n:ℕ)=0
    · simp [f,coeff,hn,b,d]
    · have hlt : N < (n:ℕ) := by change (n:ℕ) ∉ Finset.Icc 1 N at hnot; simp at hnot; omega
      have h₁ := htail hT ht t (abs_of_pos ht0) hlt
      have h₂ := htail hT ht (-t) (by rw [abs_neg,abs_of_pos ht0]) hlt
      apply (norm_add_le _ _).trans
      dsimp only [b]
      linarith only [h₁,h₂]
  have hnorm := hf.summable.norm.subtype (fun n : ℕ => n ∈ (A:Set ℕ)ᶜ)
  apply (norm_tsum_le_tsum_norm hnorm).trans
  exact hnorm.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective (fun n _ => hb n) hcomp hsb


/-- The square mean of either truncated piece is bounded uniformly on dyadic intervals. -/
theorem fourthMomentPiece_mean_sq {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ {T : ℝ} {N : ℕ}, 2 ≤ T → (N:ℝ) ≤ 2*T^(1+η) → ∀ neg : Bool,
      IntervalIntegrable (fun t => ‖fourthMomentPiece η N neg t‖^2) volume T (2*T) ∧
      (∫ t in T..(2*T), ‖fourthMomentPiece η N neg t‖^2) ≤ D*T^(1+3*η) := by
  obtain ⟨K,hK,hb⟩ := norm_normalized_xiGaussianKernel_sq_le hη
  obtain ⟨D,hD,hm⟩ := divisorPolynomial_gaussian_dyadic hη
  refine ⟨D*K^2,by positivity,?_⟩
  intro T N hT hN neg
  let F (t v : ℝ) := G t (if neg then -t else t) η v
  let P (t v : ℝ) := divisorPolynomial N (((1/2+η:ℝ):ℂ)+((if neg then v-t else v+t):ℝ)*I)
  have hF (t : ℝ) (ht : t ∈ Set.Ioc T (2*T)) (v : ℝ) : ‖F t v‖ ≤ K*T^η*Real.exp (-(1/2:ℝ)*v^2) := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hh := hb hT ⟨ht.1.le,ht.2⟩ (if neg then -t else t) v (by cases neg <;> simp [abs_of_pos ht0])
    change ‖G t (if neg then -t else t) η v‖ ≤ _ at hh
    rw [show -(1/2:ℝ)*v^2 = -v^2/2 by ring]
    exact hh
  refine ⟨?_,hm (by linarith) hK.le hN neg F hF⟩
  have hFc : Continuous (Function.uncurry F) := G_continuous hη neg
  have hPc : Continuous (Function.uncurry P) := by
    have hh := divisorPolynomial_continuous N (1/2+η)
    cases neg <;> first | exact hh.comp (continuous_snd.add continuous_fst) | exact hh.comp (continuous_snd.sub continuous_fst)
  have hmeas : StronglyMeasurable (fourthMomentPiece η N neg) := by
    have hFcP : Continuous (Function.uncurry (fun t v => F t v*P t v)) := hFc.mul hPc
    exact hFcP.stronglyMeasurable.integral_prod_right
  obtain ⟨M,hM⟩ := divisorPolynomial_vertical_bounded N (1/2+η)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hT0 : 0 < T := by linarith
  have hg : Integrable (fun v : ℝ => K*T^η*Real.exp (-(1/2:ℝ)*v^2)*M) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).const_mul (K*T^η)).mul_const M
  have hmax (t : ℝ) (ht : t ∈ Set.Ioc T (2*T)) :
      ‖fourthMomentPiece η N neg t‖ ≤ ∫ v : ℝ, K*T^η*Real.exp (-(1/2:ℝ)*v^2)*M := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards with v
    change ‖F t v * P t v‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hF t ht v) (hM _) (norm_nonneg _) (by positivity)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : T ≤ 2*T)]
  apply Measure.integrableOn_of_bounded (by simp) (hmeas.norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖‖fourthMomentPiece η N neg t‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hmax t ht) 2

end AnalyticNumberTheory.RiemannZeta
