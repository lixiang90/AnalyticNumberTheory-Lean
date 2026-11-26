import AnalyticNumberTheory.AnalyticTools.Gamma.RealGammaFactor
import AnalyticNumberTheory.AnalyticTools.Gamma.DigammaBounds
import AnalyticNumberTheory.DirichletSeries.VerticalOrder
import AnalyticNumberTheory.DirichletSeries.Operations
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Reflection and logarithmic growth of the zeta logarithmic derivative on the left -/

noncomputable section

open Filter Set
open scoped Topology ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools.Gamma AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.RiemannZeta

private theorem half_nonPole_of_re_pos {s : ℂ} (hs : 0 < s.re) : s/2 ∈ nonPoleSet := by
  intro n he
  have hre := congrArg Complex.re he
  norm_num [Complex.div_re, Complex.normSq] at hre
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem reflected_factorization {s : ℂ} (hs : s.re < 0) :
    riemannZeta s = (riemannZeta (1-s) * Complex.Gammaℝ (1-s))/Complex.Gammaℝ s := by
  have hR : 0 < (1-s).re := by simp; linarith
  have h₀ : s ≠ 0 := fun he => by simp [he] at hs
  have h₁ : 1-s ≠ 0 := fun he => by simp [he] at hR
  rw [riemannZeta_def_of_ne_zero h₀, riemannZeta_def_of_ne_zero h₁,
    div_mul_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hR), completedRiemannZeta_one_sub]

/-- On the open left half-plane away from the trivial zeros, the logarithmic derivative
reflects to an absolutely convergent right-half-plane Dirichlet series and two digamma terms. -/
theorem logDeriv_zeta_reflect_gamma {s : ℂ} (hs : s.re < 0) (hp : s/2 ∈ nonPoleSet) :
    logDeriv riemannZeta s = (Real.log Real.pi : ℂ) - logDeriv riemannZeta (1-s) -
      digamma (s/2)/2 - digamma ((1-s)/2)/2 := by
  let F (z : ℂ) := riemannZeta z * Complex.Gammaℝ z
  let r (z : ℂ) := 1-z
  have hR : 1 < (1-s).re := by simp; linarith
  have h₁ : 1-s ≠ 1 := fun he => by simp [he] at hR
  have hzp := _root_.riemannZeta_ne_zero_of_one_lt_re hR
  have hgp := half_nonPole_of_re_pos (zero_lt_one.trans hR)
  have hz := differentiableAt_riemannZeta h₁
  have hG := (hasDerivAt_gammaReal hgp).differentiableAt
  have hF : DifferentiableAt ℂ F (r s) := hz.mul hG
  have hr : HasDerivAt r (-1) s := (hasDerivAt_id s).const_sub 1
  have he : riemannZeta =ᶠ[𝓝 s] fun z => F (r z)/Complex.Gammaℝ z := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs] with z hz'
    exact reflected_factorization hz'
  have h := (logDeriv_congr_nhds he).eq_of_nhds
  change logDeriv riemannZeta s = logDeriv ((F ∘ r)/Complex.Gammaℝ) s at h
  have hFn : (F ∘ r) s ≠ 0 := mul_ne_zero hzp (gammaReal_ne_zero hgp)
  rw [h, logDeriv_div (f := F ∘ r) (g := Complex.Gammaℝ) s hFn (gammaReal_ne_zero hp)
    (hF.comp s hr.differentiableAt) (hasDerivAt_gammaReal hp).differentiableAt,
    logDeriv_comp hF hr.differentiableAt, hr.deriv]
  change logDeriv (riemannZeta * Complex.Gammaℝ) (1-s) * (-1) - logDeriv Complex.Gammaℝ s = _
  rw [logDeriv_mul _ hzp (gammaReal_ne_zero hgp) hz hG, logDeriv_gammaReal hgp, logDeriv_gammaReal hp]
  ring

private theorem half_nonPole_of_separation {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hsep : ∀ n : ℕ, d ≤ ‖s+2*(n : ℂ)‖) : s/2 ∈ nonPoleSet := by
  intro n he
  have hz : s+2*(n : ℂ) = 0 := by linear_combination 2*he
  have hh := hsep n
  rw [hz, norm_zero] at hh
  linarith

private theorem half_separation {s : ℂ} {d : ℝ} (hsep : ∀ n : ℕ, d ≤ ‖s+2*(n : ℂ)‖) :
    d/2 ≤ poleDistance (s/2) := by
  obtain ⟨n, he⟩ := exists_poleDistance_eq_norm (s/2)
  rw [he, show s/2+(n : ℂ) = (s+2*(n : ℂ))/2 by ring, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hsep n) (by norm_num)

/-- Uniform growth to the left of `Re s=-1/2`. At distance at least `d` from the
nonpositive even integers, a single inverse distance accounts for the poles. -/
theorem norm_logDeriv_zeta_left_le_inv_add_log :
    ∃ C > 0, ∀ {s : ℂ} {d : ℝ}, s.re ≤ -1/2 → 0 < d →
      (∀ n : ℕ, d ≤ ‖s+2*(n : ℂ)‖) →
      ‖logDeriv riemannZeta s‖ ≤ d⁻¹ + 5*Real.log (‖s‖+3) + C := by
  let M := ∑' n : ℕ, ‖LSeries.term (fun k => (Λ k : ℂ)) ((3/2 : ℝ) : ℂ) n‖
  let A := Real.pi + 6 + Real.log 2
  refine ⟨‖(Real.log Real.pi : ℂ)‖ + M + A + 2, ?_, fun {s d} hs hd hsep => ?_⟩
  · have hM : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
    dsimp only [A]
    positivity
  have hRe : (3/2 : ℝ) ≤ (1-s).re := by simp; linarith
  have hR : 1 < (1-s).re := by linarith
  have hL : ‖logDeriv riemannZeta (1-s)‖ ≤ M := by
    have hz : logDeriv riemannZeta (1-s) = -LSeries (fun k => (Λ k : ℂ)) (1-s) := by
      rw [LSeries_vonMangoldt_eq hR, logDeriv_apply, neg_div, neg_neg]
    rw [hz, norm_neg]
    exact norm_LSeries_le_tsum_norm_of_re_ge (LSeriesSummable_vonMangoldt_iff.mpr (by norm_num)) hRe
  have hp := half_nonPole_of_separation hd hsep
  have hp' := half_nonPole_of_re_pos (zero_lt_one.trans hR)
  have hd₁ : (poleDistance (s/2))⁻¹ ≤ 2*d⁻¹ := by
    simpa [div_eq_mul_inv, mul_inv_rev] using inv_anti₀ (half_pos hd) (half_separation hsep)
  have hd₂ : (poleDistance ((1-s)/2))⁻¹ ≤ 2 := by
    have hdist : 1/2 ≤ poleDistance ((1-s)/2) := by
      obtain ⟨n, he⟩ := exists_poleDistance_eq_norm ((1-s)/2)
      rw [he]
      apply le_trans _ (Complex.re_le_norm _)
      norm_num [Complex.div_re, Complex.normSq]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa using inv_anti₀ (by norm_num : (0 : ℝ)<1/2) hdist
  have log₁ : Real.log (‖s/2‖+2) ≤ Real.log (‖s‖+3) := by
    apply Real.log_le_log (by positivity)
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_nonneg s]
  have log₂ : Real.log (‖(1-s)/2‖+2) ≤ Real.log (‖s‖+3) := by
    apply Real.log_le_log (by positivity)
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_sub_le (1 : ℂ) s, norm_one (α := ℂ), norm_nonneg s]
  have hu := norm_digamma_le_poleDistance_inv_add_log hp
  have hv := norm_digamma_le_poleDistance_inv_add_log hp'
  rw [logDeriv_zeta_reflect_gamma (by linarith) hp]
  apply (norm_sub_le ..).trans
  apply (add_le_add (norm_sub_le ..) le_rfl).trans
  apply (add_le_add (add_le_add (norm_sub_le ..) le_rfl) le_rfl).trans
  simp only [norm_div, Complex.norm_ofNat]
  dsimp only [A]
  linarith

/-- On the horizontal lines at heights of modulus at least one and on every negative odd
vertical line, the logarithmic derivative grows at most logarithmically, uniformly. -/
theorem norm_logDeriv_zeta_left_edges :
    ∃ C > 0, ∀ {s : ℂ}, s.re ≤ -1/2 → (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -(2*k+1 : ℝ)) →
      ‖logDeriv riemannZeta s‖ ≤ 5*Real.log (‖s‖+3) + C := by
  obtain ⟨C, hC, H⟩ := norm_logDeriv_zeta_left_le_inv_add_log
  refine ⟨C+1, by linarith, fun {s} hs he => ?_⟩
  have hsep (n : ℕ) : 1 ≤ ‖s+2*(n : ℂ)‖ := by
    rcases he with hi | ⟨k, hk⟩
    · apply hi.trans
      simpa [Complex.mul_im] using Complex.abs_im_le_norm (s+2*(n : ℂ))
    · apply le_trans _ (Complex.abs_re_le_norm _)
      simp [Complex.mul_re, hk]
      by_cases hnk : n ≤ k
      · have h := (Nat.cast_le (α := ℝ)).mpr hnk
        exact le_abs.mpr (Or.inr (by linarith))
      · have h := (Nat.cast_le (α := ℝ)).mpr (Nat.succ_le_of_lt (lt_of_not_ge hnk))
        push_cast at h
        exact le_abs.mpr (Or.inl (by linarith))
  have h := H hs zero_lt_one hsep
  rw [inv_one] at h
  linarith

end AnalyticNumberTheory.RiemannZeta
