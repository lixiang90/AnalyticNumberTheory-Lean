import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LogDerivativeResidues
import AnalyticNumberTheory.PrimeDistribution.ZetaRectangleZeros
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-! # The exact residue identity for the full zeta Perron rectangle -/

noncomputable section

open Complex Set Filter Finset
open scoped Topology Classical
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis AnalyticNumberTheory.RiemannZeta
open AnalyticNumberTheory.DirichletLFunctions

namespace AnalyticNumberTheory.PrimeDistribution

/-- The sharp Perron integrand of the von Mangoldt series after meromorphic continuation. -/
def zetaPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * (x : ℂ)^s/s

private theorem zeta_an {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) s hs

private theorem zeta_finite_order {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hconn := (isConnected_compl_singleton_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected
  apply (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton).analyticOrderAt_ne_top_of_isPreconnected
    hconn (x := (0 : ℂ)) (by simp) hs
  rw [(zeta_an zero_ne_one).analyticOrderAt_eq_zero.mpr (by rw [riemannZeta_zero]; norm_num)]
  simp

private theorem pow_an {x : ℝ} (hx : 0 < x) (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => (x : ℂ)^z) s :=
  (show Differentiable ℂ (fun z : ℂ => (x : ℂ)^z) from fun _ =>
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).analyticAt s

private theorem zetaOne_logDeriv_off {z : ℂ} (hz : z ≠ 1) (hn : riemannZeta z ≠ 0) :
    logDeriv zetaOne z = 1/(z-1) + logDeriv riemannZeta z := by
  have he : zetaOne =ᶠ[𝓝 z] (fun w : ℂ => w-1) * riemannZeta :=
    (eventually_ne_nhds hz).mono fun _ hh => zetaOne_eq_sub_one_mul hh
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_mul (f := fun w : ℂ => w-1) (g := riemannZeta) z (sub_ne_zero.mpr hz) hn
      (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hz), logDeriv_apply,
    show deriv (fun w : ℂ => w-1) z = 1 from ((hasDerivAt_id z).sub_const 1).deriv]

/-- Principal part of the sharp Perron integrand at the zeta pole. -/
theorem zetaPerron_principalPart_one {x : ℝ} (hx : 0 < x) :
    HasSimplePrincipalPartAt (zetaPerronIntegrand x) 1 (x : ℂ) := by
  have han := differentiable_zetaOne.analyticAt (1 : ℂ)
  have hn : zetaOne 1 ≠ 0 := by simp
  have hneg : HasSimplePrincipalPartAt (fun z => -logDeriv riemannZeta z) 1 1 := by
    refine ⟨fun z => -logDeriv zetaOne z, (han.deriv.div han hn).neg, ?_⟩
    filter_upwards [self_mem_nhdsWithin, (han.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds]
      with z hz hz₁
    change z ≠ 1 at hz
    have hnz : riemannZeta z ≠ 0 := fun he => hz₁ (by rw [zetaOne_eq_sub_one_mul hz, he, mul_zero])
    rw [zetaOne_logDeriv_off hz hnz]
    ring
  have H := hneg.mul_analytic ((pow_an hx 1).div analyticAt_id one_ne_zero)
  change HasSimplePrincipalPartAt (fun z => -logDeriv riemannZeta z*(x : ℂ)^z/z) 1 (x : ℂ)
  simpa only [Pi.div_apply, id_eq, one_mul, Complex.cpow_one, div_one, mul_div_assoc] using H

/-- Principal part at the origin comes from the value of the logarithmic derivative there. -/
theorem zetaPerron_principalPart_zero {x : ℝ} (hx : 0 < x) :
    HasSimplePrincipalPartAt (zetaPerronIntegrand x) 0 (-Complex.log (2*(Real.pi : ℂ))) := by
  have han := zeta_an zero_ne_one
  have hn : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hg : AnalyticAt ℂ (fun z => -logDeriv riemannZeta z * (x : ℂ)^z) 0 :=
    ((han.deriv.div han hn).neg).mul (pow_an hx 0)
  have H := hasSimplePrincipalPartAt_div_sub hg
  have hc : -logDeriv riemannZeta 0 = -Complex.log (2*(Real.pi : ℂ)) := by
    simpa only [logDeriv_apply, neg_div] using neg_logDeriv_riemannZeta_zero
  change HasSimplePrincipalPartAt (fun z => -logDeriv riemannZeta z*(x : ℂ)^z/z) 0 _
  simpa only [sub_zero, Complex.cpow_zero, mul_one, hc] using H

/-- Both kinds of zeros enter with the negative analytic multiplicity. -/
theorem zetaPerron_principalPart_at_zero {x : ℝ} (hx : 0 < x) {p : ℂ} (hp : p ≠ 0) (h₁ : p ≠ 1) :
    HasSimplePrincipalPartAt (zetaPerronIntegrand x) p
      (-((zeroMultiplicity p : ℂ)*((x : ℂ)^p/p))) := by
  have hw : AnalyticAt ℂ (fun z => -((x : ℂ)^z/z)) p := ((pow_an hx p).div analyticAt_id hp).neg
  have H := (hasSimplePrincipalPartAt_logDeriv (zeta_an h₁) (zeta_finite_order h₁)).mul_analytic hw
  convert H using 1
  · funext z; dsimp only [zetaPerronIntegrand]; ring
  · dsimp only [zeroMultiplicity]; ring

/-- Exact finite contour formula, valid without any relationship between the cutoff `x`,
the horizontal height `T`, and the number `N` of enclosed trivial zeros. The height
is chosen off the critical-strip zero ordinates. -/
theorem rectangleBoundary_zetaPerron {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (N : ℕ)
    (havoid : ∀ z ∈ nontrivialZerosUpTo T, |z.im| ≠ T) :
    rectangleBoundary (zetaPerronIntegrand x) ⟨-(2*(N : ℝ)+1),-T⟩ ⟨2,T⟩ =
      2*Real.pi*I*((x : ℂ)-Complex.log (2*(Real.pi : ℂ))-
        (∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*((x : ℂ)^z/z))-
        ∑ n ∈ range N, (x : ℂ)^(trivialZetaZero n)/(trivialZetaZero n)) := by
  let Z := zetaRectangleZeros N T
  let a := -(2*(N : ℝ)+1)
  have ha : a < 0 := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have h₀ (z : ℂ) (hz : z ∈ Z) : z ≠ 0 ∧ z ≠ 1 := by
    have hv := ((mem_zetaRectangleZeros_iff hT.le).mp hz).1
    exact ⟨fun he => by rw [he,riemannZeta_zero] at hv; norm_num at hv,
      fun he => by rw [he] at hv; exact _root_.riemannZeta_ne_zero_of_one_le_re (by simp) hv⟩
  have hn₀ : (0 : ℂ) ∉ Z := fun h => (h₀ 0 h).1 rfl
  have hn₁ : (1 : ℂ) ∉ Z := fun h => (h₀ 1 h).2 rfl
  let S := insert 0 (insert 1 Z)
  let w (z : ℂ) := (x : ℂ)^z/z
  let r (z : ℂ) := if z=0 then -Complex.log (2*(Real.pi : ℂ)) else if z=1 then (x : ℂ)
    else -((zeroMultiplicity z : ℂ)*w z)
  have hsum : (∑ z ∈ S, r z) = (x : ℂ)-Complex.log (2*(Real.pi : ℂ)) -
      (∑ z ∈ nontrivialZerosUpTo T, (zeroMultiplicity z : ℂ)*w z) - ∑ n ∈ range N, w (trivialZetaZero n) := by
    have h₀' : (0 : ℂ) ∉ insert 1 Z := by simp [hn₀]
    rw [show S=insert 0 (insert 1 Z) from rfl, sum_insert h₀', sum_insert hn₁]
    have hzr : (∑ z ∈ Z, r z) = -(∑ z ∈ Z, (zeroMultiplicity z : ℂ)*w z) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun z hz => by simp [r, (h₀ z hz).1, (h₀ z hz).2]
    rw [hzr, sum_zetaRectangleZeros]
    simp [r]
    ring
  change rectangleBoundary _ ⟨a,-T⟩ ⟨2,T⟩ = 2*Real.pi*I*_
  rw [← hsum]
  apply rectangleBoundary_eq_sum_simpleResidues (by linarith : a<2) (by linarith : -T<T)
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨⟨by simpa using ha, by norm_num⟩, by simpa using neg_lt_zero.mpr hT, by simpa using hT⟩
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨⟨by simp; linarith, by norm_num⟩, by simpa using neg_lt_zero.mpr hT, by simpa using hT⟩
    exact zetaRectangleZeros_mem_interior hT havoid hz
  · intro z hz hnot
    have hn0 : z ≠ 0 := fun he => hnot (mem_insert.mpr (Or.inl he))
    have hn1 : z ≠ 1 := fun he => hnot (mem_insert_of_mem (mem_insert.mpr (Or.inl he)))
    have hn : riemannZeta z ≠ 0 := by
      intro he
      apply hnot
      exact mem_insert_of_mem (mem_insert_of_mem ((mem_zetaRectangleZeros_iff hT.le).mpr
        ⟨he,hz.1.1,hz.1.2,abs_le.mpr hz.2⟩))
    have han := zeta_an hn1
    have hlog : AnalyticAt ℂ (logDeriv riemannZeta) z := han.deriv.div han hn
    exact ((hlog.neg.mul (pow_an hx z)).div analyticAt_id hn0).differentiableAt
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · simpa [r] using zetaPerron_principalPart_zero hx
    rcases mem_insert.mp hp with rfl | hp
    · simpa [r] using zetaPerron_principalPart_one hx
    simpa only [r, ite_eq_right (h₀ p hp).1, ite_eq_right (h₀ p hp).2, w] using
      zetaPerron_principalPart_at_zero hx (h₀ p hp).1 (h₀ p hp).2

end AnalyticNumberTheory.PrimeDistribution
