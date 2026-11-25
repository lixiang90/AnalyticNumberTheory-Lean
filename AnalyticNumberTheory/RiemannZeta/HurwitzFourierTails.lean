import AnalyticNumberTheory.RiemannZeta.HurwitzFourierIntegrals

/-!
# The Fourier tails of Hurwitz zeta

The oscillatory gamma factor minus its lower incomplete integral is the
improper Fourier tail. Two integrations by parts express the same quantity
in terms of the absolutely convergent integral in Euler–Maclaurin summation.
-/
noncomputable section
open Real Complex Filter MeasureTheory Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- Complex Laplace frequency corresponding to the Fourier frequency ω. -/
def hurwitzFrequency (ω : ℝ) : ℂ := -(ω:ℂ)*I

/-- Gamma factor of one Fourier mode of a Dirichlet monomial. -/
def hurwitzDualMode (s : ℂ) (ω : ℝ) : ℂ := (hurwitzFrequency ω)^(s-1)*Complex.Gamma (1-s)

/-- The Fourier tail after the direct cutoff. -/
def hurwitzTail (s : ℂ) (ω x : ℝ) :=
  hurwitzDualMode s ω - ∫ u in 0..x,hurwitzMode s ω u

@[simp] theorem hurwitzFrequency_re (ω : ℝ) : (hurwitzFrequency ω).re=0 := by simp [hurwitzFrequency]
theorem hurwitzFrequency_ne {ω : ℝ} (hω : ω≠0) : hurwitzFrequency ω≠0 :=
  mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hω)) Complex.I_ne_zero

theorem hurwitzTail_eq {s : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1) {ω x : ℝ} (hω : ω≠0) (hx : 0<x) :
    hurwitzTail s ω x=(hurwitzMode s ω x-s*∫ u in Ioi x,hurwitzMode (s+1) ω u)/hurwitzFrequency ω := by
  have h := oscillatoryGamma_split (s:=1-s) (by simp; linarith) (by simp; linarith)
    (hurwitzFrequency_re ω) (hurwitzFrequency_ne hω) hx
  dsimp only [hurwitzTail,hurwitzDualMode]
  rw [intervalIntegral.integral_of_le hx.le]
  simp_rw [hurwitzMode_eq_gamma]
  rw [show -(1-s)=s-1 by ring,show 1-s-1= -s by ring] at h
  rw [show 1-(s+1)= -s by ring]
  change _ = (gammaLaplaceKernel (1-s) (hurwitzFrequency ω) x-s*_)/_
  rw [h]; simp only [hurwitzFrequency]; ring

theorem hurwitzTail_second_order {s : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1) {ω x : ℝ} (hω : ω≠0) (hx : 0<x) :
    hurwitzTail s ω x = hurwitzMode s ω x/hurwitzFrequency ω -
      s*hurwitzMode (s+1) ω x/(hurwitzFrequency ω)^2 +
      s*(s+1)/(hurwitzFrequency ω)^2*∫ u in Ioi x,hurwitzMode (s+2) ω u := by
  let z := hurwitzFrequency ω
  have hzne : z≠0 := hurwitzFrequency_ne hω
  have hz : 0≤z.re := (hurwitzFrequency_re ω).ge
  have hi := integrable_gammaLaplaceKernel_tail (s:=1-s) (by simp; linarith) hz hx
  rw [show 1-s-1= -s by ring] at hi
  have hr := gammaLaplace_tail_recurrence (s:=-s) (by simp; linarith) hz hx hi
  rw [hurwitzTail_eq hs₀ hs₁ hω hx]
  simp_rw [hurwitzMode_eq_gamma]
  rw [show 1-(s+1)= -s by ring,show 1-(s+2)= -s-1 by ring]
  change (gammaLaplaceKernel (1-s) z x-s*∫ u in Ioi x,gammaLaplaceKernel (-s) z u)/z=
    gammaLaplaceKernel (1-s) z x/z-s*gammaLaplaceKernel (-s) z x/z^2+
      s*(s+1)/z^2*∫ u in Ioi x,gammaLaplaceKernel (-s-1) z u
  field_simp [hzne]; linear_combination -s*hr

/-- The tail is the limit of the ordinary finite Fourier integrals. -/
theorem tendsto_integral_hurwitzMode {s : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1) {ω x : ℝ} (hω : ω≠0) (hx : 0<x) :
    Tendsto (fun b : ℝ => ∫ u in x..b,hurwitzMode s ω u) atTop (𝓝 (hurwitzTail s ω x)) := by
  have hk : Tendsto (hurwitzMode s ω) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb using (norm_hurwitzMode s ω hb).le
    · exact tendsto_rpow_neg_atTop hs₀
  have ht := tendsto_integral_Ioi_zero (μ:=volume) (f:=hurwitzMode (s+1) ω) (tendsto_id (α:=ℝ))
  have hh : Tendsto (hurwitzTail s ω) atTop (𝓝 0) := by
    have h0 := (hk.sub (ht.const_mul s)).div_const (hurwitzFrequency ω)
    simp only [mul_zero,sub_zero,zero_div] at h0
    exact h0.congr' (by filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb using (hurwitzTail_eq hs₀ hs₁ hω hb).symm)
  have h' := hh.const_sub (hurwitzTail s ω x)
  rw [sub_zero] at h'
  apply h'.congr'
  filter_upwards [eventually_ge_atTop x] with b hb
  have h := hurwitzMode_integrable_at_zero hs₁ ω (hx.le.trans hb)
  have h₁ := hurwitzMode_integrable_at_zero hs₁ ω hx.le
  have h₂ := h₁.symm.trans h
  dsimp [hurwitzTail]
  rw [←intervalIntegral.integral_add_adjacent_intervals h₁ h₂]; ring

/-- Nonstationary estimate for the upper improper Fourier tail. -/
theorem hurwitzTail_first {s : ℂ} (hs₀ : 0<s.re) (hs₁ : s.re<1) (ht : 0≤s.im)
    {ω x D : ℝ} (hω : ω≠0) (hx : 0<x) (hD : 0<D) (hg : ∀ u : ℝ, x≤u → D≤|ω-s.im/u|) :
    ‖hurwitzTail s ω x‖ ≤ x^(-s.re)*(4/D) := by
  apply le_of_tendsto (tendsto_integral_hurwitzMode hs₀ hs₁ hω hx).norm
  filter_upwards [eventually_ge_atTop x] with b hb
  exact hurwitzMode_first hx hb hs₀.le ht hD (fun u hu => hg u hu.1)

end AnalyticNumberTheory.RiemannZeta
