import AnalyticNumberTheory.PrimeDistribution.MontgomeryZetaLowZeros
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityBalance

/-!
# From high distinct zeros to the Montgomery count with multiplicities

The pole cutoff costs only half the density exponent. The high zeros
each have multiplicity bounded by one logarithm. Rounding the height
changes only the absolute constant.
-/

open Real Complex Finset Set
open scoped Classical
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- A bound for distinct zeros above the polar cutoff, with the upper
height `L` and sparse-sampling parameter `L+2`. -/
def MontgomeryHighZetaCount (D : ℝ) : Prop :=
  ∀{L : ℕ} {σ : ℝ},16≤L → σ∈Icc (4/5:ℝ) 1 → ∀ S : Finset ℂ,
    (∀ z∈S,riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0<z.im ∧ z.im<L ∧
      96*(montgomeryCutoff ((L:ℝ)+2) σ)^(1-σ)*(1+Real.log (montgomeryCutoff ((L:ℝ)+2) σ))^3≤z.im) →
    (S.card:ℝ)≤D*(1+Real.log ((L:ℝ)+2))^11*((L:ℝ)+2)^(montgomeryExponent σ)

/-- An eleventh logarithmic power for high distinct zeros gives the
twelfth power for the complete count, with multiplicity. -/
theorem montgomery_zeta_weighted_of_high {D : ℝ} (hD : 0<D) (h : MontgomeryHighZetaCount D) :
    ∃ C : ℝ,0<C ∧ ∀ {T σ : ℝ},2≤T → σ∈Icc (4/5:ℝ) 1 →
      (∑z∈zeroDensityFinset σ T,(zeroMultiplicity z:ℝ))≤C*T^(montgomeryExponent σ)*(Real.log T)^12 := by
  obtain ⟨A,hA,HA⟩ := montgomery_zeta_low_zeros_balanced
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_strip_le
  refine ⟨(D*K+A)*11*23^12,by positivity,?_⟩
  intro T σ hT hσ
  let L : ℕ := ⌈T⌉₊+16
  let H : ℝ := (L:ℝ)+2
  let ℓ := 1+Real.log H
  let Y := montgomeryCutoff H σ
  let U := 96*Y^(1-σ)*(1+Real.log Y)^3
  let W := zeroDensityFinset σ T
  let P := W.filter (fun z => U≤z.im)
  let V := W.filter (fun z => ¬ U≤z.im)
  have hL : 16≤L := by dsimp [L];omega
  have hLT : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.le_ceil T]
  have hH : 1≤H := by dsimp [H];linarith [Nat.cast_nonneg (α:=ℝ) L]
  have hH' : H≤11*T := by dsimp [H,L];push_cast;linarith [Nat.ceil_lt_add_one (by linarith : 0≤T)]
  have hℓ : 1≤ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  have hPc : (P.card:ℝ)≤D*ℓ^11*H^(montgomeryExponent σ) := h hL hσ P (fun z hz => by
    obtain ⟨hz,hu⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := mem_zeroDensityFinset.mp hz
    exact ⟨h₁,h₂,h₃,h₄,lt_of_le_of_lt h₅ hLT,hu⟩)
  have hPm (z : ℂ) (hz : z∈P) : (zeroMultiplicity z:ℝ)≤K*ℓ := by
    obtain ⟨hz₁,hz₂,hz₃,hz₄,hz₅⟩ := mem_zeroDensityFinset.mp (Finset.mem_filter.mp hz).1
    have hh := HK z.im {z} (fun w hw => by
      obtain rfl := Finset.mem_singleton.mp hw
      exact ⟨hz₁,by linarith [hσ.1],hz₃,by simp⟩)
    simp only [Finset.sum_singleton,abs_of_pos hz₄] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by
      change Real.log (z.im+2)≤1+Real.log H
      linarith [Real.log_le_log (by linarith : 0<z.im+2) (by dsimp [H];linarith : z.im+2≤H)]) hK.le)
  have hP := Finset.sum_le_sum hPm
  rw [sum_const,nsmul_eq_mul] at hP
  have hP' := hP.trans (mul_le_mul_of_nonneg_right hPc (by positivity : 0≤K*ℓ))
  have hV := HA (show 3/4≤σ by linarith [hσ.1]) hσ.2 hH V (fun z hz => by
    obtain ⟨hz,hu⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁,h₂,h₃,h₄,_⟩ := mem_zeroDensityFinset.mp hz
    exact ⟨h₁,h₂,h₃,h₄,(lt_of_not_ge hu).le⟩)
  have he₀ : 0≤montgomeryExponent σ := by unfold montgomeryExponent;positivity [sub_nonneg.mpr hσ.2,show 0<σ by linarith [hσ.1]]
  have he₁ : montgomeryExponent σ≤1 := by unfold montgomeryExponent;apply (div_le_iff₀ (by linarith [hσ.1])).mpr;linarith [hσ.1]
  have hhalf : (1-σ)/σ≤montgomeryExponent σ := by
    unfold montgomeryExponent
    exact div_le_div_of_nonneg_right (by linarith [hσ.2]) (by linarith [hσ.1])
  have hV' := hV.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH hhalf) hA.le)
    (pow_le_pow_right₀ hℓ (by decide : 4≤12)) (pow_nonneg (zero_le_one.trans hℓ) 4) (by positivity))
  change (∑ z∈V,(zeroMultiplicity z:ℝ))≤A*H^(montgomeryExponent σ)*ℓ^12 at hV'
  have hsum : (∑z∈W,(zeroMultiplicity z:ℝ))=(∑z∈P,(zeroMultiplicity z:ℝ))+(∑z∈V,(zeroMultiplicity z:ℝ)) :=
    (sum_filter_add_sum_filter_not ..).symm
  change (∑z∈W,(zeroMultiplicity z:ℝ))≤_
  rw [hsum]
  have hbound : (∑z∈P,(zeroMultiplicity z:ℝ))+(∑z∈V,(zeroMultiplicity z:ℝ))≤(D*K+A)*H^(montgomeryExponent σ)*ℓ^12 := by
    nlinarith only [hP',hV']
  have hlogT : 1/2≤Real.log T := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans (Real.log_le_log (by norm_num) hT)
  have hlogH := Real.log_le_log (zero_lt_one.trans_le hH) hH'
  rw [Real.log_mul (by norm_num) (by linarith : T≠0)] at hlogH
  have hlog : ℓ≤23*Real.log T := by dsimp [ℓ];linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<11)]
  have hpow := Real.rpow_le_rpow (zero_le_one.trans hH) hH' he₀
  rw [Real.mul_rpow (by norm_num) (by linarith : 0≤T)] at hpow
  have h11 : (11:ℝ)^(montgomeryExponent σ)≤11 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤11) he₁
  have hp := hpow.trans (mul_le_mul_of_nonneg_right h11 (Real.rpow_nonneg (by linarith : 0≤T) _))
  have hlp := pow_le_pow_left₀ (zero_le_one.trans hℓ) hlog 12
  apply hbound.trans
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity : 0≤D*K+A)) hlp (pow_nonneg (zero_le_one.trans hℓ) 12) (by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
