import AnalyticNumberTheory.PrimeDistribution.ShortIntervalsAndLinnik
import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula
import AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# Low zeros in the pole-corrected zeta detector

The ordinates below the explicit pole-correction cutoff contribute only
one power of the cutoff times its logarithm, including multiplicities.
-/

open Real Complex Finset Set
open scoped Classical
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Any selected zeros on the positive side of the strip contribute at
most the full Riemann zero count through the same height. -/
theorem sum_zeroMultiplicity_le_zeroCountUpTo {T : ℝ} (S : Finset ℂ)
    (hS : ∀ z∈S,riemannZeta z=0 ∧ 0<z.re ∧ z.re<1 ∧ 0<z.im ∧ z.im≤T) :
    ∑ z∈S,zeroMultiplicity z≤zeroCountUpTo T := by
  rw [zeroCountUpTo_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro z hz
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hS z hz
  exact Finset.mem_filter.mpr ⟨(criticalStripZeros_strip_finite 0 T).mem_toFinset.mpr
    ⟨mem_criticalStripZeros.mpr ⟨h₁,h₂,h₃⟩,h₄.le,h₅⟩,h₄⟩

/-- Zeros excluded by the polar term contribute at most a constant times
`Y^(1-σ) (1+log Y)^4`, with their full analytic multiplicities. -/
theorem montgomery_zeta_low_zeros :
    ∃ C : ℝ,0<C ∧ ∀{σ Y : ℝ},0<σ → σ≤1 → 1≤Y → ∀ S : Finset ℂ,
      (∀ z∈S,riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0<z.im ∧ z.im≤96*Y^(1-σ)*(1+Real.log Y)^3) →
      (∑z∈S,(zeroMultiplicity z:ℝ))≤C*Y^(1-σ)*(1+Real.log Y)^4 := by
  obtain ⟨A,hA,H⟩ := zeroCountUpTo_le_mul_log
  refine ⟨9600*A,by positivity,?_⟩
  intro σ Y hσ hσ' hY S hS
  let L := 1+Real.log Y
  let U := 96*Y^(1-σ)*L^3
  have hp : 0<Y := by linarith
  have hy := Real.log_nonneg hY
  have hL : 1≤L := by dsimp [L];linarith
  have hL' : 0<L := by linarith
  have hpow := Real.one_le_rpow hY (sub_nonneg.mpr hσ')
  have hU : 2≤U := by
    dsimp [U]
    nlinarith only [mul_le_mul hpow (one_le_pow₀ hL (n:=3)) zero_le_one (by positivity)]
  have hlog : Real.log U≤100*L := by
    rw [show U=96*Y^(1-σ)*L^3 by rfl,Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hp _).ne',Real.log_rpow hp,Real.log_pow]
    have h₁ := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<96)
    have h₂ := Real.log_le_sub_one_of_pos hL'
    dsimp only [L] at h₂ ⊢
    norm_num only [Nat.cast_ofNat] at *
    nlinarith only [h₁,h₂,mul_nonneg hσ.le hy,hy]
  have hz := sum_zeroMultiplicity_le_zeroCountUpTo (T:=U) S (fun z hz => by
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hS z hz
    exact ⟨h₁,hσ.trans_le h₂,h₃,h₄,h₅⟩)
  have hc : (∑z∈S,(zeroMultiplicity z:ℝ))≤zeroCountUpTo U := by exact_mod_cast hz
  apply (hc.trans (H U hU)).trans
  exact (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤A*U)).trans_eq (by dsimp [U,L];ring)

/-- At Montgomery's balancing length, the discarded low zeros have at
most half the main density exponent. -/
theorem montgomery_zeta_low_zeros_balanced :
    ∃ C : ℝ,0<C ∧ ∀{σ H : ℝ},3/4≤σ → σ≤1 → 1≤H → ∀ S : Finset ℂ,
      (∀ z∈S,riemannZeta z=0 ∧ σ≤z.re ∧ z.re<1 ∧ 0<z.im ∧
        z.im≤96*(H^(1/σ:ℝ))^(1-σ)*(1+Real.log (H^(1/σ:ℝ)))^3) →
      (∑z∈S,(zeroMultiplicity z:ℝ))≤C*H^((1-σ)/σ)*(1+Real.log H)^4 := by
  obtain ⟨A,hA,K⟩ := montgomery_zeta_low_zeros
  refine ⟨16*A,by positivity,?_⟩
  intro σ H hσ hσ' hH S hS
  have hσ₀ : 0<σ := by linarith
  have hH₀ : 0<H := by linarith
  have hlog := Real.log_nonneg hH
  have hγ : 1/σ≤2 := (div_le_iff₀ hσ₀).mpr (by linarith)
  have hh := K hσ₀ hσ' (Real.one_le_rpow hH (by positivity : 0≤1/σ)) S hS
  rw [←Real.rpow_mul hH₀.le,Real.log_rpow hH₀,show (1/σ)*(1-σ)=(1-σ)/σ by ring] at hh
  have hl := pow_le_pow_left₀ (by positivity : 0≤1+1/σ*Real.log H)
    (by linarith only [mul_le_mul_of_nonneg_right hγ hlog] : 1+1/σ*Real.log H≤2*(1+Real.log H)) 4
  exact hh.trans ((mul_le_mul_of_nonneg_left hl (by positivity : 0≤A*H^((1-σ)/σ))).trans_eq (by ring))

end AnalyticNumberTheory.PrimeDistribution
