import AnalyticNumberTheory.AnalyticTools.WeightedPowerSums
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyZeroWeights

/-! # The density estimate for the power weights in the explicit formula -/
noncomputable section
open Real Finset Complex
open scoped Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- An affine majorant of Ingham's exponent, exact at the critical line. -/
theorem inghamExponent_le_affine {σ : ℝ} (hs : σ≤1) : inghamExponent σ≤(5-4*σ)/3 := by
  unfold inghamExponent
  apply (div_le_iff₀ (by linarith)).mpr
  nlinarith only [sq_nonneg (2*σ-1)]

/-- The power weight times the affine density bound is largest at an endpoint
of the interval [1/2,1]. This estimate works on either side of x = H^(4/3). -/
theorem density_weight_affine_le {x H σ : ℝ} (hx : 0<x) (hH : 0<H) (hs : σ∈Set.Icc (1/2:ℝ) 1) :
    x^σ*H^((5-4*σ)/3)≤x^(1/2:ℝ)*H+x*H^(1/3:ℝ) := by
  let f (s : ℝ) := x^s*H^((5-4*s)/3)
  have he (s : ℝ) : f s=Real.exp ((Real.log x-4/3*Real.log H)*s+(5/3)*Real.log H) := by
    dsimp only [f]
    rw [Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hH,←Real.exp_add];congr 1;ring
  have ha : f (1/2)=x^(1/2:ℝ)*H := by norm_num [f]
  have hb : f 1=x*H^(1/3:ℝ) := by norm_num [f]
  change f σ≤_
  by_cases h : 0≤Real.log x-4/3*Real.log H
  · have hl : f σ≤f 1 := by rw [he,he];apply Real.exp_le_exp.mpr;linarith only [mul_le_mul_of_nonneg_left hs.2 h]
    exact (hl.trans_eq hb).trans (le_add_of_nonneg_left (by positivity))
  · have hl : f σ≤f (1/2) := by rw [he,he];apply Real.exp_le_exp.mpr;linarith only [mul_le_mul_of_nonpos_left hs.1 (le_of_not_ge h)]
    exact (hl.trans_eq ha).trans (le_add_of_nonneg_right (by positivity))

/-- The primitive-character explicit-formula zero sum, over all zeros of the
open critical strip at both signs of height, counted with multiplicity. -/
theorem primitive_family_zero_power_sum :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {T x : ℝ},1≤Q → 2≤T → 2≤x →
    primitiveFamilyZeroWeight Q T (fun z => x^z.re) ≤
      C*(Real.sqrt x*((Q:ℝ)^2*T)+x*((Q:ℝ)^2*T)^(1/3:ℝ))*Real.log x*(Real.log ((Q:ℝ)*T))^8 := by
  obtain ⟨A,hA,HA⟩ := primitive_family_density_trivial
  obtain ⟨B,hB,HB⟩ := primitive_conductors_ingham_log_eight
  refine ⟨256*A+B,by positivity,?_⟩
  intro Q T x hQ hT hx
  let H := (Q:ℝ)^2*T
  let ℓ := Real.log ((Q:ℝ)*T)
  let M := Real.sqrt x*H+x*H^(1/3:ℝ)
  let S := primitiveFamilyZeros Q T
  let w (p : (i : PrimitiveCharacterIndex) × ℂ) := (characterZeroMultiplicity p.1.2 p.2:ℝ)
  have hq : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hQT : 2≤(Q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) hq)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (by linarith)
  have hH₀ := zero_lt_one.trans_le hH
  have hx₀ : 0<x := by linarith
  have hl₂ : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl : 1/2≤ℓ := hl₂.trans (Real.log_le_log zero_lt_two hQT)
  have hxlog := hl₂.trans (Real.log_le_log zero_lt_two hx)
  have hM : 0≤M := by dsimp [M];positivity
  have htail (σ : ℝ) (hs : σ∈Set.Icc (1/2:ℝ) 1) :
      x^σ*(∑ p∈S,w p*(if σ≤p.2.re then 1 else 0))≤B*M*ℓ^8 := by
    change x^σ*primitiveFamilyZeroWeight Q T (fun z => if σ≤z.re then 1 else 0)≤_
    rw [primitiveFamilyZeroWeight_tail]
    apply (mul_le_mul_of_nonneg_left (HB hQ hs hT) (Real.rpow_nonneg hx₀.le _)).trans
    have hp := Real.rpow_le_rpow_of_exponent_le hH (inghamExponent_le_affine hs.2)
    have he := (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hx₀.le σ)).trans (density_weight_affine_le hx₀ hH₀ hs)
    rw [←Real.sqrt_eq_rpow] at he
    change x^σ*(B*H^(inghamExponent σ)*ℓ^8)≤B*M*ℓ^8
    change x^σ*H^(inghamExponent σ)≤M at he
    linarith only [mul_le_mul_of_nonneg_right he (mul_nonneg hB.le (pow_nonneg (by linarith : 0≤ℓ) 8))]
  have hsum := weighted_rpow_sum_le_of_tail S w (fun p => p.2.re) (by linarith : 1≤x)
    (by norm_num : (1/2:ℝ)≤1) (fun _ _ => Nat.cast_nonneg _) (fun _ hp => (primitiveFamilyZeros_re hp).2.le) htail
  have hcard : (∑ p∈S,w p)≤A*H*ℓ := by
    have h := HA hQ hT 0
    rw [←primitiveFamilyZeroWeight_tail] at h
    apply le_trans _ h
    apply sum_le_sum;intro p hp
    simp only [if_pos (primitiveFamilyZeros_re hp).1.le,mul_one];rfl
  have he := mul_le_mul_of_nonneg_left hcard (Real.sqrt_nonneg x)
  have hma : Real.sqrt x*H≤M := le_add_of_nonneg_right (mul_nonneg hx₀.le (Real.rpow_nonneg hH₀.le _))
  have hfactor : ℓ≤256*Real.log x*ℓ^8 := by
    have hh := one_le_pow₀ (by linarith : 1≤2*ℓ) (n:=7)
    have hp := mul_le_mul (by linarith : 1≤2*Real.log x) hh (by norm_num) (by linarith)
    linarith only [mul_le_mul_of_nonneg_right hp (by linarith : 0≤ℓ)]
  rw [←Real.sqrt_eq_rpow] at hsum
  have hmain : Real.sqrt x*(A*H*ℓ)≤256*A*M*Real.log x*ℓ^8 := by
    have hh := mul_le_mul hma hfactor (by linarith) hM
    linarith only [mul_le_mul_of_nonneg_left hh hA.le]
  change (∑ p∈S,w p*x^p.2.re)≤(256*A+B)*M*Real.log x*ℓ^8
  linarith only [hsum,he.trans hmain,mul_nonneg (mul_nonneg (mul_nonneg hB.le hM) (by linarith : 0≤Real.log x)) (pow_nonneg (by linarith : 0≤ℓ) 8)]

end AnalyticNumberTheory.PrimeDistribution
