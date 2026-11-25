import Mathlib.Analysis.Complex.ExponentialBounds
import AnalyticNumberTheory.PrimeDistribution.InghamBalance

/-! # The cutoffs and exponents in Montgomery's density estimate -/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

/-- The density exponent furnished by Montgomery's sparse mean value. -/
def montgomeryExponent (σ : ℝ) := 2*(1-σ)/σ

/-- The Riesz cutoff, depending only on the conductor-height parameter and σ. -/
def montgomeryCutoff (H σ : ℝ) := H^(1/σ)

/-- The mollifier length is chosen after counting the samples and may exceed
the Riesz cutoff. -/
def montgomeryMollifierLength (R H : ℝ) : ℕ := ⌈R*Real.sqrt H⌉₊

/-- At the chosen cutoff the powers from the polynomial and integral zero detectors agree. -/
theorem montgomeryCutoff_balance {H σ : ℝ} (hH : 0<H) (hσ : 0<σ) :
    (montgomeryCutoff H σ)^(2*(1-σ))=H^(montgomeryExponent σ) ∧
      H^2*(montgomeryCutoff H σ)^(2-4*σ)=H^(montgomeryExponent σ) := by
  unfold montgomeryCutoff montgomeryExponent
  constructor
  · rw [←Real.rpow_mul hH.le];congr 1;ring
  · rw [←Real.rpow_mul hH.le,←Real.rpow_two H,←Real.rpow_add hH]
    congr 1;field_simp;ring

theorem inghamExponent_le_montgomeryExponent {σ : ℝ} (hσ : 0<σ) (hσ' : σ≤4/5) :
    inghamExponent σ≤montgomeryExponent σ := by
  unfold inghamExponent montgomeryExponent
  rw [div_le_div_iff₀ (by linarith) hσ]
  nlinarith only [mul_nonneg (by linarith : 0≤1-σ) (by linarith : 0≤4-5*σ)]

theorem montgomeryCutoff_bounds {H σ : ℝ} (hH : 1≤H) (hσ : σ∈Icc (1/2:ℝ) 1) :
    H≤montgomeryCutoff H σ ∧ montgomeryCutoff H σ≤H^2 := by
  have hp : 0<σ := by linarith [hσ.1]
  unfold montgomeryCutoff
  constructor
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH ((le_div_iff₀ hp).mpr (by linarith [hσ.2]) : 1≤1/σ)
  · simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hH ((div_le_iff₀ hp).mpr (by linarith [hσ.1]) : 1/σ≤2)

theorem montgomeryMollifierLength_bounds {R H : ℝ} (hR : 1≤R) (hH : 1≤H) :
    R*Real.sqrt H≤montgomeryMollifierLength R H ∧
    (montgomeryMollifierLength R H:ℝ)≤2*R*Real.sqrt H := by
  have hs : 1≤Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH
  have hp := one_le_mul_of_one_le_of_one_le hR hs
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (by linarith : 0≤R*Real.sqrt H)).le.trans (by linarith)⟩

/-- A crude linear-logarithmic bound for the number of samples ensures the
mollifier length has the same logarithmic scale as H. -/
theorem montgomeryMollifierLength_log {A R H : ℝ} (hA : 1≤A) (hR : 1≤R) (hH : 1≤H)
    (h : R≤A*H*(1+Real.log H)) :
    1+Real.log (montgomeryMollifierLength R H) ≤ (4+Real.log (2*A))*(1+Real.log H) := by
  have ha := zero_lt_one.trans_le hA
  have hh := zero_lt_one.trans_le hH
  have hs : Real.sqrt H≤H := by nlinarith only [Real.sq_sqrt hh.le,sq_nonneg (Real.sqrt H-1),hH]
  have hb := montgomeryMollifierLength_bounds hR hH
  have hx : 0<(montgomeryMollifierLength R H:ℝ) :=
    (mul_pos (zero_lt_one.trans_le hR) (Real.sqrt_pos.mpr hh)).trans_le hb.1
  have hl := Real.log_le_sub_one_of_pos hh
  have hp : (montgomeryMollifierLength R H:ℝ)≤(2*A)*H^3 := by
    apply hb.2.trans
    calc _ ≤ 2*(A*H*H)*H := mul_le_mul (mul_le_mul_of_nonneg_left
                (h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))) (by norm_num)) hs
                (Real.sqrt_nonneg _) (by positivity)
         _ = _ := by ring
  have hlog := Real.log_le_log hx hp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hpos := Real.log_nonneg (by linarith : 1≤2*A)
  nlinarith only [hlog,mul_nonneg hpos (Real.log_nonneg hH),Real.log_nonneg hH]

/-- Remove the fourth power of the detector threshold at the chosen Y. -/
theorem montgomery_cubic_balance {R r A D H σ ℓ : ℝ} (hH : 0<H) (hσ : 0<σ) (hA : 0<A)
    (h : r^3*(1/(A*(montgomeryCutoff H σ)^(1/2-σ)))^4≤D*R^2*H^2*ℓ^11) :
    r^3≤(D*A^4)*R^2*ℓ^11*H^(montgomeryExponent σ) := by
  let Y := montgomeryCutoff H σ
  have hy : 0<Y := Real.rpow_pos_of_pos hH _
  change r^3*(1/(A*Y^(1/2-σ)))^4≤_ at h
  rw [div_pow,one_pow,←div_eq_mul_one_div,div_le_iff₀ (by positivity)] at h
  apply h.trans_eq
  have hp : (Y^(1/2-σ))^4=Y^(2-4*σ) := by
    rw [←Real.rpow_mul_natCast hy.le];congr 1;push_cast;ring
  rw [mul_pow,hp,←(montgomeryCutoff_balance hH hσ).2];change _=_*(H^2*Y^(2-4*σ));ring

/-- The two detector populations sum to R. If the second population dominates,
cancel the square of R in its cubic large-values bound. -/
theorem montgomery_count_absorption {R r₁ r₂ a b W : ℝ}
    (hR : 0<R) (hr : R=r₁+r₂) (hr₂ : 0≤r₂) (ha : 0≤a) (hb : 0≤b) (hW : 0≤W)
    (h₁ : r₁≤a*W) (h₂ : r₂^3≤b*R^2*W) : R≤(2*a+8*b)*W := by
  by_cases h : R≤2*r₁
  · nlinarith only [h,h₁,mul_nonneg hb hW]
  · have hh : R≤2*r₂ := by linarith
    have hh' := pow_le_pow_left₀ hR.le hh 3
    have hc : R^3≤8*b*R^2*W := by nlinarith only [h₂,hh']
    have h' : R≤8*b*W := le_of_mul_le_mul_right (a:=R^2) (by nlinarith only [hc]) (sq_pos_of_pos hR)
    nlinarith only [h',mul_nonneg ha hW]

/-- Passing from a rounded cutoff up to 10H to the usual conductor-height
parameter H, with the logarithm measured at Y and H at most Y squared. -/
theorem montgomery_scale_bound {X H Y σ : ℝ} (hX : 1≤X) (hH : 0≤H) (hY : 2≤Y)
    (hXH : X≤10*H) (hHY : H≤Y^2) (hσ : σ∈Set.Icc (1/2:ℝ) 1) :
    (1+Real.log X)^12*X^(montgomeryExponent σ) ≤
      (100*24^13)*(Real.log Y)^13*H^(montgomeryExponent σ) := by
  have he : 0 ≤ montgomeryExponent σ := by unfold montgomeryExponent;apply div_nonneg <;> nlinarith [hσ.2,hσ.1]
  have he' : montgomeryExponent σ≤2 := by
    unfold montgomeryExponent;apply (div_le_iff₀ (by linarith [hσ.1])).mpr;linarith [hσ.1]
  have hp := Real.rpow_le_rpow (zero_le_one.trans hX) hXH he
  rw [Real.mul_rpow (by norm_num) hH] at hp
  have hg : (10:ℝ)^(montgomeryExponent σ)≤100  := by
    convert (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(10:ℝ)) he') using 1 <;> norm_num
  have hZ := hp.trans (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hH _))
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) (hXH.trans (mul_le_mul_of_nonneg_left hHY (by norm_num)))
  have hy₀ : 0<Y := by linarith
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hy₀.ne'),Real.log_pow] at hlog
  have hylog : 1/2≤Real.log Y := (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hY)
  have h9 : Real.log (10:ℝ)≤9 := by simpa only [show (10:ℝ)-1=9 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)
  norm_num only [Nat.cast_ofNat] at hlog
  have hL : 1+Real.log X≤24*Real.log Y := by linarith only [hlog,h9,hylog]
  have h₇ : (1+Real.log X)^12≤(24*Real.log Y)^13 :=
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) hL 12).trans (pow_le_pow_right₀ (by linarith) (by decide))
  exact (mul_le_mul h₇ hZ (Real.rpow_nonneg (zero_le_one.trans hX) _) (by positivity [show 0≤Real.log Y by linarith])).trans_eq (by ring)

end AnalyticNumberTheory.PrimeDistribution
