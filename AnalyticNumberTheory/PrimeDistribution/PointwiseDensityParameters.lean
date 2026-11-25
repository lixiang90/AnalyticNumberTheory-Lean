import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Parameter selection for a zero density bound from pointwise L-estimates

The length Y absorbs the integral detector into the left side. All
powers and logarithms are uniform up to the endpoint σ=1.
-/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

/-- The conductor exponent supplied by growth H^a on the critical line. -/
def pointwiseDensityExponent (a σ : ℝ) : ℝ := (1+4*a)*(1-σ)/(2*σ-1)

/-- The cutoff balancing the pointwise integral detector against the count of zeros. -/
noncomputable def pointwiseDensityCutoff (A b a H σ : ℝ) : ℝ :=
  (16*max 1 A*(1+Real.log H)^(3+2*b)*H^(1/2+2*a))^(1/(2*σ-1))

/-- Size, logarithm, off-diagonal damping, and polynomial cost at the pointwise cutoff. -/
theorem pointwise_density_cutoff_estimates {A a b : ℝ} (hA : 0≤A) (ha : a∈Icc (0:ℝ) (1/4)) (hb : 0≤b) :
    ∃C : ℝ,0<C ∧ ∀{H σ : ℝ},1≤H → σ∈Icc (3/4:ℝ) 1 →
    let L := 1+Real.log H
    let Y := pointwiseDensityCutoff A b a H σ
    16≤Y ∧ 1+Real.log Y≤C*L ∧ A*L^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)≤1/16 ∧
      Y^(2*(1-σ))≤16*max 1 A*L^(3+2*b)*H^(pointwiseDensityExponent a σ) := by
  let M := 16*max 1 A
  have hM : 16≤M := by dsimp [M];linarith [le_max_left 1 A]
  let C := 3+2*(Real.log M+(3+2*b))
  have hm : 0<M := by linarith
  have hmlog := Real.log_nonneg (by linarith : 1≤M)
  have hC : 0<C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro H σ hH hσ
  dsimp only
  let L := 1+Real.log H
  let k := 3+2*b
  let e := 1/2+2*a
  let d := 2*σ-1
  let W := M*L^k*H^e
  have hH' := zero_lt_one.trans_le hH
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg hH]
  have hL' := zero_lt_one.trans_le hL
  have hk : 0≤k := by dsimp [k];linarith
  have he : 0≤e := by dsimp [e];linarith [ha.1]
  have he' : e≤1 := by dsimp [e];linarith [ha.2]
  have hd : 1/2≤d := by dsimp [d];linarith [hσ.1]
  have hd' : d≤1 := by dsimp [d];linarith [hσ.2]
  have hdp : 0<d := by linarith
  have hdi : 1≤1/d := (one_le_div hdp).mpr hd'
  have hdi' : 1/d≤2 := (div_le_iff₀ hdp).mpr (by linarith)
  have hWL : 1≤L^k := Real.one_le_rpow hL hk
  have hWH : 1≤H^e := Real.one_le_rpow hH he
  have hW : M≤W := by
    dsimp [W];exact (le_mul_of_one_le_right hm.le hWL).trans
      (le_mul_of_one_le_right (by positivity) hWH)
  have hw : 0<W := hm.trans_le hW
  have hW₁ : 1≤W := by linarith
  change 16≤W^(1/d) ∧ 1+Real.log (W^(1/d))≤C*L ∧
    A*L^k*H^e*(W^(1/d))^(1-2*σ)≤1/16 ∧
    (W^(1/d))^(2*(1-σ))≤M*L^k*H^(pointwiseDensityExponent a σ)
  refine ⟨(hM.trans hW).trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hW₁ hdi),?_,?_,?_⟩
  · rw [Real.log_rpow hw]
    have hlogW : Real.log W=Real.log M+k*Real.log L+e*Real.log H := by
      dsimp [W];rw [Real.log_mul (by positivity) (by positivity),Real.log_mul hm.ne' (by positivity),
        Real.log_rpow hL',Real.log_rpow hH']
    have h1 : Real.log L≤L := by linarith [Real.log_le_sub_one_of_pos hL']
    have h2 : Real.log H≤L := by dsimp [L];linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hk
    have h4 := mul_le_mul he' h2 (Real.log_nonneg hH) zero_le_one
    have h5 := mul_le_mul_of_nonneg_left hL hmlog
    have h6 := mul_le_mul_of_nonneg_right hdi' (Real.log_nonneg hW₁)
    rw [hlogW] at h6
    rw [hlogW];dsimp [C];change _≤(3+2*(Real.log M+k))*L
    nlinarith only [h3,h4,h5,h6,hL]
  · rw [←Real.rpow_mul hw.le,show 1/d*(1-2*σ)= -1 by
      rw [show 1-2*σ= -d by dsimp [d];ring];field_simp,Real.rpow_neg_one]
    rw [←div_eq_mul_inv,div_le_div_iff₀ hw (by norm_num)]
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 A) (mul_nonneg (Real.rpow_nonneg hL'.le k) (Real.rpow_nonneg hH'.le e))
    dsimp [W,M];nlinarith only [h]
  · let r := 1/d*(2*(1-σ))
    have hr : 0≤r := by dsimp [r];exact mul_nonneg (by positivity) (by linarith [hσ.2])
    have hr' : r≤1 := by
      dsimp [r];rw [one_div_mul_eq_div,div_le_one hdp];dsimp [d];linarith [hσ.1]
    have hre : e*r=pointwiseDensityExponent a σ := by dsimp [e,r,d,pointwiseDensityExponent];ring
    rw [←Real.rpow_mul hw.le]
    change W^r≤_
    dsimp only [W];rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hH'.le e),←Real.rpow_mul hH'.le,hre]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hH'.le _)
    exact (Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le (by linarith : 1≤M) hWL) hr').trans_eq (Real.rpow_one _)

/-- Undo the detector threshold and the adaptive mollifier length in the
integral alternative. The exponent 3 is the logarithmic cost of the
sparse Möbius mean. -/
theorem pointwise_typeII_damping {r R K D J W H Y σ a b ℓ X : ℝ}
    (hr : 0≤r) (hR : 0≤R) (hK : 0≤K) (hD : 0≤D) (hJ : 0≤J) (hW : 0<W)
    (hH : 0<H) (hY : 0<Y) (hℓ : 0<ℓ) (hrR : r≤R) (hX : X≤2*R*Real.sqrt H)
    (hlog₀ : 0≤1+Real.log X) (hlog : 1+Real.log X≤J*ℓ)
    (h : r*(1/(W*Y^(1/2-σ)))^2 ≤
      D*H^(2*a)*ℓ^(2*b)*(K*ℓ*X+r*Real.sqrt H*ℓ)*(1+Real.log X)^2) :
    r ≤ (D*(2*K+1)*J^2*W^2)*ℓ^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)*R := by
  rw [div_pow,one_pow,←div_eq_mul_one_div,div_le_iff₀ (by positivity)] at h
  have h1 := add_le_add (mul_le_mul_of_nonneg_left hX (mul_nonneg hK hℓ.le))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrR (Real.sqrt_nonneg H)) hℓ.le)
  apply h.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity))
    (pow_le_pow_left₀ hlog₀ hlog 2) (sq_nonneg _) (by positivity)) (sq_nonneg _)).trans_eq
  have he : (Y^(1/2-σ))^2=Y^(1-2*σ) := by rw [←Real.rpow_mul_natCast hY.le];congr 1;push_cast;ring
  rw [mul_pow W,he,Real.rpow_add hℓ,Real.rpow_add hH,Real.rpow_ofNat ℓ 3,←Real.sqrt_eq_rpow]
  ring

/-- Absorb the integral alternative and evaluate the two logarithmic
factors in the polynomial alternative. -/
theorem pointwise_balance_of_unbalanced {A a b : ℝ} (hA : 0<A) (ha : a∈Icc (0:ℝ) (1/4)) (hb : 0≤b) :
    ∃C : ℝ,0<C ∧ ∀{R H σ : ℝ},0≤R → 1≤H → σ∈Icc (3/4:ℝ) 1 →
    let L := 1+Real.log H
    let Y := pointwiseDensityCutoff A b a H σ
    (R≤A*L*(1+Real.log Y)^5*Y^(2*(1-σ))+A*L^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)*R) →
    R≤C*L^(9+2*b)*H^(pointwiseDensityExponent a σ) := by
  obtain ⟨B,hB,HB⟩ := pointwise_density_cutoff_estimates hA.le ha hb
  refine ⟨2*A*B^5*(16*max 1 A),by positivity,?_⟩
  intro R H σ hR hH hs
  let L := 1+Real.log H
  let Y := pointwiseDensityCutoff A b a H σ
  have hL : 0<L := by dsimp [L];linarith [Real.log_nonneg hH]
  obtain ⟨hY,hlog,hd,hP⟩ := HB hH hs
  change 16≤Y at hY
  change 1+Real.log Y≤B*L at hlog
  change A*L^(3+2*b)*H^(1/2+2*a)*Y^(1-2*σ)≤1/16 at hd
  dsimp only
  intro h
  change R≤A*L*(1+Real.log Y)^5*Y^(2*(1-σ))+_*R at h
  have hu : R≤2*(A*L*(1+Real.log Y)^5*Y^(2*(1-σ))) := by nlinarith only [h,mul_le_mul_of_nonneg_right hd hR,hR]
  have hlog' := pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : 1≤Y)] : 0≤1+Real.log Y) hlog 5
  apply hu.trans
  calc _ ≤ 2*(A*L*(B*L)^5*(16*max 1 A*L^(3+2*b)*H^(pointwiseDensityExponent a σ))) := by
             apply mul_le_mul_of_nonneg_left _ (by norm_num)
             exact mul_le_mul (mul_le_mul_of_nonneg_left hlog' (mul_nonneg hA.le hL.le)) hP (by positivity) (by positivity)
       _ = _ := by
             change _=_*L^(9+2*b)*_
             rw [show 9+2*b=6+(3+2*b) by ring,Real.rpow_add hL 6 (3+2*b),Real.rpow_ofNat L 6];ring

/-- Conversion from rounded conductor-height parameters to the classical
logarithm, including heights between two and e. -/
theorem pointwise_density_scale {b : ℝ} (hb : 0≤b) {X H Z e : ℝ} (hX : 1≤X)
    (hH : 0≤H) (hZ : 2≤Z) (hc : X≤12*H) (hh : H≤Z^2) (he : e∈Icc (0:ℝ) 1) :
    (1+Real.log X)^(10+2*b)*X^e ≤
      (12*30^(10+2*b))*(Real.log Z)^(10+2*b)*H^e := by
  have hz : 0<Z := by linarith
  have hl : 1/2≤Real.log Z := (by linarith [Real.log_two_gt_d9] : 1/2≤Real.log 2).trans
    (Real.log_le_log zero_lt_two hZ)
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) (hc.trans (mul_le_mul_of_nonneg_left hh (by norm_num)))
  rw [Real.log_mul (by norm_num) (by positivity : Z^2≠0),Real.log_pow] at hlog
  have hlog' : 1+Real.log X≤30*Real.log Z := by
    norm_num only [Nat.cast_ofNat] at hlog
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(12:ℝ))]
  have h₁ := Real.rpow_le_rpow (by linarith [Real.log_nonneg hX] : 0≤1+Real.log X) hlog' (by linarith : 0≤10+2*b)
  rw [Real.mul_rpow (by norm_num) (by linarith : 0≤Real.log Z)] at h₁
  have h₂ := Real.rpow_le_rpow (zero_le_one.trans hX) hc he.1
  rw [Real.mul_rpow (by norm_num) hH] at h₂
  have h12 : (12:ℝ)^e≤12 := (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(12:ℝ)) he.2).trans_eq (Real.rpow_one _)
  exact (mul_le_mul h₁ (h₂.trans (mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hH _)))
    (Real.rpow_nonneg (zero_le_one.trans hX) e) (by positivity [show 0≤Real.log Z by linarith])).trans_eq (by ring)

/-- The conductor exponent lies between zero and one throughout the parameter strip. -/
theorem pointwiseDensityExponent_mem {a σ : ℝ} (ha : a∈Icc (0:ℝ) (1/4)) (hs : σ∈Icc (3/4:ℝ) 1) :
    pointwiseDensityExponent a σ∈Icc (0:ℝ) 1 := by
  have hd : 0<2*σ-1 := by linarith [hs.1]
  unfold pointwiseDensityExponent
  exact ⟨div_nonneg (mul_nonneg (by linarith [ha.1]) (by linarith [hs.2])) hd.le,
    (div_le_one hd).mpr (by nlinarith only [mul_nonneg (show 0≤1-4*a by linarith [ha.2]) (sub_nonneg.mpr hs.2),hs.1])⟩

/-- A genuine subconvex conductor exponent gives a stronger height power
than the density hypothesis whenever 3/4+a < σ < 1. -/
theorem pointwiseDensityExponent_lt_density_hypothesis {a σ : ℝ} (ha : 0≤a)
    (hs : 3/4+a<σ) (hs' : σ<1) :
    pointwiseDensityExponent a σ<2*(1-σ) := by
  unfold pointwiseDensityExponent
  rw [div_lt_iff₀ (by linarith : 0<2*σ-1)]
  nlinarith only [mul_pos (show 0<1-σ by linarith) (show 0<4*σ-3-4*a by linarith)]

end AnalyticNumberTheory.PrimeDistribution
