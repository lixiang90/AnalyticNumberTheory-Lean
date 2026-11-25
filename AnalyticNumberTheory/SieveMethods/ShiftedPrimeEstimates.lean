import AnalyticNumberTheory.SieveMethods.ShiftedPrimeProgressions
import AnalyticNumberTheory.SieveMethods.KuhnWeights

/-!
# Quantitative inputs for the weighted shifted-prime sieve

The level z^3.98 lies inside the Bombieri–Vinogradov range for x = z^8.
The fixed shift changes each progression count by at most |h|+1.
-/
noncomputable section
open Finset Set Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

theorem shifted_log_power_small {d : ℝ} (hd : 0<d) (a : ℝ) {c : ℝ} (hc : 0<c) :
    ∀ᶠ z : ℝ in atTop,(log z)^a≤c*z^d := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hd).bound hc,eventually_ge_atTop (2:ℝ)] with z hz hz₂
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (log_nonneg (by linarith : 1≤z)) a),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0≤z) d)] using hz

private theorem kuhn_level_within_BV (B : ℝ) :
    ∀ᶠ z : ℝ in atTop, z^kuhnLevel≤sqrt (z^8)/log (z^8)^B := by
  have he : 0<4-kuhnLevel := by norm_num [kuhnLevel]
  filter_upwards [shifted_log_power_small he B (c:=1/(8:ℝ)^B) (by positivity),eventually_ge_atTop (2:ℝ)] with z h hz
  have hz₀ : 0<z := by linarith
  have hlz := log_pos (by linarith : 1<z)
  have hs : sqrt (z^8)=z^4 := by rw [show z^8=(z^4)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hs,Real.log_pow]; push_cast
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) B)).mpr
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤8) hlz.le]
  have h₁ : (8:ℝ)^B*log z^B≤z^(4-kuhnLevel) := by
    calc _ ≤ (8:ℝ)^B*(1/8^B*z^(4-kuhnLevel)) := mul_le_mul_of_nonneg_left h (by positivity)
         _ = _ := by field_simp
  apply (mul_le_mul_of_nonneg_left h₁ (Real.rpow_nonneg hz₀.le _)).trans_eq
  rw [←Real.rpow_add hz₀]; ring_nf; norm_cast

/-- Standard progression majorant for the fixed shift h. -/
def shiftedPrimeError (h : ℤ) (x : ℝ) (d : ℕ) := maximalPiAPError x d+((h.natAbs:ℝ)+1)

theorem shiftedPrimeError_nonneg {h : ℤ} {x : ℝ} (hx : 2≤x) {d : ℕ} (hd : 0<d) :
    0≤shiftedPrimeError h x d := by
  have he := piAPError_le_maximal hx hd.ne' (Nat.coprime_one_left d)
  dsimp [shiftedPrimeError]; linarith [abs_nonneg (piAP x d 1-logIntegral x/d.totient),Nat.cast_nonneg (α:=ℝ) h.natAbs]

/-- The entire progression budget is o(z^8/(log z)^2), for fixed h. -/
theorem shiftedPrime_error_sum (h : ℤ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ z : ℝ in atTop,
      (∑d∈Finset.Icc 1 ⌊z^kuhnLevel⌋₊,shiftedPrimeError h (z^8) d)≤ε*z^8/(log z)^2 := by
  obtain ⟨B,_,C,hC,HB⟩ := bombieriVinogradov_piAP 3
  let H := (h.natAbs:ℝ)+1
  have hH : 0<H := by dsimp [H]; positivity
  have hgap : 0<8-kuhnLevel := by norm_num [kuhnLevel]
  filter_upwards [kuhn_level_within_BV B,shifted_log_power_small hgap 2 (c:=ε/(2*H)) (by positivity),
    Real.tendsto_log_atTop.eventually_ge_atTop (2*C/ε),eventually_ge_atTop (2:ℝ)] with z hq hsmall hbig hz
  have hz₀ : 0<z := by linarith
  have hz₁ : 1≤z := by linarith
  have hl := log_pos (by linarith : 1<z)
  have hzpow : 1≤z^kuhnLevel := Real.one_le_rpow hz₁ (by norm_num [kuhnLevel])
  have hx : 2≤z^8 := by calc (2:ℝ)≤2^8 := by norm_num
                                _ ≤ _ := pow_le_pow_left₀ (by norm_num) hz 8
  have h := HB hx hzpow hq
  rw [Real.log_pow] at h; push_cast at h; norm_num only [Real.rpow_ofNat] at h
  have h₁ : C*z^8/(8*log z)^3≤(ε/2)*z^8/(log z)^2 := by
    have hCl : 2*C≤ε*log z := by linarith [(div_le_iff₀ hε).mp hbig]
    have hr : C≤(ε/2)*log z := by linarith
    calc _ ≤ C*z^8/(log z)^3 := by gcongr; linarith
         _ = (C/log z)*z^8/(log z)^2 := by ring
         _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ((div_le_iff₀ hl).mpr hr) (by positivity)) (sq_nonneg (log z))
  have h₂ : z^kuhnLevel*H≤(ε/2)*z^8/(log z)^2 := by
    rw [Real.rpow_ofNat] at hsmall
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hprod := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (Real.rpow_nonneg hz₀.le kuhnLevel) hH.le)
    apply le_trans _ ((show z^kuhnLevel*H*(log z)^2≤z^kuhnLevel*H*(ε/(2*H)*z^(8-kuhnLevel)) from hprod).trans_eq ?_)
    · exact le_rfl
    · rw [show z^kuhnLevel*H*(ε/(2*H)*z^(8-kuhnLevel))=(ε/2)*(z^kuhnLevel*z^(8-kuhnLevel)) by field_simp <;> ring,
          ←Real.rpow_add hz₀,add_sub_cancel,Real.rpow_ofNat]
  have hcard : ((Finset.Icc 1 ⌊z^kuhnLevel⌋₊).card:ℝ)≤z^kuhnLevel := by
    rw [Nat.card_Icc]; simp only [Nat.add_sub_cancel]; exact Nat.floor_le (zero_le_one.trans hzpow)
  unfold shiftedPrimeError; rw [sum_add_distrib,sum_const,nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_right hcard hH.le
  change _+_*H≤_
  exact (add_le_add (h.trans h₁) (hh.trans h₂)).trans_eq (by ring)

/-- Lower main-term bound, uniform in the prime data except for the fixed
logarithmic mass and atom constants. -/
theorem shiftedPrime_main_lower {K : ℝ} (hK : 0≤K) :
    ∃ c : ℝ, 0<c ∧ ∀ {h : ℕ}, (hh : Even h) → ∀ (A : Finset ℕ) {z : ℝ}, 2≤z →
      let x := z^8
      let X := logIntegral x
      let s := shiftedPrimeSieveData A X h hh
      let P := shiftedSievePrimes h (z^kuhnPrimeExponent)
      SieveLogMassBounds P s.density 2 z K K →
        c*z^8/(log z)^2≤X*sieveEulerBelow P s.density z := by
  let J := exp (2*linearSieveEulerConstant K 2)
  let c := log 2/(16*J)
  have hJ : 0<J := exp_pos _
  have hl₂ := log_pos (by norm_num : (1:ℝ)<2)
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro h hh A z hz x X s P H
  have hz₁ : 1≤z := by linarith
  have hlz := log_pos (by linarith : 1<z)
  have hx : 4≤x := by calc (4:ℝ)≤2^8 := by norm_num
                            _ ≤ _ := pow_le_pow_left₀ (by norm_num) hz 8
  have hX := (shifted_logIntegral_bounds (by linarith : 2≤x)).1
  have hxlog : log x=8*log z := by dsimp [x]; rw [Real.log_pow]; norm_num
  have hXlower : x/(16*log z)≤X := by
    change (x-2)/log x≤X at hX
    rw [hxlog] at hX
    apply le_trans _ hX; rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) hlz.le]
  have hP (p : ℕ) (hp : p∈P) := (mem_shiftedSievePrimes.mp hp).1
  have hg (p : ℕ) (hp : p∈P) := And.intro (s.density_nonneg_of_prime (hP p hp)) (shiftedPrime_separation A X hh p hp)
  have he := (sieveEulerBelow_ratio_comparison (w:=2) (by norm_num) hz (fun p hp => (hP p hp).one_lt.le)
    (by norm_num : (0:ℝ)<2) hg hK hK H).1
  have hset : P.filter (fun p : ℕ => (p:ℝ)<2)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp
    obtain ⟨hp,hlt⟩ := mem_filter.mp hp
    exact (not_lt.mpr (show (2:ℝ)≤p by exact_mod_cast (hP p hp).two_le)) hlt
  have he₂ : sieveEulerBelow P s.density 2=1 := by rw [sieveEulerBelow,hset,Finset.prod_empty]
  rw [he₂] at he
  let V := sieveEulerBelow P s.density z
  have hV : 0<V := sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z
  have hVlow : log 2/(J*log z)≤V := by
    change 1/V≤J*(log z/log 2) at he
    apply (div_le_iff₀ (mul_pos hJ hlz)).mpr
    have h := (div_le_iff₀ hV).mp he
    field_simp [hl₂.ne'] at h; linarith only [h]
  have hmul := mul_le_mul hXlower hVlow (div_nonneg hl₂.le (mul_pos hJ hlz).le) ((div_nonneg (by dsimp [x]; positivity) (by positivity)).trans hXlower)
  apply le_trans _ hmul; dsimp only [c,x]; ring_nf; exact le_rfl

end AnalyticNumberTheory.SieveMethods
