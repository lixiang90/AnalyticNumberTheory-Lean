import AnalyticNumberTheory.SieveMethods.SelbergDenominatorConstant
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The coefficient two for long prime-counting intervals

The positive second-order margin from the Selberg denominator absorbs
the quadratic counting error at sieve limit √y/2.
-/

open Finset Filter Real
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- Denominator of the Selberg estimate with all primes available for sifting. -/
noncomputable def selbergDenominator (z : ℝ) :=
  ∑ d∈(Icc 1 ⌊z⌋₊).filter Squarefree,(d.totient:ℝ)⁻¹

/-- Weight mass of the unrestricted sieve with real endpoint. -/
noncomputable def selbergIntervalWeightMass (z : ℝ) :=
  selbergWeightMass ((Icc 1 ⌊z⌋₊).filter Squarefree)

/-- After subtracting the logarithm, the real-cutoff Selberg denominator converges to its Euler-product constant. -/
theorem tendsto_selbergDenominator_sub_log :
    Tendsto (fun z : ℝ => selbergDenominator z-log z) atTop (𝓝 selbergDenominatorConstant) := by
  have h := tendsto_selberg_denominator_centered.comp (tendsto_nat_floor_atTop (α:=ℝ))
  have hh := (Real.continuousAt_log (x:=1) one_ne_zero).tendsto.comp (tendsto_nat_floor_div_atTop (R:=ℝ))
  rw [Real.log_one] at hh
  rw [← add_zero selbergDenominatorConstant]
  apply (h.add hh).congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
  have hz' : (0:ℝ)<⌊z⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hz
  change selbergDenominator z-log ⌊z⌋₊+log ((⌊z⌋₊:ℝ)/z)=_
  rw [Real.log_div hz'.ne' (by linarith)]; ring

/-- The absolute Selberg weight mass per unit of sieve level tends to fifteen divided by pi squared. -/
theorem tendsto_selbergIntervalWeightMass_div :
    Tendsto (fun z : ℝ => selbergIntervalWeightMass z/z) atTop (𝓝 (15/π^2)) := by
  have h := tendsto_selbergWeightMass_div.comp (tendsto_nat_floor_atTop (α:=ℝ))
  have hh := h.mul (tendsto_nat_floor_div_atTop (R:=ℝ))
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
  have hz' : (0:ℝ)<⌊z⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hz
  change selbergIntervalWeightMass z/(⌊z⌋₊:ℝ)*((⌊z⌋₊:ℝ)/z)=_
  field_simp

private theorem weight_constant_margin : (15/π^2)^2<4*(selbergDenominatorConstant-log 2) := by
  have ha : π^2>(314/100:ℝ)^2 := by nlinarith [Real.pi_gt_d2,Real.pi_pos]
  have hb : 15/π^2<(153/100:ℝ) := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hn : 0≤15/π^2 := by positivity
  nlinarith [mul_pos (sub_pos.mpr hb) (show 0<153/100+15/π^2 by positivity),
    selbergDenominatorConstant_gt,Real.log_two_lt_d9]

/-- The optimal Selberg weights give the coefficient two for all sufficiently large intervals.
The numerical margin includes the contribution of primes at most the sieve limit. -/
theorem eventually_selberg_interval_majorant :
    ∀ᶠ z : ℝ in atTop, z+4*z^2/selbergDenominator z+
      (selbergIntervalWeightMass z/selbergDenominator z)^2 ≤
        4*z^2/(Real.log z+Real.log 2) := by
  let G := selbergDenominator
  let H := selbergIntervalWeightMass
  let B := selbergDenominatorConstant
  have hD : Tendsto (fun z : ℝ => G z-log z) atTop (𝓝 B) := tendsto_selbergDenominator_sub_log
  have hL : Tendsto (fun z : ℝ => log z+log 2) atTop atTop := tendsto_atTop_add_const_right atTop _ Real.tendsto_log_atTop
  have hd := hD.sub_const (log 2)
  have hR := hd.div_atTop hL
  have hr : Tendsto (fun z : ℝ => G z/(log z+log 2)) atTop (𝓝 1) := by
    have hh := hR.const_add 1
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with z hz
    change 1+(G z-log z-log 2)/(log z+log 2)=_
    have hp : 0<log z+log 2 := add_pos (log_pos hz) (log_pos (by norm_num))
    field_simp; ring
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero
  have hzpow := tendsto_rpow_atTop (show (0:ℝ)<1/2 by norm_num)
  have hx := (hD.div_atTop hzpow).add hlog
  rw [add_zero] at hx
  have hg : Tendsto (fun z : ℝ => (G z)^2/z) atTop (𝓝 0) := by
    have hh := hx.pow 2
    rw [zero_pow (by decide : 2≠0)] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
    change ((G z-log z)/z^(1/2:ℝ)+log z/z^(1/2:ℝ))^2=_
    rw [←add_div,sub_add_cancel,div_pow,←Real.rpow_natCast (z^(1/2:ℝ)) 2,←Real.rpow_mul hz.le]
    norm_num
  have hs := hg.add (tendsto_selbergIntervalWeightMass_div.pow 2)
  have ht := (hr.mul hd).const_mul 4
  rw [zero_add] at hs
  rw [one_mul] at ht
  have he := hs.eventually_lt ht weight_constant_margin
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with z he hz
  have hL' : 0<log z+log 2 := add_pos (log_pos hz) (log_pos (by norm_num))
  have hG : 0<G z := lt_of_lt_of_le (log_pos hz) (sum_squarefree_inv_totient_ge_log hz.le)
  have hzp : 0<z := by linarith
  change G z^2/z+(H z/z)^2 < 4*(G z/(log z+log 2)*(G z-log z-log 2)) at he
  change z+4*z^2/G z+(H z/G z)^2 ≤ 4*z^2/(log z+log 2)
  field_simp [hL'.ne',hG.ne',hzp.ne'] at he ⊢
  nlinarith

end AnalyticNumberTheory.SieveMethods
