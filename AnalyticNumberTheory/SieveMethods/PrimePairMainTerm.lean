import AnalyticNumberTheory.SieveMethods.PrimePairDenominator
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-!
# The main term at the quarter-power Selberg level

At level z² = √x/(log x)^B, the reciprocal of the logarithmic denominator
has leading factor 4/log x. The additive denominator error and the loss in
the level give a relative error of order log log x/log x.
-/

noncomputable section
open Finset Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution

theorem twinPrimeEulerConstant_le_primePairSingularFactor (h : ℕ) :
    twinPrimeEulerConstant≤primePairSingularFactor h := by
  apply le_mul_of_one_le_right twinPrimeEulerConstant_pos.le
  apply Finset.one_le_prod₀
  intro p hp
  have h2 : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2
  exact le_add_of_nonneg_right (by positivity)

/-- The positive square root of the level of distribution for the prime-pair sieve. -/
def primePairSieveLimit (B x : ℝ) := √(√x/(log x)^B)

private theorem logIntegral_main_upper :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ x : ℝ in atTop, logIntegral x≤x/log x*(1+K/log x) := by
  obtain ⟨K,hK,H⟩ := Chebyshev.integral_one_div_log_sq_isBigO.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [H.bound,eventually_ge_atTop (2:ℝ)] with x hx hx₂
  have hl := log_pos (show 1<x by linarith)
  have hp : 0≤x/log x^2 := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hp] at hx
  rw [logIntegral_eq_div_log_add_integral hx₂]
  have hi := (le_abs_self _).trans hx
  have htwo : 0<2/log 2 := by positivity
  calc _ ≤ x/log x+K*(x/log x^2) := by linarith
       _ = _ := by ring

private theorem level_expansion {B L : ℝ} (hB : 0≤B) (hL : 0≤L) :
    ∀ᶠ x : ℝ in atTop, let l := log x; let m := log l; let z := primePairSieveLimit B x
      1≤m ∧ m≤l ∧ 2≤z ∧ z≤√x ∧ z^2=√x/l^B ∧
      l/4-(B/2+L)*m ≤ log z-L ∧ (B/2+L)*m ≤ l/8 := by
  let A := B/2+L
  have hA : 0≤A := by dsimp [A];positivity
  have hd : Tendsto (fun l : ℝ => log l/l) atTop (𝓝 0) :=
    (isLittleO_log_id_atTop).tendsto_div_nhds_zero
  have hm := (hd.comp Real.tendsto_log_atTop).eventually_lt_const
    (show 0<1/(8*(A+1)) by positivity)
  filter_upwards [hm,Real.tendsto_log_atTop.eventually_ge_atTop (max 16 (exp 1)),eventually_ge_atTop (2:ℝ)] with x hr hlog hx
  let l := log x
  let m := log l
  let z := primePairSieveLimit B x
  have hl16 : 16≤l := (le_max_left ..).trans hlog
  have hl : 0<l := by linarith
  have hx0 : 0<x := by linarith
  have hml : m≤l := (Real.log_le_sub_one_of_pos hl).trans (by linarith)
  have hm1 : 1≤m := (Real.le_log_iff_exp_le hl).mpr ((le_max_right ..).trans hlog)
  have hm0 : 0≤m := by linarith
  change m/l < 1/(8*(A+1)) at hr
  have hsmall : A*m≤l/8 := by
    have ha : 0<8*(A+1) := by positivity
    rw [div_lt_div_iff₀ hl ha] at hr
    nlinarith
  have hzpos : 0<z := Real.sqrt_pos.2 (div_pos (Real.sqrt_pos.2 hx0) (Real.rpow_pos_of_pos hl _))
  have hzsq : z^2=√x/l^B := Real.sq_sqrt (by positivity)
  have hzlog : log z=l/4-B/2*m := by
    dsimp only [z,primePairSieveLimit]
    rw [Real.log_sqrt (by positivity),Real.log_div (Real.sqrt_pos.2 hx0).ne' (Real.rpow_pos_of_pos hl _).ne',
      Real.log_sqrt hx0.le,Real.log_rpow hl];dsimp [l,m];ring
  have hLmul := mul_le_mul_of_nonneg_left hm1 hL
  have hδ : l/4-A*m ≤ log z-L := by dsimp [A];rw [hzlog];nlinarith
  have hz2 : 2≤z := by
    have his := Real.log_le_sub_one_of_pos hzpos
    linarith
  have hzupper : z≤√x := by
    have hr1 : 1≤l^B := Real.one_le_rpow (by linarith) hB
    have hsmall' := div_le_self (Real.sqrt_nonneg x) hr1
    nlinarith [Real.sq_sqrt hx0.le,Real.sqrt_nonneg x,hzsq]
  exact ⟨hm1,hml,hz2,hzupper,hzsq,hδ,hsmall⟩

/-- Uniform asymptotic upper bound for the Selberg main term at a logarithmically
reduced quarter-power cutoff. The parameter B is fixed independently of the shift. -/
theorem primePair_selberg_mainTerm {B : ℝ} (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, let z := primePairSieveLimit B x
      2≤z ∧ z≤√x ∧ z^2=√x/(log x)^B ∧ ∀ {h : ℕ}, h≠0 →
        logIntegral x / primePairDenominator h z ≤
          8*primePairSingularFactor h*(x/(log x)^2)*(1+C*(log (log x)/log x)) := by
  obtain ⟨L,hL,HL⟩ := primePairDenominator_lower
  obtain ⟨K,hK,HK⟩ := logIntegral_main_upper
  let a := 8*(B/2+L)
  have ha : 0≤a := by dsimp [a];positivity
  refine ⟨a+K+a*K,by positivity,?_⟩
  filter_upwards [level_expansion hB hL,HK,eventually_ge_atTop (2:ℝ)] with x hlevel hli hx
  obtain ⟨hm,hmle,hz,hzx,hzsq,hD,hmin⟩ := hlevel
  refine ⟨hz,hzx,hzsq,?_⟩
  intro h hh
  let l := log x
  let m := log l
  let r := m/l
  let z := primePairSieveLimit B x
  let S := primePairSingularFactor h
  let D := primePairDenominator h z
  let d := (B/2+L)*m
  have hl : 0<l := log_pos (by linarith)
  have hm0 : 0≤m := le_trans zero_le_one hm
  have hS : 0<S := twinPrimeEulerConstant_pos.trans_le (twinPrimeEulerConstant_le_primePairSingularFactor _)
  have hd : 0≤d := by dsimp [d];positivity
  have hr : 0≤r := div_nonneg hm0 hl.le
  have hr1 : r≤1 := (div_le_one hl).mpr hmle
  have hden : l/4-d≤(2*S)*D := hD.trans (HL hz hh)
  have hd' : d≤l/8 := hmin
  have hDpos : 0<D := pos_of_mul_pos_right (by linarith : 0<(2*S)*D) (by positivity)
  have hmain : 1/D ≤ (8*S/l)*(1+a*r) := by
    have hprod := mul_nonneg hd (show 0≤l-8*d by linarith)
    have hcal : 1≤ (4/l)*(1+8*d/l)*(l/4-d) := by
      field_simp [hl.ne']; nlinarith
    have hm' := mul_le_mul_of_nonneg_left hden (by positivity : 0≤(4/l)*(1+8*d/l))
    rw [div_le_iff₀ hDpos]
    have he : (4/l)*(1+8*d/l)*(2*S*D)=(8*S/l)*(1+a*r)*D := by dsimp [a,d,r];ring
    exact hcal.trans (hm'.trans_eq he)
  have hKL : K/l≤K*r := by
    dsimp [r];rw [←mul_div_assoc];exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hK.le hm) hl.le
  have hli' : logIntegral x≤ x/l*(1+K*r) := hli.trans (by gcongr)
  have hfin : (1+K*r)*(1+a*r)≤1+(a+K+a*K)*r := by
    nlinarith only [mul_nonneg (mul_nonneg ha hK.le) (mul_nonneg hr (sub_nonneg.mpr hr1))]
  have hx0 : 0≤x := by linarith
  calc logIntegral x / D = logIntegral x*(1/D) := by ring
       _ ≤ (x/l*(1+K*r))*((8*S/l)*(1+a*r)) :=
         mul_le_mul hli' hmain (by positivity) (by positivity)
       _ = 8*S*(x/l^2)*((1+K*r)*(1+a*r)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)

end AnalyticNumberTheory.SieveMethods
