import AnalyticNumberTheory.AnalyticTools.LogarithmicMass
import AnalyticNumberTheory.PrimeDistribution.Oscillation
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import Mathlib.MeasureTheory.Function.Floor

/-! # The weak Mertens hypothesis and the zeros of zeta -/

noncomputable section

open Real Complex Set Filter MeasureTheory Asymptotics
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The weak Mertens hypothesis bounds the logarithmic mean square of M(x)/√x. -/
def WeakMertensHypothesis : Prop :=
  (fun X : ℝ => ∫ x in (1:ℝ)..X, (mertensM x/x)^2) =O[atTop] Real.log

/-- The real and integer versions of the Mertens summatory function agree. -/
theorem mertensM_eq_intCast (x : ℝ) : mertensM x = (RiemannZeta.mertensM x : ℝ) := by
  simp only [mertensM,RiemannZeta.mertensM,Int.cast_sum]

/-- The Mertens summatory function is measurable as a step function. -/
theorem measurable_mertensM : Measurable mertensM :=
  (measurable_from_top (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n:ℝ))).comp
    Nat.measurable_floor

private theorem mertens_abs_le {x : ℝ} (hx : 0 ≤ x) : |mertensM x| ≤ x := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1:ℝ) := Finset.sum_le_sum fun n _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    _ = (⌊x⌋₊:ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

private theorem locally_integrable_of_unit_bound {f : ℝ → ℝ} (hm : Measurable f)
    (hb : ∀ x ≥ 1, |f x| ≤ 1) {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable f volume 1 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  apply (integrableOn_const (C := (1:ℝ)) (hs := (measure_Ioc_lt_top : volume (Ioc (1:ℝ) X) < ⊤).ne)).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
  exact hb x hx.1.le

/-- Under the weak Mertens hypothesis the absolute Mellin integral of M is bounded by
B + C/(σ−1/2) for every real σ > 1/2, with common constants B and C. -/
theorem WeakMertensHypothesis.absolute_mellin_bound (h : WeakMertensHypothesis) :
    ∃ B > 0, ∃ C > 0, ∀ σ : ℝ, 1/2 < σ →
      IntegrableOn (fun x : ℝ => |mertensM x| * x^(-σ-1)) (Ioi 1) ∧
      ∫ x in Ioi (1:ℝ), |mertensM x| * x^(-σ-1) ≤ B+C/(σ-1/2) := by
  let u (x : ℝ) := mertensM x / x
  let f (x : ℝ) := |u x| / Real.sqrt x
  have hu : Measurable u := measurable_mertensM.div measurable_id
  have hf : Measurable f := (continuous_abs.measurable.comp hu).div Real.continuous_sqrt.measurable
  have hu₁ (x : ℝ) (hx : 1 ≤ x) : |u x| ≤ 1 := by
    have hx₀ := zero_lt_one.trans_le hx
    change |mertensM x/x| ≤ 1
    rw [abs_div,abs_of_pos hx₀]
    exact (div_le_one hx₀).mpr (mertens_abs_le hx₀.le)
  have hsq (x : ℝ) (hx : 1 ≤ x) : |(u x)^2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hu₁ x hx) 2
  have hfn (x : ℝ) : 0 ≤ f x := div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hf₁ (x : ℝ) (hx : 1 ≤ x) : |f x| ≤ 1 := by
    rw [abs_of_nonneg (hfn x)]
    have hr : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
    exact (div_le_one (zero_lt_one.trans_le hr)).mpr ((hu₁ x hx).trans hr)
  have hiF (X : ℝ) (hX : 1 ≤ X) := locally_integrable_of_unit_bound hf hf₁ hX
  have hiS (X : ℝ) (hX : 1 ≤ X) := locally_integrable_of_unit_bound (hu.pow_const 2) hsq hX
  obtain ⟨K,hK,HK⟩ := h.exists_pos
  obtain ⟨a,ha⟩ := eventually_atTop.mp HK.bound
  let A := max 1 a
  have hA : 1 ≤ A := le_max_left ..
  have hB (X : ℝ) (hX : 1 ≤ X) : ∫ x in (1:ℝ)..X, (u x)^2 ≤ A+K*Real.log X := by
    rcases le_total A X with hlarge | hsmall
    · have hh := ha X ((le_max_right ..).trans hlarge)
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hX)] at hh
      exact ((le_abs_self _).trans hh).trans (le_add_of_nonneg_left (zero_le_one.trans hA))
    · have hb := intervalIntegral.integral_mono_on hX (hiS X hX)
          (intervalIntegrable_const (c := (1:ℝ))) (fun x hx => (le_abs_self _).trans (hsq x hx.1))
      simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hb
      linarith [mul_nonneg hK.le (Real.log_nonneg hX)]
  have hmass (X : ℝ) (hX : 1 ≤ X) : ∫ x in (1:ℝ)..X, f x ≤ A+(K+1)*Real.log X := by
    have hiInv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 1 X := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hX]
      exact continuousOn_id.inv₀ (fun x hx => (zero_lt_one.trans_le hx.1).ne')
    have hh := intervalIntegral.integral_mono_on hX (hiF X hX) ((hiS X hX).add hiInv) (fun x hx => by
      have hx₀ := zero_lt_one.trans_le hx.1
      have he : (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by rw [inv_pow,Real.sq_sqrt hx₀.le]
      change |u x| / Real.sqrt x ≤ (u x)^2 + x⁻¹
      rw [div_eq_mul_inv,←he,←sq_abs (u x)]
      nlinarith [sq_nonneg (|u x|-(Real.sqrt x)⁻¹),sq_nonneg (|u x|+(Real.sqrt x)⁻¹)])
    rw [intervalIntegral.integral_add (hiS X hX) hiInv,integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hX),div_one] at hh
    linarith [hB X hX]
  refine ⟨A,zero_lt_one.trans_le hA,K+1,by positivity,?_⟩
  intro σ hσ
  have hw := mellin_weight_of_logarithmic_mass (by positivity : 0 ≤ K+1)
    (fun x _ => hfn x) hiF hmass (sub_pos.mpr hσ)
  have he (x : ℝ) (hx : x ∈ Ioi (1:ℝ)) :
      x^(-(σ-1/2))*f x = |mertensM x| * x^(-σ-1) := by
    have hx₀ : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
    dsimp only [f,u]
    rw [abs_div,abs_of_pos hx₀,Real.sqrt_eq_rpow,
      div_eq_mul_inv (|mertensM x| / x) _,div_eq_mul_inv |mertensM x| x,
      ←Real.rpow_neg hx₀.le (1/2),←Real.rpow_neg_one x]
    calc
      _ = |mertensM x| * (x^(-(σ-1/2))*x^(-1:ℝ)*x^(-(1/2):ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hx₀,← Real.rpow_add hx₀]; congr 2 <;> ring
  exact ⟨hw.1.congr_fun he measurableSet_Ioi,(setIntegral_congr_fun measurableSet_Ioi he).symm.trans_le hw.2⟩

end AnalyticNumberTheory.PrimeDistribution
