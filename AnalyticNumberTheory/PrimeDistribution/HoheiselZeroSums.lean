import AnalyticNumberTheory.PrimeDistribution.ZetaLogFreeDensity
import AnalyticNumberTheory.PrimeDistribution.DensityPowerSums

/-!
# Zeta zero sums for short intervals

A log-free density bound controls the weighted zero sum in terms of the
least scaled zero gap. The classical zero-free region supplies a positive
constant gap. A zero-free width with `δ(t) log t → ∞` gives a growing gap
throughout the entire height range.
-/

noncomputable section
open Finset Complex Filter
open scoped Classical Topology
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Exponential moment bound, uniform as the allowed height and the height
of the power weight vary independently. -/
theorem zeta_zero_sum_of_scaled_gap :
    ∃ A > 0, ∃ K > 0, ∀ {T x b r : ℝ}, 0≤T → 0<x → 0≤b →
      (A+1+b)*Real.log (T+2) ≤ Real.log x →
      (∀ z ∈ nontrivialZerosUpTo T,r ≤ (1-z.re)*Real.log (T+2)) →
      ∑ z ∈ nontrivialZerosUpTo T,(zeroMultiplicity z:ℝ)*x^(z.re-1) ≤ K*Real.exp (-b*r) := by
  obtain ⟨C,hC,A,hA,HD⟩ := zetaDensityCount_log_free
  have hex : Real.exp (-1)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A,hA,C*Real.exp A/(1-Real.exp (-1)),by positivity,?_⟩
  intro T x b r hT hx hb hpow hr
  let S := nontrivialZerosUpTo T
  let L := Real.log (T+2)
  let w (z : ℂ) := (zeroMultiplicity z:ℝ)
  let g (z : ℂ) := (1-z.re)*L
  have hTp : 0<T+2 := by linarith
  have hL : 0<L := Real.log_pos (by linarith)
  have hcnt (t : ℝ) (ht : 0≤t) : (∑ z ∈ S.filter (fun z => g z≤t),w z) ≤ C*Real.exp (A*t) := by
    let σ := max 0 (1-t/L)
    have hσ : σ∈Set.Icc (0:ℝ) 1 := ⟨le_max_left ..,max_le (by norm_num) (by linarith [div_nonneg ht hL.le])⟩
    have hsub : S.filter (fun z => g z≤t) ⊆ zetaDensityZeros σ T := by
      intro z hz
      obtain ⟨hz,hg⟩ := mem_filter.mp hz
      change z∈S.filter (fun z => σ≤z.re)
      refine mem_filter.mpr ⟨hz,max_le (mem_nontrivialZerosUpTo.mp hz).2.1.le ?_⟩
      have hh := (le_div_iff₀ hL).mpr (show (1-z.re)*L≤t from hg); linarith
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Nat.cast_nonneg _)).trans
    apply (HD hT hσ).trans
    rw [Real.rpow_def_of_pos hTp]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    change L*(A*(1-σ))≤A*t
    have hs : 1-t/L≤σ := le_max_right ..
    have hh := (le_div_iff₀ hL).mp (show 1-σ≤t/L by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left hh hA.le]
  apply le_trans _ (finite_density_exponential_moment S w g hA.le hC.le hb (fun _ _ => Nat.cast_nonneg _)
    (fun z hz => mul_nonneg (sub_nonneg.mpr (mem_nontrivialZerosUpTo.mp hz).2.2.1.le) hL.le) hr hcnt)
  apply sum_le_sum; intro z hz
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Real.rpow_def_of_pos hx]; apply Real.exp_le_exp.mpr
  have hd := sub_nonneg.mpr (mem_nontrivialZerosUpTo.mp hz).2.2.1.le
  dsimp only [g,L]
  nlinarith only [mul_le_mul_of_nonneg_right hpow hd]

/-- The scaled distance to one is uniformly positive throughout a height
range, by the classical zeta zero-free region. -/
theorem zeta_scaled_gap_pos :
    ∃ c > 0, ∀ {T : ℝ} (z : ℂ), z∈nontrivialZerosUpTo T → c≤(1-z.re)*Real.log (T+2) := by
  obtain ⟨c,hc,H⟩ := zeta_zeroFreeRegion
  refine ⟨c,hc,?_⟩
  intro T z hz
  obtain ⟨hz,_,hr,hT⟩ := mem_nontrivialZerosUpTo.mp hz
  have h1 : z≠1 := fun he => by simpa [he] using hr
  have hh : z.re < 1-c/Real.log (|z.im|+2) := lt_of_not_ge (fun h => H z h1 h hz)
  have hl : 0<Real.log (|z.im|+2) := Real.log_pos (by linarith [abs_nonneg z.im])
  have h := (div_le_iff₀ hl).mp (show c/Real.log (|z.im|+2) ≤ 1-z.re by linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (sub_nonneg.mpr hr.le))

/-- A zero-free width improves on the classical logarithmic scale when its
product with `log t` tends to infinity. No monotonicity is required. -/
def ImprovingLogZeroFreeHypothesis : Prop :=
  ∃ δ : ℝ → ℝ, ∃ T₀ : ℝ, Tendsto (fun t => δ t*Real.log t) atTop atTop ∧
    ∀ z : ℂ, riemannZeta z=0 → 0<z.re → z.re<1 → T₀≤|z.im| → z.re≤1-δ |z.im|

/-- A growing zero-free width at individual ordinates improves the common
scaled gap in the complete symmetric box. -/
theorem eventually_zeta_scaled_gap (h : ImprovingLogZeroFreeHypothesis) (r : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ z ∈ nontrivialZerosUpTo T, r≤(1-z.re)*Real.log (T+2) := by
  obtain ⟨δ,T₀,hδ,H⟩ := h
  obtain ⟨c,hc,Hc⟩ := zeta_scaled_gap_pos
  obtain ⟨V,hV⟩ := eventually_atTop.mp (hδ.eventually_ge_atTop r)
  let U := max 2 (max T₀ V)
  have hU : 2≤U := le_max_left ..
  have hU₀ : T₀≤U := (le_max_left ..).trans (le_max_right ..)
  have hUV : V≤U := (le_max_right ..).trans (le_max_right ..)
  have hlU : 0<Real.log (U+2) := Real.log_pos (by linarith)
  have hT := Real.tendsto_log_atTop.eventually_ge_atTop (r*Real.log (U+2)/c)
  filter_upwards [hT,eventually_ge_atTop (2:ℝ)] with T hT hT2
  intro z hz
  obtain ⟨hz',h0,h1,ht⟩ := mem_nontrivialZerosUpTo.mp hz
  have hTp : 0<T := by linarith
  by_cases hu : U≤|z.im|
  · have hu' : 2≤|z.im| := hU.trans hu
    have hg := H z hz' h0 h1 (hU₀.trans hu)
    have hh := hV |z.im| (hUV.trans hu)
    have hl := Real.log_nonneg (by linarith : 1≤|z.im|)
    apply hh.trans
    exact mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith)) hl (sub_nonneg.mpr h1.le)
  · have hzU : z∈nontrivialZerosUpTo U := mem_nontrivialZerosUpTo.mpr ⟨hz',h0,h1,(lt_of_not_ge hu).le⟩
    have hsmall := Hc z hzU
    have hbound : r*Real.log (U+2) ≤ Real.log (T+2)*c :=
      (div_le_iff₀ hc).mp (hT.trans (Real.log_le_log hTp (by linarith)))
    have hscale := mul_le_mul_of_nonneg_left hsmall (Real.log_nonneg (by linarith : 1≤T+2))
    apply le_of_mul_le_mul_right (a:=Real.log (U+2)) _ hlU
    nlinarith only [hbound,hscale]

/-- The minimum scaled distance of all zeros up to height `T` tends to
infinity. This formulation accepts zero-free estimates with arbitrary
fixed multiples of `1/log t` directly. -/
def GrowingZetaScaledGap : Prop :=
  ∀ r : ℝ, ∀ᶠ T : ℝ in atTop, ∀ z ∈ nontrivialZerosUpTo T, r≤(1-z.re)*Real.log (T+2)

/-- An arbitrarily large fixed multiple of the classical region, valid above
a height depending on that multiple, gives a growing common scaled gap. -/
theorem growingZetaScaledGap_of_arbitrary_width
    (H : ∀ B : ℝ, 0<B → ∀ᶠ U : ℝ in atTop, ∀ σ t : ℝ, U ≤ |t| →
      1-B/Real.log |t| ≤ σ → riemannZeta ((σ:ℂ)+(t:ℂ)*I)≠0) : GrowingZetaScaledGap := by
  intro r
  obtain ⟨c,hc,Hc⟩ := zeta_scaled_gap_pos
  let B := |r|+1
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨V,hV⟩ := eventually_atTop.mp (H B hB)
  let U := max 2 V
  have hU : 2≤U := le_max_left ..
  have H' := hV U (le_max_right ..)
  have hlU : 0<Real.log (U+2) := Real.log_pos (by linarith)
  have hbound := Real.tendsto_log_atTop.eventually_ge_atTop (r*Real.log (U+2)/c)
  filter_upwards [hbound,eventually_ge_atTop (2:ℝ)] with T hb hT
  intro z hz
  obtain ⟨hz',h0,h1,ht⟩ := mem_nontrivialZerosUpTo.mp hz
  have hTp : 0<T := by linarith
  by_cases hu : U≤|z.im|
  · have hu' := hU.trans hu
    have hl : 0<Real.log |z.im| := Real.log_pos (by linarith)
    have hg : z.re < 1-B/Real.log |z.im| := lt_of_not_ge (fun h => H' z.re z.im hu h (by rwa [Complex.re_add_im]))
    have hh := (div_le_iff₀ hl).mp (show B/Real.log |z.im|≤1-z.re by linarith)
    apply (show r≤B by dsimp [B]; linarith [le_abs_self r]).trans (hh.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (sub_nonneg.mpr h1.le)
  · have hs := Hc z (T:=U) (mem_nontrivialZerosUpTo.mpr ⟨hz',h0,h1,(lt_of_not_ge hu).le⟩)
    have hbd := (div_le_iff₀ hc).mp (hb.trans (Real.log_le_log hTp (by linarith : T≤T+2)))
    have hh := mul_le_mul_of_nonneg_left hs (Real.log_nonneg (by linarith : 1≤T+2))
    apply le_of_mul_le_mul_right (a:=Real.log (U+2)) _ hlU
    nlinarith only [hbd,hh]


end AnalyticNumberTheory.PrimeDistribution
