import AnalyticNumberTheory.PrimeDistribution.HoheiselZeroSums
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalZeroSums
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalPrimeCounts

/-!
# Hoheisel's theorem on intervals of power length

A sufficiently small positive power of the endpoint is used as truncation
height. Log-free density and the classical zero-free region leave a fixed
fraction of the expected von Mangoldt mass. An improving logarithmic
zero-free width makes the relative error tend to zero.
-/

noncomputable section
open Finset Filter Asymptotics
open scoped Classical Topology
namespace AnalyticNumberTheory.PrimeDistribution

private theorem normalized_short_interval_error {α θ : ℝ} (hα : 0<α) (hα' : α≤1)
    (hθ : 0<θ) (hθ' : θ≤1) (hgap : 1<α+θ) :
    ∃ f : ℝ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ x : ℝ in atTop,
    |(Chebyshev.psi (x+x^θ)-Chebyshev.psi x)/x^θ-1| ≤ f x +
      ∑ z ∈ nontrivialZerosUpTo (x^α),(zeroMultiplicity z:ℝ)*x^(z.re-1) := by
  obtain ⟨C,hC,H⟩ := psi_interval_zero_sum_bound
  let f (x : ℝ) := C*((Real.log x)^2/x^(α+θ-1)+Real.log x/x^θ)
  have h1 := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show 0<α+θ-1 by linarith)).tendsto_div_nhds_zero
  have h2 := (isLittleO_log_rpow_rpow_atTop (1:ℝ) hθ).tendsto_div_nhds_zero
  refine ⟨f,?_,?_⟩
  · simpa only [f,Real.rpow_two,Real.rpow_one,add_zero,mul_zero] using (h1.add h2).const_mul C
  have ht := (tendsto_rpow_atTop hα).eventually_ge_atTop (2:ℝ)
  filter_upwards [eventually_ge_atTop (2:ℝ),ht] with x hx hT
  have hx0 : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 θ
  have htx := Real.rpow_le_rpow_of_exponent_le hx1 hα'
  have hhx := Real.rpow_le_rpow_of_exponent_le hx1 hθ'
  rw [Real.rpow_one] at htx hhx
  have hf := H hx hh.le hhx hT htx
  let Z := ∑ z ∈ nontrivialZerosUpTo (x^α),(zeroMultiplicity z:ℝ)*x^(z.re-1)
  have hxe : x^(α+θ-1)=x^α*x^θ/x := by rw [Real.rpow_sub hx0,Real.rpow_add hx0,Real.rpow_one]
  have hdiv (y : ℝ) : y/x^θ-1=(y-x^θ)/x^θ := by field_simp
  rw [hdiv,abs_div,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  apply hf.trans_eq
  change C*(x*(Real.log x)^2/x^α+Real.log x)+x^θ*Z=(f x+Z)*x^θ
  dsimp only [f]; rw [hxe]
  field_simp [hx0.ne',hh.ne',(Real.rpow_pos_of_pos hx0 α).ne']

private lemma truncation_scale {D α x : ℝ} (hD : 0≤D) (hx : 1≤x)
    (hT : 2≤x^α) (hDα : 2*D*α≤1) : D*Real.log (x^α+2) ≤ Real.log x := by
  have hx0 : 0<x := by linarith
  have hT0 := Real.rpow_pos_of_pos hx0 α
  have hsq : x^α+2 ≤ (x^α)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0≤x^α+1 by positivity)]
  have hL := Real.log_le_log (by positivity : 0<x^α+2) hsq
  rw [Real.log_pow,Real.log_rpow hx0] at hL
  norm_num only [Nat.cast_ofNat] at hL
  calc
    _ ≤ D*(2*(α*Real.log x)) := mul_le_mul_of_nonneg_left hL hD
    _ = (2*D*α)*Real.log x := by ring
    _ ≤ _ := mul_le_of_le_one_left (Real.log_nonneg hx) hDα

/-- There is a fixed `θ₀<1` such that every `θ₀≤θ<1` gives an unconditional
lower bound for the von Mangoldt mass in `(x,x+x^θ]`. A zero-free width
satisfying `δ(t) log t → ∞` gives the asymptotic for the same exponents. -/
theorem hoheisel_power_intervals :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
    (∀ᶠ x : ℝ in atTop, x^θ/2 ≤ Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ∧
    (GrowingZetaScaledGap →
      (fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ~[atTop] (fun x : ℝ => x^θ)) := by
  obtain ⟨A,hA,K,hK,H⟩ := zeta_zero_sum_of_scaled_gap
  obtain ⟨c,hc,HG⟩ := zeta_scaled_gap_pos
  let b := (|Real.log (4*K)|+1)/c
  have hb : 0<b := by dsimp [b]; positivity
  let D := A+1+b
  have hD : 1≤D := by dsimp only [D]; linarith
  have hDp : 0<D := by linarith
  let α := 1/(4*D)
  have hα : 0<α := by dsimp [α]; positivity
  have hα' : α≤1/4 := by dsimp [α]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hDα : 2*D*α≤1 := by dsimp only [α]; field_simp; linarith
  let θ₀ := 1-α/2
  have hθ₀ : θ₀∈Set.Ioo (1/2:ℝ) 1 := ⟨by dsimp [θ₀]; linarith,by dsimp [θ₀]; linarith⟩
  refine ⟨θ₀,hθ₀,?_⟩
  intro θ hθ
  have hθp : 0<θ := by linarith [hθ.1,hθ₀.1]
  have hgap : 1<α+θ := by have hh := hθ.1; dsimp only [θ₀] at hh; linarith
  obtain ⟨f,hf,HE⟩ := normalized_short_interval_error hα (by linarith) hθp hθ.2.le hgap
  have hT := tendsto_rpow_atTop hα
  have hT2 := hT.eventually_ge_atTop (2:ℝ)
  have hden : ∀ᶠ x : ℝ in atTop, x^θ≠0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact (Real.rpow_pos_of_pos hx _).ne'
  constructor
  · have he : K*Real.exp (-b*c)≤1/4 := by
      have hbc : b*c=|Real.log (4*K)|+1 := by dsimp [b]; field_simp
      calc
        _ ≤ K*Real.exp (-Real.log (4*K)) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          rw [neg_mul, hbc]; linarith [le_abs_self (Real.log (4*K))]
        _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)]; field_simp
    filter_upwards [HE,hf.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),hT2,eventually_ge_atTop (2:ℝ)] with x he' hfx ht hx
    have hx0 : 0<x := by linarith
    have hsum := H (T:=x^α) (by linarith) hx0 hb.le (truncation_scale hDp.le (by linarith) ht hDα) (HG (T:=x^α))
    have herr := (abs_le.mp he').1
    have hlo : 1/2 ≤ (Chebyshev.psi (x+x^θ)-Chebyshev.psi x)/x^θ := by linarith
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hx0 θ)).mp hlo
    linarith only [hh]
  · intro hz
    rw [isEquivalent_iff_tendsto_one hden,Metric.tendsto_nhds]
    intro ε hε
    let r := (|Real.log (2*K/ε)|+1)/b
    have hbr : b*r=|Real.log (2*K/ε)|+1 := by dsimp only [r]; field_simp
    have he : K*Real.exp (-b*r)≤ε/2 := by
      calc
        _ ≤ K*Real.exp (-Real.log (2*K/ε)) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          rw [neg_mul,hbr]; linarith [le_abs_self (Real.log (2*K/ε))]
        _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)]; field_simp
    have hrg := hT.eventually (hz r)
    filter_upwards [HE,hf.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2)),hT2,hrg,eventually_ge_atTop (2:ℝ)] with x herr hfx ht hr hx
    have hx0 : 0<x := by linarith
    have hsum := H (T:=x^α) (by linarith) hx0 hb.le (truncation_scale hDp.le (by linarith) ht hDα) hr
    rw [Real.dist_eq]
    change |(Chebyshev.psi (x+x^θ)-Chebyshev.psi x)/x^θ-1| < ε
    linarith only [herr,hsum,he,hfx]

/-- **Hoheisel's theorem.** For every exponent sufficiently close to one,
every sufficiently large interval `(x,x+x^θ]` contains a prime and in fact
contains at least `x^θ/(8 log x)` primes. -/
theorem hoheisel_primes_in_power_intervals :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      ∀ᶠ x : ℝ in atTop,
        x^θ/(8*Real.log x) ≤ primePi (x+x^θ)-primePi x ∧
          ∃ p : ℕ, p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤x+x^θ := by
  obtain ⟨θ₀,hθ₀,H⟩ := hoheisel_power_intervals
  refine ⟨θ₀,hθ₀,?_⟩
  intro θ hθ
  have hp := (H θ hθ).1
  have hθ' := hθ₀.1.trans_le hθ.1
  have hψ : ∀ᶠ x : ℝ in atTop, (1/2)*x^θ≤Chebyshev.psi (x+x^θ)-Chebyshev.psi x := by
    filter_upwards [hp] with x hx
    linarith only [hx]
  have hπ := eventually_primePi_interval_lower_of_psi hθ' hθ.2.le (by norm_num : (0:ℝ)<1/2) hψ
  have he := eventually_exists_prime_interval_of_psi_lower hθ' hθ.2.le (by norm_num : (0:ℝ)<1/2) hψ
  filter_upwards [hπ,he] with x hx hp'
  exact ⟨(show x^θ/(8*Real.log x)=(1/2/4)*x^θ/Real.log x by ring).trans_le hx,hp'⟩

/-- A common scaled gap tending to infinity gives the prime-counting
asymptotic on all power intervals of sufficiently large fixed exponent. -/
theorem hoheisel_prime_asymptotic_of_growing_gap (hz : GrowingZetaScaledGap) :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] (fun x : ℝ => x^θ/Real.log x) := by
  obtain ⟨θ₀,hθ₀,H⟩ := hoheisel_power_intervals
  exact ⟨θ₀,hθ₀,fun θ hθ => primePi_shortInterval_of_theta_equivalent hθ.2.le
    (theta_shortInterval_of_psi_equivalent (hθ₀.1.trans_le hθ.1) hθ.2.le ((H θ hθ).2 hz))⟩

/-- A pointwise zero-free width satisfying `δ(t) log t → ∞` suffices for the
short-interval prime number theorem, even without monotonicity of the width. -/
theorem hoheisel_prime_asymptotic_of_improving_width (hz : ImprovingLogZeroFreeHypothesis) :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      (fun x : ℝ => primePi (x+x^θ)-primePi x) ~[atTop] (fun x : ℝ => x^θ/Real.log x) :=
  hoheisel_prime_asymptotic_of_growing_gap (eventually_zeta_scaled_gap hz)


end AnalyticNumberTheory.PrimeDistribution
