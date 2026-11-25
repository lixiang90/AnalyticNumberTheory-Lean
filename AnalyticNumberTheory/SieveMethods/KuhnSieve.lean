import AnalyticNumberTheory.SieveMethods.KuhnRemainders
import AnalyticNumberTheory.SieveMethods.LinearSieveBranches

/-!
# Kuhn's weighted sieve in dimension one

A lower sieve at level z^3.98 and upper sieves at levels z^3.98/q give
a positive main term. The error uses the same distribution majorant for
all divisors, including the tagged prime.
-/
noncomputable section
open Finset Set Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The weighted lower bound before exceptional squares are removed. -/
theorem kuhn_weighted_sieve {K B : ℝ} (hK : 0≤K) (hB : 0<B) :
    ∀ᶠ z : ℝ in atTop, ∀ (P : Finset ℕ) (s : SieveData), (∀p∈P,p.Prime) → 0≤s.X →
      (∀p∈P,s.density p≤1-1/B) → SieveLogMassBounds P s.density 2 (z^kuhnPrimeExponent) K K →
      ∀ F : ℕ → ℝ, (∀d∈Finset.Icc 1 ⌊z^kuhnLevel⌋₊,0≤F d) →
        (∀d, d∣sieveProductBelow P (z^kuhnPrimeExponent) → |s.rem d|≤F d) →
        let M := sievePrimeWindow P z (z^kuhnPrimeExponent)
        let D := sieveProductBelow P z
        (kuhnScale/200)*(s.X*sieveEulerBelow P s.density z)-
          (5/2:ℝ)*∑n∈Finset.Icc 1 ⌊z^kuhnLevel⌋₊,F n ≤
          (siftedCountOf s.A D:ℝ)-(1/2:ℝ)*∑q∈M,(siftedCountOf (sieveMultiple s.A q) D:ℝ) := by
  let ε := kuhnScale/1000
  have hε : 0<ε := div_pos kuhnScale_pos (by norm_num)
  filter_upwards [linearSieve_sifted_bounds hK hK hB hε,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1000*K)] with z hh hz hlog
  intro P s hP hX hsep H F hF hrem M D
  let g := s.density
  let V := sieveEulerBelow P g z
  let y := z^kuhnLevel
  let T := z^kuhnPrimeExponent
  let R := fun d : ℕ => F d
  let Rq := fun q : ℕ => ∑d∈D.divisors.filter (fun d : ℕ => (d:ℝ)<y/q),F (q*d)
  let R₀ := ∑d∈D.divisors.filter (fun d : ℕ => (d:ℝ)<y),F d
  let main := s.X*V
  let S := (siftedCountOf s.A D:ℝ)
  let S' := fun q : ℕ => (siftedCountOf (sieveMultiple s.A q) D:ℝ)
  let U := fun q : ℕ => linearSieveUpper (kuhnLevel-log q/log z)+ε
  have hz₁ : 1<z := by linarith
  have hz₀ : 0<z := by linarith
  have hlz := log_pos hz₁
  have hzt : z≤T := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz₁.le (by norm_num [kuhnPrimeExponent] : 1≤kuhnPrimeExponent)
  have hD : D∣sieveProductBelow P T := prod_dvd_prod_of_subset _ _ _
    (fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans_le hzt⟩)
  have hg (p : ℕ) (hp : p∈P) := s.density_nonneg_of_prime (hP p hp)
  have hmain : 0≤main := mul_nonneg hX (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le
  have hdim := H.mono_interval le_rfl hzt
  have h₀ := (hh s P hP hX hsep hdim kuhnLevel (by norm_num [kuhnLevel])).1
  have hbase : ∑d∈D.divisors.filter (fun d : ℕ => (d:ℝ)<y),|s.rem d|≤R₀ := by
    apply sum_le_sum; intro d hd; exact hrem d ((Nat.dvd_of_mem_divisors (mem_filter.mp hd).1).trans hD)
  have hlow : main*(linearSieveLower kuhnLevel-ε)-R₀≤S := by
    change main*(linearSieveLower kuhnLevel-ε)-_≤S at h₀; linarith only [h₀,hbase]
  have hpoint (q : ℕ) (hq : q∈M) : S' q≤main*(g q*U q)+Rq q := by
    obtain ⟨hPq,hzq,hqt⟩ := mem_filter.mp hq
    have hQ := hP q hPq
    have hq₀ : (0:ℝ)<q := by exact_mod_cast hQ.pos
    have htag : q∣sieveProductBelow P T := dvd_prod_of_mem _ (mem_filter.mpr ⟨hPq,hqt⟩)
    have hcop : q.Coprime D := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp; have ⟨hPp,hpz⟩ := mem_filter.mp hp
      apply (Nat.coprime_primes hQ (hP p hPp)).mpr
      exact_mod_cast ne_of_gt (hpz.trans_le hzq)
    let v := log q/log z
    have hv : v≤kuhnPrimeExponent := by
      have ht := log_le_log hq₀ hqt.le; rw [Real.log_rpow hz₀] at ht
      exact (div_le_iff₀ hlz).mpr ht
    have hu : 1≤kuhnLevel-v := by dsimp [kuhnLevel,kuhnPrimeExponent] at *; linarith
    have hexp : z^(kuhnLevel-v)=y/q := by
      rw [Real.rpow_sub hz₀]
      have he : z^v=(q:ℝ) := by rw [Real.rpow_def_of_pos hz₀]; dsimp only [v]; rw [show log z*(log q/log z)=log q by field_simp,Real.exp_log hq₀]
      rw [he]
    have hh' := (hh (s.atMultiple q) P hP (mul_nonneg hX (hg q hPq)) hsep hdim (kuhnLevel-v) hu).2
    rw [hexp] at hh'
    have hr : (∑d∈D.divisors.filter (fun d : ℕ => (d:ℝ)<y/q),|(s.atMultiple q).rem d|)≤Rq q := by
      apply sum_le_sum; intro d hd
      have hd' := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      have hc := hcop.of_dvd_right hd'
      rw [s.atMultiple_rem hc]; exact hrem _ (hc.mul_dvd_of_dvd_of_dvd htag (hd'.trans hD))
    change S' q≤(s.X*g q)*V*U q+_ at hh'
    change S' q≤(s.X*V)*(g q*U q)+Rq q
    linarith only [hh',hr]
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib,←mul_sum] at hsum
  have hweight := kuhn_weight_positive hz hg H (by linarith)
  change kuhnScale/200≤linearSieveLower kuhnLevel-ε-1/2*(∑q∈M,g q*U q) at hweight
  have hdist := kuhn_remainder_sum (N:=D) F hz₁ (y:=y) (by
    change z^kuhnLevel<z^4
    rw [←Real.rpow_natCast z 4]
    exact Real.rpow_lt_rpow_of_exponent_lt hz₁ (by norm_num [kuhnLevel])) (M:=M)
    (fun p hp => ⟨hP p (mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩) (Real.rpow_pos_of_pos hz₀ _).le hF (sieveProductBelow_squarefree hP z).ne_zero
  change R₀+1/2*(∑q∈M,Rq q)≤(5/2:ℝ)*_ at hdist
  change (kuhnScale/200)*main-5/2*∑n∈Finset.Icc 1 ⌊y⌋₊,F n≤S-1/2*∑q∈M,S' q
  linarith only [mul_le_mul_of_nonneg_right hweight hmain,hlow,hsum,hdist]

end AnalyticNumberTheory.SieveMethods
