import AnalyticNumberTheory.SieveMethods.LinearSieveEstimate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The fundamental theorem of the one-dimensional linear sieve

For fixed dimension bounds, at any fixed accuracy all sufficiently large
sifting cutoffs admit the upper and lower linear-sieve functions. The
threshold is uniform in the arithmetic sequence, sifting primes, and
logarithmic level. The arithmetic error is the ordinary sum of absolute
remainders over the strict level z^u.
-/
noncomputable section
open Set Finset Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open Classical

private theorem choose_sieve_cutoffs (K C : ℝ) (hK : 0<K) (hC : 0<C) {ε : ℝ} (hε : 0<ε) :
    ∃ m : ℕ, ∃ r : ℝ, 1≤r ∧ C*(2560*(19/20:ℝ)^m)≤ε/3 ∧
      C*((2*m:ℕ)*(K*r)^2*exp (-(r/2^(2*m))))≤ε/3 := by
  have hpow : Tendsto (fun m : ℕ => C*(2560*(19/20:ℝ)^m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤19/20)
      (by norm_num : (19/20:ℝ)<1)).const_mul 2560).const_mul C
  obtain ⟨m,hm⟩ := (hpow.eventually_le_const (show 0<ε/3 by positivity)).exists
  let t : ℝ := 2^(2*m)
  have ht : 0<t := by dsimp [t]; positivity
  have hr : Tendsto (fun r : ℝ => C*((2*m:ℕ)*(K*r)^2*exp (-(r/t)))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/t) (by positivity)).const_mul (C*(2*m:ℕ)*K^2)
    rw [mul_zero] at hh
    apply hh.congr; intro r; rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast]
    rw [show -(1/t)*r= -(r/t) by ring]; ring
  obtain ⟨r,hr₁,hr₂⟩ := ((eventually_ge_atTop (1:ℝ)).and (hr.eventually_le_const (show 0<ε/3 by positivity))).exists
  exact ⟨m,r,hr₁,hm,hr₂⟩

/-- Fixed-accuracy fundamental theorem for the linear sieve in dimension one.
The implied cutoff may depend on the dimension constants and accuracy.
It is uniform in the level u, admissible prime set, and arithmetic data. -/
theorem linearSieve_fundamental_theorem {L A B : ℝ} (hL : 0≤L) (hA : 0≤A) (hB : 0<B)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      (∀p∈P,s.density p≤1-1/B) → SieveLogMassBounds P s.density 2 z L A →
      ∀ (b : Bool) (u : ℝ), (if b then (1:ℝ) else 2)≤u →
        linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-
          s.X*sieveEulerBelow P s.density z*linearSieveFunction b u)≤
          ε*s.X*sieveEulerBelow P s.density z+
            ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<z^u),|s.rem d| := by
  let k := linearSieveEulerConstant A B
  let K := exp (2*k)
  let D := K*(L+k)
  have hk : 0≤k := by dsimp [k,linearSieveEulerConstant]; positivity
  have hK : 1≤K := one_le_exp (by positivity)
  have hKp : 0<K := exp_pos _
  have hD : 0≤D := mul_nonneg hKp.le (add_nonneg hL hk)
  obtain ⟨C,hC,hf⟩ := linearSieve_two_cutoff hK
  obtain ⟨m,r,hr,hm,hshort⟩ := choose_sieve_cutoffs K C hKp hC hε
  have hrp : 0<r := by linarith
  let Q := K*r
  let J := 6*exp eulerMascheroniConstant*Q^2
  have hJ : 0<J := by dsimp [J,Q]; positivity
  let η := min (1/10000) ((ε/3)/J)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη' : η≤1/10000 := min_le_left ..
  have hηJ : J*η≤ε/3 := by linarith [(le_div_iff₀ hJ).mp (min_le_right (1/10000) ((ε/3)/J))]
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max (r*log 2) (D*r^2/η)),eventually_ge_atTop (2:ℝ)] with z hz hz₂
  intro s P hP hX hsep H b u hu
  let w := exp (log z/r)
  have hz₀ : 0<z := by linarith
  have hlz := log_pos (show 1<z by linarith)
  have hlw : log w=log z/r := log_exp _
  have hw : 2≤w := (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mp
    ((le_div_iff₀ hrp).mpr (by linarith [(le_max_left (r*log 2) (D*r^2/η)).trans hz]))
  have hwz : w≤z := (Real.le_log_iff_exp_le hz₀).mp (div_le_self hlz.le hr)
  have hparam : log z/log w=r := by rw [hlw]; field_simp
  have hu₁ : 1≤u := by cases b <;> simp_all <;> linarith
  have hu₀ : 0<u := by linarith
  let Y := u*log z
  have hY : 0<Y := mul_pos hu₀ hlz
  have huY : Y/log z=u := mul_div_cancel_right₀ _ hlz.ne'
  have hP₁ (p : ℕ) (hp : p∈P) : 1≤p := (hP p hp).one_lt.le
  have hg (p : ℕ) (hp : p∈P) := And.intro (s.density_nonneg_of_prime (hP p hp)) (hsep p hp)
  have hdim : SieveEulerDimensionOne P s.density z K := by
    intro c hc a ha
    exact (sieveEulerBelow_ratio_comparison ha.1 ha.2 hP₁ hB hg hL hA (H.mono_interval ha.1 hc.2)).1
  have happrox : SieveEulerApprox P s.density w z η := by
    intro c hc t ht
    have hh := sieveEulerBelow_uniform_comparison hw hc.1 hP₁ hB hg hL hA (H.mono_interval hw hc.2) t ht
    have hW := (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) c).le
    apply hh.trans
    have hbound : D*log z/(log w)^2≤η := by
      rw [hlw,show D*log z/(log z/r)^2=D*r^2/log z by field_simp <;> ring]
      apply (div_le_iff₀ hlz).mpr
      linarith [(div_le_iff₀ hη).mp ((le_max_right (r*log 2) (D*r^2/η)).trans hz)]
    have hlog := log_le_log (show 0<c by linarith [hc.1]) hc.2
    have hh' := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hD) (sq_nonneg (log w))).trans hbound
    change D*sieveEulerBelow P s.density c*log c/(log w)^2≤_
    convert mul_le_mul_of_nonneg_right hh' hW using 1 <;> ring
  have h := hf s P hP hX hw hwz hY hη.le hη' hdim happrox m b (huY.symm ▸ hu)
  dsimp only at h
  rw [huY,hparam,linearSieveProfile,max_eq_right hu₁] at h
  have he : exp Y=z^u := by rw [Real.rpow_def_of_pos hz₀]; dsimp only [Y]; rw [mul_comm]
  rw [he] at h
  apply h.trans; apply add_le_add_left
  have hcut : exp (-(u*r/2^(2*m)))≤exp (-(r/2^(2*m))) := by
    apply exp_le_exp.mpr; apply neg_le_neg; apply div_le_div_of_nonneg_right _ (by positivity)
    exact le_mul_of_one_le_left hrp.le hu₁
  have hsh := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut
    (mul_nonneg (Nat.cast_nonneg (α:=ℝ) (2*m)) (sq_nonneg (K*r)))) hC.le).trans hshort
  have hcoeff : 6*exp eulerMascheroniConstant*η*(K*r)^2+C*((2*m:ℕ)*(K*r)^2*exp (-(u*r/2^(2*m)))+2560*(19/20:ℝ)^m)≤ε := by
    change 6*exp eulerMascheroniConstant*(K*r)^2*η≤ε/3 at hηJ
    linarith only [hηJ,hm,hsh]
  convert mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hX (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le) using 1 <;> ring


/-- The two conventional inequalities, with both F and f defined for all
u ≥ 1. In the initial lower range 1 ≤ u ≤ 2 the profile vanishes. -/
theorem linearSieve_sifted_bounds {L A B : ℝ} (hL : 0≤L) (hA : 0≤A) (hB : 0<B)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ z : ℝ in atTop, ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      (∀p∈P,s.density p≤1-1/B) → SieveLogMassBounds P s.density 2 z L A →
      ∀ u : ℝ, 1≤u →
        let X := s.X*sieveEulerBelow P s.density z
        let R := ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<z^u),|s.rem d|
        X*(linearSieveLower u-ε)-R≤(siftedCountOf s.A (sieveProductBelow P z):ℝ) ∧
          (siftedCountOf s.A (sieveProductBelow P z):ℝ)≤X*(linearSieveUpper u+ε)+R := by
  filter_upwards [linearSieve_fundamental_theorem hL hA hB hε] with z hz
  intro s P hP hX hsep H u hu X R
  let S : ℝ := siftedCountOf s.A (sieveProductBelow P z)
  let V := sieveEulerBelow P s.density z
  have hXV : 0≤X := mul_nonneg hX (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le
  have hR : 0≤R := sum_nonneg (fun _ _ => abs_nonneg _)
  have hS : 0≤S := Nat.cast_nonneg _
  have hh := hz s P hP hX hsep H true u hu
  change S-s.X*V*linearSieveUpper u≤ε*s.X*V+R at hh
  constructor
  · by_cases h : 2≤u
    · have hl := hz s P hP hX hsep H false u h
      change -(S-s.X*V*linearSieveLower u)≤ε*s.X*V+R at hl
      change s.X*V*(linearSieveLower u-ε)-R≤S
      linarith only [hl]
    · rw [(linearSieve_initial ⟨hu,(not_le.mp h).le⟩).2]
      change X*(0-ε)-R≤S
      nlinarith only [mul_nonneg hXV hε.le,hR,hS]
  · change S≤s.X*V*(linearSieveUpper u+ε)+R
    linarith only [hh]


end AnalyticNumberTheory.SieveMethods
