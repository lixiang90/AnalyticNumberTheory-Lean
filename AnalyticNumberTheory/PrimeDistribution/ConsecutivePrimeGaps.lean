import AnalyticNumberTheory.PrimeDistribution.Hoheisel
import Mathlib.NumberTheory.PrimeCounting

/-!
# Gaps between consecutive primes and primes between powers

An upper bound on the distance to a prime from any large real number
bounds every consecutive prime gap. Substitution at perfect powers also
gives primes strictly between successive powers.
-/
noncomputable section
open Filter Asymptotics Real
open scoped Topology
namespace AnalyticNumberTheory.PrimeDistribution

/-- The gap from the prime of index n to the next prime, with indexing starting at two. -/
def consecutivePrimeGap (n : ℕ) : ℝ :=
  (Nat.nth Nat.Prime (n+1):ℝ)-(Nat.nth Nat.Prime n:ℝ)

theorem consecutivePrimeGap_pos (n : ℕ) : 0<consecutivePrimeGap n := by
  apply sub_pos.mpr; exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime n.lt_succ_self

theorem tendsto_nth_prime_real : Tendsto (fun n => (Nat.nth Nat.Prime n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- An interval result with an arbitrary length function gives a bound of
the same size for the gap from the nth prime to the next one. -/
theorem consecutivePrimeGap_le_of_interval {h : ℝ → ℝ}
    (hp : ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤x+h x) :
    ∀ᶠ n : ℕ in atTop, consecutivePrimeGap n≤h (Nat.nth Nat.Prime n) := by
  filter_upwards [tendsto_nth_prime_real.eventually hp] with n hn
  obtain ⟨p,hp',hlt,hup⟩ := hn
  have hnxt := (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hp').mpr (by exact_mod_cast hlt)
  have hnr : (Nat.nth Nat.Prime (n+1):ℝ)≤p := by exact_mod_cast hnxt
  dsimp [consecutivePrimeGap]; linarith

/-- Hoheisel's theorem bounds individual prime gaps at every admissible power. -/
theorem hoheisel_prime_gap :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ico θ₀ 1,
      consecutivePrimeGap =O[atTop] (fun n => (Nat.nth Nat.Prime n:ℝ)^θ) := by
  obtain ⟨θ₀,hθ₀,H⟩ := hoheisel_primes_in_power_intervals
  refine ⟨θ₀,hθ₀,fun θ hθ => IsBigO.of_bound 1 ?_⟩
  have h := consecutivePrimeGap_le_of_interval ((H θ hθ).mono fun _ hx => hx.2)
  filter_upwards [h] with n hn
  rwa [one_mul,Real.norm_of_nonneg (consecutivePrimeGap_pos n).le,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- For any power strictly above the absolute threshold the gap is
little-o of that power of the smaller prime. -/
theorem hoheisel_prime_gap_littleO :
    ∃ θ₀ ∈ Set.Ioo (1/2:ℝ) 1, ∀ θ ∈ Set.Ioo θ₀ 1,
      consecutivePrimeGap =o[atTop] (fun n => (Nat.nth Nat.Prime n:ℝ)^θ) := by
  obtain ⟨θ₀,hθ₀,H⟩ := hoheisel_prime_gap
  refine ⟨θ₀,hθ₀,fun θ hθ => ?_⟩
  let α := (θ₀+θ)/2
  have hα : θ₀≤α ∧ α<θ := by dsimp [α]; constructor <;> linarith [hθ.1]
  apply (H α ⟨hα.1,hα.2.trans hθ.2⟩).trans_isLittleO
  have he : (fun x : ℝ => x^α) =o[atTop] (fun x => x^θ) := by
    apply (isLittleO_iff_tendsto' (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      exact fun hz => absurd hz (Real.rpow_pos_of_pos hx θ).ne')).mpr
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hα.2)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [←Real.rpow_sub hx]; congr 1; ring
  exact he.comp_tendsto tendsto_nth_prime_real

/-- If kθ ≤ k−1 and k≥2, an interval of length x^θ starting at n^k ends
strictly before the next kth power for every sufficiently large n. -/
theorem primes_between_powers_of_interval {θ : ℝ} {k : ℕ} (hk : 2≤k)
    (hkθ : (k:ℝ)*θ≤k-1)
    (hp : ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤x+x^θ) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n^k<p ∧ p<(n+1)^k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hj : 0<j := by omega
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(j+1)) atTop atTop := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      (tendsto_rpow_atTop (by positivity : (0:ℝ)<(j+1:ℕ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually hp,eventually_ge_atTop 1] with n hn hn1
  obtain ⟨p,hp',hlt,hup⟩ := hn
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn1
  have hnp : (0:ℝ)<n := by linarith
  refine ⟨p,hp',by exact_mod_cast hlt,?_⟩
  have hpow : ((n:ℝ)^(j+1))^θ≤(n:ℝ)^j := by
    rw [←Real.rpow_natCast_mul hnp.le,←Real.rpow_natCast (x:=(n:ℝ)) (n:=j)]
    apply Real.rpow_le_rpow_of_exponent_le hnr
    push_cast at hkθ ⊢; linarith
  have hstep : (n:ℝ)^(j+1)+(n:ℝ)^j<((n:ℝ)+1)^(j+1) := by
    rw [pow_succ,pow_succ]
    calc (n:ℝ)^j*n+(n:ℝ)^j = (n:ℝ)^j*(n+1) := by ring
         _ < _ := by gcongr <;> linarith
  exact_mod_cast hup.trans_lt ((add_le_add le_rfl hpow).trans_lt hstep)

/-- Some fixed integral power, and every larger fixed power, has a prime
strictly between successive values for all sufficiently large arguments. -/
theorem hoheisel_primes_between_powers :
    ∃ k₀ : ℕ, 2≤k₀ ∧ ∀ k≥k₀, ∀ᶠ n : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ n^k<p ∧ p<(n+1)^k := by
  obtain ⟨θ,hθ,H⟩ := hoheisel_primes_in_power_intervals
  obtain ⟨m,hm⟩ := exists_nat_gt ((1-θ)⁻¹)
  refine ⟨max m 2,le_max_right ..,fun k hk => ?_⟩
  have hk' : (m:ℝ)≤k := by exact_mod_cast (le_max_left m 2).trans hk
  have hscale : 1≤(k:ℝ)*(1-θ) := by
    apply (div_le_iff₀ (show 0<1-θ by linarith [hθ.2])).mp
    rw [one_div]; exact hm.le.trans hk'
  apply primes_between_powers_of_interval (θ:=θ) ((le_max_right m 2).trans hk) (by linarith only [hscale])
  exact (H θ ⟨le_rfl,hθ.2⟩).mono fun _ hx => hx.2

end AnalyticNumberTheory.PrimeDistribution
