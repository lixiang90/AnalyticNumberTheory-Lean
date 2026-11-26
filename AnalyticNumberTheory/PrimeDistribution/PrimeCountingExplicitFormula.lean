import AnalyticNumberTheory.PrimeDistribution.RiemannCountingSharp

/-!
# Sharp explicit formulas at a single cutoff for prime powers and primes

Normalize the logarithmic integrals at any fixed point between one and two. Here the
prime-power count is zero. Finite Möbius inversion of the height truncations gives
the prime count with the same midpoint convention.
-/

noncomputable section

open Filter Finset
open scoped Topology Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.PrimeDistribution

/-- The pole, nontrivial-zero logarithmic integral sum and trivial-zero integral,
all measured from the same reference point. -/
def riemannExplicitIncrement (a b T : ℝ) : ℂ :=
  zeroLogIntegral 1 a b - sharpZeroLogIntegral a b T - (trivialZeroLogIntegral a b : ℂ)

/-- Reversing the endpoints reverses all three contributions at each finite height. -/
theorem riemannExplicitIncrement_swap (a b T : ℝ) :
    riemannExplicitIncrement a b T = -riemannExplicitIncrement b a T := by
  have hk (z : ℂ) : zeroLogIntegral z a b = -zeroLogIntegral z b a := intervalIntegral.integral_symm b a
  have hz : sharpZeroLogIntegral a b T = -sharpZeroLogIntegral b a T := by
    unfold sharpZeroLogIntegral
    simp_rw [hk, mul_neg, sum_neg_distrib]
  have ht : trivialZeroLogIntegral a b = -trivialZeroLogIntegral b a := intervalIntegral.integral_symm b a
  rw [riemannExplicitIncrement,riemannExplicitIncrement,hk,hz,ht,Complex.ofReal_neg]
  ring

/-- The interval explicit formula with either ordering of endpoints, both above one. -/
theorem tendsto_riemannExplicitIncrement {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Tendsto (riemannExplicitIncrement a b) atTop
      (𝓝 ((riemannPrimeCounting (1/2) b - riemannPrimeCounting (1/2) a : ℝ) : ℂ)) := by
  rcases le_total a b with hab | hba
  · exact tendsto_riemannPrimeCounting_interval_explicit_formula ha hab
  have H := (tendsto_riemannPrimeCounting_interval_explicit_formula hb hba).neg
  change Tendsto (fun T => -riemannExplicitIncrement b a T) atTop (𝓝 (-((riemannPrimeCounting (1/2) a - riemannPrimeCounting (1/2) b : ℝ) : ℂ))) at H
  rw [←Complex.ofReal_neg,neg_sub] at H
  exact H.congr fun T => (riemannExplicitIncrement_swap a b T).symm

/-- There are no prime powers in the interval from one to any real cutoff below two. -/
theorem riemannPrimeCounting_eq_zero_of_one_le_lt_two (c : ℝ) {a : ℝ} (ha : 1 ≤ a) (ha' : a < 2) :
    riemannPrimeCounting c a = 0 := by
  have hf : ⌊a⌋₊ = 1 := (Nat.floor_eq_iff (zero_le_one.trans ha)).mpr (by norm_num; exact ⟨ha,ha'⟩)
  simp [riemannPrimeCounting,hf]

/-- For every x > 1, normalizing all logarithmic integrals at any a in (1,2)
gives a sharp height-ordered formula for Riemann's midpoint count at x. -/
theorem tendsto_riemannExplicitIncrement_midpoint {a x : ℝ} (ha : 1 < a) (ha' : a < 2) (hx : 1 < x) :
    Tendsto (riemannExplicitIncrement a x) atTop (𝓝 (riemannPrimeCounting (1/2) x : ℂ)) := by
  simpa only [riemannPrimeCounting_eq_zero_of_one_le_lt_two _ ha.le ha',sub_zero] using tendsto_riemannExplicitIncrement ha hx

/-- A single symmetric height for all positive roots suffices in the finite Möbius
inversion formula for the midpoint prime count. The exponent cutoff can be enlarged. -/
theorem tendsto_primePi_midpoint_explicit_formula {a x : ℝ} (ha : 1 < a) (ha' : a < 2)
    (hx : 1 < x) {N : ℕ} (hN : 1 ≤ N) (hcut : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    Tendsto (fun T => ∑ d ∈ Icc 1 N, (((μ d : ℝ) / d : ℝ) : ℂ) *
      riemannExplicitIncrement a (x^((1 : ℝ)/d)) T) atTop (𝓝 (primePiWithEndpoint (1/2) x : ℂ)) := by
  rw [primePiWithEndpoint_eq_sum_moebius_riemannPrimeCounting _ (zero_lt_one.trans hx) hN hcut,
    Complex.ofReal_sum]
  apply tendsto_finsetSum
  intro d hd
  have hd₀ : 0 < (d : ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
  rw [Complex.ofReal_mul]
  exact (tendsto_riemannExplicitIncrement_midpoint ha ha'
    (Real.one_lt_rpow hx (one_div_pos.mpr hd₀))).const_mul _

/-- Away from prime endpoints, the midpoint prime count agrees with the ordinary count,
including at higher powers of a prime. -/
theorem primePiWithEndpoint_eq_primePi_of_ne_prime {x : ℝ} (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≠ x) (c : ℝ) :
    primePiWithEndpoint c x = primePi x := by
  rw [← primePiWithEndpoint_one x, primePiWithEndpoint,primePiWithEndpoint]
  exact sum_congr rfl fun p hp => by simp [endpointWeight,h p (Nat.prime_of_mem_primesLE hp)]

/-- The ordinary inclusive count differs from the half-weight count by one half
exactly when the cutoff is itself a prime. -/
theorem primePi_eq_midpoint_add_endpoint (x : ℝ) :
    primePi x = primePiWithEndpoint (1/2) x + (if ∃ p : ℕ, p.Prime ∧ (p : ℝ) = x then 1/2 else 0) := by
  split_ifs with h
  · obtain ⟨p,hp,rfl⟩ := h
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    rw [← primePiWithEndpoint_one, primePiWithEndpoint_succ, primePiWithEndpoint_succ]
    simp [hp]
    ring
  · rw [primePiWithEndpoint_eq_primePi_of_ne_prime (fun p hp he => h ⟨p,hp,he⟩),add_zero]

/-- Inclusive prime counting at every real cutoff above one, with the endpoint
correction outside the finite Möbius transform. -/
theorem tendsto_primePi_explicit_formula {a x : ℝ} (ha : 1 < a) (ha' : a < 2) (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N) (hcut : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    Tendsto (fun T => (∑ d ∈ Icc 1 N, (((μ d : ℝ) / d : ℝ) : ℂ) *
      riemannExplicitIncrement a (x^((1 : ℝ)/d)) T) +
        ((if ∃ p : ℕ, p.Prime ∧ (p : ℝ) = x then 1/2 else 0 : ℝ) : ℂ))
      atTop (𝓝 (primePi x : ℂ)) := by
  rw [primePi_eq_midpoint_add_endpoint, Complex.ofReal_add]
  exact (tendsto_primePi_midpoint_explicit_formula ha ha' hx hN hcut).add_const _

end AnalyticNumberTheory.PrimeDistribution
