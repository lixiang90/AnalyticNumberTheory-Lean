import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Choice of the prime and scaling in the Vinogradov iteration

Bertrand's postulate supplies a prime comparable to the degree-th root of
the interval length. The same choice works at small lengths, with an
explicit factor depending only on the degree.
-/

open Real
namespace AnalyticNumberTheory.ExponentialSums

/-- A prime for which `m=1` in the mixed-modulus box estimate and a
shortened interval of size at most twice the expected power of `N`. -/
theorem vinogradov_prime_scale {k N : ℕ} (hk : 2≤k) (hN : 1≤N) :
    ∃ p : ℕ, p.Prime ∧ k<p ∧ N≤p^k ∧
      (p:ℝ)≤4*(k+1:ℝ)*(N:ℝ)^((k:ℝ)⁻¹) ∧
      ((N/p+1:ℕ):ℝ)≤2*(N:ℝ)^(1-(k:ℝ)⁻¹) := by
  let x := (N:ℝ)^((k:ℝ)⁻¹)
  let L := max k ⌈x⌉₊
  have hk0 : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : 0<(N:ℝ) := by linarith
  have hx : 1≤x := Real.one_le_rpow hn1 (inv_nonneg.mpr hk0.le)
  have hx0 : 0<x := by linarith
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul L (by
    have := le_max_left k ⌈x⌉₊; dsimp [L]; omega)
  have hkp : k<p := (le_max_left ..).trans_lt hlo
  have hxp : x≤(p:ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast (le_max_right k ⌈x⌉₊).trans hlo.le)
  have hxk : x^k=(N:ℝ) := Real.rpow_inv_natCast_pow hn0.le (by omega)
  have hNp : N≤p^k := by
    exact_mod_cast (hxk ▸ pow_le_pow_left₀ hx0.le hxp k : (N:ℝ)≤(p:ℝ)^k)
  refine ⟨p,hp,hkp,hNp,?_,?_⟩
  · change (p:ℝ)≤4*((k:ℝ)+1)*x
    have hpc : (p:ℝ)≤2*(L:ℝ) := by exact_mod_cast hhi
    apply hpc.trans
    rw [show (L:ℝ)=max (k:ℝ) (⌈x⌉₊:ℝ) by simp [L]]
    have hceil := (Nat.ceil_lt_add_one (by linarith : 0≤x)).le
    have hkx : (k:ℝ)≤(k:ℝ)*x := le_mul_of_one_le_right hk0.le hx
    rcases le_total (k:ℝ) (⌈x⌉₊:ℝ) with h|h
    · rw [max_eq_right h]; nlinarith only [hceil,hx,hkx,hk0.le]
    · rw [max_eq_left h]; nlinarith only [hx,hkx,hk0.le]
  · have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
    have he : (N:ℝ)/x=(N:ℝ)^(1-(k:ℝ)⁻¹) := by
      dsimp only [x]; rw [Real.rpow_sub hn0,Real.rpow_one]
    have hq : ((N/p:ℕ):ℝ)≤(N:ℝ)/p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    have hqr := hq.trans (div_le_div_of_nonneg_left hn0.le hx0 hxp)
    rw [he] at hqr
    have hk1 : 1≤(k:ℝ) := by exact_mod_cast (by omega : 1≤k)
    have hx1 := Real.one_le_rpow hn1 (sub_nonneg.mpr (inv_le_one_of_one_le₀ hk1))
    push_cast
    linarith

/-- A product of prime and shortened-length powers has the expected
height exponent. The constants are retained for subsequent iteration. -/
theorem vinogradov_scaled_product {N P Q A a b u v : ℝ} (hN : 0<N) (hA : 0<A)
    (hP : 0≤P) (hQ : 0≤Q) (hu : 0≤u) (hv : 0≤v)
    (hp : P≤A*N^a) (hq : Q≤A*N^b) :
    P^u*Q^v ≤ A^(u+v)*N^(a*u+b*v) := by
  apply (mul_le_mul (Real.rpow_le_rpow hP hp hu) (Real.rpow_le_rpow hQ hq hv)
    (Real.rpow_nonneg hQ _) (Real.rpow_nonneg (by positivity) _)).trans_eq
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _),Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _),
    ←Real.rpow_mul hN.le,←Real.rpow_mul hN.le,Real.rpow_add hA,Real.rpow_add hN]
  ring

/-- Compare a single monomial in the prime conditioning estimate to its
target constant and target power of the original interval length. -/
theorem vinogradov_scaled_monomial {N P Q A a C u v g r J E : ℝ}
    (hN : 1≤N) (hA : 1≤A) (hP : 0≤P) (hQ : 0≤Q)
    (hu : 0≤u) (hv : 0≤v) (hp : P≤A*N^a) (hq : Q≤A*N^(1-a))
    (hc : C≤A^r) (hJ : r+u+v≤J) (hE : g+a*u+(1-a)*v≤E) :
    C*(P^u*Q^v)*N^g ≤ A^J*N^E := by
  have hN0 : 0<N := by linarith
  have hA0 : 0<A := by linarith
  have hprod := vinogradov_scaled_product hN0 hA0 hP hQ hu hv hp hq
  calc C*(P^u*Q^v)*N^g ≤ A^r*(A^(u+v)*N^(a*u+(1-a)*v))*N^g := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
            exact mul_le_mul hc hprod (by positivity) (by positivity)
       _ = A^(r+u+v)*N^(g+a*u+(1-a)*v) := by
            rw [Real.rpow_add hA0 (r+u) v,Real.rpow_add hA0 r u,Real.rpow_add hA0 u v,
              Real.rpow_add hN0 (g+a*u) ((1-a)*v),Real.rpow_add hN0 g (a*u),Real.rpow_add hN0 (a*u) ((1-a)*v)]
            ring
       _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hA hJ)
            (Real.rpow_le_rpow_of_exponent_le hN hE) (by positivity) (by positivity)

end AnalyticNumberTheory.ExponentialSums
