import AnalyticNumberTheory.SieveMethods.SelbergMeanCoefficients
import AnalyticNumberTheory.DirichletSeries.EulerLogMoment
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler products and moments of the Selberg coefficients

The two local masses are 1 and 1+p⁻². At mass one the logarithmic
derivative is an absolutely convergent sum indexed by primes.
-/

open Filter Real Finset
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- The normalized Möbius transform of the Selberg weight. -/
noncomputable def selbergNormalizedCoefficient (c : ℝ) (n : ℕ) := selbergMeanCoefficient c n/(n:ℝ)

private theorem normalized_one (c : ℝ) : selbergNormalizedCoefficient c 1=1 := by
  simp [selbergNormalizedCoefficient,(selbergMeanCoefficient_multiplicative c).1]

private theorem normalized_mul (c : ℝ) {m n : ℕ} (hm : m.Coprime n) :
    selbergNormalizedCoefficient c (m*n)=selbergNormalizedCoefficient c m*selbergNormalizedCoefficient c n := by
  rw [selbergNormalizedCoefficient, (selbergMeanCoefficient_multiplicative c).2 hm,Nat.cast_mul]
  simp [selbergNormalizedCoefficient,div_eq_mul_inv]; ring

/-- The local Euler factor at one is exactly 1+c/p². -/
theorem selbergNormalizedCoefficient_local_mass (c : ℝ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => selbergNormalizedCoefficient c (p^j)) (1+c/(p:ℝ)^2) := by
  obtain ⟨ha,hb,hd⟩ := selbergMeanCoefficient_local c hp
  have ht (j : ℕ) (hj : j∉range 3) : selbergNormalizedCoefficient c (p^j)=0 := by
    simp [selbergNormalizedCoefficient,hd j (by simpa using hj)]
  have hx := hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) ht
  convert hx using 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,normalized_one]
  rw [selbergNormalizedCoefficient,ha,selbergNormalizedCoefficient,hb,Nat.cast_pow]
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  field_simp; ring

/-- Exact contribution of one prime to the logarithmic moment of the denominator weight. -/
theorem selbergNormalizedCoefficient_local_log {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => selbergNormalizedCoefficient 0 (p^j)*log (p^j:ℕ)) (-log p/((p:ℝ)*(p-1))) := by
  obtain ⟨ha,hb,hd⟩ := selbergMeanCoefficient_local 0 hp
  have ht (j : ℕ) (hj : j∉range 3) : selbergNormalizedCoefficient 0 (p^j)*log (p^j:ℕ)=0 := by
    simp [selbergNormalizedCoefficient,hd j (by simpa using hj)]
  convert hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) ht using 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,normalized_one,
    Nat.cast_one,Real.log_one,mul_zero,zero_add]
  rw [selbergNormalizedCoefficient,ha,selbergNormalizedCoefficient,hb,Nat.cast_pow,Real.log_pow]
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  field_simp; ring

private theorem coefficient_euler_product {c : ℝ} (hc : 0≤c) (hc' : c≤1) :
    HasProd (fun p : Nat.Primes => 1+c/(p.val:ℝ)^2) (∑' n : ℕ,selbergNormalizedCoefficient c n) := by
  have h := EulerProduct.eulerProduct_hasProd (normalized_one c) (fun {_ _} h => normalized_mul c h)
    (by simpa only [Real.norm_eq_abs,selbergNormalizedCoefficient] using (selbergMeanCoefficient_moments hc hc').1)
    (by simp [selbergNormalizedCoefficient])
  simp_rw [show ∀ p : Nat.Primes, (∑' j : ℕ,selbergNormalizedCoefficient c (p.val^j))=1+c/(p.val:ℝ)^2 from fun p => (selbergNormalizedCoefficient_local_mass c p.prop).tsum_eq] at h
  exact h

/-- The normalized denominator coefficients have total mass one. -/
theorem tsum_selbergNormalizedCoefficient_zero : (∑' n : ℕ,selbergNormalizedCoefficient 0 n)=1 := by
  have h := coefficient_euler_product (c:=0) (le_refl 0) (by norm_num)
  simpa using h.tprod_eq.symm

/-- The first logarithmic moment is a convergent sum of local contributions. -/
theorem hasSum_selbergNormalizedCoefficient_log :
    HasSum (fun p : Nat.Primes => -log p.val/((p.val:ℝ)*(p.val-1)))
      (∑' n : ℕ,selbergNormalizedCoefficient 0 n*log n) := by
  have H := selbergMeanCoefficient_moments (c:=0) (le_refl _) (by norm_num)
  apply DirichletSeries.hasSum_euler_log_moment (by simp [selbergNormalizedCoefficient]) (normalized_one 0)
    (fun {_ _} h => normalized_mul 0 h) H.1 H.2
  intro p
  exact ⟨by simpa using selbergNormalizedCoefficient_local_mass 0 p.prop,selbergNormalizedCoefficient_local_log p.prop⟩

private theorem zeta_hasProd_pow (k : ℕ) (hk : 0<k) {Z : ℝ}
    (h : HasSum (fun n : ℕ => 1/(n:ℝ)^k) Z) :
    HasProd (fun p : Nat.Primes => (1-1/(p.val:ℝ)^k)⁻¹) Z := by
  let f : ℕ →*₀ ℝ := {
    toFun := fun n => 1/(n:ℝ)^k
    map_one' := by simp
    map_zero' := by simp [Nat.ne_of_gt hk]
    map_mul' := by intro m n; simp [mul_pow,one_div,mul_comm] }
  have hf (n : ℕ) : ‖f n‖=1/(n:ℝ)^k := Real.norm_of_nonneg (by change 0≤1/(n:ℝ)^k; positivity)
  have hs : Summable (fun n => ‖f n‖) := by simpa only [hf] using h.summable
  have H := EulerProduct.eulerProduct_completely_multiplicative_hasProd hs
  change HasProd (fun p : Nat.Primes => (1-1/(p.val:ℝ)^k)⁻¹) (∑' n : ℕ,1/(n:ℝ)^k) at H
  simpa only [h.tsum_eq] using H

/-- The normalized mass of the absolute-weight coefficients equals ζ(2)/ζ(4). -/
theorem tsum_selbergNormalizedCoefficient_one : (∑' n : ℕ,selbergNormalizedCoefficient 1 n)=15/π^2 := by
  have h := (zeta_hasProd_pow 2 (by norm_num) hasSum_zeta_two).div₀
    (zeta_hasProd_pow 4 (by norm_num) hasSum_zeta_four) (by positivity)
  have hp (p : Nat.Primes) : (1-1/(p.val:ℝ)^2)⁻¹/(1-1/(p.val:ℝ)^4)⁻¹=1+1/(p.val:ℝ)^2 := by
    have ha : (1:ℝ)<p.val := by exact_mod_cast p.prop.one_lt
    have hne : 1-1/(p.val:ℝ)^2≠0 := by
      have hh : 1<(p.val:ℝ)^2 := by nlinarith
      have := (div_lt_one (by positivity : 0<(p.val:ℝ)^2)).mpr hh
      linarith
    have he : 1-1/(p.val:ℝ)^4=(1-1/(p.val:ℝ)^2)*(1+1/(p.val:ℝ)^2) := by field_simp; ring
    rw [div_inv_eq_mul,he,←mul_assoc,inv_mul_cancel₀ hne,one_mul]
  simp_rw [hp] at h
  have he := (coefficient_euler_product (c:=1) (by norm_num) (le_refl _)).unique h
  rw [he]; field_simp; ring

end AnalyticNumberTheory.SieveMethods
