import AnalyticNumberTheory.ExponentialSums.VinogradovIteration

/-!
# Vinogradov mean values with variable degree

When the number of conditioning steps is a fixed multiple of the degree,
the exponent defect is exponentially small in that multiple. All remaining
constant losses are bounded by an exponential of the fourth power of the
degree, as needed in logarithmic-phase applications.
-/

open Real
namespace AnalyticNumberTheory.ExponentialSums

/-- At `d*k` steps the defect is at most `k(k+1) exp(-d)/2`. -/
theorem vinogradovDefect_mul_le {k : ℕ} (hk : 2≤k) (d : ℕ) :
    vinogradovDefect k (d*k)≤vinogradovWeight k*Real.exp (-(d:ℝ)) := by
  have hk' : 1≤(k:ℝ) := by exact_mod_cast (by omega : 1≤k)
  have hk0 : (k:ℝ)≠0 := by linarith
  have hx := Real.add_one_le_exp (-(k:ℝ)⁻¹)
  have hbase : 1-(k:ℝ)⁻¹≤Real.exp (-(k:ℝ)⁻¹) := by linarith
  have h := pow_le_pow_left₀ (sub_nonneg.mpr (inv_le_one_of_one_le₀ hk')) hbase (d*k)
  unfold vinogradovDefect
  apply mul_le_mul_of_nonneg_left _ (by dsimp [vinogradovWeight]; positivity)
  apply h.trans_eq
  rw [←Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hk0]

private theorem degree_prefactor {k : ℕ} (hk : 2≤k) (d : ℕ) :
    let s : ℕ := (d+1)*k^2
    (8*((s:ℝ)+1)*((k:ℝ)+1))^(12*s*(d*k)) ≤ Real.exp (200*((d:ℝ)+2)^3*(k:ℝ)^4) := by
  intro s
  let A := 8*((s:ℝ)+1)*((k:ℝ)+1)
  have hA : 0<A := by dsimp only [A]; positivity
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hk0 : 0<(k:ℝ) := by linarith
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg _
  have hsr : (s:ℝ)=((d:ℝ)+1)*k^2 := by dsimp only [s]; push_cast; rfl
  have hsl : Real.log ((s:ℝ)+1)≤Real.log ((d:ℝ)+2)+2*Real.log k := by
    have hx : (s:ℝ)+1≤((d:ℝ)+2)*k^2 := by rw [hsr]; nlinarith [sq_nonneg ((k:ℝ)-1)]
    have h := Real.log_le_log (by positivity) hx
    rwa [Real.log_mul (by positivity) (by positivity),Real.log_pow,Nat.cast_ofNat] at h
  have hlog : Real.log A≤16*((d:ℝ)+2)*k := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity)]
    have hcross := mul_nonneg hd0 hk0.le
    nlinarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8),hsl,
      Real.log_le_sub_one_of_pos (by positivity : 0<(d:ℝ)+2),Real.log_le_sub_one_of_pos hk0,
      Real.log_le_sub_one_of_pos (by positivity : 0<(k:ℝ)+1),hcross,hd0,hkR]
  change A^(12*s*(d*k))≤_
  rw [←Real.exp_log hA,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) (12*s*(d*k)))
  push_cast at h ⊢
  rw [hsr] at h ⊢
  apply h.trans
  have hc : (12:ℝ)*16*(((d:ℝ)+1)*(d:ℝ)*((d:ℝ)+2))≤200*((d:ℝ)+2)^3 := by
    nlinarith only [pow_nonneg hd0 3,sq_nonneg (d:ℝ),hd0]
  have H := mul_le_mul_of_nonneg_right hc (pow_nonneg hk0.le 4)
  linarith only [H]

/-- Uniform form at the moment `s=(d+1)k²`. Its constant has logarithm
`O_d(k^4)`, so it stays controlled after a double moment argument. -/
theorem vinogradov_mean_value_degree_multiple {k N : ℕ} (hk : 2≤k) (hN : 1≤N) (d : ℕ) :
    let s : ℕ := (d+1)*k^2
    vinogradovJ s k N ≤ Real.exp (200*((d:ℝ)+2)^3*(k:ℝ)^4)*
      (N:ℝ)^(vinogradovMeanExponent s k (vinogradovWeight k*Real.exp (-(d:ℝ)))) := by
  intro s
  have hh : k*k+k*(d*k)≤s := by dsimp [s]; exact le_of_eq (by ring)
  have h := vinogradov_mean_value_classical (τ:=d*k) hk hh hN
  apply h.trans
  apply mul_le_mul (degree_prefactor hk d) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  dsimp only [vinogradovMeanExponent]; linarith only [vinogradovDefect_mul_le hk d]

end AnalyticNumberTheory.ExponentialSums
