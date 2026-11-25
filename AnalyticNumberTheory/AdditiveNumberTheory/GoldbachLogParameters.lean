import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachExceptionalReduction

/-!
# Complementary logarithmic parameters for the ternary circle method

A numerical threshold in log N suffices for every elementary comparison
used with a twelfth-power major-arc cutoff and Y equal to the square root of N.
-/

open Real
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- A sufficient logarithmic threshold expressed in integers and factorials. -/
def pageGoldbachLogThreshold : ℝ :=
  max 32 (max (2*(Nat.factorial 31:ℝ)) (3*2^13*(Nat.factorial 26:ℝ)))

/-- Numerical bounds for the Page conductor cutoff and the complementary arcs. -/
theorem goldbach_log_cutoffs {x : ℝ} (hx : 0<x) (hsize : pageGoldbachLogThreshold ≤ log x) :
    let L := log x
    let M := ⌊L^12⌋₊
    let K := exp (sqrt (log (sqrt x)))-2
    2≤L ∧ 1≤M ∧ (M:ℝ)≤L^12 ∧ L^6≤2*sqrt M ∧ 2*(M:ℝ)^2≤x ∧
      L^6≤x^(1/5:ℝ) ∧ exp 16≤sqrt x ∧ 2≤K ∧ (M:ℝ)≤K ∧
      log (K+2)=sqrt (L/2) := by
  let L := log x
  let M := ⌊L^12⌋₊
  have h32 : 32≤L := (le_max_left ..).trans hsize
  have h31 : 2*(Nat.factorial 31:ℝ)≤L := (le_max_left ..).trans ((le_max_right ..).trans hsize)
  have h26 : 3*2^13*(Nat.factorial 26:ℝ)≤L := (le_max_right ..).trans ((le_max_right ..).trans hsize)
  have hL : 1≤L := by linarith
  have hLp : 0<L := by linarith
  have hM : 1≤M := Nat.le_floor (by simpa using one_le_pow₀ hL (n:=12))
  have hmr : 1≤(M:ℝ) := by exact_mod_cast hM
  have hmle : (M:ℝ)≤L^12 := Nat.floor_le (by positivity)
  have hfloor := Nat.lt_floor_add_one (L^12)
  change L^12 < (M:ℝ)+1 at hfloor
  have hs : L^6 ≤ 2*sqrt M := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [←pow_mul, mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num;linarith
  have he : 2*L^30≤x := by
    have H := Real.pow_div_factorial_le_exp L hLp.le 31
    rw [exp_log hx] at H
    have hfac : (0:ℝ)<Nat.factorial 31 := by exact_mod_cast Nat.factorial_pos 31
    apply le_trans _ H
    rw [le_div_iff₀ hfac,pow_succ]
    linarith only [mul_le_mul_of_nonneg_left h31 (by positivity : 0≤L^30)]
  have hM2 : 2*(M:ℝ)^2≤x := by
    apply le_trans _ he
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg M) hmle 2
    rw [←pow_mul] at hh
    linarith only [hh, pow_le_pow_right₀ hL (by decide : 12*2≤30)]
  have hnslow : L^6 ≤ x^(1/5:ℝ) := by
    have H : (L^6)^5≤x := by rw [←pow_mul];norm_num; linarith only [he,pow_nonneg hLp.le 30]
    have H' := Real.rpow_le_rpow (by positivity : 0≤(L^6)^5) H (by norm_num : 0≤(1/5:ℝ))
    rw [←Real.rpow_natCast (L^6) 5,←Real.rpow_mul (by positivity)] at H'
    norm_num at H'
    exact H'
  have hslog : log (sqrt x)=L/2 := Real.log_sqrt hx.le
  have hy : exp 16 ≤ sqrt x := by
    rw [←Real.le_log_iff_exp_le (sqrt_pos.mpr hx), hslog];linarith
  let u := sqrt (L/2)
  have hu : 0≤u := sqrt_nonneg _
  have hu2 : u^2=L/2 := sq_sqrt (by positivity)
  have hu26 : u^26=(L/2)^13 := by rw [show 26=2*13 by decide,pow_mul,hu2]
  have hgap : 3*L^12 ≤ exp u := by
    have H := Real.pow_div_factorial_le_exp u hu 26
    apply le_trans _ H
    rw [hu26,div_pow,le_div_iff₀ (by positivity),le_div_iff₀ (by positivity),pow_succ L 12]
    linarith only [mul_le_mul_of_nonneg_left h26 (by positivity : 0≤L^12)]
  have h3 := one_le_pow₀ hL (n:=12)
  have h4 : 2≤L^12 := by linarith [pow_le_pow_right₀ hL (by decide : 1≤12)]
  dsimp only
  rw [hslog]
  exact ⟨by linarith,hM,hmle,hs,hM2,hnslow,hy,by change 2≤exp u-2;linarith,
    by change (M:ℝ)≤exp u-2;linarith,by rw [sub_add_cancel,Real.log_exp]⟩

end AnalyticNumberTheory.AdditiveNumberTheory
