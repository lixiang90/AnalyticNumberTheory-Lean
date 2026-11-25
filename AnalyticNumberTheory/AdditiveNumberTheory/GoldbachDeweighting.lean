import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachLogDeficit
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachAsymptotic

/-!
# Transferring logarithmic savings to unweighted prime triples
-/

open Real Filter Asymptotics
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Replacing all three logarithmic weights by the logarithm of the target costs
at most one inverse logarithm before dividing by the common cubed weight. -/
theorem goldbachTernary_common_log_error (T : ℕ→ℕ)
    (ho : ∀N,goldbachTernaryOddCount N≤T N) (ha : ∀N,T N≤goldbachTernaryCount N) :
    (fun N : ℕ => (log N)^3*(T N:ℝ)-goldbachTernaryWeighted N) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)) := by
  obtain ⟨C,hC,H⟩ := goldbach_binary_log_deficit
  apply IsBigO.of_bound (3*C+327)
  have hcast := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [H,hcast.eventually (eventually_const_log_pow_le_rpow 1 2 (by norm_num : (0:ℝ)<1/2)),
    hcast.eventually (eventually_const_log_pow_le_rpow 1 3 (by norm_num : (0:ℝ)<1)),eventually_ge_atTop (2:ℕ)] with
    N h hsqrt hcube hN
  let L := log (N:ℝ)
  have hnn : (2:ℝ)≤N := by exact_mod_cast hN
  have hn : 0<(N:ℝ) := by linarith
  have hL : 0<L := log_pos (by linarith)
  have hu := goldbachTernaryCount_log_weight_loss hN
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0≤3*(log N)^2)
  have hmain₁ : L^3*(T N:ℝ)-goldbachTernaryWeighted N≤3*C*((N:ℝ)^2/L) := by
    have hA : L^3*(T N:ℝ)≤L^3*(goldbachTernaryCount N:ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast ha N) (by positivity)
    have he : 3*(log N)^2*(C*((N:ℝ)^2/(log N)^3))=3*C*((N:ℝ)^2/L) := by
      change 3*L^2*(C*((N:ℝ)^2/L^3))=_;field_simp <;> ring
    rw [he] at hh
    change L^3*(_ : ℝ)-_≤_ at hu
    linarith only [hA,hu,hh,goldbachTernaryThetaWeighted_le_weighted N]
  have hpow := goldbachTernaryWeighted_sub_thetaWeighted_le hN
  have htwo := goldbachTernaryThetaWeighted_sub_odd_le hN
  have ho' : L^3*(goldbachTernaryOddCount N:ℝ)≤L^3*(T N:ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ho N) (by positivity)
  have hr : (N:ℝ)^(3/2:ℝ) = N*sqrt N := by
    conv_rhs => lhs;rw [←Real.rpow_one (N:ℝ)]
    rw [sqrt_eq_rpow,←Real.rpow_add hn];norm_num
  have h₁ : (N:ℝ)^(3/2:ℝ)*L≤(N:ℝ)^2/L := by
    rw [hr,le_div_iff₀ hL]
    rw [one_mul,←sqrt_eq_rpow] at hsqrt
    change L^2≤sqrt N at hsqrt
    have hh := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hn.le (sqrt_nonneg (N:ℝ)))
    have he := congrArg (fun v : ℝ => N*v) (sq_sqrt hn.le)
    nlinarith only [he,hh]
  have h₂ : (N:ℝ)*L^2≤(N:ℝ)^2/L := by
    rw [one_mul,rpow_one] at hcube
    rw [le_div_iff₀ hL]
    change L^3≤N at hcube
    nlinarith only [mul_le_mul_of_nonneg_left hcube hn.le]
  change goldbachTernaryWeighted N-goldbachTernaryThetaWeighted N≤324*(N:ℝ)^(3/2:ℝ)*L at hpow
  change goldbachTernaryThetaWeighted N-L^3*(goldbachTernaryOddCount N:ℝ)≤3*N*L^2 at htwo
  have hmain₂ : goldbachTernaryWeighted N-L^3*(T N:ℝ)≤327*((N:ℝ)^2/L) := by
    linarith only [hpow,htwo,ho',h₁,h₂]
  have hscale : 0≤(N:ℝ)^2/L := by positivity
  change ‖L^3*(T N:ℝ)-goldbachTernaryWeighted N‖ ≤ (3*C+327)*‖(N:ℝ)^2/L‖
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hscale,abs_le]
  constructor <;> nlinarith only [hmain₁,hmain₂,mul_nonneg hC.le hscale,hscale]

/-- Transfer a weighted three-prime estimate with a real logarithmic saving
of at most one to an ordinary ordered representation count. -/
theorem goldbachTernary_deweight (T : ℕ→ℕ) (ho : ∀N,goldbachTernaryOddCount N≤T N)
    (ha : ∀N,T N≤goldbachTernaryCount N) {η : ℝ} (hη : η≤1)
    (hweighted : (fun N : ℕ => goldbachTernaryWeighted N-goldbachTernarySingularSeries N*(N:ℝ)^2/2) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^η)) :
    (fun N : ℕ => (T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^(3+η)) := by
  obtain ⟨C,hC,HC⟩ := (goldbachTernary_common_log_error T ho ha).exists_pos
  obtain ⟨B,hB,HB⟩ := hweighted.exists_pos
  apply IsBigO.of_bound (C+B)
  filter_upwards [HC,HB,(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1]
    with N hc hb hlog
  let L := log (N:ℝ)
  let M := goldbachTernarySingularSeries N*(N:ℝ)^2/2
  have hL : 0<L := zero_lt_one.trans_le hlog
  change ‖L^3*(T N:ℝ)-goldbachTernaryWeighted N‖≤C*‖(N:ℝ)^2/L‖ at hc
  change ‖goldbachTernaryWeighted N-M‖≤B*‖(N:ℝ)^2/L^η‖ at hb
  rw [Real.norm_of_nonneg (show 0≤(N:ℝ)^2/L by positivity)] at hc
  rw [Real.norm_of_nonneg (show 0≤(N:ℝ)^2/L^η by positivity)] at hb
  have hle : L^η ≤ L := (Real.rpow_le_rpow_of_exponent_le hlog hη).trans_eq (Real.rpow_one _)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hL _) hle) hC.le)
  have H := (norm_sub_le_norm_sub_add_norm_sub (L^3*(T N:ℝ)) (goldbachTernaryWeighted N) M).trans (add_le_add hc' hb)
  change ‖(T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*L^3)‖≤(C+B)*‖(N:ℝ)^2/L^(3+η)‖
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (show 0≤(N:ℝ)^2/L^(3+η) by positivity),
    show (T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*L^3)=(L^3*(T N:ℝ)-M)/L^3 by
      dsimp only [M]; field_simp <;> ring, abs_div,abs_of_pos (pow_pos hL 3),
    Real.rpow_add hL, Real.rpow_ofNat]
  apply (div_le_div_of_nonneg_right H (by positivity : 0≤L^3)).trans_eq
  ring

end AnalyticNumberTheory.AdditiveNumberTheory
