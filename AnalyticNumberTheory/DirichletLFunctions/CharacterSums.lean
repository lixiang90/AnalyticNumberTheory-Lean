import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.DirichletSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Character Sums and the Pólya–Vinogradov Inequality

This file proves bounds on partial sums of Dirichlet characters:

- Complete proof of the **Pólya–Vinogradov inequality** for both primitive and general
  non-principal characters modulo `q ≥ 2` (`polya_vinogradov_primitive`, `polya_vinogradov`,
  `polya_vinogradov_Ioc`, `polya_vinogradov_Icc_one`, and integer-interval variant
  `polya_vinogradov_Ioc_int`), proved via Gauss sums, finite Fourier expansion, the
  cotangent/sine kernel bound `‖∑_{n ∈ Ioc M (M + N)} exp(2πi a n / q)‖ ≤ 1 / sin(π a / q)`,
  and reduction to the inducing primitive character with `∑_{k ∣ r} |μ(k)| ≤ 2 √r`.
- Elementary bounds and discrepancy estimates for principal characters modulo `q`
  (`norm_sum_principal_sub_le`, `sum_principal_Ioc_period`).
- Tail and partial-sum bounds for `∑ χ(n) / n^σ` and `∑ χ(n) * n^(-s)` for `σ > 0`
  (`norm_sum_Ioc_char_div_rpow_le`, `norm_sum_Ioc_char_mul_cpow_neg_le`,
  `norm_sum_Icc_one_char_div_nat_le`, `norm_sum_Icc_one_char_div_rpow_le`).
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius Classical
open AnalyticNumberTheory.AnalyticTools.Summation
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.DirichletLFunctions

section KernelAndHarmonicBounds

private theorem sum_zmod_eq_sum_range' {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ a : ZMod q, f a = ∑ a ∈ Finset.range q, f (a : ZMod q) := by
  refine Finset.sum_bij (fun a _ ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ _ a₂ _ h
    exact ZMod.val_injective q h
  · intro b hb
    refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)
  · intro a _
    simp

/-- Norm of `1 - exp (θ * I)` equals `2 * |sin (θ / 2)|`. -/
theorem norm_one_sub_cexp_ofReal_mul_I (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq : ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_sub]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      have hsc := Real.sin_sq_add_cos_sq (θ / 2)
      linarith
    have hsc0 := Real.sin_sq_add_cos_sq θ
    calc
      (1 - Real.cos θ) * (1 - Real.cos θ) + -Real.sin θ * -Real.sin θ
          = 1 - 2 * Real.cos θ + (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = 2 - 2 * Real.cos θ := by rw [hsc0]; ring
      _ = 4 * Real.sin (θ / 2) ^ 2 := by rw [hcos]; ring
      _ = (2 * |Real.sin (θ / 2)|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have h1 : 0 ≤ ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith

/-- Exponential sum bound over an interval `Finset.Ioc M (M + N)`:
for `1 ≤ a < q`, `‖∑_{n ∈ Ioc M (M + N)} exp(2πi a n / q)‖ ≤ (sin (π * a / q))⁻¹`. -/
theorem norm_sum_Ioc_cexp_le {q a : ℕ} (ha1 : 1 ≤ a) (haq : a < q) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N),
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))‖ ≤
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le ha1 haq.le)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  let θ : ℝ := 2 * Real.pi * (a : ℝ) / (q : ℝ)
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hsin_pos : 0 < Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast ha1)) hq0
    · rw [div_lt_iff₀ hq0]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast haq) Real.pi_pos
  have hnorm_sub : ‖1 - ζ‖ = 2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
    rw [norm_one_sub_cexp_ofReal_mul_I θ]
    have hhalf : θ / 2 = Real.pi * (a : ℝ) / (q : ℝ) := by
      simp only [θ]
      ring
    rw [hhalf, abs_of_pos hsin_pos]
  have hζ_ne : ζ ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm_sub
    linarith
  have hnorm_ζ : ‖ζ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hsum_eq :
      (∑ n ∈ Finset.Ioc M (M + N),
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))) =
        ζ ^ (M + 1) * ∑ k ∈ Finset.range N, ζ ^ k := by
    have hbij :
        (∑ n ∈ Finset.Ioc M (M + N),
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))) =
          ∑ k ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * ((M + 1 + k : ℕ) : ℂ) / (q : ℂ)) := by
      refine Finset.sum_bij (fun n _ ↦ n - (M + 1)) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_Ioc] at hn
        simp only [Finset.mem_range]
        omega
      · intro n₁ hn₁ n₂ hn₂ h
        simp only [Finset.mem_Ioc] at hn₁ hn₂
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        refine ⟨M + 1 + k, ?_, by omega⟩
        simp only [Finset.mem_Ioc]
        omega
      · intro n hn
        simp only [Finset.mem_Ioc] at hn
        congr 5
        omega
    rw [hbij, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    dsimp only [ζ, θ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsum_eq, norm_mul, norm_pow, hnorm_ζ, one_pow, one_mul, geom_sum_eq hζ_ne, norm_div]
  have hnum : ‖ζ ^ N - 1‖ ≤ 2 := by
    calc
      ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖ζ‖ ^ N + 1 := by rw [norm_pow, norm_one]
      _ = 2 := by rw [hnorm_ζ, one_pow]; norm_num
  have hden : ‖ζ - 1‖ = 2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
    rw [norm_sub_rev, hnorm_sub]
  rw [hden]
  calc
    ‖ζ ^ N - 1‖ / (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))
        ≤ 2 / (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) := by
          gcongr
    _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
          rw [← div_div, div_self two_ne_zero, one_div]

private theorem sum_Icc_inv_le_one_add_log :
    ∀ m : ℕ, 1 ≤ m → ∑ a ∈ Finset.Icc 1 m, (a : ℝ)⁻¹ ≤ 1 + Real.log (m : ℝ)
  | 0, hm => by omega
  | 1, _ => by simp
  | m + 2, _ => by
    have hm1 : 1 ≤ m + 1 := Nat.succ_pos m
    have ih := sum_Icc_inv_le_one_add_log (m + 1) hm1
    have hm1_pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hm2_pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    have hlog_step : ((m + 2 : ℕ) : ℝ)⁻¹ ≤
        Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
      have hratio_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hratio_pos
      rw [Real.log_div hm1_pos.ne' hm2_pos.ne'] at h1
      have hdiff : ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 = -((m + 2 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp [hm2_pos.ne']
        ring
      linarith
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 2)]
    linarith

/-- Cotangent / sine kernel sum bound:
for `q ≥ 2`, `∑ a ∈ Finset.Ico 1 q, (sin (π * a / q))⁻¹ ≤ 2 * q * log q`. -/
theorem sum_inv_sin_pi_div_le {q : ℕ} (hq : 2 ≤ q) :
    ∑ a ∈ Finset.Ico 1 q, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
      2 * (q : ℝ) * Real.log (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by positivity
  let m := q / 2
  have hm_pos : 1 ≤ m := by omega
  have hsplit : Finset.Ico 1 q = Finset.Icc 1 m ∪ Finset.Ioc m (q - 1) := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m (q - 1)) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha1 ha2
    omega
  have hle_half : ∀ a ∈ Finset.Icc 1 m,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤ (q : ℝ) / (2 * (a : ℝ)) := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha.1
    have hangle_nonneg : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
    have hangle_le : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
      have hm2 : (2 * a : ℝ) ≤ (q : ℝ) := by
        have : 2 * a ≤ q := by omega
        exact_mod_cast this
      rw [div_le_div_iff₀ hq0 two_pos]
      nlinarith [Real.pi_pos]
    have hsin := Real.mul_le_sin hangle_nonneg hangle_le
    have hsin_eq : 2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)) = 2 * (a : ℝ) / (q : ℝ) := by
      field_simp [Real.pi_ne_zero, hq0.ne']
    rw [hsin_eq] at hsin
    have hpos_rhs : 0 < 2 * (a : ℝ) / (q : ℝ) := by positivity
    simpa [one_div, inv_div] using inv_anti₀ hpos_rhs hsin
  have hle_hi :
      ∑ a ∈ Finset.Ioc m (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
        ∑ a ∈ Finset.Icc 1 m, (q : ℝ) / (2 * (a : ℝ)) := by
    have hsymm : ∀ a ∈ Finset.Ioc m (q - 1),
        Real.sin (Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ)) =
          Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
      intro a ha
      simp only [Finset.mem_Ioc] at ha
      have haq : a ≤ q := by omega
      rw [Nat.cast_sub haq]
      have harg : Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
          Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
        field_simp [hq0.ne']
      rw [harg, Real.sin_pi_sub]
    have hbij :
        ∑ a ∈ Finset.Ioc m (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ =
          ∑ b ∈ Finset.Ico 1 (q - m), (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹ := by
      refine Finset.sum_bij (fun a _ ↦ q - a) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Ioc] at ha
        simp only [Finset.mem_Ico]
        omega
      · intro a₁ ha₁ a₂ ha₂ h
        simp only [Finset.mem_Ioc] at ha₁ ha₂
        omega
      · intro b hb
        simp only [Finset.mem_Ico] at hb
        refine ⟨q - b, ?_, by omega⟩
        simp only [Finset.mem_Ioc]
        omega
      · intro a ha
        rw [hsymm a ha]
    have hsub : Finset.Ico 1 (q - m) ⊆ Finset.Icc 1 m := by
      intro b hb
      simp only [Finset.mem_Ico] at hb
      simp only [Finset.mem_Icc]
      omega
    rw [hbij]
    calc
      ∑ b ∈ Finset.Ico 1 (q - m), (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹
          ≤ ∑ b ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (b : ℝ) / (q : ℝ)))⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ ↦ ?_
            simp only [Finset.mem_Icc] at hb
            have hsin_pos : 0 ≤ Real.sin (Real.pi * (b : ℝ) / (q : ℝ)) := by
              apply Real.sin_nonneg_of_nonneg_of_le_pi
              · positivity
              · rw [div_le_iff₀ hq0]
                exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : b ≤ q)) Real.pi_pos.le
            positivity
      _ ≤ ∑ b ∈ Finset.Icc 1 m, (q : ℝ) / (2 * (b : ℝ)) := Finset.sum_le_sum hle_half
  have hsum_combine :
      ∑ a ∈ Finset.Ico 1 q, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
        (q : ℝ) * ∑ a ∈ Finset.Icc 1 m, (a : ℝ)⁻¹ := by
    rw [hsplit, Finset.sum_union hdisj]
    have h1 : ∑ a ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
        ∑ a ∈ Finset.Icc 1 m, (q : ℝ) / (2 * (a : ℝ)) := Finset.sum_le_sum hle_half
    calc
      ∑ a ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ +
          ∑ a ∈ Finset.Ioc m (q - 1), (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹
          ≤ ∑ a ∈ Finset.Icc 1 m, (q : ℝ) / (2 * (a : ℝ)) +
              ∑ a ∈ Finset.Icc 1 m, (q : ℝ) / (2 * (a : ℝ)) := add_le_add h1 hle_hi
      _ = ∑ a ∈ Finset.Icc 1 m, ((q : ℝ) * (a : ℝ)⁻¹) := by
            rw [← two_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            ring
      _ = (q : ℝ) * ∑ a ∈ Finset.Icc 1 m, (a : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
  have hlog_half : 1 + Real.log (m : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    have hm_le : (m : ℝ) ≤ (q : ℝ) / 2 := by
      have : 2 * m ≤ q := by omega
      have : (2 : ℝ) * m ≤ q := by exact_mod_cast this
      linarith
    have hm_posR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have h1 : Real.log (m : ℝ) ≤ Real.log ((q : ℝ) / 2) := Real.log_le_log hm_posR hm_le
    rw [Real.log_div hq0.ne' two_ne_zero] at h1
    have hlog2_gt : 1 / 2 < Real.log 2 := by
      have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hlog4 : 1 < Real.log 4 := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) hexp
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      linarith
    have hlogq : Real.log 2 ≤ Real.log (q : ℝ) :=
      Real.log_le_log two_pos (by exact_mod_cast hq)
    linarith
  have hharm := (sum_Icc_inv_le_one_add_log m hm_pos).trans hlog_half
  calc
    ∑ a ∈ Finset.Ico 1 q, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹
        ≤ (q : ℝ) * ∑ a ∈ Finset.Icc 1 m, (a : ℝ)⁻¹ := hsum_combine
    _ ≤ (q : ℝ) * (2 * Real.log (q : ℝ)) := mul_le_mul_of_nonneg_left hharm hq0.le
    _ = 2 * (q : ℝ) * Real.log (q : ℝ) := by ring

end KernelAndHarmonicBounds

section PolyaVinogradov

/-- **Pólya–Vinogradov inequality for primitive characters**:
for a primitive Dirichlet character `χ` modulo `q ≥ 2`, and any `M N : ℕ`,
`‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ 2 * √q * log q`. -/
theorem polya_vinogradov_primitive {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ 2 * Real.sqrt q * Real.log q := by
  have : NeZero q := ⟨by omega⟩
  have hq_pos : (0 : ℝ) < q := by positivity
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  let G : ℂ := _root_.gaussSum χ⁻¹ ZMod.stdAddChar
  have hG_norm : ‖G‖ = Real.sqrt q := DirichletCharacter.norm_gaussSum_stdAddChar hχ.inv
  have hpoint (n : ℕ) :
      χ n * G = ∑ a ∈ Finset.Ico 1 q,
        χ⁻¹ (a : ZMod q) * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ)) := by
    have hgs := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (n : ZMod q)
    simp only [inv_inv] at hgs
    have hlhs : _root_.gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) =
        ∑ a ∈ Finset.range q,
          χ⁻¹ (a : ZMod q) *
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ)) := by
      rw [_root_.gaussSum, sum_zmod_eq_sum_range' (fun a ↦ χ⁻¹ a * ZMod.stdAddChar.mulShift (n : ZMod q) a)]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [AddChar.mulShift_apply]
      have hcoe : ((n : ZMod q) * (a : ZMod q)) = (((((n : ℤ) * (a : ℤ)) : ℤ)) : ZMod q) := by
        push_cast
        rfl
      rw [hcoe, ZMod.stdAddChar_coe]
      push_cast
      ring_nf
    rw [← hgs, hlhs]
    have h0 : Finset.range q = insert 0 (Finset.Ico 1 q) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hzero : χ⁻¹ ((0 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_zero]
      exact χ⁻¹.map_zero' (by omega)
    rw [h0, Finset.sum_insert (by simp), hzero, zero_mul, zero_add]
  have hsum_eq :
      (∑ n ∈ Finset.Ioc M (M + N), χ n) * G =
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + N),
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ)) := by
    rw [Finset.sum_mul]
    simp_rw [hpoint, Finset.mul_sum]
    exact Finset.sum_comm
  have hnorm_mul :
      ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ * Real.sqrt q ≤
        2 * (q : ℝ) * Real.log (q : ℝ) := by
    rw [← hG_norm, ← norm_mul, hsum_eq]
    calc
      ‖∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + N),
            Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))‖
          ≤ ∑ a ∈ Finset.Ico 1 q, ‖χ⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + N),
                Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
            refine Finset.sum_le_sum fun a ha ↦ ?_
            simp only [Finset.mem_Ico] at ha
            rw [norm_mul]
            calc
              ‖χ⁻¹ (a : ZMod q)‖ *
                  ‖∑ n ∈ Finset.Ioc M (M + N),
                    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ) / (q : ℂ))‖
                  ≤ 1 * (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
                    mul_le_mul (χ⁻¹.norm_le_one _) (norm_sum_Ioc_cexp_le ha.1 ha.2 M N)
                      (norm_nonneg _) zero_le_one
              _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
      _ ≤ 2 * (q : ℝ) * Real.log (q : ℝ) := sum_inv_sin_pi_div_le hq
  rw [← le_div_iff₀ hsqrt_pos] at hnorm_mul
  refine hnorm_mul.trans_eq ?_
  have hq_sq : (q : ℝ) / Real.sqrt q = Real.sqrt q := by
    rw [div_eq_iff hsqrt_pos.ne', Real.mul_self_sqrt hq_pos.le]
  calc
    2 * (q : ℝ) * Real.log (q : ℝ) / Real.sqrt q
        = 2 * ((q : ℝ) / Real.sqrt q) * Real.log (q : ℝ) := by ring
    _ = 2 * Real.sqrt q * Real.log (q : ℝ) := by rw [hq_sq]

private theorem sum_abs_moebius_divisors_eq_prod (r : ℕ) (hr : 0 < r) :
    ∑ k ∈ r.divisors, |(μ k : ℝ)| = ∏ _p ∈ r.primeFactors, (2 : ℝ) := by
  let g : ArithmeticFunction ℝ :=
    { toFun := fun k ↦ |(μ k : ℝ)|
      map_zero' := by simp }
  have hg_mult : g.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨by simp [g], fun {m n} _ _ hmn ↦ ?_⟩
    simp only [g, ArithmeticFunction.coe_mk]
    have hmul : μ (m * n) = μ m * μ n := ArithmeticFunction.isMultiplicative_moebius.2 hmn
    rw [hmul, Int.cast_mul, abs_mul]
  let F : ArithmeticFunction ℝ := g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hF_mult : F.IsMultiplicative :=
    hg_mult.mul (ArithmeticFunction.isMultiplicative_zeta.natCast)
  have hF_eq : F r = ∑ k ∈ r.divisors, |(μ k : ℝ)| := by
    change (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) r = ∑ k ∈ r.divisors, |(μ k : ℝ)|
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    simp [g]
  have hF_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → F (p ^ k) = 2 := by
    intro p k hp hk
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      Finset.sum_range_succ']
    simp only [pow_zero, g, ArithmeticFunction.coe_mk, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, abs_one]
    have htail : ∑ x ∈ Finset.range k, |(μ (p ^ (x + 1)) : ℝ)| = 1 := by
      cases k with
      | zero => exact absurd rfl hk
      | succ k' =>
        rw [Finset.sum_range_succ']
        have h1 : |(μ (p ^ (0 + 1)) : ℝ)| = 1 := by
          simp [ArithmeticFunction.moebius_apply_prime hp]
        have hrest : ∑ x ∈ Finset.range k', |(μ (p ^ (x + 1 + 1)) : ℝ)| = 0 := by
          refine Finset.sum_eq_zero fun x _ ↦ ?_
          rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
          simp
        rw [h1, hrest, zero_add]
    rw [htail]
    norm_num
  rw [← hF_eq, hF_mult.multiplicative_factorization F hr.ne']
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hfac : r.factorization p ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd hp' hr.ne' (Nat.dvd_of_mem_primeFactors hp)).ne'
  exact hF_prime_pow hp' hfac

/-- Upper bound `∑ k ∈ r.divisors, |μ k| ≤ 2 * √r` for every `r > 0`. -/
theorem sum_abs_moebius_divisors_le_two_sqrt {r : ℕ} (hr : 0 < r) :
    ∑ k ∈ r.divisors, |(μ k : ℝ)| ≤ 2 * Real.sqrt r := by
  rw [sum_abs_moebius_divisors_eq_prod r hr]
  have hprod_le_r : (∏ p ∈ r.primeFactors, Real.sqrt p) ≤ Real.sqrt r := by
    have hprod_nat : ∏ p ∈ r.primeFactors, p ≤ r :=
      Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r)
    have hprod_real : ∏ p ∈ r.primeFactors, (p : ℝ) ≤ (r : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast hprod_nat
    have hsqrt_prod : ∏ p ∈ r.primeFactors, Real.sqrt p =
        Real.sqrt (∏ p ∈ r.primeFactors, (p : ℝ)) := by
      symm
      exact Real.sqrt_prod r.primeFactors (fun p _ ↦ Nat.cast_nonneg p)
    rw [hsqrt_prod]
    exact Real.sqrt_le_sqrt hprod_real
  have hratio : (∏ p ∈ r.primeFactors, (2 : ℝ) / Real.sqrt p) ≤ 2 := by
    let s₁ := r.primeFactors.filter (· < 4)
    let s₂ := r.primeFactors.filter (4 ≤ ·)
    have hpart : r.primeFactors = s₁ ∪ s₂ := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, s₁, s₂]
      by_cases hp4 : p < 4
      · simp [hp4]
      · simp [hp4, Nat.not_lt.mp hp4]
    have hdisj : Disjoint s₁ s₂ := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter, s₁, s₂] at h1 h2
      omega
    rw [hpart, Finset.prod_union hdisj]
    have hs₂ : ∏ p ∈ s₂, ((2 : ℝ) / Real.sqrt p) ≤ 1 := by
      have hprod_le_one : ∀ s : Finset ℕ,
          (∀ p ∈ s, 0 ≤ (2 : ℝ) / Real.sqrt p ∧ (2 : ℝ) / Real.sqrt p ≤ 1) →
            ∏ p ∈ s, ((2 : ℝ) / Real.sqrt p) ≤ 1 := by
        intro s hs
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.prod_insert ha]
          have h1 := hs a (Finset.mem_insert_self a s)
          have h2 := ih fun p hp ↦ hs p (Finset.mem_insert_of_mem hp)
          nlinarith
      refine hprod_le_one s₂ fun p hp ↦ ⟨by positivity, ?_⟩
      simp only [Finset.mem_filter, s₂] at hp
      rw [div_le_one (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p)))]
      have h4p : (4 : ℝ) ≤ p := by exact_mod_cast hp.2
      calc
        (2 : ℝ) = Real.sqrt 4 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt p := Real.sqrt_le_sqrt h4p
    have hs₁ : ∏ p ∈ s₁, ((2 : ℝ) / Real.sqrt p) ≤ 2 := by
      have hsub : s₁ ⊆ ({2, 3} : Finset ℕ) := by
        intro p hp
        simp only [Finset.mem_filter, s₁] at hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp.1
        have hp2 : 2 ≤ p := hp_prime.two_le
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      by_cases h2 : 2 ∈ s₁ <;> by_cases h3 : 3 ∈ s₁
      · have hs₁_eq : s₁ = ({2, 3} : Finset ℕ) := by
          ext p
          constructor
          · exact fun hp ↦ hsub hp
          · intro hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl <;> assumption
        rw [hs₁_eq, Finset.prod_pair (by norm_num)]
        have hsq6 : (2 / Real.sqrt 2 * (2 / Real.sqrt 3)) ^ 2 ≤ 2 ^ 2 := by
          rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
          norm_num
        nlinarith [show 0 ≤ 2 / Real.sqrt 2 * (2 / Real.sqrt 3) by positivity]
      · have hs₁_eq : s₁ = {2} := by
          ext p
          simp only [Finset.mem_singleton]
          constructor
          · intro hp
            have := hsub hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · rfl
            · exact absurd hp h3
          · rintro rfl; exact h2
        rw [hs₁_eq, Finset.prod_singleton]
        have hsq2 : (2 / Real.sqrt 2) ^ 2 ≤ 2 ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        nlinarith [show 0 ≤ 2 / Real.sqrt 2 by positivity]
      · have hs₁_eq : s₁ = {3} := by
          ext p
          simp only [Finset.mem_singleton]
          constructor
          · intro hp
            have := hsub hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · exact absurd hp h2
            · rfl
          · rintro rfl; exact h3
        rw [hs₁_eq, Finset.prod_singleton]
        have hsq3 : (2 / Real.sqrt 3) ^ 2 ≤ 2 ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        nlinarith [show 0 ≤ 2 / Real.sqrt 3 by positivity]
      · have hs₁_eq : s₁ = ∅ := by
          ext p
          simp only [Finset.notMem_empty, iff_false]
          intro hp
          have := hsub hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact h2 hp
          · exact h3 hp
        rw [hs₁_eq, Finset.prod_empty]
        norm_num
    calc
      (∏ p ∈ s₁, (2 : ℝ) / Real.sqrt p) * (∏ p ∈ s₂, (2 : ℝ) / Real.sqrt p)
          ≤ 2 * 1 := mul_le_mul hs₁ hs₂ (Finset.prod_nonneg fun p _ ↦ by positivity) zero_le_two
      _ = 2 := mul_one 2
  have hprod_eq :
      (∏ _p ∈ r.primeFactors, (2 : ℝ)) =
        (∏ p ∈ r.primeFactors, (2 : ℝ) / Real.sqrt p) * (∏ p ∈ r.primeFactors, Real.sqrt p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
    have hsq_ne : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp_pos).ne'
    field_simp [hsq_ne]
  rw [hprod_eq]
  exact mul_le_mul hratio hprod_le_r (Finset.prod_nonneg fun _ _ ↦ Real.sqrt_nonneg _) zero_le_two

private theorem char_eq_primitive_mul_moebius' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℕ) :
    χ x = χ.primitiveCharacter x *
      ∑ k ∈ (q / χ.conductor).divisors, if k ∣ x then (μ k : ℂ) else 0 := by
  let d := χ.conductor
  let r := q / d
  have hd_dvd : d ∣ q := χ.conductor_dvd_level
  have hq_eq : q = d * r := (Nat.mul_div_cancel' hd_dvd).symm
  have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd_dvd)
    (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hsum_gcd : ∑ k ∈ r.divisors, (if k ∣ x then (μ k : ℂ) else 0) =
      if Nat.Coprime x r then 1 else 0 := by
    have hsub : ∑ k ∈ r.divisors, (if k ∣ x then (μ k : ℂ) else 0) =
        ∑ k ∈ (Nat.gcd x r).divisors, (μ k : ℂ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext k
      simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hkr, _⟩, hkx⟩
        exact ⟨⟨hkx, hkr⟩, fun h0 ↦ hr_pos.ne' (Nat.gcd_eq_zero_iff.mp h0).2⟩
      · rintro ⟨⟨hkx, hkr⟩, _⟩
        exact ⟨⟨hkr, hr_pos.ne'⟩, hkx⟩
    rw [hsub]
    have hmu : (∑ k ∈ (Nat.gcd x r).divisors, μ k) =
        if Nat.gcd x r = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    have hmuC : (∑ k ∈ (Nat.gcd x r).divisors, (μ k : ℂ)) =
        if Nat.Coprime x r then 1 else 0 := by
      have := congrArg (Int.cast (R := ℂ)) hmu
      push_cast at this
      simpa [Nat.Coprime] using this
    exact hmuC
  rw [hsum_gcd]
  split_ifs with hxr
  · rw [mul_one]
    by_cases hxd : Nat.Coprime x d
    · have hxq : Nat.Coprime x q := by
        rw [hq_eq]
        exact Nat.Coprime.mul_right hxd hxr
      have hx_int : χ ((x : ℤ) : ZMod q) = χ.primitiveCharacter ((x : ℤ) : ZMod d) :=
        (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hxq)).symm
      simpa using hx_int
    · have hxq : ¬ Nat.Coprime x q := fun h ↦ hxd (h.coprime_dvd_right hd_dvd)
      have h1 : χ x = 0 := by
        rw [← Int.cast_natCast x, χ.apply_eq_zero_iff]
        exact mt Nat.isCoprime_iff_coprime.mp hxq
      have h2 : χ.primitiveCharacter x = 0 := by
        rw [← Int.cast_natCast x, χ.primitiveCharacter.apply_eq_zero_iff]
        exact mt Nat.isCoprime_iff_coprime.mp hxd
      rw [h1, h2]
  · have hxq : ¬ Nat.Coprime x q := by
      intro h
      exact hxr (h.coprime_dvd_right (Nat.div_dvd_of_dvd hd_dvd))
    have h1 : χ x = 0 := by
      rw [← Int.cast_natCast x, χ.apply_eq_zero_iff]
      exact mt Nat.isCoprime_iff_coprime.mp hxq
    simp [h1]

/-- **Pólya–Vinogradov inequality** for general non-principal Dirichlet characters:
for any non-principal character `χ ≠ 1` modulo `q ≥ 2`, and any `M N : ℕ`,
`‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ 4 * √q * log q`. -/
theorem polya_vinogradov {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ 4 * Real.sqrt q * Real.log q := by
  have : NeZero q := ⟨by omega⟩
  let d := χ.conductor
  let r := q / d
  let χs := χ.primitiveCharacter
  have hd_dvd : d ∣ q := χ.conductor_dvd_level
  have hd_pos : 0 < d := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd_dvd) hd_pos
  have hq_eq : q = d * r := (Nat.mul_div_cancel' hd_dvd).symm
  have hd_ge2 : 2 ≤ d := by
    by_contra hd1
    have hdeq : d = 1 := by omega
    exact hχ (χ.eq_one_iff_conductor_eq_one.mpr hdeq)
  have hsum_split :
      ∑ n ∈ Finset.Ioc M (M + N), χ n =
        ∑ k ∈ r.divisors, (μ k : ℂ) * χs k *
          ∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m := by
    simp_rw [char_eq_primitive_mul_moebius' χ]
    calc
      ∑ n ∈ Finset.Ioc M (M + N),
          χs n * ∑ k ∈ r.divisors, (if k ∣ n then (μ k : ℂ) else 0)
          = ∑ n ∈ Finset.Ioc M (M + N), ∑ k ∈ r.divisors,
              (μ k : ℂ) * (if k ∣ n then χs n else 0) := by
            refine Finset.sum_congr rfl fun n _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            split_ifs <;> ring
      _ = ∑ k ∈ r.divisors, ∑ n ∈ Finset.Ioc M (M + N),
              (μ k : ℂ) * (if k ∣ n then χs n else 0) := Finset.sum_comm
      _ = ∑ k ∈ r.divisors, (μ k : ℂ) *
            ∑ n ∈ (Finset.Ioc M (M + N)).filter (fun n ↦ k ∣ n), χs n := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [← Finset.mul_sum, Finset.sum_filter]
      _ = ∑ k ∈ r.divisors, (μ k : ℂ) * χs k *
            ∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
            rw [mul_assoc]
            congr 1
            rw [Finset.mul_sum]
            symm
            refine Finset.sum_bij (fun m _ ↦ k * m) ?_ ?_ ?_ ?_
            · intro m hm
              simp only [Finset.mem_Ioc] at hm
              simp only [Finset.mem_filter, Finset.mem_Ioc]
              refine ⟨⟨?_, ?_⟩, dvd_mul_right k m⟩
              · rw [mul_comm]
                exact (Nat.div_lt_iff_lt_mul hk_pos).mp hm.1
              · rw [mul_comm]
                exact (Nat.le_div_iff_mul_le hk_pos).mp hm.2
            · intro m₁ _ m₂ _ h
              exact Nat.mul_left_cancel hk_pos h
            · intro n hn
              simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
              obtain ⟨m, rfl⟩ := hn.2
              refine ⟨m, ?_, rfl⟩
              simp only [Finset.mem_Ioc]
              refine ⟨(Nat.div_lt_iff_lt_mul hk_pos).mpr (by rw [mul_comm]; exact hn.1.1),
                (Nat.le_div_iff_mul_le hk_pos).mpr (by rw [mul_comm]; exact hn.1.2)⟩
            · intro m _
              push_cast
              rw [map_mul]
  rw [hsum_split]
  have hinner (k : ℕ) :
      ‖∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m‖ ≤ 2 * Real.sqrt d * Real.log d := by
    have hlen : M / k ≤ (M + N) / k := Nat.div_le_div_right (Nat.le_add_right M N)
    have heq : (M + N) / k = M / k + ((M + N) / k - M / k) := (Nat.add_sub_of_le hlen).symm
    rw [heq]
    exact polya_vinogradov_primitive hd_ge2 χ.primitiveCharacter_isPrimitive (M / k)
      ((M + N) / k - M / k)
  calc
    ‖∑ k ∈ r.divisors, (μ k : ℂ) * χs k *
        ∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m‖
        ≤ ∑ k ∈ r.divisors, ‖(μ k : ℂ) * χs k *
            ∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ r.divisors, |(μ k : ℝ)| * (2 * Real.sqrt d * Real.log d) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [norm_mul, norm_mul, Complex.norm_intCast]
          have h1 : ‖χs k‖ ≤ 1 := χs.norm_le_one _
          have h2 := hinner k
          calc
            |(μ k : ℝ)| * ‖χs k‖ * ‖∑ m ∈ Finset.Ioc (M / k) ((M + N) / k), χs m‖
                ≤ |(μ k : ℝ)| * 1 * (2 * Real.sqrt d * Real.log d) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
                    (norm_nonneg _) (by positivity)
            _ = |(μ k : ℝ)| * (2 * Real.sqrt d * Real.log d) := by ring
    _ = (∑ k ∈ r.divisors, |(μ k : ℝ)|) * (2 * Real.sqrt d * Real.log d) :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ (2 * Real.sqrt r) * (2 * Real.sqrt d * Real.log d) := by
          refine mul_le_mul_of_nonneg_right (sum_abs_moebius_divisors_le_two_sqrt hr_pos) ?_
          have : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
          positivity
    _ = 4 * (Real.sqrt d * Real.sqrt r) * Real.log d := by ring
    _ = 4 * Real.sqrt q * Real.log d := by
          rw [← Real.sqrt_mul (Nat.cast_nonneg d), ← Nat.cast_mul, ← hq_eq]
    _ ≤ 4 * Real.sqrt q * Real.log q := by
          have hdq : (d : ℝ) ≤ q := by
            exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hd_dvd
          have hlog : Real.log d ≤ Real.log q :=
            Real.log_le_log (by exact_mod_cast hd_pos) hdq
          gcongr

/-- **Pólya–Vinogradov inequality** over `Finset.Ioc a b` (`a b : ℕ`). -/
theorem polya_vinogradov_Ioc {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (a b : ℕ) :
    ‖∑ n ∈ Finset.Ioc a b, χ n‖ ≤ 4 * Real.sqrt q * Real.log q := by
  rcases le_or_gt a b with hab | hab
  · simpa [Nat.add_sub_of_le hab] using polya_vinogradov hq hχ a (b - a)
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
    positivity

/-- **Pólya–Vinogradov inequality** over `Finset.Icc 1 N` (`N : ℕ`). -/
theorem polya_vinogradov_Icc_one {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n‖ ≤ 4 * Real.sqrt q * Real.log q := by
  have heq : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [heq]
  exact polya_vinogradov_Ioc hq hχ 0 N

/-- **Pólya–Vinogradov inequality** over `Finset.Icc a b` (`1 ≤ a`). -/
theorem polya_vinogradov_Icc {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {a b : ℕ} (ha : 1 ≤ a) :
    ‖∑ n ∈ Finset.Icc a b, χ n‖ ≤ 4 * Real.sqrt q * Real.log q := by
  have heq : Finset.Icc a b = Finset.Ioc (a - 1) b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [heq]
  exact polya_vinogradov_Ioc hq hχ (a - 1) b

/-- **Pólya–Vinogradov inequality** over integer intervals `Finset.Ioc M (M + N)` (`M : ℤ, N : ℕ`). -/
theorem polya_vinogradov_Ioc_int {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ 4 * Real.sqrt q * Real.log q := by
  let K : ℕ := M.natAbs
  let M' : ℕ := (M + K * (q : ℤ)).toNat
  have hM'_nonneg : 0 ≤ M + K * (q : ℤ) := by
    have h1 : -((M.natAbs : ℤ)) ≤ M := by
      rcases Int.natAbs_eq M with h | h <;> omega
    have hq2 : (1 : ℤ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have h2 : (M.natAbs : ℤ) ≤ K * (q : ℤ) := by
      dsimp only [K]
      nlinarith
    linarith
  have hM'_eq : (M' : ℤ) = M + K * (q : ℤ) := Int.toNat_of_nonneg hM'_nonneg
  have hbij :
      ∑ n ∈ Finset.Ioc M (M + N), χ n = ∑ m ∈ Finset.Ioc M' (M' + N), χ m := by
    refine Finset.sum_bij (fun n _ ↦ (n + K * (q : ℤ)).toNat) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ioc] at hn ⊢
      have hn0 : 0 ≤ n + K * (q : ℤ) := by linarith
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ioc] at hn₁ hn₂
      have h1 : 0 ≤ n₁ + K * (q : ℤ) := by linarith
      have h2 : 0 ≤ n₂ + K * (q : ℤ) := by linarith
      omega
    · intro m hm
      simp only [Finset.mem_Ioc] at hm
      refine ⟨(m : ℤ) - K * (q : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_Ioc]
        omega
      · omega
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hn0 : 0 ≤ n + K * (q : ℤ) := by linarith
      have hcast : (((n + K * (q : ℤ)).toNat : ℕ) : ℤ) = n + K * (q : ℤ) :=
        Int.toNat_of_nonneg hn0
      rw [← Int.cast_natCast, hcast]
      push_cast
      rw [ZMod.natCast_self, mul_zero, add_zero]
  rw [hbij]
  exact polya_vinogradov hq hχ M' N

/-- Combined trivial and Pólya–Vinogradov bound:
`‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ min N (4 * √q * log q)`. -/
theorem polya_vinogradov_min {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖ ≤ min (N : ℝ) (4 * Real.sqrt q * Real.log q) := by
  refine le_min ?_ (polya_vinogradov hq hχ M N)
  calc
    ‖∑ n ∈ Finset.Ioc M (M + N), χ n‖
        ≤ ∑ _n ∈ Finset.Ioc M (M + N), (1 : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ χ.norm_le_one _)
    _ = (N : ℝ) := by
          simp [Nat.card_Ioc]

end PolyaVinogradov

section PrincipalCharacterBounds

/-- Sum of the principal character over a full period `Finset.Ioc M (M + q)` equals `q.totient`. -/
theorem sum_principal_Ioc_period {q : ℕ} [NeZero q] (M : ℕ) :
    ∑ n ∈ Finset.Ioc M (M + q), (1 : DirichletCharacter ℂ q) n = (q.totient : ℂ) := by
  have hshift :
      ∑ n ∈ Finset.Ioc M (M + q), (1 : DirichletCharacter ℂ q) n =
        ∑ a ∈ Finset.range q, (1 : DirichletCharacter ℂ q) (M + 1 + a : ℕ) := by
    refine Finset.sum_bij (fun n _ ↦ n - (M + 1)) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_range]; omega
    · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ioc] at hn₁ hn₂; omega
    · intro a ha; simp only [Finset.mem_range] at ha
      refine ⟨M + 1 + a, by simp only [Finset.mem_Ioc]; omega, by omega⟩
    · intro n hn; simp only [Finset.mem_Ioc] at hn; congr 2; omega
  rw [hshift]
  have hz : ∑ a ∈ Finset.range q, (1 : DirichletCharacter ℂ q) (M + 1 + a : ℕ) =
      ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) (((M + 1 : ℕ) : ZMod q) + a) := by
    symm
    rw [sum_zmod_eq_sum_range']
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    push_cast
    rfl
  rw [hz]
  exact (Equiv.sum_comp (Equiv.addLeft ((M + 1 : ℕ) : ZMod q))
    (fun a ↦ (1 : DirichletCharacter ℂ q) a)).trans
    (by rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient])

/-- Trivial bound `‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n‖ ≤ N`. -/
theorem norm_sum_principal_Ioc_le (q M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n‖ ≤ N := by
  calc
    ‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n‖
        ≤ ∑ _n ∈ Finset.Ioc M (M + N), (1 : ℝ) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ (1 : DirichletCharacter ℂ q).norm_le_one _)
    _ = (N : ℝ) := by simp [Nat.card_Ioc]

/-- Discrepancy bound for the principal character modulo `q > 0`:
`‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n - N * φ(q) / q‖ ≤ ∑ k ∈ q.divisors, |μ k|`. -/
theorem norm_sum_principal_sub_le_sum_moebius {q : ℕ} (hq : 0 < q) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n -
        (N : ℂ) * (q.totient : ℂ) / (q : ℂ)‖ ≤
      ∑ k ∈ q.divisors, |(μ k : ℝ)| := by
  have : NeZero q := ⟨hq.ne'⟩
  have h1_eq (n : ℕ) :
      (1 : DirichletCharacter ℂ q) n =
        ∑ k ∈ q.divisors, if k ∣ n then (μ k : ℂ) else 0 := by
    have hsub : ∑ k ∈ q.divisors, (if k ∣ n then (μ k : ℂ) else 0) =
        ∑ k ∈ (Nat.gcd n q).divisors, (μ k : ℂ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext k
      simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hkq, _⟩, hkn⟩
        exact ⟨⟨hkn, hkq⟩, fun h0 ↦ hq.ne' (Nat.gcd_eq_zero_iff.mp h0).2⟩
      · rintro ⟨⟨hkn, hkq⟩, _⟩
        exact ⟨⟨hkq, hq.ne'⟩, hkn⟩
    rw [hsub]
    have hmu : (∑ k ∈ (Nat.gcd n q).divisors, μ k) = if Nat.gcd n q = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
        ArithmeticFunction.one_apply]
    have hmuC : (∑ k ∈ (Nat.gcd n q).divisors, (μ k : ℂ)) =
        if Nat.Coprime n q then 1 else 0 := by
      have := congrArg (Int.cast (R := ℂ)) hmu
      push_cast at this
      simpa [Nat.Coprime] using this
    rw [hmuC]
    split_ifs with hnq
    · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hnq)
    · exact (1 : DirichletCharacter ℂ q).map_nonunit
        (fun hu ↦ hnq ((ZMod.isUnit_iff_coprime n q).mp hu))
  have hsum_eq :
      ∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n =
        ∑ k ∈ q.divisors, (μ k : ℂ) * (((M + N) / k - M / k : ℕ) : ℂ) := by
    simp_rw [h1_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have hcard : ((Finset.Ioc M (M + N)).filter (fun n ↦ k ∣ n)).card =
        (Finset.Ioc (M / k) ((M + N) / k)).card := by
      refine Finset.card_bij (fun n _ ↦ n / k) ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
        obtain ⟨m, rfl⟩ := hn.2
        rw [Nat.mul_div_cancel_left _ hk_pos]
        exact ⟨(Nat.div_lt_iff_lt_mul hk_pos).mpr (by rw [mul_comm]; exact hn.1.1),
          (Nat.le_div_iff_mul_le hk_pos).mpr (by rw [mul_comm]; exact hn.1.2)⟩
      · intro n₁ hn₁ n₂ hn₂ h
        simp only [Finset.mem_filter] at hn₁ hn₂
        obtain ⟨m₁, rfl⟩ := hn₁.2
        obtain ⟨m₂, rfl⟩ := hn₂.2
        rw [Nat.mul_div_cancel_left _ hk_pos, Nat.mul_div_cancel_left _ hk_pos] at h
        rw [h]
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        refine ⟨k * m, ?_, Nat.mul_div_cancel_left _ hk_pos⟩
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, dvd_mul_right k m⟩
        · rw [mul_comm]
          exact (Nat.div_lt_iff_lt_mul hk_pos).mp hm.1
        · rw [mul_comm]
          exact (Nat.le_div_iff_mul_le hk_pos).mp hm.2
    rw [hcard, Nat.card_Ioc]
  have htot : (q.totient : ℤ) = ∑ k ∈ q.divisors, μ k * ((q / k : ℕ) : ℤ) := by
    have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun n ↦ (n.totient : ℤ)) (g := fun n ↦ (n : ℤ)) |>.mp
      (fun n _ ↦ by exact_mod_cast Nat.sum_totient n) q hq
    have h' : (∑ x ∈ q.divisorsAntidiagonal, μ x.1 * (x.2 : ℤ)) = (q.totient : ℤ) := by
      simpa using h
    rw [Nat.sum_divisorsAntidiagonal (f := fun x y ↦ μ x * (y : ℤ))] at h'
    exact h'.symm
  have htotC : (N : ℂ) * (q.totient : ℂ) / (q : ℂ) =
      ∑ k ∈ q.divisors, (μ k : ℂ) * ((N : ℂ) / (k : ℂ)) := by
    have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    have htotC' : (q.totient : ℂ) = ∑ k ∈ q.divisors, (μ k : ℂ) * ((q / k : ℕ) : ℂ) := by
      have hcast := congrArg (Int.cast (R := ℂ)) htot
      push_cast at hcast
      exact hcast
    rw [htotC', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk_dvd : k ∣ q := Nat.dvd_of_mem_divisors hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
    have hqk : ((q / k : ℕ) : ℂ) = (q : ℂ) / (k : ℂ) := by
      rw [Nat.cast_div hk_dvd hkC]
    rw [hqk]
    field_simp [hqC, hkC]
  rw [hsum_eq, htotC, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ q.divisors,
        ((μ k : ℂ) * (((M + N) / k - M / k : ℕ) : ℂ) - (μ k : ℂ) * ((N : ℂ) / (k : ℂ)))‖
        ≤ ∑ k ∈ q.divisors,
            ‖(μ k : ℂ) * ((((M + N) / k - M / k : ℕ) : ℂ) - (N : ℂ) / (k : ℂ))‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          rw [mul_sub]
      _ ≤ ∑ k ∈ q.divisors, |(μ k : ℝ)| := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
          have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
          rw [norm_mul, Complex.norm_intCast]
          have herr : ‖((((M + N) / k - M / k : ℕ) : ℂ) - (N : ℂ) / (k : ℂ))‖ ≤ 1 := by
            have hreal : ((((M + N) / k - M / k : ℕ) : ℂ) - (N : ℂ) / (k : ℂ)) =
                (((((M + N) / k - M / k : ℕ) : ℝ) - (N : ℝ) / (k : ℝ) : ℝ) : ℂ) := by
              push_cast
              rfl
            rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_le]
            have hle : M / k ≤ (M + N) / k := Nat.div_le_div_right (Nat.le_add_right M N)
            have hc : (((M + N) / k - M / k : ℕ) : ℝ) =
                ((M + N) / k : ℕ) - (M / k : ℕ) := by
              rw [Nat.cast_sub hle]
            have h1 : (k : ℝ) * (((M + N) / k : ℕ) : ℝ) ≤ (M + N : ℕ) := by
              exact_mod_cast Nat.mul_div_le (M + N) k
            have h2 : ((M + N : ℕ) : ℝ) < (k : ℝ) * ((((M + N) / k : ℕ) : ℝ) + 1) := by
              exact_mod_cast Nat.lt_mul_div_succ (M + N) hk_pos
            have h3 : (k : ℝ) * ((M / k : ℕ) : ℝ) ≤ (M : ℕ) := by
              exact_mod_cast Nat.mul_div_le M k
            have h4 : ((M : ℕ) : ℝ) < (k : ℝ) * (((M / k : ℕ) : ℝ) + 1) := by
              exact_mod_cast Nat.lt_mul_div_succ M hk_pos
            push_cast at h1 h2 h3 h4
            have hy : (k : ℝ) * ((N : ℝ) / (k : ℝ)) = (N : ℝ) :=
              mul_div_cancel₀ (N : ℝ) hkR.ne'
            rw [hc]
            constructor
            · rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left hkR]
              linarith [h2, h3, hy]
            · rw [sub_le_iff_le_add, ← mul_le_mul_iff_of_pos_left hkR]
              linarith [h1, h4, hy]
          exact mul_le_of_le_one_right (abs_nonneg _) herr

/-- Discrepancy bound for the principal character modulo `q > 0`:
`‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n - N * φ(q) / q‖ ≤ 2 * √q`. -/
theorem norm_sum_principal_sub_le {q : ℕ} (hq : 0 < q) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + N), (1 : DirichletCharacter ℂ q) n -
        (N : ℂ) * (q.totient : ℂ) / (q : ℂ)‖ ≤ 2 * Real.sqrt q :=
  (norm_sum_principal_sub_le_sum_moebius hq M N).trans
    (sum_abs_moebius_divisors_le_two_sqrt hq)

end PrincipalCharacterBounds

section PartialSumBounds

/-- Real-exponent tail bound via Pólya–Vinogradov and Abel summation:
for `χ ≠ 1` modulo `q ≥ 2`, `σ > 0`, and `M ≤ N`,
`‖∑ n ∈ Finset.Ioc M N, χ n * ((n : ℝ) ^ (-σ) : ℂ)‖ ≤ 4 * √q * log q * (M + 1) ^ (-σ)`. -/
theorem norm_sum_Ioc_char_div_rpow_le {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M N, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤
      4 * Real.sqrt q * Real.log q * ((M + 1 : ℕ) : ℝ) ^ (-σ) := by
  let B : ℝ := 4 * Real.sqrt q * Real.log q
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hB_nonneg : 0 ≤ B := by positivity
  rcases le_or_gt N M with hNM | hMN
  · have hsum0 : Finset.Ioc M N = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hsum0, Finset.sum_empty, norm_zero]
    positivity
  · have htelescope_sum :
        ∑ k ∈ Finset.Ico (M + 1) N, ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) =
          ((M + 1 : ℕ) : ℝ) ^ (-σ) - (N : ℝ) ^ (-σ) := by
      induction N, hMN using Nat.le_induction with
      | base => simp
      | succ K hMK ih =>
        rw [Finset.sum_Ico_succ_top hMK, ih]
        ring
    have htelescope :
        ((N : ℝ) ^ (-σ) +
          ∑ k ∈ Finset.Ico (M + 1) N, ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ))) =
          ((M + 1 : ℕ) : ℝ) ^ (-σ) := by
      rw [htelescope_sum]
      ring
    let S : ℕ → ℂ := fun k ↦ ∑ i ∈ Finset.Ioc M k, χ i
    have hS_bound (k : ℕ) : ‖S k‖ ≤ B := polya_vinogradov_Ioc hq hχ M k
    have hab := abel_discrete_Ioc_from (fun n ↦ χ n) (fun n ↦ (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) hMN.le
    rw [hab]
    have hsplit_Ico : Finset.Ico M N = insert M (Finset.Ico (M + 1) N) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hSM : ∑ i ∈ Finset.Ioc M M, χ i = 0 := by simp
    have hIco_clean :
        ∑ k ∈ Finset.Ico M N,
            (∑ i ∈ Finset.Ioc M k, χ i) *
              (((((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) - (((k : ℝ) ^ (-σ) : ℝ) : ℂ)) =
          ∑ k ∈ Finset.Ico (M + 1) N,
            S k * (((((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) - (((k : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
      rw [hsplit_Ico, Finset.sum_insert (by simp), hSM, zero_mul, zero_add]
    have hrewrite :
        (∑ i ∈ Finset.Ioc M N, χ i) * (((N : ℝ) ^ (-σ) : ℝ) : ℂ) -
            ∑ k ∈ Finset.Ico M N,
              (∑ i ∈ Finset.Ioc M k, χ i) *
                (((((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) - (((k : ℝ) ^ (-σ) : ℝ) : ℂ)) =
          S N * (((N : ℝ) ^ (-σ) : ℝ) : ℂ) +
            ∑ k ∈ Finset.Ico (M + 1) N,
              S k * (((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [hIco_clean, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      change -(S k * (((((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) - (((k : ℝ) ^ (-σ) : ℝ) : ℂ))) =
        S k * (((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)
      push_cast
      ring
    rw [hrewrite]
    have hdiff_nonneg : ∀ k ∈ Finset.Ico (M + 1) N,
        0 ≤ (k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hk_le : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
      have hrpow := Real.rpow_le_rpow_of_nonpos hk_pos hk_le (by linarith : -σ ≤ 0)
      linarith
    calc
      ‖S N * (((N : ℝ) ^ (-σ) : ℝ) : ℂ) +
          ∑ k ∈ Finset.Ico (M + 1) N,
            S k * (((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖
          ≤ ‖S N * (((N : ℝ) ^ (-σ) : ℝ) : ℂ)‖ +
              ‖∑ k ∈ Finset.Ico (M + 1) N,
                S k * (((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ :=
            norm_add_le _ _
      _ ≤ B * (N : ℝ) ^ (-σ) +
            ∑ k ∈ Finset.Ico (M + 1) N, B * ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) := by
          refine add_le_add ?_ ?_
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
            exact mul_le_mul_of_nonneg_right (hS_bound N) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiff_nonneg k hk)]
            exact mul_le_mul_of_nonneg_right (hS_bound k) (hdiff_nonneg k hk)
      _ = B * ((N : ℝ) ^ (-σ) +
            ∑ k ∈ Finset.Ico (M + 1) N, ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ))) := by
          rw [← Finset.mul_sum, ← mul_add]
      _ = B * ((M + 1 : ℕ) : ℝ) ^ (-σ) := by rw [htelescope]

/-- Complex-exponent tail bound via Pólya–Vinogradov and Abel summation:
for `χ ≠ 1` modulo `q ≥ 2`, `s : ℂ` with `0 < s.re`, and `M ≤ N`,
`‖∑ n ∈ Finset.Ioc M N, χ n * (n : ℂ) ^ (-s)‖ ≤ 4 * √q * log q * (1 + ‖s‖ / s.re) * (M + 1) ^ (-s.re)`. -/
theorem norm_sum_Ioc_char_mul_cpow_neg_le {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M N, χ n * (n : ℂ) ^ (-s)‖ ≤
      4 * Real.sqrt q * Real.log q * (1 + ‖s‖ / s.re) * ((M + 1 : ℕ) : ℝ) ^ (-s.re) := by
  let B : ℝ := 4 * Real.sqrt q * Real.log q
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hB_nonneg : 0 ≤ B := by positivity
  rcases le_or_gt N M with hNM | hMN
  · have hsum0 : Finset.Ioc M N = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hsum0, Finset.sum_empty, norm_zero]
    positivity
  · have htelescope :
        ∑ k ∈ Finset.Ico (M + 1) N, ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) =
          ((M + 1 : ℕ) : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re) := by
      induction N, hMN using Nat.le_induction with
      | base => simp
      | succ K hMK ih =>
        rw [Finset.sum_Ico_succ_top hMK, ih]
        ring
    let S : ℕ → ℂ := fun k ↦ ∑ i ∈ Finset.Ioc M k, χ i
    have hS_bound (k : ℕ) : ‖S k‖ ≤ B := polya_vinogradov_Ioc hq hχ M k
    have hab := abel_discrete_Ioc_from (fun n ↦ χ n) (fun n ↦ (n : ℂ) ^ (-s)) hMN.le
    rw [hab]
    have hsplit_Ico : Finset.Ico M N = insert M (Finset.Ico (M + 1) N) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hSM : ∑ i ∈ Finset.Ioc M M, χ i = 0 := by simp
    have hrewrite :
        (∑ i ∈ Finset.Ioc M N, χ i) * (N : ℂ) ^ (-s) -
            ∑ k ∈ Finset.Ico M N,
              (∑ i ∈ Finset.Ioc M k, χ i) * (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)) =
          S N * (N : ℂ) ^ (-s) +
            ∑ k ∈ Finset.Ico (M + 1) N,
              S k * ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)) := by
      rw [hsplit_Ico, Finset.sum_insert (by simp), hSM, zero_mul, zero_add, sub_eq_add_neg,
        ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      change -(S k * (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s))) =
        S k * ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))
      ring
    rw [hrewrite]
    have hnorm_N : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN_pos]
      simp
    have hN_le : (N : ℝ) ^ (-s.re) ≤ ((M + 1 : ℕ) : ℝ) ^ (-s.re) := by
      have hM1_pos : (0 : ℝ) < (M + 1 : ℕ) := by positivity
      have hM1_le : ((M + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
      exact Real.rpow_le_rpow_of_nonpos hM1_pos hM1_le (by linarith)
    have hdiff_le : ∀ k ∈ Finset.Ico (M + 1) N,
        ‖(k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
          (‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      exact norm_cpow_neg_sub_succ_le (by omega : 1 ≤ k) hs
    calc
      ‖S N * (N : ℂ) ^ (-s) +
          ∑ k ∈ Finset.Ico (M + 1) N, S k * ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))‖
          ≤ ‖S N * (N : ℂ) ^ (-s)‖ +
              ‖∑ k ∈ Finset.Ico (M + 1) N, S k * ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))‖ :=
            norm_add_le _ _
      _ ≤ B * ((M + 1 : ℕ) : ℝ) ^ (-s.re) +
            ∑ k ∈ Finset.Ico (M + 1) N,
              B * ((‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
          refine add_le_add ?_ ?_
          · rw [norm_mul, hnorm_N]
            exact mul_le_mul (hS_bound N) hN_le (Real.rpow_nonneg (Nat.cast_nonneg N) _) hB_nonneg
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
            rw [norm_mul]
            exact mul_le_mul (hS_bound k) (hdiff_le k hk) (norm_nonneg _) hB_nonneg
      _ = B * ((M + 1 : ℕ) : ℝ) ^ (-s.re) +
            B * (‖s‖ / s.re) * (((M + 1 : ℕ) : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re)) := by
          have hpull :
              ∑ k ∈ Finset.Ico (M + 1) N,
                  B * ((‖s‖ / s.re) * ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re))) =
                B * (‖s‖ / s.re) *
                  ∑ k ∈ Finset.Ico (M + 1) N,
                    ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            ring
          rw [hpull, htelescope]
      _ ≤ B * ((M + 1 : ℕ) : ℝ) ^ (-s.re) +
            B * (‖s‖ / s.re) * ((M + 1 : ℕ) : ℝ) ^ (-s.re) := by
          have hN_nn : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg N) _
          have hfac_nn : 0 ≤ B * (‖s‖ / s.re) := by positivity
          gcongr
          linarith
      _ = B * (1 + ‖s‖ / s.re) * ((M + 1 : ℕ) : ℝ) ^ (-s.re) := by ring

/-- Partial sum bound at `s = 1` for non-principal characters `χ ≠ 1` modulo `q ≥ 2`:
`‖∑ n ∈ Finset.Icc 1 N, χ n / n‖ ≤ 1 + log q + 4 * log q / √q`. -/
theorem norm_sum_Icc_one_char_div_nat_le {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n / (n : ℂ)‖ ≤
      1 + Real.log q + 4 * Real.log q / Real.sqrt q := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by positivity)
  rcases le_or_gt N q with hNq | hqN
  · calc
      ‖∑ n ∈ Finset.Icc 1 N, χ n / (n : ℂ)‖
          ≤ ∑ n ∈ Finset.Icc 1 N, ‖χ n / (n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          simp only [Finset.mem_Icc] at hn
          rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
          exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
      _ ≤ ∑ n ∈ Finset.Icc 1 q, (n : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hNq)
            (fun _ _ _ ↦ by positivity)
      _ ≤ 1 + Real.log q := sum_Icc_inv_le_one_add_log q (by omega)
      _ ≤ 1 + Real.log q + 4 * Real.log q / Real.sqrt q := by
          linarith [show 0 ≤ 4 * Real.log q / Real.sqrt q by positivity]
  · have hsplit : Finset.Icc 1 N = Finset.Icc 1 q ∪ Finset.Ioc q N := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 q) (Finset.Ioc q N) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have h1 : ‖∑ n ∈ Finset.Icc 1 q, χ n / (n : ℂ)‖ ≤ 1 + Real.log q := by
      calc
        ‖∑ n ∈ Finset.Icc 1 q, χ n / (n : ℂ)‖
            ≤ ∑ n ∈ Finset.Icc 1 q, ‖χ n / (n : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 q, (n : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun n _ ↦ ?_
            rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
            exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
        _ ≤ 1 + Real.log q := sum_Icc_inv_le_one_add_log q (by omega)
    have h2 : ‖∑ n ∈ Finset.Ioc q N, χ n / (n : ℂ)‖ ≤ 4 * Real.log q / Real.sqrt q := by
      have heq : ∑ n ∈ Finset.Ioc q N, χ n / (n : ℂ) =
          ∑ n ∈ Finset.Ioc q N, χ n * (((n : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
      rw [heq]
      have htail := norm_sum_Ioc_char_div_rpow_le hq hχ zero_lt_one q N
      have hM1 : ((q + 1 : ℕ) : ℝ) ^ (-1 : ℝ) ≤ (q : ℝ)⁻¹ := by
        rw [Real.rpow_neg_one]
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.le_succ q)
      have hq_pos : (0 : ℝ) < q := by positivity
      have hsqrt_div : Real.sqrt q / (q : ℝ) = (Real.sqrt q)⁻¹ := by
        have hqsq : (q : ℝ) = Real.sqrt q * Real.sqrt q := (Real.mul_self_sqrt hq_pos.le).symm
        conv_lhs => rhs; rw [hqsq]
        field_simp [hsqrt_pos.ne']
      calc
        ‖∑ n ∈ Finset.Ioc q N, χ n * (((n : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ)‖
            ≤ 4 * Real.sqrt q * Real.log q * ((q + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := htail
        _ ≤ 4 * Real.sqrt q * Real.log q * (q : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left hM1 (by positivity)
        _ = 4 * Real.log q * (Real.sqrt q / (q : ℝ)) := by ring
        _ = 4 * Real.log q / Real.sqrt q := by rw [hsqrt_div, div_eq_mul_inv]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Partial sum bound for `∑ χ(n) / n^σ` with `0 < σ ≤ 1` and arbitrary cutoff `1 ≤ X`:
for `χ ≠ 1` modulo `q ≥ 2`,
`‖∑ n ∈ Finset.Icc 1 N, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤ X ^ (1 - σ) * (1 + log X) + 4 * √q * log q * X ^ (-σ)`. -/
theorem norm_sum_Icc_one_char_div_rpow_le {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {X : ℕ} (hX : 1 ≤ X) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤
      (X : ℝ) ^ (1 - σ) * (1 + Real.log X) +
        4 * Real.sqrt q * Real.log q * (X : ℝ) ^ (-σ) := by
  have hX_pos : (0 : ℝ) < X := by positivity
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hhead_le : ∀ M ≤ X, ‖∑ n ∈ Finset.Icc 1 M, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤
      (X : ℝ) ^ (1 - σ) * (1 + Real.log X) := by
    intro M hMX
    calc
      ‖∑ n ∈ Finset.Icc 1 M, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖
          ≤ ∑ n ∈ Finset.Icc 1 M, ‖χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 M, (X : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          simp only [Finset.mem_Icc] at hn
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn.1
          have hnX : (n : ℝ) ≤ X := by exact_mod_cast hn.2.trans hMX
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hn_pos.le _)]
          have hrpow : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
            rw [sub_eq_add_neg, Real.rpow_add hn_pos, Real.rpow_one]
            field_simp [hn_pos.ne']
          have h1s : (n : ℝ) ^ (1 - σ) ≤ (X : ℝ) ^ (1 - σ) :=
            Real.rpow_le_rpow hn_pos.le hnX (by linarith)
          calc
            ‖χ n‖ * (n : ℝ) ^ (-σ)
                ≤ 1 * (n : ℝ) ^ (-σ) :=
                  mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg hn_pos.le _)
            _ = (n : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by rw [one_mul, hrpow]
            _ ≤ (X : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ :=
                  mul_le_mul_of_nonneg_right h1s (by positivity)
      _ ≤ ∑ n ∈ Finset.Icc 1 X, (X : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hMX)
            (fun _ _ _ ↦ by positivity)
      _ = (X : ℝ) ^ (1 - σ) * ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ (X : ℝ) ^ (1 - σ) * (1 + Real.log X) :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_le_one_add_log X hX)
            (Real.rpow_nonneg hX_pos.le _)
  rcases le_or_gt N X with hNX | hXN
  · exact (hhead_le N hNX).trans (by linarith [show 0 ≤ 4 * Real.sqrt q * Real.log q * (X : ℝ) ^ (-σ) by positivity])
  · have hsplit : Finset.Icc 1 N = Finset.Icc 1 X ∪ Finset.Ioc X N := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Icc 1 X) (Finset.Ioc X N) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail := norm_sum_Ioc_char_div_rpow_le hq hχ hσ0 X N
    have hX1 : ((X + 1 : ℕ) : ℝ) ^ (-σ) ≤ (X : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hX_pos (by exact_mod_cast Nat.le_succ X) (by linarith)
    have htail' : ‖∑ n ∈ Finset.Ioc X N, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤
        4 * Real.sqrt q * Real.log q * (X : ℝ) ^ (-σ) :=
      htail.trans (mul_le_mul_of_nonneg_left hX1 (by positivity))
    exact (norm_add_le _ _).trans (add_le_add (hhead_le X le_rfl) htail')

end PartialSumBounds

end AnalyticNumberTheory.DirichletLFunctions
