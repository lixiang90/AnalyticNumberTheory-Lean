import AnalyticNumberTheory.DirichletLFunctions.VinogradovStrips
import AnalyticNumberTheory.RiemannZeta.HurwitzPoleStrips

/-!
# Classical narrow logarithmic strips

The two classical widths `log L/L` and `(log L)^2/L`, where
`L=log |Im s|`, both lie inside a constant multiple of `L^(-2/3)`.
For periodic L-functions the first period must still be estimated with
the actual width, to preserve the sharper dependence on the modulus.
-/

open Real Complex Finset Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem log_rpow_sixth {L : ℝ} (hL : 1<L) :
    Real.log L≤6*L^(1/6:ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hL) (1/6:ℝ))
  rw [Real.log_rpow (zero_lt_one.trans hL)] at h; linarith

/-- Elementary comparison of the two narrow logarithmic widths with the
two-thirds width. The last inequality is used to simplify the height factor. -/
theorem narrow_logarithmic_widths {L : ℝ} (hL : 1<L) :
    (Real.log L)^2/L≤36/L^(2/3:ℝ) ∧ Real.log L/L≤3/L^(2/3:ℝ) ∧
      L^(2/3:ℝ)≤3*(L/Real.log L) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hL) (1/3:ℝ))
  have hp := zero_lt_one.trans hL
  have hl := Real.log_pos hL
  rw [Real.log_rpow hp] at h
  have h3 : Real.log L≤3*L^(1/3:ℝ) := by linarith
  have h6 := log_rpow_sixth hL
  have hsq := pow_le_pow_left₀ hl.le h6 2
  rw [mul_pow,←Real.rpow_mul_natCast hp.le,show (1/6:ℝ)*(2:ℕ)=1/3 by norm_num] at hsq
  have h1 : L^(1/3:ℝ)*L^(2/3:ℝ)=L := by rw [←Real.rpow_add hp]; norm_num
  have hsq' := mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hp.le (2/3:ℝ))
  have h3' := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hp.le (2/3:ℝ))
  rw [mul_assoc,h1] at hsq' h3'
  refine ⟨(div_le_div_iff₀ hp (Real.rpow_pos_of_pos hp _)).mpr (by linarith only [hsq']),
    (div_le_div_iff₀ hp (Real.rpow_pos_of_pos hp _)).mpr h3',?_⟩
  rw [←mul_div_assoc,le_div_iff₀ hl,mul_comm (L^_)]; exact h3'

private theorem sq_log_div_lt_one {L : ℝ} (hL : 1<L) : (Real.log L)^2/L<1 := by
  have hp := zero_lt_one.trans hL
  have hs := Real.sqrt_pos.mpr hp
  have h := Real.log_le_sub_one_of_pos (show 0<Real.sqrt L/2 by positivity)
  rw [Real.log_div hs.ne' (by norm_num),Real.log_sqrt hp.le] at h
  have h2 : Real.log 2<1 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
  have hlt : Real.log L<Real.sqrt L := by linarith
  rw [div_lt_one hp]
  nlinarith [Real.sq_sqrt hp.le, mul_pos (sub_pos.mpr hlt) (add_pos (Real.log_pos hL) hs)]

/-- On the strip of width `(log log T)^2 / log T`, the regular Hurwitz
part satisfies the stronger two-thirds logarithmic estimate. -/
theorem hurwitzZeta_sub_initial_log_squared_strip :
    ∃ C : ℝ,0<C ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 10≤|s.im| →
      let L := Real.log |s.im|
      1-(Real.log L)^2/L≤s.re →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤C*L^(2/3:ℝ) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_near_one (R:=36) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro a s ha ht; dsimp only; intro hstrip
  have hL : 1<Real.log |s.im| := (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hσ : 0<s.re := by linarith only [sq_log_div_lt_one hL,hstrip]
  exact H ha hσ (by linarith) (by linarith only [hstrip,(narrow_logarithmic_widths hL).1])

/-- The classical bound `log T / log log T` on each strip of width
`R log log T / log T`, uniformly in the shift. -/
theorem hurwitzZeta_sub_initial_log_over_loglog_strip {R : ℝ} (hR : 0≤R) :
    ∃ C : ℝ,0<C ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 0≤s.re → 10≤|s.im| →
      let L := Real.log |s.im|
      1-R*(Real.log L/L)≤s.re →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤C*(L/Real.log L) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_near_one (R:=R*3) (mul_nonneg hR (by norm_num))
  refine ⟨3*C,by positivity,?_⟩
  intro a s ha hσ ht; dsimp only; intro hstrip
  let L := Real.log |s.im|
  have hL : 1<L := (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  obtain ⟨_,hw,hh⟩ := narrow_logarithmic_widths hL
  have h : R*(Real.log L/L)≤R*3/L^(2/3:ℝ) := (mul_le_mul_of_nonneg_left hw hR).trans_eq (by ring)
  let f (u : ℝ) := ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (s+u)-(a:ℂ)^(-(s+u))‖
  have hs : s≠1 := by intro he; norm_num [he] at ht
  have hf : ContinuousAt f 0 := by
    dsimp only [f]; apply ContinuousAt.norm; apply ContinuousAt.sub
    · apply ContinuousAt.comp (f:=fun u : ℝ => s+(u:ℂ)) (HurwitzZeta.differentiableAt_hurwitzZeta _ (by simpa using hs)).continuousAt
      fun_prop
    · simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.1.ne')]; fun_prop
  have hu : ∀ᶠ u : ℝ in 𝓝[>] 0, f u≤3*C*(L/Real.log L) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0<u := hu
    have hz : (s+u).im=s.im := by simp
    have hx := H (s:=s+u) ha (by simp; linarith) (by rw [hz]; linarith)
      (by rw [hz]; change 1-R*3/L^(2/3:ℝ)≤(s+u).re; simp; linarith only [hstrip,h,hu'])
    rw [hz] at hx
    exact hx.trans ((mul_le_mul_of_nonneg_left hh hC.le).trans_eq (by ring))
  simpa [f,L] using le_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds) hu

end AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.RiemannZeta

/-- Preserving the actual logarithmic width gives the conductor contribution
`q^(R log log T / log T)` for arbitrary characters. -/
theorem LFunction_log_over_loglog_strip {R : ℝ} (hR : 0<R) :
    ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      0≤s.re → 10≤|s.im| →
      let L := Real.log |s.im|
      let δ := R*(Real.log L/L)
      1-δ≤s.re → ‖χ.LFunction s‖≤D*(q:ℝ)^δ*(L/Real.log L) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_log_over_loglog_strip hR.le
  refine ⟨C+1+1/R,by positivity,?_⟩
  intro q _ χ s hσ ht
  let L := Real.log |s.im|
  let V := L/Real.log L
  let δ := R*(Real.log L/L)
  have hL : 1<L := (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hl := Real.log_pos hL
  have hV : 1≤V := (le_div_iff₀ hl).mpr (by linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hL)])
  have hδ : 0<δ := by dsimp [δ]; positivity
  change 1-δ≤s.re → ‖χ.LFunction s‖≤(C+1+1/R)*(q:ℝ)^δ*V
  intro hstrip
  have h := periodicLFunction_le_of_regular_hurwitz χ (norm_char_le_one χ) s (fun _ ha => H ha hσ ht hstrip)
  have hq : 1≤q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hd := first_period_power_sum_le hq hδ hσ hstrip
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq : (1:ℝ)≤q) (show 1-s.re≤δ by linarith)
  apply h.trans
  apply (add_le_add hd (mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*V))).trans
  have hh : 1/δ=V/R := by dsimp [δ,V]; field_simp
  rw [hh]
  change _≤(C+1+1/R)*(q:ℝ)^δ*V
  calc _ = (q:ℝ)^δ*(1+V/R+C*V) := by ring
       _ ≤ (q:ℝ)^δ*(V+V/R+C*V) := by gcongr
       _ = _ := by ring

/-- Uniform conductor dependence in the squared-iterated-logarithm strip.
The elementary sum over the first period gives a single logarithm. -/
theorem LFunction_log_squared_strip :
    ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      10≤|s.im| →
      let L := Real.log |s.im|
      let δ := (Real.log L)^2/L
      1-δ≤s.re → ‖χ.LFunction s‖≤D*(q:ℝ)^δ*L := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_log_squared_strip
  let B := Real.log (Real.log 10)
  have h₁ : 1<Real.log 10 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hB : 0<B := Real.log_pos h₁
  refine ⟨C+1+B⁻¹^2,by positivity,?_⟩
  intro q _ χ s ht
  let L := Real.log |s.im|
  let δ := (Real.log L)^2/L
  have hL₀ : Real.log 10≤L := Real.log_le_log (by norm_num) ht
  have hL := h₁.trans_le hL₀
  have hl := Real.log_pos hL
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hBL : B≤Real.log L := Real.log_le_log (by linarith) hL₀
  change 1-δ≤s.re → ‖χ.LFunction s‖≤(C+1+B⁻¹^2)*(q:ℝ)^δ*L
  intro hstrip
  have h := periodicLFunction_le_of_regular_hurwitz χ (norm_char_le_one χ) s (fun _ ha => H ha ht hstrip)
  have hq : 1≤q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hσ : 0<s.re := by linarith only [hstrip,show δ<1 from sq_log_div_lt_one hL]
  have hd := first_period_power_sum_le hq hδ hσ.le hstrip
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq : (1:ℝ)≤q) (show 1-s.re≤δ by linarith)
  have hU := Real.rpow_le_rpow_of_exponent_le hL.le (by norm_num : (2/3:ℝ)≤1)
  rw [Real.rpow_one] at hU
  have hh : 1/δ≤L/B^2 := by
    rw [show 1/δ=L/(Real.log L)^2 by dsimp [δ]; field_simp]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hB.le hBL _)
  apply h.trans
  apply (add_le_add hd (mul_le_mul hpow (mul_le_mul_of_nonneg_left hU hC.le) (by positivity) (by positivity))).trans
  calc _ = (q:ℝ)^δ*(1+1/δ+C*L) := by ring
       _ ≤ (q:ℝ)^δ*(L+L/B^2+C*L) := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL.le hh) le_rfl) (by positivity)
       _ = _ := by ring

/-- The all-height finite derivative estimates for Dirichlet L-functions.
The constants are uniform in the order, period, and character; the pole
contribution is displayed inside the remainder from the first period. -/
theorem LFunction_derivative_strips_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {k : ℕ} {s : ℂ},
      2≤k → 0≤s.re → 1-k/((2:ℝ)^k-2)≤s.re → s≠1 →
      let T := 2+|s.im|
      ‖χ.LFunction s‖≤(∑ n∈Icc 1 q,(n:ℝ)^(-s.re))+(q:ℝ)^(1-s.re)*
        (C*T^(1/((2:ℝ)^k-2))*(1+Real.log T)+16*T^(1-s.re)/(|1-s.re|+|s.im|)) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_derivative_strips_all_heights
  exact ⟨C,hC,fun χ k s hk hσ hline hs => periodicLFunction_le_of_regular_hurwitz χ
    (norm_char_le_one χ) s (fun _ ha => H hk ha hσ hline hs)⟩

end AnalyticNumberTheory.DirichletLFunctions
