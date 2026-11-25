import AnalyticNumberTheory.DirichletLFunctions.GaussianPolynomialShift

/-!
# The balanced critical-line integral

On the positive line the tail after length `X` has norm at most
`4 X^(-1/4)`. Shifting the initial polynomial across zero yields its
central value and a negative-line integral. The three terms have size
at most a constant times `sqrt X`.
-/

open Real Complex Finset MeasureTheory Filter
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

/-- A right-line integral of any Dirichlet L-function has critical size
at most the square root of the balanced conductor length. -/
theorem norm_completedLGaussianIntegral_critical :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      let s := (1/2:ℂ)+t*I
      ‖completedLGaussianIntegral χ s (3/4)/χ.gammaFactor s‖≤C*(conductorLength q t)^(1/2:ℝ) := by
  obtain ⟨U,hU,HU⟩ := norm_characterGaussianMean_le (c:=3/4) (by norm_num) (by norm_num)
  obtain ⟨V,hV,HV⟩ := norm_characterGaussianMean_le (c:=-(1/4)) (by norm_num) (by norm_num)
  refine ⟨4*U+6*V+12*π,by positivity,?_⟩
  intro q _ χ t
  let s := (1/2:ℂ)+t*I
  let X := conductorLength q t
  let N := ⌈X⌉₊
  have hX : 1≤X := one_le_conductorLength t
  have hx := zero_lt_one.trans_le hX
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr hx
  have hXN : X≤(N:ℝ) := Nat.le_ceil _
  have hNX : (N:ℝ)≤2*X := (Nat.ceil_lt_add_one hx.le).le.trans (by linarith)
  let P := dirichletPoly (fun n : ℕ => χ n) N
  let R (z : ℂ) := χ.LFunction z-P z
  let line (c v : ℝ) := s+((c:ℂ)+v*I)
  have hline (c v : ℝ) : (line c v).re=1/2+c := by simp [line,s]
  have hRN (v : ℝ) : ‖R (line (3/4) v)‖≤4*X^(-(1/4):ℝ) := by
    have h := norm_LFunction_sub_polynomial_absolute χ hN (s:=line (3/4) v) (by rw [hline]; norm_num)
    rw [hline] at h
    norm_num only [show 1-(1/2+3/4:ℝ)=-(1/4) by norm_num,show (1/2+3/4:ℝ)-1=1/4 by norm_num] at h
    apply h.trans
    have hh := Real.rpow_le_rpow_of_nonpos hx hXN (by norm_num : -(1/4:ℝ)≤0)
    linarith only [hh]
  have hNP {r : ℝ} (hr₀ : 0≤r) (hr : r≤1) : (N:ℝ)^r≤2*X^r := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg N) hNX hr₀
    rw [Real.mul_rpow (by norm_num) hx.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hr) (by positivity))
  have hPneg (v : ℝ) : ‖P (line (-(1/4)) v)‖≤6*X^(3/4:ℝ) := by
    have h := norm_characterPolynomial_le χ hN (s:=line (-(1/4)) v)
      (by rw [hline]; norm_num) (by rw [hline]; norm_num)
    rw [hline] at h
    norm_num at h
    linarith only [h,hNP (r:=3/4) (by norm_num) (by norm_num),Real.rpow_nonneg hx.le (3/4:ℝ)]
  have hP₀ : ‖P s‖≤6*X^(1/2:ℝ) := by
    have h := norm_characterPolynomial_le χ hN (s:=s) (by norm_num [s]) (by norm_num [s])
    norm_num [s] at h
    change ‖P s‖≤_
    linarith only [h,hNP (r:=1/2) (by norm_num) (by norm_num)]
  have hPr (v : ℝ) : ‖P (line (3/4) v)‖≤N := by
    apply (norm_characterPolynomial_le_power_sum χ N _).trans
    calc _ ≤ ∑ _n∈Icc 1 N,(1:ℝ) := by
                apply sum_le_sum; intro n hn
                apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (mem_Icc.mp hn).1)
                rw [hline]; norm_num
         _ = _ := by simp
  have hcP : Continuous P := (differentiable_dirichletPoly _ _).continuous
  have hcLine (c : ℝ) : Continuous (line c) := by dsimp [line]; fun_prop
  have hcL : Continuous (fun v => χ.LFunction (line (3/4) v)) := by
    apply continuous_iff_continuousAt.mpr; intro v
    apply (DirichletCharacter.differentiableAt_LFunction χ _ ?_).continuousAt.comp (hcLine _).continuousAt
    left; intro h; have := congrArg Complex.re h; rw [hline] at this; norm_num at this
  have hcR := hcL.sub (hcP.comp (hcLine (3/4)))
  have hiR := integrable_characterGaussianMean χ t (c:=3/4) (by norm_num) (by norm_num)
    R (by positivity : 0≤4*X^(-(1/4):ℝ)) hcR hRN
  have hiP := integrable_characterGaussianMean χ t (c:=3/4) (by norm_num) (by norm_num)
    P (Nat.cast_nonneg N) (hcP.comp (hcLine _)) hPr
  have hsum : characterGaussianMean χ t (3/4) χ.LFunction =
      characterGaussianMean χ t (3/4) R+characterGaussianMean χ t (3/4) P := by
    unfold characterGaussianMean
    rw [←integral_add hiR hiP]
    apply integral_congr_ae; filter_upwards with v; dsimp [R]; ring
  have hres := characterGaussianMean_polynomial_shift χ N t
  change characterGaussianMean χ t (3/4) P-characterGaussianMean χ t (-(1/4)) P=2*π*P s at hres
  have hpos := HU χ t R (by positivity) hRN
  have hneg := HV χ t P (by positivity) hPneg
  change ‖characterGaussianMean χ t (3/4) R‖≤U*X^(3/4:ℝ)*(4*X^(-(1/4):ℝ)) at hpos
  change ‖characterGaussianMean χ t (-(1/4)) P‖≤V*X^(-(1/4):ℝ)*(6*X^(3/4:ℝ)) at hneg
  have hpow : X^(3/4:ℝ)*X^(-(1/4):ℝ)=X^(1/2:ℝ) := by rw [←Real.rpow_add hx]; norm_num
  have hpos' := hpos.trans_eq (show U*X^(3/4:ℝ)*(4*X^(-(1/4):ℝ))=4*U*X^(1/2:ℝ) by rw [←hpow]; ring)
  have hneg' := hneg.trans_eq (show V*X^(-(1/4):ℝ)*(6*X^(3/4:ℝ))=6*V*X^(1/2:ℝ) by rw [←hpow]; ring)
  dsimp only
  rw [completedLGaussianIntegral_div_eq χ t (c:=3/4) (by norm_num),hsum,
    show characterGaussianMean χ t (3/4) P = 2*π*P s+characterGaussianMean χ t (-(1/4)) P by linear_combination hres]
  apply (norm_add_le ..).trans
  apply (add_le_add hpos' ((norm_add_le ..).trans (add_le_add (le_of_eq rfl) hneg'))).trans
  rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  change _≤(4*U+6*V+12*π)*X^(1/2:ℝ)
  nlinarith only [mul_le_mul_of_nonneg_left hP₀ (by positivity : 0≤2*π)]

end AnalyticNumberTheory.DirichletLFunctions
