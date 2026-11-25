import AnalyticNumberTheory.RiemannZeta.HurwitzDerivativeBounds

/-!
# Uniformity in the order of the finite derivative estimates

A cubic polynomial in the differentiation order is eventually smaller
than an exponential. Consequently Vinogradov's bound gives the finite
derivative estimate with an absolute constant at all sufficiently high
orders. Only finitely many low-order constants have to be enlarged.
-/

open Complex Real Finset Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem eventually_order_cube_le (K : ℝ) :
    ∀ᶠ k : ℕ in atTop,K^2*(k:ℝ)^3≤(2:ℝ)^k-2 := by
  have H := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1:ℝ)<2)
  have h := H.const_mul (K^2)
  simp only [mul_zero] at h
  filter_upwards [h.eventually_le_const (by norm_num : (0:ℝ)<1/2),eventually_ge_atTop (2:ℕ)] with k hk hk'
  have hp : (4:ℝ)≤2^k := (by norm_num : (4:ℝ)=2^2).le.trans (pow_le_pow_right₀ (by norm_num) hk')
  have hkp : K^2*(k:ℝ)^3≤(1/2:ℝ)*2^k := (div_le_iff₀ (by positivity)).mp (by
    change K^2*((k:ℝ)^3/2^k)≤1/2 at hk
    rwa [mul_div_assoc])
  linarith

private theorem three_halves_le_reciprocal {K Q m : ℝ} (hQ : 0<Q) (hm : 0≤m)
    (h : K^2*m^3≤Q) : K*(m/Q)^(3/2:ℝ)≤1/Q := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow,←Real.rpow_mul_natCast (div_nonneg hm hQ.le)]
  rw [show (3/2:ℝ)*(2:ℕ)=(3:ℕ) by norm_num,Real.rpow_natCast,div_pow]
  calc _ = (K^2*m^3)/Q^3 := by ring
       _ ≤ Q/Q^3 := div_le_div_of_nonneg_right h (by positivity)
       _ = _ := by field_simp

/-- For all orders `k≥2` simultaneously, the regular part of Hurwitz
zeta is bounded by an absolute constant times
`T^(1/(2^k−2)) (1+log T)` to the right of `1−k/(2^k−2)`. -/
theorem hurwitzZeta_sub_initial_derivative_strips :
    ∃ C : ℝ,0<C ∧ ∀ {k : ℕ} {a : ℝ} {s : ℂ},2≤k → a∈Set.Ioc (0:ℝ) 1 →
      0<s.re → 1-k/((2:ℝ)^k-2)≤s.re → 2≤|s.im| →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        C*|s.im|^(1/((2:ℝ)^k-2))*(1+Real.log |s.im|) := by
  classical
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_order_cube_le K)
  choose C hC HC using fun j : ℕ => hurwitzZeta_sub_initial_higher_derivative (k:=max 2 j) (le_max_left ..)
  let B := ∑ j∈range N,C j
  have hB : 0≤B := sum_nonneg (fun j _ => (hC j).le)
  refine ⟨D+B,by positivity,?_⟩
  intro k a s hk ha hσ hline ht
  let T := |s.im|
  let L := Real.log T
  let Q := (2:ℝ)^k-2
  have hQ : 0<Q := by
    dsimp [Q]
    linarith only [(by norm_num : (4:ℝ)=2^2).le.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk)]
  have ht₀ : 0<T := by change 2≤T at ht; linarith
  have hL : 0≤L := Real.log_nonneg (by change 2≤T at ht; linarith)
  let V := T^(1/Q)
  have hV : 0<V := Real.rpow_pos_of_pos ht₀ _
  change ‖_‖≤(D+B)*V*(1+L)
  by_cases hn : k<N
  · have hp := HC k (a:=a) (s:=s)
    rw [max_eq_right hk] at hp
    apply (hp ha hσ hline ht).trans
    have hCB : C k≤B := single_le_sum (fun j _ => (hC j).le) (mem_range.mpr hn)
    change C k*V*(1+L)≤_
    gcongr; linarith
  · have hη : max (1-s.re) 0≤(k:ℝ)/Q := max_le (by linarith only [hline]) (by positivity)
    have hthree := three_halves_le_reciprocal hQ (Nat.cast_nonneg k) (hN k (le_of_not_gt hn))
    have h := (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_max_right ..) hη (by norm_num : 0≤(3/2:ℝ))) hK.le).trans hthree
    have hexp : Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*L)≤V := by
      rw [show V=Real.exp (L*(1/Q)) from Real.rpow_def_of_pos ht₀ _]
      exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right h hL).trans_eq (mul_comm ..))
    have hlog : L^(2/3:ℝ)≤1+L := by
      rcases le_total 1 L with hh|hh
      · have hz := Real.rpow_le_rpow_of_exponent_le hh (by norm_num : (2/3:ℝ)≤1)
        rw [Real.rpow_one] at hz; linarith
      · have hz := Real.rpow_le_one hL hh (by norm_num : 0≤(2/3:ℝ))
        linarith
    apply (H ha hσ ht).trans
    change D*L^(2/3:ℝ)*Real.exp _≤_
    calc _ ≤ D*(1+L)*V := by gcongr
         _ = D*V*(1+L) := by ring
         _ ≤ _ := by gcongr; linarith

end AnalyticNumberTheory.RiemannZeta
