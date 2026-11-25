import AnalyticNumberTheory.DirichletLFunctions.VinogradovStrips

/-!
# Weyl growth at every critical height

On bounded height intervals the first Hurwitz term is the only possible
loss as the shift approaches zero. This gives all-height Weyl estimates
for the regular part and, after summing one period, for all characters.
-/

open Complex Real Finset
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.RiemannZeta

private theorem hurwitz_regular_bounded_critical :
    ∃ C : ℝ,0<C ∧ ∀ {a t : ℝ},a∈Set.Ioc (0:ℝ) 1 → |t|≤8 →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)-(a:ℂ)^(-((1/2:ℂ)+t*I))‖≤C := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_approx_dirichletPoly (c:=2) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨K+14,by positivity,?_⟩
  intro a t ha ht
  let s := (1/2:ℂ)+t*I
  have hs : s.re=1/2 := by simp [s]
  have hne : s≠1 := by intro h; rw [h] at hs; norm_num at hs
  let M := (4:ℝ)+a
  have hM : 1≤M := by dsimp [M]; linarith only [ha.1]
  have hM₀ := zero_lt_one.trans_le hM
  let f (n : ℕ) := ((n:ℂ)+a)^(-s)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let R := ((M:ℝ):ℂ)^(1-s)/(1-s)
  have HH := H ha (σ:=1/2) (t:=t) (N:=4) (by norm_num) (by simpa [s] using hne)
    (by norm_num; linarith only [ht,ha.1])
  have hb : ‖Z-((∑ n∈Icc 0 4,f n)-R)‖≤K*M^(-(1/2):ℝ) := by simpa [Z,f,R,M,s] using HH
  have hpoly : (∑ n∈Icc 0 4,f n)=f 0+∑ n∈Icc 1 4,f n := by
    rw [show Icc 0 4=insert 0 (Icc 1 4) by decide,sum_insert (by decide)]
  have hhead : f 0=(a:ℂ)^(-s) := by simp [f]
  let P := ∑ n∈Icc 1 4,f n
  have hP : ‖P‖≤4 := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑ _n∈Icc 1 4,(1:ℝ) := by
                apply sum_le_sum; intro n hn
                have hbase : 1≤(n:ℝ)+a := by linarith only [ha.1,show (1:ℝ)≤n by exact_mod_cast (mem_Icc.mp hn).1]
                dsimp only [f]
                rw [←Complex.ofReal_natCast,←Complex.ofReal_add,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hbase),Complex.neg_re,hs]
                exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
         _ = _ := by norm_num
  have hr : ‖R‖≤10 := by
    have hd : 1/2≤‖1-s‖ := by
      have hh := Complex.re_le_norm (1-s)
      rw [Complex.sub_re,Complex.one_re,hs] at hh; linarith
    dsimp only [R]; rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hM₀,Complex.sub_re,Complex.one_re,hs,div_le_iff₀ (by linarith)]
    have h := Real.rpow_le_rpow_of_exponent_le hM (by norm_num : 1-(1/2:ℝ)≤1)
    rw [Real.rpow_one] at h
    dsimp [M] at h; linarith only [h,ha.2,hd]
  have hK' := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hM (by norm_num : -(1/2:ℝ)≤0)) hK.le
  rw [hpoly,hhead] at hb
  change ‖Z-((a:ℂ)^(-s)+P-R)‖≤_ at hb
  have htri := norm_sub_le (Z-((a:ℂ)^(-s)+P-R)+P) R
  have htr' := norm_add_le (Z-((a:ℂ)^(-s)+P-R)) P
  rw [show Z-((a:ℂ)^(-s)+P-R)+P-R=Z-(a:ℂ)^(-s) by ring] at htri
  change ‖Z-(a:ℂ)^(-s)‖≤_
  linarith only [htri,htr',hP,hr,hK',hb]

/-- Uniform all-height Weyl growth of the regular part of Hurwitz zeta. -/
theorem hurwitzZeta_sub_initial_weyl_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {a t : ℝ},a∈Set.Ioc (0:ℝ) 1 →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)-(a:ℂ)^(-((1/2:ℂ)+t*I))‖≤
        C*(2+|t|)^(1/6:ℝ)*(1+Real.log (2+|t|)) := by
  obtain ⟨A,hA,H⟩ := hurwitzZeta_sub_initial_weyl_bound
  obtain ⟨B,hB,HB⟩ := hurwitz_regular_bounded_critical
  refine ⟨A+B,by positivity,?_⟩
  intro a t ha
  let T := 2+|t|
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg t]
  have hlog := Real.log_nonneg hT
  have hpow := Real.one_le_rpow hT (by norm_num : 0≤(1/6:ℝ))
  by_cases ht : 2*π≤|t|
  · have ht' : 1≤|t| := by linarith [Real.pi_gt_three]
    have hl := Real.log_nonneg ht'
    have hh : |t|≤T := by dsimp [T]; linarith
    apply (H ha ht).trans
    change _≤(A+B)*T^(1/6:ℝ)*(1+Real.log T)
    gcongr <;> first | linarith | exact zero_lt_one.trans_le ht'
  · have h := HB ha (by linarith [Real.pi_le_four] : |t|≤8)
    have hh := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hpow (by linarith : 1≤1+Real.log T)) hB.le
    change _≤(A+B)*T^(1/6:ℝ)*(1+Real.log T)
    nlinarith only [h,hh,show 0≤A*T^(1/6:ℝ)*(1+Real.log T) by positivity]

end AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Weyl's height exponent for all characters and all critical heights,
uniformly in the modulus. -/
theorem LFunction_weyl_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖χ.LFunction ((1/2:ℂ)+t*I)‖≤C*(q:ℝ)^(1/2:ℝ)*(2+|t|)^(1/6:ℝ)*(1+Real.log (2+|t|)) := by
  obtain ⟨A,hA,H⟩ := RiemannZeta.hurwitzZeta_sub_initial_weyl_all_heights
  refine ⟨A+3,by positivity,?_⟩
  intro q _ χ t
  let s := (1/2:ℂ)+t*I
  have hs : s.re=1/2 := by simp [s]
  have h := periodicLFunction_le_of_regular_hurwitz χ (norm_char_le_one χ) s (fun a ha => H (t:=t) ha)
  have hq : 1≤q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hp := first_period_power_sum_le hq (δ:=1/2) (σ:=1/2) (by norm_num) (by norm_num) (by norm_num)
  rw [hs] at h; norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at h
  let T := 2+|t|
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg t]
  have he := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT (by norm_num : 0≤(1/6:ℝ)))
    (by linarith [Real.log_nonneg hT] : 1≤1+Real.log T)
  have hdom := mul_le_mul_of_nonneg_left he (by positivity : 0≤3*(q:ℝ)^(1/2:ℝ))
  change ‖χ.LFunction s‖≤(A+3)*(q:ℝ)^(1/2:ℝ)*T^(1/6:ℝ)*(1+Real.log T)
  change ‖χ.LFunction s‖≤_+(q:ℝ)^(1/2:ℝ)*(A*T^(1/6:ℝ)*(1+Real.log T)) at h
  norm_num at hp
  nlinarith only [h,hp,hdom]

end AnalyticNumberTheory.DirichletLFunctions
