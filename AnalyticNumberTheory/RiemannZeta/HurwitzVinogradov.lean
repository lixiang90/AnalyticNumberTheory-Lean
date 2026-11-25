import AnalyticNumberTheory.RiemannZeta.HurwitzVinogradovBlocks
import AnalyticNumberTheory.RiemannZeta.HurwitzApproximation

/-!
# Uniform Vinogradov–Korobov growth for Hurwitz zeta

Subtracting `a^(-s)` removes the singular dependence on the shift. The
resulting estimate has the classical two-thirds logarithmic prefactor
and holds throughout the critical strip and to its right.
-/

open Complex Real Finset Filter
namespace AnalyticNumberTheory.RiemannZeta

/-- Bounded-error truncation of the regular part for lengths between half
and all of the height, uniformly in the shift and the real part. -/
theorem regular_hurwitz_truncation :
    ∃ A : ℝ, 0<A ∧ ∀ {a : ℝ} {N : ℕ} {s : ℂ}, a∈Set.Ioc (0:ℝ) 1 → 1≤N →
      0<s.re → 2≤|s.im| → (N:ℝ)≤|s.im| → |s.im|≤2*N →
      ‖(HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s))-
        ∑ n∈Icc 1 N,((n:ℂ)+a)^(-s)‖≤A := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_approx_dirichletPoly (c:=2) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨K+2,by positivity,?_⟩
  intro a N s ha hN hσ ht hlo hhi
  let M := (N:ℝ)+a
  have hMr : 1≤M := by dsimp [M]; linarith only [ha.1,show (1:ℝ)≤N by exact_mod_cast hN]
  have hM := zero_lt_one.trans_le hMr
  have hs : s≠1 := by rintro rfl; norm_num at ht
  have hTN : |s.im|≤2*M := by dsimp [M]; linarith only [hhi,ha.1]
  have herr := H ha (σ:=s.re) (t:=s.im) (N:=N) hσ (by rwa [Complex.re_add_im]) hTN
  rw [Complex.re_add_im] at herr
  let f (n : ℕ) := ((n:ℂ)+a)^(-s)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s
  let P := ∑ n∈Icc 0 N,f n
  let R := ((M:ℝ):ℂ)^(1-s)/(1-s)
  have HR : ‖Z-(P-R)‖≤K*M^(-s.re) := by simpa [Z,P,R,M,f] using herr
  have hd : |s.im|≤‖1-s‖ := by simpa using Complex.abs_im_le_norm (1-s)
  have hr : ‖R‖≤2 := by
    dsimp [R]
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hM,Complex.sub_re,Complex.one_re,div_le_iff₀ (by linarith : 0<‖1-s‖)]
    have hb := Real.rpow_le_rpow_of_exponent_le hMr (show 1-s.re≤1 by linarith)
    rw [Real.rpow_one] at hb
    dsimp [M] at hb; linarith only [hb,hd,hlo,ht,ha.2]
  have hKG := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hMr (neg_nonpos.mpr hσ.le)) hK.le
  have hpoly : P=(a:ℂ)^(-s)+∑ n∈Icc 1 N,f n := by
    have he : Icc 0 N=insert 0 (Icc 1 N) := by ext n; simp only [mem_Icc,mem_insert]; omega
    simp [P,he,f]
  have Htri := norm_sub_le (Z-(P-R)) R
  rw [show Z-(P-R)-R=Z-P by ring] at Htri
  change ‖Z-(a:ℂ)^(-s)-∑ n∈Icc 1 N,f n‖≤_
  rw [sub_sub,←hpoly]; linarith only [Htri,HR,hKG,hr]

/-- Vinogradov–Korobov growth of the regular part of Hurwitz zeta. The
constants are absolute for all positive shifts at most one and `|Im s|≥2`. -/
theorem hurwitzZeta_sub_initial_vinogradov_bound :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 →
      0<s.re → 2≤|s.im| →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖ ≤
        D*(Real.log |s.im|)^(2/3:ℝ)*Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log |s.im|) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitz_polynomial_vinogradov_bound
  obtain ⟨A,hA,HA⟩ := regular_hurwitz_truncation
  let B := (Real.log 2)^(2/3:ℝ)
  have hB : 0<B := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨K,hK,(A+16)/B+D,by positivity,?_⟩
  intro a s ha hσ ht
  let T := |s.im|
  let N := ⌈T/2⌉₊
  have hT : 2≤T := ht
  have hT₀ : 0<T := by linarith
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hNT : (N:ℝ)≤T := (Nat.ceil_lt_add_one (by positivity : 0≤T/2)).le.trans (by linarith)
  have hTN : T≤2*N := by linarith only [Nat.le_ceil (T/2)]
  let E := Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log T)
  let L := (Real.log T)^(2/3:ℝ)
  have hlog := Real.log_pos (by linarith : 1<T)
  have hE : 1≤E := Real.one_le_exp (by positivity)
  have hL : B≤L := Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) hT) (by norm_num)
  have hdom : A+16≤((A+16)/B)*L*E := by
    calc A+16=((A+16)/B)*B := by field_simp
         _ ≤ ((A+16)/B)*L := mul_le_mul_of_nonneg_left hL (by positivity)
         _ ≤ _ := le_mul_of_one_le_right (by positivity) hE
  let P := ∑ n∈Icc 1 N,((n:ℂ)+a)^(-s)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)
  have herr : ‖Z-P‖≤A := HA ha hN hσ ht hNT hTN
  have htri := norm_add_le (Z-P) P
  rw [sub_add_cancel] at htri
  change ‖Z‖≤((A+16)/B+D)*L*E
  by_cases hb : 16≤T
  · have H' := H (t:=s.im) ha hσ.le hb hN hNT
    rw [Complex.re_add_im] at H'
    change ‖P‖≤D*L*E at H'
    linarith only [herr,htri,H',hdom]
  · have hp : ‖P‖≤(N:ℝ) := by
      apply (norm_sum_le ..).trans
      calc _ ≤ ∑ _n∈Icc 1 N,(1:ℝ) := by
                 apply sum_le_sum; intro n hn
                 have h₁ : 1≤(n:ℝ)+a := by linarith only [ha.1,show (1:ℝ)≤n by exact_mod_cast (mem_Icc.mp hn).1]
                 rw [←Complex.ofReal_natCast,←Complex.ofReal_add,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le h₁),Complex.neg_re]
                 exact Real.rpow_le_one_of_one_le_of_nonpos h₁ (neg_nonpos.mpr hσ.le)
           _ = _ := by simp
    have hpos : 0≤D*L*E := by dsimp [L,E]; positivity
    linarith only [herr,htri,hp,hNT,lt_of_not_ge hb,hdom,hpos]

/-- The two-thirds logarithmic Vinogradov bound for Riemann zeta. -/
theorem riemannZeta_vinogradov_bound :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {s : ℂ},0<s.re → 2≤|s.im| →
      ‖riemannZeta s‖≤D*(Real.log |s.im|)^(2/3:ℝ)*
        Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log |s.im|) := by
  obtain ⟨K,hK,D,hD,H⟩ := hurwitzZeta_sub_initial_vinogradov_bound
  let B := (Real.log 2)^(2/3:ℝ)
  have hB : 0<B := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨K,hK,D+1/B,by positivity,?_⟩
  intro s hσ ht
  have h := H (a:=1) (s:=s) ⟨zero_lt_one,le_rfl⟩ hσ ht
  simp only [Complex.ofReal_one,Complex.one_cpow,AddCircle.coe_period,HurwitzZeta.hurwitzZeta_zero] at h
  let E := Real.exp (K*(max (1-s.re) 0)^(3/2:ℝ)*Real.log |s.im|)
  let L := (Real.log |s.im|)^(2/3:ℝ)
  have hl := Real.log_nonneg (by linarith : 1≤|s.im|)
  have hE : 1≤E := Real.one_le_exp (by positivity)
  have hL : B≤L := Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) ht) (by norm_num)
  have hB' := mul_le_mul hL hE zero_le_one (by positivity : 0≤L)
  have h1 := (le_div_iff₀ hB).mpr (by simpa using hB' : 1*B≤L*E)
  have htri := norm_add_le (riemannZeta s-1) 1
  rw [sub_add_cancel,norm_one] at htri
  change ‖riemannZeta s-1‖≤D*L*E at h
  change ‖riemannZeta s‖≤(D+1/B)*L*E
  calc _ ≤ D*L*E+L*E/B := htri.trans (add_le_add h h1)
       _ = _ := by ring

end AnalyticNumberTheory.RiemannZeta
