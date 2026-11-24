import AnalyticNumberTheory.ExponentialSums.VaughanIdentity
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialMoments

/-!
# Logarithmic mean-square bounds for divisor polynomials

Partial summation uses the second moment of the divisor function on
initial intervals. On a block away from zero a decreasing power is
bounded by its value at the left endpoint.
-/

open Real Complex Finset Filter MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods
open scoped Topology

namespace AnalyticNumberTheory.RiemannZeta

private theorem partial_sum_weight_bound {a w : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (hA : ∀ k, k≤N → ∑ n ∈ Ioc 0 k, a n ≤ B*k) (hw0 : ∀ n, 0≤w n)
    (hw : ∀ k, 1≤k → w (k+1)≤w k) :
    ∑ n ∈ Ioc 0 N, a n*w n ≤ B*∑ n ∈ Ioc 0 N, w n := by
  let S (k : ℕ) := ∑ n ∈ Ioc 0 k, a n
  let R (k : ℕ) := (∑ n ∈ Ioc 0 k, a n*w n)-B*∑ n ∈ Ioc 0 k, w n
  have aux (k : ℕ) (hk : k≤N) : R k ≤ (S k-B*k)*w k := by
    induction k with
    | zero => simp [R,S]
    | succ k ih =>
      have h := ih (by omega)
      have hb : S k-B*k ≤ 0 := sub_nonpos.mpr (hA k (by omega))
      have hstep : (S k-B*k)*w k ≤ (S k-B*k)*w (k+1) := by
        cases k with
        | zero => simp [S]
        | succ j => exact mul_le_mul_of_nonpos_left (hw (j+1) (Nat.succ_pos _)) hb
      dsimp only [R,S] at h hstep ⊢
      simp only [sum_Ioc_succ_top (Nat.zero_le _),Nat.cast_add,Nat.cast_one]
      linarith only [h,hstep]
  exact sub_nonpos.mp ((aux N le_rfl).trans (mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hA N le_rfl)) (hw0 N)))

private theorem divisor_diagonal_compare {N : ℕ} (hN : 1≤N) {s : ℝ} (hs : 0≤s) :
    ∑ n ∈ Icc 1 N, (n.divisors.card:ℝ)^2*(n:ℝ)^(-s) ≤
      (1+Real.log N)^3*∑ n ∈ Icc 1 N, (n:ℝ)^(-s) := by
  let B := (1+Real.log N)^3
  have he (k : ℕ) : Ioc 0 k = Icc 1 k := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  have hA (k : ℕ) (hk : k≤N) : ∑ n ∈ Ioc 0 k, (n.divisors.card:ℝ)^2 ≤ B*k := by
    rw [he,mul_comm B]
    apply (sum_Icc_card_divisors_sq_le k).trans
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 3) (Nat.cast_nonneg k)
    · have : (1:ℝ)≤(max k 1:ℕ) := by exact_mod_cast le_max_right k 1
      linarith [Real.log_nonneg this]
    · apply add_le_add_right
      have hpos : (0:ℕ)<max k 1 := by omega
      apply Real.log_le_log (by exact_mod_cast hpos)
      exact_mod_cast max_le hk hN
  simpa only [he,B] using partial_sum_weight_bound hA (w:=fun n : ℕ => (n:ℝ)^(-s))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n hn => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by exact_mod_cast n.le_succ) (neg_nonpos.mpr hs))

/-- The critical-line diagonal of the divisor polynomial is bounded by
the fourth power of the logarithmic weight. -/
theorem divisor_diagonal_critical {N : ℕ} (hN : 1≤N) :
    ∑ n ∈ Icc 1 N, (n.divisors.card:ℝ)^2*(n:ℝ)^(-(1:ℝ)) ≤ (1+Real.log N)^4 := by
  have h := divisor_diagonal_compare hN (s:=1) zero_le_one
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hw := sum_inv_le_one_add_log hn
  rw [Nat.floor_natCast] at hw
  simp only [Real.rpow_neg_one] at h ⊢
  exact h.trans ((mul_le_mul_of_nonneg_left hw (by positivity [Real.log_nonneg hn])).trans_eq (by ring))

/-- On the line `Re s = 1/4` the diagonal growth is at most
`2 √N (1+log N)^3`. -/
theorem divisor_diagonal_quarter {N : ℕ} (hN : 1≤N) :
    ∑ n ∈ Icc 1 N, (n.divisors.card:ℝ)^2*(n:ℝ)^(-(1/2):ℝ) ≤ 2*√N*(1+Real.log N)^3 := by
  have h := divisor_diagonal_compare hN (s:=1/2) (by norm_num)
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hw : ∑ n ∈ Icc 1 N, (n:ℝ)^(-(1/2):ℝ) ≤ 2*√N := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _) _,← Real.sqrt_eq_rpow] using sum_Icc_inv_sqrt_le N
  exact h.trans ((mul_le_mul_of_nonneg_left hw (by positivity [Real.log_nonneg hn])).trans_eq (by ring))

private theorem divisor_vertical_diagonal {N : ℕ} {σ a b : ℝ} (hab : a≤b) :
    (∫ t in a..b, ‖divisorPolynomial N ((σ:ℂ)+t*I)‖^2) ≤
      (b-a+2*π*N)*∑ n ∈ Icc 1 N, (n.divisors.card:ℝ)^2*(n:ℝ)^(-2*σ) := by
  have h := dirichletPoly_mean_sq_asymp (fun n => (n.divisors.card:ℂ)) N σ hab
  simp only [Real.norm_eq_abs,Complex.norm_natCast] at h
  unfold divisorPolynomial
  linarith only [(abs_le.mp h).2]

private theorem ceil_log_bounds {T : ℝ} (hT : 2≤T) :
    let N := ⌈T⌉₊
    1≤N ∧ (N:ℝ)≤2*T ∧ 1+Real.log N ≤ 2*(1+Real.log T) := by
  have ht : 0<T := by linarith
  have hn : (⌈T⌉₊:ℝ) ≤ 2*T := by linarith [Nat.ceil_lt_add_one ht.le]
  have hn' := Nat.one_le_ceil_iff.mpr ht
  refine ⟨hn',hn,?_⟩
  have h := Real.log_le_log (by exact_mod_cast hn' : 0<(⌈T⌉₊:ℝ)) hn
  rw [Real.log_mul (by norm_num) ht.ne'] at h
  linarith [Real.log_nonneg (by linarith : 1≤T),Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

/-- A length-`⌈T⌉` divisor polynomial on the critical line has dyadic
mean square `O(T (1+log T)^4)`. -/
theorem divisorPolynomial_critical_dyadic_log {T : ℝ} (hT : 2≤T) :
    (∫ t in T..2*T, ‖divisorPolynomial ⌈T⌉₊ ((1/2:ℂ)+t*I)‖^2) ≤
      (16*(1+4*π))*T*(1+Real.log T)^4 := by
  obtain ⟨hn,hN,hl⟩ := ceil_log_bounds hT
  have h := divisor_vertical_diagonal (N:=⌈T⌉₊) (σ:=1/2) (a:=T) (b:=2*T) (by linarith)
  simp only [show -2*(1/2:ℝ) = -1 by norm_num,show 2*T-T=T by ring,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h
  apply h.trans
  have hb : T+2*π*⌈T⌉₊ ≤ (1+4*π)*T := by nlinarith only [mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
  have hnlog := Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤⌈T⌉₊)
  have htlog := Real.log_nonneg (by linarith : 1≤T)
  have hd := (divisor_diagonal_critical hn).trans (pow_le_pow_left₀ (by linarith) hl 4)
  exact (mul_le_mul hb hd (sum_nonneg fun n _ => by positivity) (by positivity)).trans_eq (by ring)

/-- The negative-shift Gaussian contribution of the short divisor polynomial
has dyadic mean square `O(K² T (1+log T)^3)`. -/
theorem divisorPolynomial_quarter_gaussian_log {T K : ℝ} (hT : 2≤T) (hK : 0≤K)
    (negative : Bool) (F : ℝ → ℝ → ℂ)
    (hF : ∀ t ∈ Set.Ioc T (2*T), ∀ v, ‖F t v‖ ≤ K*T^(-(1/4):ℝ)*Real.exp (-(1/2:ℝ)*v^2)) :
    (∫ t in T..2*T, ‖∫ v, F t v*divisorPolynomial ⌈T⌉₊
      ((1/4:ℂ)+((if negative then v-t else v+t):ℝ)*I)‖^2) ≤
      (64*π*(1+4*π))*K^2*T*(1+Real.log T)^3 := by
  obtain ⟨hn,hN,hl⟩ := ceil_log_bounds hT
  let N := ⌈T⌉₊
  have ht : 0<T := by linarith
  let p := fun u : ℝ => divisorPolynomial N (((1/4:ℝ):ℂ)+u*I)
  have hc : Continuous p := divisorPolynomial_continuous ..
  have he (a b : ℝ) (hab : b-a=T) :
      (∫ u in a..b, ‖p u‖^2) ≤ (1+4*π)*T*(32*√T)*(1+Real.log T)^3 := by
    have h := divisor_vertical_diagonal (N:=N) (σ:=1/4) (a:=a) (b:=b) (by linarith)
    rw [hab,show -2*(1/4:ℝ) = -(1/2) by norm_num] at h
    apply h.trans
    have hb : T+2*π*N ≤ (1+4*π)*T := by dsimp [N]; nlinarith only [mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
    have hd := divisor_diagonal_quarter hn
    have hs : √(N:ℝ) ≤ 2*√T := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (Nat.cast_nonneg _),mul_pow,Real.sq_sqrt ht.le]
      nlinarith only [hN,ht]
    have hl0 := Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤⌈T⌉₊)
    have hd' := hd.trans (mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2))
      (pow_le_pow_left₀ (by linarith) hl 3) (by positivity) (by positivity))
    exact (mul_le_mul hb hd' (sum_nonneg fun n _ => by positivity) (by positivity)).trans_eq (by ring)
  have h := AnalyticTools.gaussian_shifted_dyadic_mean ht.le (mul_nonneg hK (Real.rpow_nonneg ht.le _))
    p hc (divisorPolynomial_vertical_bounded ..) he negative F hF
  simp only [p,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,N] at h
  apply h.trans_eq
  have hpow : (T^(-(1/4):ℝ))^2*√T = 1 := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast ht.le,← Real.rpow_add ht]
    norm_num
  linear_combination 64*π*(1+4*π)*K^2*T*(1+Real.log T)^3*hpow

/-- A divisor block on any line of nonnegative real part. -/
theorem divisorPolynomial_block_vertical {X Y : ℕ} {σ : ℝ} (hσ : 0≤σ) (hXY : X≤Y) (hX : 1≤X) {a b : ℝ} (hab : a≤b) :
    (∫ t in a..b, ‖divisorPolynomial Y ((σ:ℂ)+t*I)-
        divisorPolynomial X ((σ:ℂ)+t*I)‖^2) ≤
      (b-a+2*π*Y)*((Y:ℝ)*(1+Real.log Y)^3/(X:ℝ)^(2*σ)) := by
  let c := fun n : ℕ => if X<n then (n.divisors.card:ℂ) else 0
  have he (s : ℂ) : divisorPolynomial Y s-divisorPolynomial X s = dirichletPoly c Y s := by
    let f := fun n : ℕ => (n.divisors.card:ℂ)*(n:ℂ)^(-s)
    have hfilter : (Icc 1 Y).filter (fun n => n≤X) = Icc 1 X := by ext n; simp only [mem_filter,mem_Icc]; omega
    have h := sum_filter_add_sum_filter_not (Icc 1 Y) (fun n => n≤X) f
    rw [hfilter] at h
    simp only [divisorPolynomial,dirichletPoly,c,ite_mul,zero_mul,← sum_filter,not_le] at h ⊢
    change _ - _ = ∑ n ∈ (Icc 1 Y).filter (fun n => X<n), f n
    linear_combination -h
  simp_rw [he]
  have h := dirichletPoly_mean_sq_asymp c Y σ hab
  simp only [Real.norm_eq_abs,show -2*σ = -(2*σ) by ring] at h
  have hdiag : ∑ n ∈ Icc 1 Y, ‖c n‖^2*(n:ℝ)^(-(2*σ)) ≤ (Y:ℝ)*(1+Real.log Y)^3/(X:ℝ)^(2*σ) := by
    calc _ ≤ ∑ n ∈ Icc 1 Y, (n.divisors.card:ℝ)^2/(X:ℝ)^(2*σ) := by
              apply sum_le_sum
              intro n _
              by_cases hXn : X<n
              · simp only [c,hXn,ite_true,Complex.norm_natCast]
                rw [div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg _)]
                apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
                apply inv_anti₀ (Real.rpow_pos_of_pos (by exact_mod_cast hX) _)
                exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hXn.le) (by linarith)
              · simp only [c,hXn,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_mul]; positivity
         _ ≤ _ := by
              rw [← Finset.sum_div]
              apply div_le_div_of_nonneg_right _ (by positivity)
              simpa only [max_eq_left (hX.trans hXY)] using sum_Icc_card_divisors_sq_le Y
  have hp := mul_le_mul_of_nonneg_left hdiag (show 0≤b-a+2*π*Y by positivity)
  linarith only [(abs_le.mp h).2,hp]

private theorem divisorBlock_vertical {X Y : ℕ} (hXY : X≤Y) (hX : 1≤X) {a b : ℝ} (hab : a≤b) :
    (∫ t in a..b, ‖divisorPolynomial Y (((9/2:ℝ):ℂ)+t*I)-
        divisorPolynomial X (((9/2:ℝ):ℂ)+t*I)‖^2) ≤
      (b-a+2*π*Y)*((Y:ℝ)*(1+Real.log Y)^3/(X:ℝ)^9) := by
  have h := divisorPolynomial_block_vertical (σ:=9/2) (by norm_num) hXY hX hab
  simpa only [show 2*(9/2:ℝ) = (9:ℕ) by norm_num,Real.rpow_natCast] using h

/-- A Gaussian-weighted tail block on the line `Re s=9/2`. Each
doubling of the left endpoint gives a factor `2⁻⁷` in mean square. -/
theorem divisorPolynomial_tail_gaussian_log {T K : ℝ} (hT : 2≤T) (hK : 0≤K)
    {X Y j : ℕ} (hXY : X≤Y) (hYX : Y≤2*X) (hX : (2:ℝ)^j*T≤X) (hY : (Y:ℝ)≤2*T^2)
    (negative : Bool) (F : ℝ → ℝ → ℂ)
    (hF : ∀ t ∈ Set.Ioc T (2*T), ∀ v, ‖F t v‖ ≤ K*T^4*Real.exp (-(1/2:ℝ)*v^2)) :
    (∫ t in T..2*T, ‖∫ v, F t v*(divisorPolynomial Y ((9/2:ℂ)+((if negative then v-t else v+t):ℝ)*I)-
      divisorPolynomial X ((9/2:ℂ)+((if negative then v-t else v+t):ℝ)*I))‖^2) ≤
        (108*π*(1+4*π))*K^2*T*(1+Real.log T)^3*(1/2:ℝ)^(7*j) := by
  have ht : 0<T := by linarith
  have h2j : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
  have htx : T≤(X:ℝ) := (le_mul_of_one_le_left ht.le h2j).trans hX
  have hx : 0<(X:ℝ) := ht.trans_le htx
  have hxn : 1≤X := by exact_mod_cast hx
  have hy : 0<(Y:ℝ) := hx.trans_le (by exact_mod_cast hXY)
  have hyx : (Y:ℝ)≤2*X := by exact_mod_cast hYX
  have hl := Real.log_le_log hy hY
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  have htlog := Real.log_nonneg (by linarith : 1≤T)
  have hylog := Real.log_nonneg (by exact_mod_cast hxn.trans hXY : (1:ℝ)≤Y)
  have hlog : 1+Real.log Y ≤ 3*(1+Real.log T) := by
    norm_num only [Nat.cast_ofNat] at hl
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  let p := fun u : ℝ => divisorPolynomial Y (((9/2:ℝ):ℂ)+u*I)-divisorPolynomial X (((9/2:ℝ):ℂ)+u*I)
  have hc : Continuous p := (divisorPolynomial_continuous ..).sub (divisorPolynomial_continuous ..)
  obtain ⟨M₁,hM₁⟩ := divisorPolynomial_vertical_bounded Y (9/2)
  obtain ⟨M₂,hM₂⟩ := divisorPolynomial_vertical_bounded X (9/2)
  have hbound : ∃ M : ℝ, ∀ u, ‖p u‖≤M := ⟨M₁+M₂,fun u => (norm_sub_le ..).trans (add_le_add (hM₁ u) (hM₂ u))⟩
  have he (a b : ℝ) (hab : b-a=T) : (∫ u in a..b, ‖p u‖^2) ≤
      (54*(1+4*π))*(1+Real.log T)^3/(X:ℝ)^7 := by
    have h := divisorBlock_vertical hXY hxn (a:=a) (b:=b) (by linarith)
    rw [hab] at h
    have hfac : T+2*π*Y ≤ (1+4*π)*X := by nlinarith only [htx,mul_le_mul_of_nonneg_left hyx Real.pi_pos.le]
    have hnum := mul_le_mul hyx (pow_le_pow_left₀ (by linarith) hlog 3) (by positivity) (by positivity)
    apply h.trans ((mul_le_mul hfac (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity) (by positivity)).trans_eq _)
    field_simp; ring
  have h := AnalyticTools.gaussian_shifted_dyadic_mean ht.le (mul_nonneg hK (pow_nonneg ht.le 4)) p hc hbound he negative F hF
  simp only [p,Complex.ofReal_div,Complex.ofReal_ofNat] at h
  apply h.trans
  have hpow : ((2:ℝ)^j*T)^7 ≤ (X:ℝ)^7 := pow_le_pow_left₀ (by positivity) hX _
  have hdec : T^8/(X:ℝ)^7 ≤ T*(1/2:ℝ)^(7*j) := by
    calc _ ≤ T^8/((2:ℝ)^j*T)^7 := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
         _ = _ := by
           rw [mul_pow,← pow_mul,one_div,inv_pow,mul_comm 7 j]
           field_simp
  calc _ = (108*π*(1+4*π))*K^2*(1+Real.log T)^3*(T^8/(X:ℝ)^7) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hdec (by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.RiemannZeta
