import AnalyticNumberTheory.ExponentialSums.VinogradovLogarithmicSums
import AnalyticNumberTheory.RiemannZeta.VinogradovKorobovGrowth
import AnalyticNumberTheory.AnalyticTools.CubicExponentialSum

/-!
# Vinogradov estimates for shifted Dirichlet polynomials

The constants in the logarithmic block estimate are uniform in the shift.
Retaining part of the cubic decay while maximizing the strip exponent
gives a logarithmic factor of order two thirds on summation.
-/

open Real Complex Finset Filter
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem natural_log_blocks :
    ∃ c : ℝ,0<c ∧ ∃ C : ℝ,0<C ∧ ∀ {M b : ℕ} {t a : ℝ}, 1≤M → M≤b → b≤2*M →
      (M:ℝ)≤|t| → 16≤|t| → a∈Set.Icc (0:ℝ) 1 →
      ‖∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n)‖ ≤
        C*M*Real.exp (-c*(Real.log M)^3/(Real.log |t|)^2) := by
  obtain ⟨c,hc,C,hC,H⟩ := vinogradov_logarithmic_block_shift
  refine ⟨c,hc,C,hC,?_⟩
  intro M b t a hM hMb hb hMt ht ha
  have h := H M b |t| a ha hM hMb hb hMt ht
  have he (u : ℝ) : (∑ n∈Ioc (M:ℤ) (b:ℤ),e ((u/(2*π))*Real.log ((n:ℝ)+a))) =
      ∑ n∈Ioc M b,e (logPhase (u/(2*π)) a n) := by
    refine sum_bij' (fun n _ => n.toNat) (fun n _ => (n:ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Ioc] at hn ⊢; omega
    · intro n hn; simp only [mem_Ioc] at hn ⊢; omega
    · intro n hn; have := (mem_Ioc.mp hn).1; omega
    · intro n _; simp
    · intro n hn; have hn₀ : 0≤n := by have := (mem_Ioc.mp hn).1; omega
      have he : (n.toNat:ℝ)=(n:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn₀
      simp [logPhase,he]
  rw [he] at h
  rcases le_total 0 t with hpos|hneg
  · rw [abs_of_nonneg hpos] at h ⊢
    rw [show (∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n))=
      star (∑ n∈Ioc M b,e (logPhase (t/(2*π)) a n)) by
        rw [star_sum]; apply sum_congr rfl; intro n _
        rw [star_e]; unfold logPhase; congr 1; ring,norm_star]
    exact h
  · simpa only [abs_of_nonpos hneg] using h

/-- Factor a shifted Dirichlet monomial into its real weight and logarithmic phase. -/
theorem shifted_vertical_term (a σ t : ℝ) {n : ℕ} (h : 0<(n:ℝ)+a) :
    ((n:ℂ)+a)^(-((σ:ℂ)+(t:ℂ)*I)) =
      ((((n:ℝ)+a)^(-σ):ℝ):ℂ)*e (logPhase (-t/(2*π)) a n) := by
  rw [←Complex.ofReal_natCast,←Complex.ofReal_add,Real.rpow_def_of_pos h,Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),←Complex.ofReal_log h.le,e,←Complex.exp_add]
  unfold logPhase
  push_cast; congr 1
  field_simp [Real.pi_ne_zero]; ring

/-- The regular part of a shifted Dirichlet polynomial obeys the Vinogradov
three-halves bound uniformly in its length, its shift and its real part. -/
theorem hurwitz_polynomial_vinogradov_bound :
    ∃ K : ℝ,0<K ∧ ∃ D : ℝ,0<D ∧ ∀ {N : ℕ} {a σ t : ℝ}, a∈Set.Ioc (0:ℝ) 1 →
      0≤σ → 16≤|t| → 1≤N → (N:ℝ)≤|t| →
      ‖∑ n∈Icc 1 N,((n:ℂ)+a)^(-((σ:ℂ)+t*I))‖ ≤
        D*(Real.log |t|)^(2/3:ℝ)*Real.exp (K*(max (1-σ) 0)^(3/2:ℝ)*Real.log |t|) := by
  obtain ⟨c,hc,C,hC,H⟩ := natural_log_blocks
  let K := 1/√(c/2)
  let d := (c/2)*(Real.log 2)^3
  have hl2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hd : 0<d := by dsimp [d]; positivity
  let B := Real.exp d*(1+1/d)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨K,by dsimp [K]; positivity,1+C*B,by positivity,?_⟩
  intro N a σ t ha hσ ht hN hNT
  let L := Real.log |t|
  have hL : 1≤L := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < |t|)).mpr
    linarith only [ht,Real.exp_one_lt_d9]
  have hL₀ : 0<L := by linarith
  let η := max (1-σ) 0
  have hη : 0≤η := le_max_right ..
  let E := Real.exp (K*η^(3/2:ℝ)*L)
  have hE : 1≤E := Real.one_le_exp (by dsimp [K]; positivity)
  let f (n : ℕ) := ((n:ℂ)+a)^(-((σ:ℂ)+t*I))
  let w (n : ℕ) := ((n:ℝ)+a)^(-σ)
  let z (n : ℕ) := e (logPhase (-t/(2*π)) a n)
  have hw0 (n : ℕ) : 0≤w n := Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n,ha.1]) _
  have hw : Antitone w := fun m n hmn => Real.rpow_le_rpow_of_nonpos
    (by linarith only [Nat.cast_nonneg (α:=ℝ) m,ha.1])
    (add_le_add_left (by exact_mod_cast hmn : (m:ℝ)≤n) _) (neg_nonpos.mpr hσ)
  let J := Nat.log 2 N+1
  have hJN := Nat.pow_log_le_self 2 (by omega : N≠0)
  let g (j : ℕ) := Real.exp (-d*(j:ℝ)^3/L^2)
  have each (j : ℕ) (hj : j∈range J) : ‖∑ n∈dyadicBlock N j,f n‖ ≤ C*E*g j := by
    let M := 2^j
    let b := min N (2^(j+1))
    have hm : 1≤M := Nat.one_le_two_pow
    have hm' : (1:ℝ)≤M := by exact_mod_cast hm
    have hm₀ : 0<(M:ℝ) := zero_lt_one.trans_le hm'
    have hmn : M≤N := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hj))).trans hJN
    have hmb : M≤b := le_min hmn (Nat.pow_le_pow_right (by decide) (by omega))
    have hb : b≤2*M := (min_le_right ..).trans_eq (by dsimp [M]; rw [pow_succ]; ring)
    have hMt : (M:ℝ)≤|t| := (by exact_mod_cast hmn : (M:ℝ)≤N).trans hNT
    have hs := AnalyticTools.Summation.norm_sum_Ioc_antitone_weight w z hw hw0 hmb
      (show 0≤C*M*Real.exp (-c*(Real.log M)^3/L^2) by positivity)
      (fun k hk hk' => H hm hk (hk'.trans hb) hMt ht ⟨ha.1.le,ha.2⟩)
    change ‖∑ n∈Ioc M b,f n‖≤_
    rw [sum_congr rfl (fun n _ => shifted_vertical_term a σ t (n:=n) (by linarith [ha.1,Nat.cast_nonneg (α:=ℝ) n]))]
    apply hs.trans
    have hweight : w M≤(M:ℝ)^(-σ) := Real.rpow_le_rpow_of_nonpos hm₀
      (le_add_of_nonneg_right ha.1.le) (neg_nonpos.mpr hσ)
    apply (mul_le_mul_of_nonneg_right hweight (by positivity)).trans
    let x := Real.log M
    have hx : 0≤x := Real.log_nonneg hm'
    have hxj : x=j*Real.log 2 := by simp [x,M,Real.log_pow]
    have hsave := vinogradov_cubic_saving hx hη (half_pos hc) hL₀
    have hh : (1-σ)*x-c*x^3/L^2≤K*η^(3/2:ℝ)*L+(-d*(j:ℝ)^3/L^2) := by
      have h1 := mul_le_mul_of_nonneg_right (le_max_left (1-σ) 0) hx
      have h2 : d*(j:ℝ)^3=(c/2)*x^3 := by rw [hxj]; dsimp [d]; ring
      rw [neg_mul,h2]; dsimp only [K]; dsimp only [η] at hsave
      dsimp [η]
      calc (1-σ)*x-c*x^3/L^2 ≤ max (1-σ) 0*x-c*x^3/L^2 := sub_le_sub_right h1 _
           _ = (max (1-σ) 0*x-c/2*x^3/L^2) + -(c/2*x^3)/L^2 := by ring
           _ ≤ _ := add_le_add hsave le_rfl
    change (M:ℝ)^(-σ)*(C*M*Real.exp (-c*x^3/L^2))≤C*E*g j
    rw [show (M:ℝ)^(-σ)*(C*M*Real.exp (-c*x^3/L^2)) =
      C*Real.exp ((1-σ)*x-c*x^3/L^2) by
        rw [Real.rpow_def_of_pos hm₀,show (1-σ)*x-c*x^3/L^2=x+x*(-σ)+(-c*x^3/L^2) by ring,
          Real.exp_add,Real.exp_add,Real.exp_log hm₀]; ring]
    dsimp only [E,g]; rw [mul_assoc,←Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) hC.le
  have hg := AnalyticTools.cubic_exponential_sum_le hd hL
  have hG : ∑ j∈range J,g j≤B*L^(2/3:ℝ) := (hg.1.sum_le_tsum (range J) (fun _ _ => (Real.exp_pos _).le)).trans hg.2
  have h₁ : ‖f 1‖≤1 := by
    simp only [f,Nat.cast_one,←Complex.ofReal_one,←Complex.ofReal_add]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [ha.1] : 0<1+a)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ha.1]); simp [hσ]
  change ‖∑ n∈Icc 1 N,f n‖≤_
  rw [sum_Icc_eq_dyadic_blocks f hN (Nat.lt_pow_succ_log_self one_lt_two N).le]
  apply (norm_add_le ..).trans
  apply (add_le_add h₁ ((norm_sum_le ..).trans (sum_le_sum each))).trans
  rw [←mul_sum]
  have hlow := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hL (by norm_num : 0≤(2/3:ℝ))) hE
  nlinarith only [hlow,mul_le_mul_of_nonneg_left hG (mul_nonneg hC.le (zero_le_one.trans hE))]

end AnalyticNumberTheory.RiemannZeta
