import AnalyticNumberTheory.ExponentialSums.LogarithmicDerivativeBounds
import AnalyticNumberTheory.RiemannZeta.HurwitzVinogradov

/-!
# Finite order bounds in vertical strips for Hurwitz zeta

For each order `k≥2`, van der Corput's method gives exponent
`1/(2^k−2)` at and to the right of the line `1−k/(2^k−2)`. Every
constant is uniform in the shift after the first term is removed.
-/

open Real Complex Finset
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- Transfer an incomplete logarithmic block bound to the regular part
of Hurwitz zeta throughout the half-strip to the right of its block exponent. -/
theorem hurwitzZeta_sub_initial_of_log_block {α β C : ℝ} (hα : 0≤α) (hC : 0<C)
    (H : ∀ {M b : ℕ} {a t : ℝ},1≤M → b≤2*M → a∈Set.Icc (0:ℝ) 1 → (M:ℝ)≤|t| →
      ‖∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n)‖≤C*|t|^α*(M:ℝ)^β) :
    ∃ D : ℝ,0<D ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 0<s.re →
      β≤s.re → 2≤|s.im| →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        D*|s.im|^α*(1+Real.log |s.im|) := by
  obtain ⟨A,hA,HA⟩ := regular_hurwitz_truncation
  let D := 1+1/Real.log 2
  have hl := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨A+1+C*D,by positivity,?_⟩
  intro a s ha hσ hβ ht
  let T := |s.im|
  let N := ⌈T/2⌉₊
  have hT : 2≤T := ht
  have hT₀ : 0<T := by linarith
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hNT : (N:ℝ)≤T := (Nat.ceil_lt_add_one (by positivity : 0≤T/2)).le.trans (by linarith)
  have hTN : T≤2*N := by linarith only [Nat.le_ceil (T/2)]
  let J := Nat.log 2 N+1
  have hJN := Nat.pow_log_le_self 2 (by omega : N≠0)
  have hJ : (J:ℝ)≤D*(1+Real.log T) := by
    have hp : (2:ℝ)^(Nat.log 2 N)≤T := (by exact_mod_cast hJN : (2:ℝ)^(Nat.log 2 N)≤N).trans hNT
    have hx := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at hx
    have hlog := Real.log_nonneg (by linarith : 1≤T)
    have hh := (le_div_iff₀ hl).mpr hx
    dsimp [J,D]; push_cast
    calc _ ≤ Real.log T/Real.log 2+1 := by linarith only [hh]
         _ ≤ _ := by
              rw [add_mul,one_mul,div_mul_eq_mul_div,one_mul,add_div]
              linarith only [hlog,one_div_pos.mpr hl]
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)
  let f (n : ℕ) := ((n:ℂ)+a)^(-s)
  let w (n : ℕ) := ((n:ℝ)+a)^(-s.re)
  let z (n : ℕ) := e (logPhase (-s.im/(2*π)) a n)
  have hw₀ (n) : 0≤w n := Real.rpow_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) n,ha.1]) _
  have hw : Antitone w := fun m n hmn => Real.rpow_le_rpow_of_nonpos
    (by linarith only [Nat.cast_nonneg (α:=ℝ) m,ha.1])
    (by linarith only [show (m:ℝ)≤n by exact_mod_cast hmn]) (neg_nonpos.mpr hσ.le)
  have each (j : ℕ) (hj : j∈range J) :
      ‖∑ n∈dyadicBlock N j,f n‖≤C*T^α := by
    let M := 2^j
    let b := min N (2^(j+1))
    have hm : 1≤M := Nat.one_le_two_pow
    have hm' : (1:ℝ)≤M := by exact_mod_cast hm
    have hm₀ := zero_lt_one.trans_le hm'
    have hmn : M≤N := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hj))).trans hJN
    have hmb : M≤b := le_min hmn (Nat.pow_le_pow_right (by decide) (by omega))
    have hb : b≤2*M := (min_le_right ..).trans_eq (by dsimp [M]; rw [pow_succ]; ring)
    have hMt : (M:ℝ)≤T := (by exact_mod_cast hmn : (M:ℝ)≤N).trans hNT
    have hs := norm_sum_Ioc_antitone_weight w z hw hw₀ hmb
      (show 0≤C*T^α*(M:ℝ)^β by positivity)
      (fun n _ hn => H hm (hn.trans hb) ⟨ha.1.le,ha.2⟩ hMt)
    have he (n : ℕ) : f n=(w n:ℂ)*z n := by
      have h := shifted_vertical_term a s.re s.im (n:=n) (by linarith only [Nat.cast_nonneg (α:=ℝ) n,ha.1])
      rwa [Complex.re_add_im] at h
    change ‖∑ n∈Ioc M b,f n‖≤_
    simp_rw [he]
    apply hs.trans
    have hweight : w M≤(M:ℝ)^(-s.re) := Real.rpow_le_rpow_of_nonpos hm₀
      (le_add_of_nonneg_right ha.1.le) (neg_nonpos.mpr hσ.le)
    apply (mul_le_mul_of_nonneg_right hweight (by positivity)).trans
    calc _ = C*T^α*(M:ℝ)^(β-s.re) := by rw [sub_eq_add_neg,Real.rpow_add hm₀]; ring
         _ ≤ _ := mul_le_of_le_one_right (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hm' (by linarith))
  have hsum := (norm_sum_le ..).trans (sum_le_sum each)
  simp only [sum_const,card_range,nsmul_eq_mul] at hsum
  have hone : ‖f 1‖≤1 := by
    simp only [f,Nat.cast_one,←Complex.ofReal_one,←Complex.ofReal_add]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [ha.1] : 0<1+a),Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ha.1]) (by linarith)
  let P := ∑ n∈Icc 1 N,f n
  have hP : ‖P‖≤1+J*(C*T^α) := by
    rw [show P=f 1+∑ j∈range J,∑ n∈dyadicBlock N j,f n from
      sum_Icc_eq_dyadic_blocks f hN (Nat.lt_pow_succ_log_self one_lt_two N).le]
    exact (norm_add_le ..).trans (add_le_add hone hsum)
  have htri := norm_add_le (Z-P) P
  rw [sub_add_cancel] at htri
  have herr : ‖Z-P‖≤A := HA ha hN hσ ht hNT hTN
  have hlT := Real.log_nonneg (by linarith : 1≤T)
  have hpow := Real.one_le_rpow (by linarith : 1≤T) hα
  have hdom := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hpow
    (by linarith : 1≤1+Real.log T)) (by positivity : 0≤A+1)
  change ‖Z‖≤(A+1+C*D)*T^α*(1+Real.log T)
  nlinarith only [htri,herr,hP,mul_le_mul_of_nonneg_right hJ (show 0≤C*T^α by positivity),hdom]

/-- Classical order-`k` derivative bound, uniform in the height and shift. -/
theorem hurwitzZeta_sub_initial_higher_derivative {k : ℕ} (hk : 2≤k) :
    ∃ C : ℝ,0<C ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 0<s.re →
      1-k/((2:ℝ)^k-2)≤s.re → 2≤|s.im| →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        C*|s.im|^(1/((2:ℝ)^k-2))*(1+Real.log |s.im|) := by
  obtain ⟨C,hC,H⟩ := logPhase_higher_order_block hk
  have hp : 4≤(2:ℝ)^k := (by norm_num : (4:ℝ)=2^2).le.trans (pow_le_pow_right₀ (by norm_num) hk)
  exact hurwitzZeta_sub_initial_of_log_block (one_div_nonneg.mpr (by linarith)) hC H

end AnalyticNumberTheory.RiemannZeta
