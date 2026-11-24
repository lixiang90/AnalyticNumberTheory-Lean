import AnalyticNumberTheory.RiemannZeta.HurwitzApproximation
import AnalyticNumberTheory.ExponentialSums.LogarithmicBlocks
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Weyl's subconvex bound for the Hurwitz zeta function

The first term of the Hurwitz series accounts for the dependence on a
small shift. Partial summation transfers the logarithmic exponential-sum
estimate to each complete or incomplete dyadic block.
-/

open Complex Real Finset Filter
open scoped Topology Asymptotics
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.RiemannZeta

private theorem critical_term_eq {a t : ℝ} (ha : 0<a) (n : ℕ) :
    ((n:ℂ)+a)^(-((1/2:ℂ)+t*I)) =
      (((√((n:ℝ)+a))⁻¹:ℝ):ℂ)*logPhaseTerm (-t/(2*π)) a n := by
  rw [← Complex.ofReal_natCast,← Complex.ofReal_add,critical_monomial_eq (by positivity),logPhaseTerm]
  congr 2
  unfold logPhase
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem hurwitz_block {a t U : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1)
    (hU : 1≤U) (ht : |-t/(2*π)| = U^6) {M b : ℕ} (hM : 1≤M)
    (hb : b≤2*M) (hcut : (M:ℝ)≤100*U^6) :
    ‖∑ n ∈ Ioc M b, ((n:ℂ)+a)^(-((1/2:ℂ)+t*I))‖ ≤ 10000*U := by
  by_cases hab : M≤b
  · let w (n : ℕ) := (√((n:ℝ)+a))⁻¹
    have hw0 (n) : 0≤w n := by dsimp [w]; positivity
    have hw : Antitone w := by
      intro m n hmn
      apply inv_anti₀ (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) ha.1))
      apply Real.sqrt_le_sqrt
      linarith only [show (m:ℝ)≤n by exact_mod_cast hmn]
    let z := logPhaseTerm (-t/(2*π)) a
    have HS (k : ℕ) (_ : M≤k) (hk : k≤b) : ‖∑ n ∈ Ioc M k, z n‖ ≤ 10000*U*√M :=
      logPhase_weyl_block hM (hk.trans hb) ⟨ha.1.le,ha.2⟩ hU ht hcut
    simp_rw [critical_term_eq ha.1]
    have hm : 0<(M:ℝ) := by exact_mod_cast hM
    apply (norm_sum_Ioc_antitone_weight w z hw hw0 hab (by positivity) HS).trans
    have hcomp : w M ≤ (√(M:ℝ))⁻¹ := by
      apply inv_anti₀ (by positivity)
      apply Real.sqrt_le_sqrt
      linarith [ha.1]
    calc _ ≤ (√(M:ℝ))⁻¹*(10000*U*√M) := mul_le_mul_of_nonneg_right hcomp (by positivity)
         _ = _ := by field_simp
  · simp only [Ioc_eq_empty_of_le (le_of_not_ge hab),sum_empty,norm_zero]; positivity

private theorem hurwitz_finite_weyl {a t U : ℝ} (ha : a ∈ Set.Ioc (0:ℝ) 1)
    (hU : 1≤U) (ht : |-t/(2*π)| = U^6) {N K : ℕ} (hN : 1≤N)
    (hNK : N≤2^K) (hcut : (N:ℝ)≤100*U^6) :
    ‖∑ n ∈ Icc 0 N, ((n:ℂ)+a)^(-((1/2:ℂ)+t*I))‖ ≤ (√a)⁻¹+1+K*(10000*U) := by
  let f (n : ℕ) := ((n:ℂ)+a)^(-((1/2:ℂ)+t*I))
  have hnorm (n : ℕ) : ‖f n‖ = (√((n:ℝ)+a))⁻¹ := by
    dsimp only [f]
    rw [critical_term_eq ha.1,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    simp [logPhaseTerm,Complex.norm_exp]
  have hsplit := sum_Icc_eq_dyadic_blocks f hN hNK
  have hs : (Icc 0 N) = insert 0 (Icc 1 N) := by ext n; simp only [mem_Icc,mem_insert]; omega
  change ‖∑ n ∈ Icc 0 N, f n‖ ≤ _
  rw [hs,sum_insert (by simp),hsplit,← add_assoc]
  have h1 : ‖f 1‖ ≤ 1 := by
    rw [hnorm,Nat.cast_one]
    apply inv_le_one_of_one_le₀
    exact Real.one_le_sqrt.mpr (by linarith [ha.1])
  apply (norm_add_le ..).trans
  apply add_le_add
  · apply (norm_add_le ..).trans
    exact add_le_add (by simp [hnorm]) h1
  · apply (norm_sum_le ..).trans
    calc _ ≤ ∑ _j ∈ range K, 10000*U := by
              apply sum_le_sum
              intro j _
              by_cases hj : 2^j ≤ N
              · apply hurwitz_block ha hU ht (Nat.one_le_two_pow)
                · exact (min_le_right ..).trans (by rw [pow_succ]; omega)
                · exact (show (((2:ℕ)^j:ℕ):ℝ)≤N by exact_mod_cast hj).trans hcut
              · simp only [dyadicBlock,Ioc_eq_empty_of_le ((min_le_left ..).trans (le_of_not_ge hj)),sum_empty,norm_zero]
                positivity
         _ = _ := by simp

set_option maxHeartbeats 400000 in
/-- Uniform Weyl subconvexity for the Hurwitz zeta function. The initial
term `a^(-1/2)` allows the constant to be independent of the shift. -/
theorem hurwitzZeta_weyl_bound :
    ∃ C > 0, ∀ {a t : ℝ}, a ∈ Set.Ioc (0:ℝ) 1 → 2*π ≤ |t| →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)‖ ≤
        (√a)⁻¹+C*|t|^(1/6:ℝ)*(1+Real.log |t|) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_dirichletPoly_error zero_lt_one (by linarith [Real.two_le_pi] : (1:ℝ)<2*π)
  let D := 2+(Real.log 2)⁻¹
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨K+4+10000*D,by positivity,?_⟩
  intro a t ha ht
  let X := |t|
  have hX : 1≤X := by dsimp [X]; linarith [Real.two_le_pi]
  have hx : 0<X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  let U := (X/(2*π))^(1/6:ℝ)
  have hu : 1≤U := Real.one_le_rpow ((one_le_div (by positivity)).mpr ht) (by norm_num)
  have htU : U^6=X/(2*π) := by dsimp [U]; rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  have hphase : |-t/(2*π)| = U^6 := by rw [htU,abs_div,abs_neg,abs_of_pos (by positivity : 0<2*π)]
  let N := ⌊X⌋₊+1
  have hN : 1≤N := Nat.succ_pos _
  have hXN : X ≤ (N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one X).le
  have hNX : (N:ℝ) ≤ X+1 := by dsimp [N]; push_cast; linarith [Nat.floor_le hx.le]
  have hcut : (N:ℝ)≤100*U^6 := by
    rw [htU,← mul_div_assoc,le_div_iff₀ (by positivity)]
    have hp := mul_le_mul_of_nonneg_left Real.pi_le_four (Nat.cast_nonneg N : 0≤(N:ℝ))
    nlinarith only [hp,hNX,hX]
  let J := N.log2+1
  have hJ : N ≤ 2^J := (Nat.lt_log2_self (n:=N)).le
  have hjlog : (J:ℝ) ≤ D*(1+Real.log X) := by
    have h2 : (2:ℝ)^N.log2 ≤ N := by exact_mod_cast Nat.log2_self_le (n:=N) (by omega)
    have hxlog := Real.log_le_log (by positivity) (h2.trans (show (N:ℝ) ≤ 2*X by linarith))
    rw [Real.log_pow,Real.log_mul (by norm_num) hx.ne'] at hxlog
    have hh := (le_div_iff₀ hl2).mpr hxlog
    dsimp [J,D]; push_cast
    rw [add_div,div_self hl2.ne'] at hh
    nlinarith only [hh,inv_nonneg.mpr hl2.le,hlog,show Real.log X/Real.log 2=Real.log X*(Real.log 2)⁻¹ by ring]
  have huX : U≤X^(1/6:ℝ) := Real.rpow_le_rpow (by positivity)
    (div_le_self hx.le (by linarith [Real.two_le_pi])) (by norm_num)
  have hpoly := hurwitz_finite_weyl ha hu hphase hN hJ hcut
  have herr := H (N:=N) (σ:=1/2) (t:=t) ha hN (by norm_num) (by norm_num) hx
    (by simpa only [one_mul] using hXN)
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)
  let P := ∑ n ∈ Icc 0 N, ((n:ℂ)+a)^(-((1/2:ℂ)+t*I))
  change ‖Z‖ ≤ _
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at herr
  change ‖Z-P‖ ≤ ((N:ℝ)+1)^(1-1/2:ℝ)/X+K*(N:ℝ)^(-(1/2):ℝ) at herr
  have hNs : 1≤(N:ℝ) := by exact_mod_cast hN
  have hsmall : (N:ℝ)^(-(1/2):ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNs (by norm_num)
  have hlarge : ((N:ℝ)+1)^(1-1/2:ℝ)/X ≤ 2 := by
    rw [show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow,div_le_iff₀ hx]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith only [hNX,hX,mul_nonneg hx.le (sub_nonneg.mpr hX)]
  have hmain : (J:ℝ)*(10000*U) ≤ 10000*D*X^(1/6:ℝ)*(1+Real.log X) := by
    calc _ ≤ (D*(1+Real.log X))*(10000*X^(1/6:ℝ)) := by gcongr
         _ = _ := by ring
  have hone : 1 ≤ X^(1/6:ℝ)*(1+Real.log X) := one_le_mul_of_one_le_of_one_le (hu.trans huX) (by linarith)
  have hadj : ‖Z‖ ≤ ‖Z-P‖+‖P‖ := by simpa only [sub_add_cancel] using norm_add_le (Z-P) P
  change ‖P‖ ≤ _ at hpoly
  change ‖Z‖ ≤ (√a)⁻¹+(K+4+10000*D)*X^(1/6:ℝ)*(1+Real.log X)
  nlinarith only [hadj,herr,hpoly,hmain,hlarge,mul_le_mul_of_nonneg_left hsmall hK.le,
    mul_le_mul_of_nonneg_left hone (by linarith : 0 ≤ K+4)]

/-- Weyl's bound on the critical line, with one logarithm. -/
theorem riemannZeta_weyl_bound :
    ∃ C > 0, ∀ {t : ℝ}, 2*π≤|t| → ‖riemannZeta ((1/2:ℂ)+t*I)‖ ≤
      C*|t|^(1/6:ℝ)*(1+Real.log |t|) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_weyl_bound
  refine ⟨C+1,by positivity,?_⟩
  intro t ht
  have h := H (a:=1) ⟨zero_lt_one,le_rfl⟩ ht
  have h1 : ((1:ℝ):UnitAddCircle) = 0 := by exact AddCircle.coe_period _
  rw [h1,HurwitzZeta.hurwitzZeta_zero,Real.sqrt_one,inv_one] at h
  have hh : 1≤|t| := by linarith [Real.two_le_pi]
  have hlog := Real.log_nonneg hh
  have hone : 1 ≤ |t|^(1/6:ℝ)*(1+Real.log |t|) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hh (by norm_num)) (by linarith)
  nlinarith only [h,hone]

end AnalyticNumberTheory.RiemannZeta
