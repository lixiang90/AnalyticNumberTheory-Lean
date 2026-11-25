import AnalyticNumberTheory.ExponentialSums.VinogradovLogBilinear
import AnalyticNumberTheory.ExponentialSums.VinogradovLogShifts
import AnalyticNumberTheory.ExponentialSums.VinogradovDegreeBounds

/-!
# Vinogradov's logarithmic block estimate at large heights

The order of the Taylor polynomial grows in proportion to
`log t / log N`. The classical mean value theorem at moment `21 r²` gives
an absolute constant after the final root.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem exists_shift_length {N : ℝ} (hN : 0<N) (hX : 100≤Real.log N) :
    ∃ a : ℕ, 0<a ∧ Real.log N/3≤Real.log a ∧ Real.log a≤3*Real.log N/8 := by
  let A := N^(3/8:ℝ)
  let a := ⌊A⌋₊
  have hA0 : 0<A := Real.rpow_pos_of_pos hN _
  have hlog : Real.log A=3*Real.log N/8 := by rw [Real.log_rpow hN]; ring
  have hA1 : 1≤A := (Real.log_le_log_iff one_pos hA0).mp (by rw [Real.log_one,hlog]; linarith)
  have ha : 1≤a := Nat.le_floor (by simpa using hA1)
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha
  have hlo : A≤2*(a:ℝ) := by
    have H := Nat.lt_floor_add_one A
    have H' : (1:ℝ)≤a := by exact_mod_cast ha
    change A<(a:ℝ)+1 at H; linarith
  have H := Real.log_le_log hA0 hlo
  rw [Real.log_mul (by norm_num) ha0.ne',hlog] at H
  refine ⟨a,ha,by linarith only [H,hX,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))],?_⟩
  rw [←hlog]; exact Real.log_le_log ha0 (Nat.floor_le hA0.le)

private theorem logBlock_errors {a r l : ℕ} {t N : ℝ} (hN : 0<N) (hX : 100≤Real.log N)
    (ht : 0<t) (hl : 8≤l) (hT' : Real.log t≤(2*l+2)*Real.log N)
    (hr : r=16*(l+1)) (ha : 0<a) (hA : Real.log a≤3*Real.log N/8) :
    let F := Real.exp (-Real.log N/(1000000000000*(l:ℝ)^2))
    (a:ℝ)^2/N≤1/2 ∧ (a:ℝ)^2≤N*F ∧ t*((a:ℝ)^2/N)^(r+1)≤F := by
  intro F
  have ha0 : 0<(a:ℝ) := by positivity
  have hl' : (8:ℝ)≤l := by exact_mod_cast hl
  have hd : 1≤1000000000000*(l:ℝ)^2 := by nlinarith [sq_nonneg ((l:ℝ)-8)]
  have hX0 : 0≤Real.log N := by linarith
  have hQ : Real.log N/(1000000000000*(l:ℝ)^2)≤Real.log N/4 := by
    apply div_le_div_of_nonneg_left hX0 (by norm_num)
    nlinarith only [hd,hl',sq_nonneg ((l:ℝ)-8)]
  have hL := Real.log_div (pow_ne_zero 2 ha0.ne') hN.ne'
  rw [Real.log_pow,Nat.cast_ofNat] at hL
  have hL' : Real.log ((a:ℝ)^2/N)≤ -Real.log N/4 := by linarith only [hL,hA]
  have hR : (r:ℝ)=16*((l:ℝ)+1) := by exact_mod_cast hr
  have hratio := div_pos (sq_pos_of_pos ha0) hN
  have hF : 0<F := Real.exp_pos _
  have hFl : Real.log F= -Real.log N/(1000000000000*(l:ℝ)^2) := Real.log_exp _
  refine ⟨?_,?_,?_⟩
  · apply (Real.log_le_log_iff hratio (by norm_num)).mp
    rw [Real.log_div one_ne_zero (by norm_num),Real.log_one]
    linarith only [hL',hX,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  · apply (Real.log_le_log_iff (sq_pos_of_pos ha0) (mul_pos hN hF)).mp
    rw [Real.log_pow,Nat.cast_ofNat,Real.log_mul hN.ne' hF.ne',hFl]
    rw [neg_div]
    linarith only [hA,hQ]
  · apply (Real.log_le_log_iff (mul_pos ht (pow_pos hratio _)) hF).mp
    rw [hFl,Real.log_mul ht.ne' (pow_ne_zero _ hratio.ne'),Real.log_pow,Nat.cast_add,Nat.cast_one]
    have H := mul_le_mul_of_nonneg_left hL' (show 0≤(r:ℝ)+1 by positivity)
    rw [hR] at H ⊢
    rw [neg_div]
    nlinarith only [H,hT',hQ,hX0,mul_nonneg (Nat.cast_nonneg (α:=ℝ) l) hX0]

/-- The long-height logarithmic estimate with a fully explicit constant.
The integer `l` brackets `log t/(2 log N)`. -/
theorem vinogradov_logarithmic_block_large_shift {l N M : ℕ} {t θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) 1) (hN : 0<N)
    (hX : 100≤Real.log (N:ℝ)) (hNM : N≤M) (hM : M≤2*N) (ht : 0<t) (hl : 8≤l)
    (hT : 2*l*Real.log N≤Real.log t) (hT' : Real.log t≤(2*l+2)*Real.log N) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log ((n:ℝ)+θ))‖ ≤
      (Real.exp 4265200 + 4)*N*
        Real.exp (-Real.log N/(1000000000000*(l:ℝ)^2)) := by
  let r := 16*(l+1)
  let s := 21*r^2
  let C := (2129600:ℝ)
  let δ := vinogradovWeight r*Real.exp (-20)
  let F := Real.exp (-Real.log N/(1000000000000*(l:ℝ)^2))
  have hN0 : (0:ℝ)<N := by positivity
  obtain ⟨a,ha,haN,hA⟩ := exists_shift_length hN0 hX
  have ha0 : (0:ℝ)<a := by positivity
  have hA' : Real.log (a:ℝ)≤Real.log N := by linarith
  have hr : 4*l≤r := by dsimp [r]; omega
  have hr' : r≤32*l := by dsimp [r]; omega
  have hr2 : 2≤r := by dsimp [r]; omega
  have hJ : vinogradovJ s r a ≤ Real.exp (C*(r:ℝ)^4+
      (2*(s:ℝ)-(r:ℝ)*(r+1)/2+δ)*Real.log a) := by
    apply (vinogradov_mean_value_degree_multiple hr2 ha 20).trans_eq
    rw [Real.rpow_def_of_pos ha0,←Real.exp_add]; congr 1
    dsimp only [C,s,δ,vinogradovMeanExponent,vinogradovWeight]; push_cast; ring
  obtain ⟨hsmall,hbound,htail⟩ := logBlock_errors hN0 hX ht hl hT' (r:=r) rfl ha hA
  have H := logarithmic_block_bilinear_reduction_shift r t θ hθ.1 hN hNM ha hsmall
  have hlocal (n : ℤ) (hn : n∈Ioc (N:ℤ) M) :
      ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) (logTaylorCoefficients r t ((n:ℝ)+θ))‖ ≤
        (a:ℝ)^2*(Real.exp 4265200 * F) := by
    have hnN : (N:ℝ)≤n := by exact_mod_cast (mem_Ioc.mp hn).1.le
    have hn' : (n:ℝ)≤2*N := by exact_mod_cast le_trans (mem_Ioc.mp hn).2 (by exact_mod_cast hM : (M:ℤ)≤2*N)
    have hNbig : 2≤(N:ℝ) := by linarith only [hX,Real.log_le_sub_one_of_pos hN0]
    have hlog : Real.log ((n:ℝ)+θ)≤Real.log N+1 := by
      have h25 : (5/2:ℝ)≤Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
      have H := Real.log_le_log (show 0<(n:ℝ)+θ by linarith only [hN0,hnN,hθ.1])
        (show (n:ℝ)+θ≤Real.exp 1*(N:ℝ) by nlinarith only [hn',hθ.2,hNbig,mul_le_mul_of_nonneg_right h25 hN0.le])
      rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne',Real.log_exp] at H; linarith
    have HL := logTaylor_bilinear_saving_of_log_le hN0 hX (show (N:ℝ)≤(n:ℝ)+θ by linarith only [hnN,hθ.1]) hlog ht hl hT hT' hr hr' (s:=s) rfl ha haN hA'
      (by norm_num [C] : 0≤C) (show δ≤(r:ℝ)*(r+1)/2*Real.exp (-20) from le_rfl) hJ
    apply HL.trans_eq
    rw [←Real.exp_add]
    dsimp [C,F]; congr 2; ring
  have hcard : (((Ioc (N:ℤ) M).card):ℝ)=(M:ℝ)-N := by
    rw [Int.card_Ioc]; exact_mod_cast (Int.toNat_of_nonneg (show 0≤(M:ℤ)-N by omega))
  have hu := sum_le_sum hlocal
  rw [sum_const,nsmul_eq_mul,hcard] at hu
  have hlen : (M:ℝ)-N≤N := by exact_mod_cast (show (M:ℤ)-N≤N by omega)
  have hF : 0≤F := (Real.exp_pos _).le
  have hu' : (∑ n∈Ioc (N:ℤ) M, ‖vinogradovBilinearSum (Icc 1 (a:ℤ)) (logTaylorCoefficients r t ((n:ℝ)+θ))‖)/(a:ℝ)^2 ≤ (N:ℝ)*(Real.exp 4265200*F) := by
    apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
    apply hu.trans
    have hh := mul_le_mul_of_nonneg_right hlen (mul_nonneg (Real.exp_pos 4265200).le hF)
    linarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg (a:ℝ))]
  rw [abs_of_pos ht] at H
  apply H.trans
  change t*((a:ℝ)^2/N)^(r+1)≤F at htail
  have he := mul_le_mul hlen htail (mul_nonneg ht.le (pow_nonneg (div_nonneg (sq_nonneg _) hN0.le) _)) (Nat.cast_nonneg N)
  change _ ≤ (Real.exp 4265200+4)*N*F
  change (a:ℝ)^2≤(N:ℝ)*F at hbound
  linarith only [hu',hbound,he]

/-- The long-height logarithmic estimate with a fully explicit constant.
The integer `l` brackets `log t/(2 log N)`. -/
theorem vinogradov_logarithmic_block_large {l N M : ℕ} {t : ℝ} (hN : 0<N)
    (hX : 100≤Real.log (N:ℝ)) (hNM : N≤M) (hM : M≤2*N) (ht : 0<t) (hl : 8≤l)
    (hT : 2*l*Real.log N≤Real.log t) (hT' : Real.log t≤(2*l+2)*Real.log N) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log n)‖ ≤
      (Real.exp 4265200 + 4)*N*
        Real.exp (-Real.log N/(1000000000000*(l:ℝ)^2)) := by
  simpa only [add_zero] using vinogradov_logarithmic_block_large_shift (θ:=0) ⟨le_rfl,zero_le_one⟩ hN hX hNM hM ht hl hT hT'

end AnalyticNumberTheory.ExponentialSums
