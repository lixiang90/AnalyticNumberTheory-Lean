import AnalyticNumberTheory.RiemannZeta.HurwitzPolynomials
import AnalyticNumberTheory.DirichletSeries.CriticalMeanValues

/-!
# Critical-line mean square of Hurwitz zeta for real shifts

For every fixed real shift in the unit interval the leading coefficient
is one. The first term has bounded amplitude and the shifted diagonal
differs from the usual harmonic sum by at most one.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.RiemannZeta

private theorem shifted_diagonal {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) (N : ℕ) :
    |hurwitzDiagonal a (Icc 1 N)-(harmonic N:ℝ)| ≤ 1 := by
  have htel (k : ℕ) :
      ∑ n ∈ Icc 1 k, ((n:ℝ)⁻¹-((n+1:ℕ):ℝ)⁻¹) = 1-((k+1:ℕ):ℝ)⁻¹ := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_Icc_succ_top (by omega),ih]; ring
  simp only [hurwitzDiagonal,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [abs_sub_comm,← sum_sub_distrib,abs_of_nonneg]
  · apply le_trans _ ((htel N).le.trans (sub_le_self _ (by positivity)))
    apply sum_le_sum
    intro n hn
    apply sub_le_sub_left
    apply inv_anti₀ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha.1)
    push_cast; linarith [ha.2]
  · apply sum_nonneg
    intro n hn
    exact sub_nonneg.mpr (inv_anti₀ (by exact_mod_cast (mem_Icc.mp hn).1) (by linarith [ha.1]))

private theorem shifted_tail_energy {a : ℝ} (ha : 0<a) {M N : ℕ} (hM : 0<M) :
    hurwitzDiagonal a (Ioc M N) ≤ N/M := by
  unfold hurwitzDiagonal
  calc _ ≤ ∑ _n ∈ Ioc M N, (M:ℝ)⁻¹ := by
            apply sum_le_sum
            intro n hn
            apply inv_anti₀ (by exact_mod_cast hM)
            have h : (M:ℝ)<n := by exact_mod_cast (mem_Ioc.mp hn).1
            linarith
       _ ≤ _ := by
            rw [sum_const,nsmul_eq_mul,Nat.card_Ioc,div_eq_mul_inv]
            gcongr; exact_mod_cast Nat.sub_le N M

private theorem shifted_tail_mean {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) {M N : ℕ}
    (hM : 0<M) (hMN : M≤N) {T : ℝ} (hT : 1≤T) :
    (∫ t in (1:ℝ)..T, ‖(hurwitzPolynomial a (Icc 1 N)-hurwitzPolynomial a (Icc 1 M)) t‖^2) ≤
      (T+4*π*N)*(N/M) := by
  have he (t : ℝ) : (hurwitzPolynomial a (Icc 1 N)-hurwitzPolynomial a (Icc 1 M)) t =
      hurwitzPolynomial a (Ioc M N) t := by
    dsimp only [Pi.sub_apply,hurwitzPolynomial]
    have h := sum_Ioc_consecutive (fun n : ℕ => (((n:ℝ)+a:ℝ):ℂ)^(-((1/2:ℂ)+t*I))) (Nat.zero_le M) hMN
    rw [show Ioc 0 M = Icc 1 M by ext n; simp only [mem_Ioc,mem_Icc]; omega,
      show Ioc 0 N = Icc 1 N by ext n; simp only [mem_Ioc,mem_Icc]; omega] at h
    linear_combination -h
  simp_rw [he]
  have h := hurwitzPolynomial_mean_square ha (Ioc M N) (fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,(mem_Ioc.mp hn).2⟩) 1 T
  have hd : 0 ≤ hurwitzDiagonal a (Ioc M N) := sum_nonneg fun n _ => inv_nonneg.mpr (by linarith [(Nat.cast_nonneg n : 0≤(n:ℝ)),ha.1])
  apply le_trans _ (mul_le_mul_of_nonneg_left (shifted_tail_energy ha.1 hM) (by positivity : 0 ≤ T+4*π*N))
  linarith only [(abs_le.mp h).2,hd]

private noncomputable def hurwitzLine (a : ℝ) (t : ℝ) := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) ((1/2:ℂ)+t*I)

private theorem continuous_hurwitzLine (a : ℝ) : Continuous (hurwitzLine a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (1/2:ℂ)+t*I ≠ 1 := by intro h; have h' := congrArg Complex.re h; norm_num at h'
  exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).continuousAt.comp
    (f:=fun t : ℝ => (1/2:ℂ)+t*I) (by fun_prop)

private theorem hurwitz_long_error {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) :
    ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, (∫ t in (1:ℝ)..T, ‖hurwitzLine a t-
      hurwitzPolynomial a (Icc 1 (⌊T⌋₊+1)) t‖^2)/T ≤ C := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_dirichletPoly_error zero_lt_one (by linarith [Real.two_le_pi] : (1:ℝ)<2*π)
  let B := K+(√a)⁻¹
  refine ⟨6+2*B^2,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  let N := ⌊T⌋₊+1
  have hN : 1≤N := Nat.succ_pos _
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have ht0 : 0<T := by linarith
  have hcut : T≤(N:ℝ) := by simpa [N] using (Nat.lt_floor_add_one T).le
  have hhi : (N:ℝ)+1≤T+2 := by dsimp [N]; push_cast; linarith [Nat.floor_le ht0.le]
  let f := fun t : ℝ => hurwitzLine a t-hurwitzPolynomial a (Icc 1 N) t
  have hc : Continuous f := (continuous_hurwitzLine _).sub (continuous_hurwitzPolynomial ha.1 _)
  have hp (t : ℝ) (ht : t∈Set.Icc (1:ℝ) T) : ‖f t‖^2 ≤ (2*(T+2))*t^(-2:ℝ)+2*B^2 := by
    have htp : 0<t := by linarith [ht.1]
    have h := H (N:=N) (σ:=1/2) (t:=t) ha hN (by norm_num) (by norm_num) (abs_pos.mpr htp.ne')
      (by rw [abs_of_pos htp,one_mul]; exact ht.2.trans hcut)
    simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,show (1:ℝ)-1/2=1/2 by norm_num,
      ← Real.sqrt_eq_rpow,abs_of_pos htp] at h
    let s := (1/2:ℂ)+t*I
    let z := (a:ℂ)^(-s)
    have hz : ‖z‖=(√a)⁻¹ := by
      dsimp only [z,s]
      rw [critical_monomial_eq ha.1,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      simp [Complex.norm_exp]
    have he : ∑ n ∈ Icc 0 N, ((n:ℂ)+a)^(-s) = z+hurwitzPolynomial a (Icc 1 N) t := by
      rw [show Icc 0 N = insert 0 (Icc 1 N) by ext n; simp only [mem_insert,mem_Icc]; omega,sum_insert (by simp)]
      simp only [z,Nat.cast_zero,zero_add,hurwitzPolynomial,Complex.ofReal_add,Complex.ofReal_natCast,s]
    change ‖hurwitzLine a t-(∑ n ∈ Icc 0 N, ((n:ℂ)+a)^(-s))‖ ≤ _ at h
    rw [he] at h
    have hrem := Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num : -(1/2:ℝ)≤0)
    have hb : ‖f t‖ ≤ √((N:ℝ)+1)/t+B := by
      have he' : f t=(hurwitzLine a t-(z+hurwitzPolynomial a (Icc 1 N) t))+z := by dsimp [f]; ring
      rw [he']
      apply (norm_add_le ..).trans
      rw [hz]; dsimp [B]
      linarith only [h,mul_le_mul_of_nonneg_left hrem hK.le]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have htwo : (√((N:ℝ)+1)/t+B)^2 ≤ 2*(√((N:ℝ)+1)/t)^2+2*B^2 :=
      by nlinarith only [sq_nonneg (√((N:ℝ)+1)/t-B)]
    have he' : t^(-2:ℝ)=(t^2)⁻¹ := by rw [Real.rpow_neg htp.le,Real.rpow_two]
    rw [he']
    rw [div_pow,Real.sq_sqrt (by positivity)] at htwo
    nlinarith only [hsq,htwo,mul_le_mul_of_nonneg_right hhi (inv_nonneg.mpr (sq_nonneg t)),
      show ((N:ℝ)+1)/t^2 = ((N:ℝ)+1)*(t^2)⁻¹ by ring]
  have hi : IntervalIntegrable (fun t : ℝ => (2*(T+2))*t^(-2:ℝ)) volume 1 T :=
    (continuousOn_const.mul (continuousOn_id.rpow_const fun t ht => Or.inl (by dsimp; linarith [ht.1]))).intervalIntegrable_of_Icc hT
  have hb := intervalIntegral.integral_mono_on hT ((hc.norm.pow 2).intervalIntegrable ..)
    (hi.add intervalIntegrable_const) hp
  have he : (∫ t in (1:ℝ)..T, t^(-2:ℝ))=1-T⁻¹ := by
    rw [integral_rpow (Or.inr ⟨by norm_num,fun h => by rw [Set.uIcc_of_le hT] at h; linarith [h.1]⟩)]
    simp only [show (-2:ℝ)+1= -1 by norm_num,Real.rpow_neg_one]; ring
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const_mul,he,
    intervalIntegral.integral_const,smul_eq_mul] at hb
  change (∫ t in (1:ℝ)..T, ‖f t‖^2)/T ≤ _
  rw [div_le_iff₀ ht0]
  simp only [Pi.pow_apply] at hb
  have h1 := mul_le_mul_of_nonneg_left (sub_le_self 1 (inv_nonneg.mpr ht0.le)) (show 0≤2*(T+2) by positivity)
  nlinarith only [hb,h1,hT,sq_nonneg B]

/-- The critical-line mean square of the Hurwitz zeta function is
asymptotic to `T log T` for every fixed real shift `0 < a ≤ 1`. -/
theorem mean_sq_hurwitzZeta_half {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle)
      ((1/2:ℂ)+t*I)‖^2)/(T*Real.log T)) atTop (𝓝 1) := by
  refine criticalMeanSquare_of_family (continuous_hurwitzLine a) (fun N => hurwitzPolynomial a (Icc 1 N))
    (fun N => continuous_hurwitzPolynomial ha.1 _) (fun N => hurwitzDiagonal a (Icc 1 N)) (K:=4*π)
    (by positivity) zero_le_one ?_ ?_ ?_ (fun T : ℝ => ⌊T⌋₊+1) ?_ (hurwitz_long_error ha)
  · exact ⟨1,fun N => by simpa only [one_mul] using shifted_diagonal ha N⟩
  · intro T _ N
    exact hurwitzPolynomial_mean_square ha _ subset_rfl 1 T
  · intro T ht M N hm hmn
    exact shifted_tail_mean ha hm hmn ht
  · refine ⟨2,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    refine ⟨le_rfl,?_⟩
    push_cast; linarith [Nat.floor_le (by linarith : 0≤T)]

end AnalyticNumberTheory.RiemannZeta
