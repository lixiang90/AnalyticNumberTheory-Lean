import AnalyticNumberTheory.RiemannZeta.HurwitzWavePairs

/-!
# The mean square of the two shifted Hardy polynomials

All four combinations of direct and reciprocal indices are summed.
The reciprocal logarithmic spacing costs a single harmonic factor.
-/
noncomputable section
open Real Complex Finset MeasureTheory Set
open scoped Interval ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem sum_indices (N : ℕ) (f : ℕ→ℝ) :
    (∑i∈hurwitzWaveIndices N,f i.2)=2*∑m∈range N,f m := by
  rw [hurwitzWaveIndices,sum_product (f:=fun i : Bool×ℕ => f i.2),Fintype.sum_bool];ring

private theorem sum_shift_index (N : ℕ) (f : ℕ→ℝ) :
    (∑m∈range N,f (m+1))=∑m∈Finset.Icc 1 N,f m := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]

private theorem gap_nonneg (k l : ℕ) : 0≤criticalCosineGap k l := by
  unfold criticalCosineGap;split_ifs <;>positivity

private theorem cost_sum {a T : ℝ} (ha : 0<a) (hT : 0≤T) (N : ℕ) (hN : 1≤N) :
    let F := fun m n : ℕ => (if m=n then 8*Real.sqrt T*a⁻¹^2*((m+1:ℕ):ℝ)⁻¹ else 0)+
                              2*a⁻¹^3*criticalCosineGap (m+1) (n+1)
    (∑i∈hurwitzWaveIndices N,∑j∈hurwitzWaveIndices N,F i.2 j.2)≤
      32*Real.sqrt T*a⁻¹^2*(1+Real.log N)+8*a⁻¹^3*((16/Real.log 2+8)*N*(1+Real.log N)) := by
  intro F
  have e (i : Bool×ℕ) := sum_indices N (F i.2)
  simp_rw [e]
  rw [sum_indices N (fun n => 2*∑m∈range N,F n m)]
  simp only [F,sum_add_distrib,sum_ite_eq,←mul_sum]
  have hsel (m : ℕ) : (if m∈range N then 8*Real.sqrt T*a⁻¹^2*((m+1:ℕ):ℝ)⁻¹ else 0)=
      if m∈range N then (8*Real.sqrt T*a⁻¹^2)*((m+1:ℕ):ℝ)⁻¹ else 0 := rfl
  have hdiag : (∑m∈range N,if m∈range N then 8*Real.sqrt T*a⁻¹^2*((m+1:ℕ):ℝ)⁻¹ else 0)=
      (8*Real.sqrt T*a⁻¹^2)*∑m∈Finset.Icc 1 N,(m:ℝ)⁻¹ := by
    rw [←sum_shift_index,mul_sum];apply sum_congr rfl;intro m hm;rw [if_pos hm]
  have hgap : (∑m∈range N,∑n∈range N,criticalCosineGap (m+1) (n+1))=
      ∑m∈Finset.Icc 1 N,∑n∈Finset.Icc 1 N,criticalCosineGap m n := by
    simp_rw [sum_shift_index];exact sum_shift_index N (fun k => ∑n∈Finset.Icc 1 N,criticalCosineGap k n)
  have hH : (∑m∈Finset.Icc 1 N,(m:ℝ)⁻¹)≤1+Real.log N := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N
  have h₁ := mul_le_mul_of_nonneg_left hH (show 0≤32*Real.sqrt T*a⁻¹^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (sum_criticalCosineGap N hN) (show 0≤8*a⁻¹^3 by positivity)
  rw [hdiag,hgap]
  linarith only [h₁,h₂]

/-- The moving two-polynomial model differs from its harmonic diagonal in
integrated square by O_a(√T log T). -/
theorem hurwitz_wave_energy_error {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi≤T →
    let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
    |∫t in (8*Real.pi)..T,‖hurwitzWaveSum a N t‖^2-hurwitzCriticalDiagonal a t|≤
      C*Real.sqrt T*(1+Real.log T) := by
  let D := 16/Real.log 2+8
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨32*a⁻¹^2+16*a⁻¹^3*D,by have := ha.1;positivity,?_⟩
  intro T ht N
  let b := 8*Real.pi
  have hb : 0<b := by dsimp [b];positivity
  have ht₁ : 4≤T := by linarith [Real.pi_gt_three]
  have ht₀ := hb.trans_le ht
  have hN : 1≤N := Nat.succ_pos _
  have hroot : 2≤Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  have hn : (N:ℝ)≤2*Real.sqrt T := by
    dsimp only [N];rw [Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (Real.sqrt_nonneg (T/(2*Real.pi))),Real.sqrt_le_sqrt (div_le_self ht₀.le (by linarith [Real.pi_gt_three]) : T/(2*Real.pi)≤T)]
  have hnT : (N:ℝ)≤T := hn.trans (by nlinarith [Real.sq_sqrt ht₀.le,sq_nonneg (Real.sqrt T-2)])
  have hl := Real.log_le_log (Nat.cast_pos.mpr hN) hnT
  let F := fun m n : ℕ => (if m=n then 8*Real.sqrt T*a⁻¹^2*((m+1:ℕ):ℝ)⁻¹ else 0)+2*a⁻¹^3*criticalCosineGap (m+1) (n+1)
  have hpos (m n : ℕ) : 0≤F m n := by dsimp [F];split_ifs <;>positivity [gap_nonneg (m+1) (n+1),ha.1]
  have hem {t : ℝ} (htb : b≤t) (htT : t≤T) : (∑i∈hurwitzWaveIndices N,
      ‖enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t‖^2)=hurwitzCriticalDiagonal a t := by
    apply hurwitzWaveSum_diagonal ha (hb.trans_le htb).le
    · apply Real.le_sqrt_of_sq_le;apply (le_div_iff₀ (by positivity : 0<2*Real.pi)).mpr
      dsimp [b] at htb;linarith
    · apply Nat.succ_le_succ;apply Nat.floor_mono;apply Real.sqrt_le_sqrt;exact div_le_div_of_nonneg_right htT (by positivity)
  have H := moving_polynomial_energy_bound (hurwitzWaveIndices N) (hurwitzWaveEntry a) (hurwitzWave a) (continuous_hurwitzWave a) ht
  have he : (∫t in b..T,‖hurwitzWaveSum a N t‖^2-hurwitzCriticalDiagonal a t)=
      ∫t in b..T,‖hurwitzWaveSum a N t‖^2-∑i∈hurwitzWaveIndices N,‖enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t‖^2 := by
    apply intervalIntegral.integral_congr;intro t h;rw [uIcc_of_le (show b≤T from ht)] at h;dsimp only;rw [hem h.1 h.2]
  rw [he]
  apply H.trans
  have hcost := cost_sum ha.1 ht₀.le N hN
  apply le_trans (b:=(∑i∈hurwitzWaveIndices N,∑j∈hurwitzWaveIndices N,F i.2 j.2))
  · apply sum_le_sum;intro i _
    apply sum_le_sum;intro j _
    by_cases hij : i=j
    · simpa only [if_pos hij] using hpos i.2 j.2
    · rw [if_neg hij]
      let c := max b (max (hurwitzWaveEntry a i) (hurwitzWaveEntry a j))
      by_cases hc : c≤T
      · change ‖∫t in min T c..T,_‖≤_
        rw [min_eq_right hc]
        exact hurwitz_wave_pair_bound ha i j hij (hb.trans_le (le_max_left ..)) hc
          ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))
      · change ‖∫t in min T c..T,_‖≤_
        rw [min_eq_left (le_of_not_ge hc),intervalIntegral.integral_same,norm_zero];exact hpos _ _
  · apply hcost.trans
    have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left hl 1) (show 0≤32*Real.sqrt T*a⁻¹^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (mul_le_mul hn (show 1+Real.log N≤1+Real.log T by linarith) hL (by positivity)) (show 0≤8*a⁻¹^3*D by have := ha.1;positivity)
    dsimp only [D] at *;linarith only [h₁,h₂]

end AnalyticNumberTheory.RiemannZeta
