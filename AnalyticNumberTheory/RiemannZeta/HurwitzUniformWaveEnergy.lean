import AnalyticNumberTheory.RiemannZeta.HurwitzUniformWavePairs

/-!
# The uniform mean square of the two shifted Hardy polynomials

The lowest frequency gives a single inverse square root of the shift.
All other frequency pairs together cost one harmonic factor.
-/
noncomputable section
open Real Complex Finset MeasureTheory Set
open scoped Interval ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem sum_shift (N : ℕ) (f : ℕ→ℝ) :
    (∑m∈range N,f (m+1))=∑m∈Finset.Icc 1 N,f m := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]

private theorem cost_sum {a T : ℝ} (N : ℕ) (hN : 1≤N) :
    ∑m∈range N,∑n∈range N,hurwitzWavePairCost a T m n ≤
      16*Real.sqrt T*(Real.sqrt a)⁻¹+(4/Real.log 2)*(Real.sqrt a)⁻¹*N+
      64*Real.sqrt T*(1+Real.log N)+16*(16/Real.log 2+8)*N*(1+Real.log N) := by
  let B := 8*Real.sqrt T*(Real.sqrt a)⁻¹
  let D := (4/Real.log 2)*(Real.sqrt a)⁻¹
  let w := fun m : ℕ => 32*Real.sqrt T*((m+1:ℕ):ℝ)⁻¹
  have hB : 0≤B := by dsimp [B];positivity
  have hw (m : ℕ) : 0≤w m := by dsimp [w];positivity
  have edge (m : ℕ) : (∑n∈range N, if m=0 then (if n=0 then B else 0)+(if n=1 then B else 0)+D else 0) ≤
        if m=0 then 2*B+D*N else 0 := by
    by_cases hm : m=0
    · simp only [hm,ite_true,sum_add_distrib,sum_ite_eq',sum_const,nsmul_eq_mul,card_range]
      split_ifs <;>linarith only [hB]
    · simp [hm]
  have row (m : ℕ) : (∑n∈range N,hurwitzWavePairCost a T m n)≤
      (if m=0 then 2*B+D*N else 0)+2*w m+
      16*∑n∈range N,criticalCosineGap (m+1) (n+1) := by
    unfold hurwitzWavePairCost
    simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
    change (∑n∈range N,if m=0 then _ else 0)+(if m∈range N then w m else 0)+
      (if m+1∈range N then w m else 0)+_≤_
    have h₁ : (if m∈range N then w m else 0)≤w m := by split_ifs <;>simp [hw]
    have h₂ : (if m+1∈range N then w m else 0)≤w m := by split_ifs <;>simp [hw]
    apply add_le_add_left
    exact (add_le_add (add_le_add (edge m) h₁) h₂).trans_eq (by ring)
  apply (sum_le_sum fun m _ => row m).trans
  simp only [sum_add_distrib,sum_ite_eq',←mul_sum]
  rw [if_pos (Finset.mem_range.mpr (by omega : 0<N))]
  have hw' : ∑m∈range N,w m=(32*Real.sqrt T)*∑n∈Finset.Icc 1 N,(n:ℝ)⁻¹ := by
    rw [←sum_shift,mul_sum]
  have hgap : (∑m∈range N,∑n∈range N,criticalCosineGap (m+1) (n+1))=
      ∑m∈Finset.Icc 1 N,∑n∈Finset.Icc 1 N,criticalCosineGap m n := by
    simp_rw [sum_shift];exact sum_shift N (fun k => ∑n∈Finset.Icc 1 N,criticalCosineGap k n)
  have hH : (∑m∈Finset.Icc 1 N,(m:ℝ)⁻¹)≤1+Real.log N := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N
  rw [hw',hgap]
  dsimp only [B,D]
  linarith only [mul_le_mul_of_nonneg_left hH (show 0≤64*Real.sqrt T by positivity),sum_criticalCosineGap N hN]

private theorem sum_indices (N : ℕ) (f : ℕ→ℝ) :
    (∑i∈hurwitzWaveIndices N,f i.2)=2*∑m∈range N,f m := by
  rw [hurwitzWaveIndices,sum_product (f:=fun i : Bool×ℕ => f i.2),Fintype.sum_bool];ring

private theorem norm_pair_symm (a u v : ℝ) (i j : Bool×ℕ) :
    ‖∫t in u..v,hurwitzWave a i t*conj (hurwitzWave a j t)‖=
    ‖∫t in u..v,hurwitzWave a j t*conj (hurwitzWave a i t)‖ := by
  have he (t : ℝ) : hurwitzWave a i t*conj (hurwitzWave a j t)=conj (hurwitzWave a j t*conj (hurwitzWave a i t)) := by
    rw [map_mul,Complex.conj_conj];ring
  simp_rw [he];rw [intervalIntegral.intervalIntegral_conj,Complex.norm_conj]

/-- Integrated square of the direct and reciprocal moving waves, with the
harmonic diagonal removed and an absolute implied constant for all shifts. -/
theorem hurwitz_wave_energy_uniform : ∃ C : ℝ,0<C ∧ ∀ {a T : ℝ}, a∈Ioc (0:ℝ) 1 → 8*Real.pi≤T →
    let N := ⌊Real.sqrt (T/(2*Real.pi))⌋₊+1
    |∫t in (8*Real.pi)..T,‖hurwitzWaveSum a N t‖^2-hurwitzCriticalDiagonal a t|≤
      C*Real.sqrt T*((Real.sqrt a)⁻¹+(1+Real.log T)) := by
  let D := 16/Real.log 2+8
  let K := 4/Real.log 2
  have hD : 0<D := by dsimp [D];positivity
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨8*(16+2*K+64+32*D),by positivity,?_⟩
  intro a T ha ht N
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
  let F := hurwitzWavePairCost a T
  have hpos := hurwitzWavePairCost_nonneg a T
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
  apply le_trans (b:=(∑i∈hurwitzWaveIndices N,∑j∈hurwitzWaveIndices N,(F i.2 j.2+F j.2 i.2)))
  · apply sum_le_sum;intro i _
    apply sum_le_sum;intro j _
    by_cases hij : i=j
    · simpa only [if_pos hij] using add_nonneg (hpos i.2 j.2) (hpos j.2 i.2)
    · rw [if_neg hij]
      let c := max b (max (hurwitzWaveEntry a i) (hurwitzWaveEntry a j))
      by_cases hc : c≤T
      · change ‖∫t in min T c..T,_‖≤_
        rw [min_eq_right hc]
        have hcu := hb.trans_le (le_max_left b (max (hurwitzWaveEntry a i) (hurwitzWaveEntry a j)))
        have hi : hurwitzWaveEntry a i≤c := (le_max_left ..).trans (le_max_right ..)
        have hj : hurwitzWaveEntry a j≤c := (le_max_right ..).trans (le_max_right ..)
        rcases le_total i.2 j.2 with e|e
        · exact (hurwitz_wave_pair_ordered ha i j e hij hcu hc hi hj).trans (le_add_of_nonneg_right (hpos ..))
        · rw [norm_pair_symm a c T i j]
          exact (hurwitz_wave_pair_ordered ha j i e (Ne.symm hij) hcu hc hj hi).trans (le_add_of_nonneg_left (hpos ..))
      · change ‖∫t in min T c..T,_‖≤_
        rw [min_eq_left (le_of_not_ge hc),intervalIntegral.integral_same,norm_zero]
        exact add_nonneg (hpos ..) (hpos ..)
  · have hab : (∑i∈hurwitzWaveIndices N,∑j∈hurwitzWaveIndices N,(F i.2 j.2+F j.2 i.2))=
        8*∑m∈range N,∑n∈range N,F m n := by
      simp only [sum_add_distrib]
      rw [sum_comm (f:=fun i j : Bool×ℕ => F j.2 i.2)]
      simp_rw [sum_indices N]
      rw [←mul_sum,sum_indices N (fun m => ∑n∈range N,F m n)];ring
    rw [hab]
    apply (mul_le_mul_of_nonneg_left (cost_sum (a:=a) (T:=T) N hN) (by norm_num : (0:ℝ)≤8)).trans
    have hL : 0≤1+Real.log N := by have := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN);linarith
    have hL' : 0≤1+Real.log T := hL.trans (by linarith)
    let A := (Real.sqrt a)⁻¹
    let R := Real.sqrt T
    let L := 1+Real.log T
    have hf : 0≤R*A := by dsimp [R,A];positivity
    have hj : 0≤R*L := mul_nonneg (Real.sqrt_nonneg _) hL'
    have h₁ := mul_le_mul_of_nonneg_left hn (show 0≤K*A by dsimp [A];positivity)
    have h₂ := mul_le_mul_of_nonneg_left (show 1+Real.log N≤L by dsimp [L];linarith) (show 0≤64*R by dsimp [R];positivity)
    have h₃ := mul_le_mul_of_nonneg_left (mul_le_mul hn (show 1+Real.log N≤L by dsimp [L];linarith) hL (by positivity))
      (show 0≤16*D by positivity)
    change 8*(16*R*A+K*A*N+64*R*(1+Real.log N)+16*D*N*(1+Real.log N))≤
      8*(16+2*K+64+32*D)*R*(A+L)
    dsimp only [R,L] at *
    nlinarith only [h₁,h₂,h₃,hf,hj,mul_nonneg hD.le hf,mul_nonneg hK.le hj]

end AnalyticNumberTheory.RiemannZeta
