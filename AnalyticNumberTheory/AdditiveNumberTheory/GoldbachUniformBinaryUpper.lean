import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachLogWeights
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveFactor
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachAsymptotic

/-!
# A uniform binary upper bound inside a ternary problem

The ordinary binary Selberg sieve supplies the two missing prime factors
of log N even when the target varies below N. Small targets and odd targets
are handled directly.
-/

open Finset Real Filter
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AdditiveNumberTheory

theorem goldbachRepCount_le_self (m : ℕ) : goldbachRepCount m≤m := by
  exact (card_filter_le ..).trans (by simp [Nat.card_Icc])

private theorem goldbachRepCount_le_two_of_odd {m : ℕ} (hm : Odd m) : goldbachRepCount m≤2 := by
  have hsub : (Icc 1 m).filter (fun p => p.Prime ∧ (m-p).Prime) ⊆ {2,m-2} := by
    intro p hp
    obtain ⟨hi,hp,hq⟩ := mem_filter.mp hp
    have hle := (mem_Icc.mp hi).2
    rcases hp.eq_two_or_odd with he|he
    · simp [he]
    rcases hq.eq_two_or_odd with hf|hf
    · simp [show p=m-2 by omega]
    · obtain ⟨c,hc⟩ := hm
      omega
  exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans_eq (by simp))

private theorem goldbachSieveFactor_two_mul (k : ℕ) (hk : 0<k) :
    goldbachSieveFactor (2*k)=goldbachSieveFactor k := by
  unfold goldbachSieveFactor
  congr 1
  ext p
  simp only [mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp,hd,_⟩,h2⟩
    refine ⟨⟨hp,?_,hk.ne'⟩,h2⟩
    rcases hp.dvd_mul.mp hd with hd|hd
    · have := Nat.le_of_dvd (by decide : 0<2) hd;omega
    · exact hd
  · rintro ⟨⟨hp,hd,_⟩,h2⟩
    exact ⟨⟨hp,hd.trans (dvd_mul_left k 2),by positivity⟩,h2⟩

/-- The binary Selberg upper bound with one common log scale for every target m ≤ N. -/
theorem goldbachRepCount_uniform_upper :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀m≤N,
      (goldbachRepCount m:ℝ)≤C*((N:ℝ)/(log N)^2)*goldbachSieveFactor m := by
  obtain ⟨K,hK,h⟩ := selberg_goldbach_upper_bound
  let C := 4*K+2
  have hc : 2≤C := by dsimp [C];linarith
  refine ⟨C,by linarith,?_⟩
  have hcast := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [hcast.eventually (eventually_const_log_pow_le_rpow 1 2 (by norm_num : (0:ℝ)<1/2)),
    eventually_ge_atTop (4:ℕ)] with N hlog hN
  rw [one_mul,←sqrt_eq_rpow] at hlog
  have hn : (4:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<log N := log_pos (by linarith)
  have hroot : 2≤sqrt N := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) N)
  have hscale : sqrt N≤(N:ℝ)/(log N)^2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hL)]
    nlinarith [mul_le_mul_of_nonneg_left hlog (sqrt_nonneg (N:ℝ))]
  intro m hm
  have hs := one_le_goldbachSieveFactor m
  have scale : 2*sqrt N ≤ C*((N:ℝ)/(log N)^2)*goldbachSieveFactor m := by
    calc
      _ ≤ C*((N:ℝ)/(log N)^2) := mul_le_mul hc hscale (sqrt_nonneg _) (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs
  rcases Nat.even_or_odd m with ⟨k,rfl⟩|hodd
  · rw [←two_mul] at hm scale ⊢
    by_cases hk : (k:ℝ)≤sqrt N
    · exact (show (goldbachRepCount (2*k):ℝ)≤2*(k:ℝ) by exact_mod_cast goldbachRepCount_le_self (2*k)).trans ((mul_le_mul_of_nonneg_left hk (by norm_num : (0:ℝ)≤2)).trans scale)
    have hkn : 2≤k := by exact_mod_cast hroot.trans (le_of_not_ge hk)
    have hk' : 0<k := by omega
    have hkR : (k:ℝ)≤N := by exact_mod_cast (show k≤N by omega)
    have hlogk : log N/2≤log k := by
      rw [←Real.log_sqrt (by positivity)]
      exact Real.log_le_log (by positivity) (le_of_not_ge hk)
    have hfactor := goldbachSieveFactor_two_mul k hk'
    rw [hfactor]
    have H := h k hkn
    change (goldbachRepCount (2*k):ℝ)≤K*((k:ℝ)/(log k)^2)*goldbachSieveFactor k at H
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (by linarith [one_le_goldbachSieveFactor k])
    have hg : 0<log k := by linarith
    have hfrac : (k:ℝ)/(log k)^2 ≤ 4*((N:ℝ)/(log N)^2) := by
      rw [←mul_div_assoc,div_le_div_iff₀ (sq_pos_of_pos hg) (sq_pos_of_pos hL)]
      have hh : (log N)^2 ≤ 4*(log k)^2 := by nlinarith [mul_nonneg (show 0≤2*log k-log N by linarith) (show 0≤2*log k+log N by linarith)]
      nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) k),
        mul_le_mul_of_nonneg_right hkR (sq_nonneg (log k))]
    calc
      _ ≤ K*(4*((N:ℝ)/(log N)^2)) := mul_le_mul_of_nonneg_left hfrac hK.le
      _ ≤ _ := by dsimp [C];nlinarith [show 0≤(N:ℝ)/(log N)^2 by positivity]
  · have h' : (goldbachRepCount m:ℝ)≤2 := by exact_mod_cast goldbachRepCount_le_two_of_odd hodd
    linarith

end AnalyticNumberTheory.AdditiveNumberTheory
