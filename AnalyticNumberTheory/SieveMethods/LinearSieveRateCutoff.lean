import AnalyticNumberTheory.SieveMethods.LinearSieveRateParameters
import AnalyticNumberTheory.SieveMethods.LinearSieveSmallPrimes
import AnalyticNumberTheory.SieveMethods.LinearSieveEulerProducts
import AnalyticNumberTheory.SieveMethods.LinearSievePrimeContraction

/-! # The Euler product at the quantitative linear-sieve cutoff -/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods

/-- At log Y = v²⁰ the cutoff exp(Y/v²³) leaves a uniform Euler discrepancy
of order v⁻⁵⁴ even when the lower dimension loss grows like Y/v¹⁰⁰. -/
theorem linearSieve_rate_cutoff {A B D L v Y z : ℝ} (hA : 0≤A) (hB : 0<B)
    (hD : 0≤D) (hL : 0≤L) (hv : 120≤v) (hY : v^100≤120*Y) (hz : 2≤z)
    (hz' : log z≤Y) (hL' : L*v^100≤D*Y) (s : SieveData) (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) (hsep : ∀p∈P,s.density p≤1-1/B)
    (H : SieveLogMassBounds P s.density 2 z L A) :
    let k := linearSieveEulerConstant A B
    let K := exp (2*k)
    let w := min z (exp (Y/v^23))
    let η := K*(D+120*k)/v^54
    2≤w ∧ w≤z ∧ SieveEulerDimensionOne P s.density z K ∧
    SieveEulerApprox P s.density w z η ∧ log z/log w≤v^23 ∧
      v^23≤(Y/log z)*(log z/log w) := by
  intro k K w η
  have vp : 0<v := by linarith
  have hv₁ : 1≤v := by linarith
  have hYp : 0<Y := (log_pos (show 1<z by linarith)).trans_le hz'
  have hk : 0≤k := by dsimp [k,linearSieveEulerConstant]; positivity
  have hK : 0<K := exp_pos _
  have hη : 0≤η := by dsimp [η]; positivity
  have hscale : v^23≤Y := by
    have hpow : v^24≤v^100 := pow_le_pow_right₀ hv₁ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hv (pow_pos vp 23).le
    nlinarith only [hY,hpow,hh]
  have hwe : 2≤exp (Y/v^23) := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mp
    apply (le_div_iff₀ (pow_pos vp _)).mpr
    have h₂ : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_right h₂ (pow_pos vp 23).le).trans (by simpa using hscale)
  have hw : 2≤w := le_min hz hwe
  have hwz : w≤z := min_le_left ..
  have hlw := Real.log_pos (show 1<w by linarith)
  have hlz := Real.log_pos (show 1<z by linarith)
  have hP₁ (p : ℕ) (hp : p∈P) : 1≤p := (hP p hp).one_lt.le
  have hg (p : ℕ) (hp : p∈P) := And.intro (s.density_nonneg_of_prime (hP p hp)) (hsep p hp)
  have hdim : SieveEulerDimensionOne P s.density z K := by
    intro c hc a ha
    exact (sieveEulerBelow_ratio_comparison ha.1 ha.2 hP₁ hB hg hL hA (H.mono_interval ha.1 hc.2)).1
  have hlog : log w ≤ Y/v^23 := by
    rw [← Real.log_exp (Y/v^23)]
    exact Real.log_le_log (by linarith) (min_le_right ..)
  have hlast : v^23 ≤ (Y/log z)*(log z/log w) := by
    rw [show Y/log z*(log z/log w)=Y/log w by field_simp]
    apply (le_div_iff₀ hlw).mpr
    linarith [(le_div_iff₀ (pow_pos vp 23)).mp hlog]
  refine ⟨hw,hwz,hdim,?_,?_,hlast⟩
  · intro c hc t ht
    have hW := (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) c).le
    by_cases he : z≤exp (Y/v^23)
    · have hw' : w=z := min_eq_left he
      have hec : c=z := by linarith [hc.1,hc.2]
      have het : t=z := by linarith [ht.1,ht.2]
      subst c
      subst t
      simpa [hlz.ne'] using mul_nonneg hη hW
    have hw' : w=exp (Y/v^23) := min_eq_right (not_le.mp he).le
    have hew : log w=Y/v^23 := by rw [hw',log_exp]
    have hh := sieveEulerBelow_uniform_comparison hw hc.1 hP₁ hB hg hL hA (H.mono_interval hw hc.2) t ht
    have hLg : (L+k)*v^100≤(D+120*k)*Y := by
      nlinarith only [hL',mul_le_mul_of_nonneg_left hY hk]
    have hcY := (Real.log_le_log (show 0<c by linarith [hc.1]) hc.2).trans hz'
    have hcoef : K*(L+k)*log c/(log w)^2 ≤ η := by
      rw [hew]
      dsimp only [η]
      apply le_trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcY (mul_nonneg hK.le (add_nonneg hL hk)))
        (sq_nonneg (Y/v^23)))
      rw [show K*(L+k)*Y/(Y/v^23)^2=K*((L+k)*v^46/Y) by
        field_simp [hYp.ne',vp.ne'] <;> ring, mul_div_assoc K (D+120*k) (v^54)]
      apply mul_le_mul_of_nonneg_left _ hK.le
      rw [div_le_div_iff₀ hYp (pow_pos vp 54)]
      convert hLg using 1 <;> ring
    apply hh.trans
    convert mul_le_mul_of_nonneg_right hcoef hW using 1 <;> ring
  · by_cases he : z≤exp (Y/v^23)
    · rw [show w=z from min_eq_left he,div_self hlz.ne']
      exact one_le_pow₀ hv₁
    · rw [show w=exp (Y/v^23) from min_eq_right (not_le.mp he).le,log_exp]
      apply (div_le_iff₀ (div_pos hYp (pow_pos vp _))).mpr
      convert hz' using 1
      field_simp [vp.ne']

end AnalyticNumberTheory.SieveMethods
