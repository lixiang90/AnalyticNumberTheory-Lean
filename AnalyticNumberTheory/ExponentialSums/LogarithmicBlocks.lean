import AnalyticNumberTheory.ExponentialSums.LogarithmicPhases
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# Weyl bounds for incomplete logarithmic blocks

A shift of length about `M / |τ|^(1/3)` balances the two terms obtained
from van der Corput differencing. The bounds hold uniformly in the
shift in the logarithm and for all incomplete dyadic blocks.
-/

open Complex Real Finset
open AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.ExponentialSums

/-- The additive character associated to the logarithm. -/
noncomputable def logPhaseTerm (τ a : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2*Real.pi*(logPhase τ a n:ℂ)*I)

/-- A forward-differenced exponential sum of a shifted logarithm. -/
private noncomputable def diffBlock (τ a : ℝ) (M b r : ℕ) :=
  ∑ n ∈ Ioc M b, Complex.exp (2*Real.pi*((logPhase τ a (n+r:ℕ)-logPhase τ a n:ℝ):ℂ)*I)

private theorem diffBlock_norm {M b r : ℕ} (hM : 1≤M) (hb : b≤2*M)
    (hr : 1≤r) (hr' : r≤M) {a τ U : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hU : 1≤U) (hτ : |τ| = U^6) :
    ‖diffBlock τ a M b r‖ ≤ 600000*
      (U^3*√r/√M+(√M)^3/U^3*(√r)⁻¹) := by
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast hM
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hU0 : 0<U := by linarith
  have hs := Real.sqrt_pos.mpr hM0
  have hs' := Real.sq_sqrt hM0.le
  have hR := Real.sqrt_pos.mpr hr0
  have hR' := Real.sq_sqrt hr0.le
  by_cases h : M<b
  · have H := logPhase_difference_bound hM h hb hr hr' ha (by rw [hτ]; positivity)
    let lam := |τ| * r/(256*(M:ℝ)^3)
    have he : √lam = U^3*√r/(16*(√M)^3) := by
      apply (Real.sqrt_eq_iff_eq_sq (by dsimp [lam]; positivity) (by positivity)).mpr
      dsimp [lam]
      rw [hτ,← hs',← hR',Real.sqrt_sq hs.le, Real.sqrt_sq hR.le]
      field_simp
      ring
    change ‖diffBlock τ a M b r‖ ≤ 35860*(((b:ℝ)-M)*√lam+(√lam)⁻¹) at H
    rw [he] at H
    have hlen : (b:ℝ)-M ≤ (M:ℝ) := by
      have hh : (b:ℝ) ≤ 2*M := by exact_mod_cast hb
      linarith
    have h1 : ((b:ℝ)-M)*(U^3*√r/(16*(√M)^3)) ≤ U^3*√r/√M := by
      apply (mul_le_mul_of_nonneg_right hlen (by positivity)).trans
      calc (M:ℝ)*(U^3*√r/(16*(√M)^3)) = (U^3*√r/√M)/16 := by field_simp; nlinarith only [hs']
           _ ≤ _ := by
             have : 0≤U^3*√r/√M := by positivity
             linarith
    have h2 : (U^3*√r/(16*(√M)^3))⁻¹ = 16*((√M)^3/U^3*(√r)⁻¹) := by field_simp <;> ring
    apply H.trans
    rw [h2]
    nlinarith only [h1,show 0≤U^3*√r/√M by positivity,show 0≤(√M)^3/U^3*(√r)⁻¹ by positivity]
  · simp only [diffBlock,Ioc_eq_empty_of_le (not_lt.mp h),sum_empty,norm_zero]
    positivity

private theorem diff_sum {M d H : ℕ} (hM : 1 ≤ M) (hd : d ≤ M) (hH : 1≤H) (hHM : H≤M+1)
    {a τ U : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hU : 1≤U) (hτ : |τ| = U^6) :
    ∑ r ∈ Ico 1 H, (1-(r:ℝ)/H)*‖diffBlock τ a M (M+d-r) r‖ ≤
      600000*(U^3/√M*(H*√H)+(√M)^3/U^3*(2*√H)) := by
  have hsqrt : ∑ r ∈ Ico 1 H, √(r:ℝ) ≤ H*√H := by
    calc _ ≤ ∑ _r ∈ Ico 1 H, √(H:ℝ) := by
              refine sum_le_sum fun r hr => Real.sqrt_le_sqrt ?_
              exact_mod_cast (mem_Ico.mp hr).2.le
         _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast (show (Ico 1 H).card≤H by simp)
  have hinv : ∑ r ∈ Ico 1 H, (√(r:ℝ))⁻¹ ≤ 2*√H := by
    apply le_trans _ (sum_Icc_inv_sqrt_le H)
    exact sum_le_sum_of_subset_of_nonneg (fun r hr => mem_Icc.mpr ⟨(mem_Ico.mp hr).1,(mem_Ico.mp hr).2.le⟩)
      (fun r _ _ => by positivity)
  have hterm (r) (hr : r∈Ico 1 H) : (1-(r:ℝ)/H)*‖diffBlock τ a M (M+d-r) r‖ ≤
      600000*(U^3/√M*√r+(√M)^3/U^3*(√r)⁻¹) := by
    have hr' := mem_Ico.mp hr
    apply (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self 1 (by positivity))).trans
    simpa only [div_mul_eq_mul_div] using diffBlock_norm hM (by omega : M+d-r≤2*M) hr'.1 (by omega) ha hU hτ
  apply (sum_le_sum hterm).trans
  rw [← Finset.mul_sum,sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  gcongr

private theorem logPhase_weyl_middle {M d : ℕ} (hM : 1≤M) (hd : d≤M)
    {a τ U : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hU : 1≤U) (hτ : |τ| = U^6)
    (hlo : U^2 ≤ (M:ℝ)) (hhi : (M:ℝ) ≤ U^4) :
    ‖∑ n ∈ Ioc M (M+d), logPhaseTerm τ a n‖ ≤ 10000*U*√M := by
  have hu : 0<U := by linarith
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  let H := ⌊(M:ℝ)/U^2⌋₊+1
  have hH : 1≤H := Nat.succ_pos _
  have hh : 0<(H:ℝ) := by exact_mod_cast hH
  have hfloor := Nat.floor_le (by positivity : 0 ≤ (M:ℝ)/U^2)
  have hleft : (M:ℝ) ≤ H*U^2 := (div_le_iff₀ (sq_pos_of_pos hu)).mp
    (by simpa only [H,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one ((M:ℝ)/U^2)).le)
  have hu2 : 1 ≤ U^2 := one_le_pow₀ hU
  have hHM : H ≤ M+1 := by
    dsimp [H]
    apply Nat.add_le_add_right
    exact Nat.floor_le_of_le (div_le_self hm.le hu2)
  have hright : (H:ℝ)*U^2 ≤ 2*M := by
    dsimp [H]; push_cast
    nlinarith only [(le_div_iff₀ (sq_pos_of_pos hu)).mp hfloor,hlo]
  have hs := Real.sqrt_pos.mpr hm
  have hw := Real.sqrt_pos.mpr hh
  have hs' := Real.sq_sqrt hm.le
  have hw' := Real.sq_sqrt hh.le
  have hsw : √(M:ℝ) ≤ √H*U := by
    apply (sq_le_sq₀ hs.le (by positivity)).mp
    rw [mul_pow,hw',hs']
    exact hleft
  have hws : √(H:ℝ)*U ≤ 2*√M := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hw',hs']
    nlinarith only [hright,hm]
  have hA : U^3/√M*(H*√H) ≤ 2*((H:ℝ)*U^2) := by
    calc _ = ((H:ℝ)*U^2)*(√H*U/√M) := by ring
         _ ≤ ((H:ℝ)*U^2)*2 := mul_le_mul_of_nonneg_left ((div_le_iff₀ hs).mpr hws) (by positivity)
         _ = _ := by ring
  have hB : (√(M:ℝ))^3/U^3*(2*√H) ≤ 2*((H:ℝ)*U^2) := by
    have hpow : (√(M:ℝ))^3 ≤ √H*U^5 := by
      calc _ = √(M:ℝ)*M := by nlinarith only [congrArg (fun y : ℝ => √(M:ℝ)*y) hs']
           _ ≤ (√H*U)*U^4 := mul_le_mul hsw hhi hm.le (by positivity)
           _ = _ := by ring
    calc _ ≤ (√H*U^5)/U^3*(2*√H) := by gcongr
         _ = _ := by field_simp; nlinarith only [hw',congrArg (fun y : ℝ => 2*U^5*y) hw']
  have hdh : (d:ℝ)+H ≤ 3*M := by
    have hd' : (d:ℝ) ≤ M := by exact_mod_cast hd
    have hH' : (H:ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast hHM
    linarith [show (1:ℝ)≤M by exact_mod_cast hM]
  have hsum := diff_sum hM hd hH hHM ha hU hτ
  have hW := vanDerCorput_weyl_differencing (logPhase τ a) M d H hH
  change (H:ℝ)*‖∑ n ∈ Ioc M (M+d), logPhaseTerm τ a n‖^2 ≤
    ((d:ℝ)+H)*((d:ℝ)+H+2*∑ r ∈ Ico 1 H, (1-(r:ℝ)/H)*‖diffBlock τ a M (M+d-r) r‖) at hW
  have hh' : (d:ℝ)+H+2*∑ r ∈ Ico 1 H, (1-(r:ℝ)/H)*‖diffBlock τ a M (M+d-r) r‖ ≤
      5000000*((H:ℝ)*U^2) := by nlinarith only [hdh,hleft,hsum,hA,hB, mul_nonneg hh.le (sq_nonneg U)]
  have hsq := hW.trans ((mul_le_mul_of_nonneg_left hh' (by positivity)).trans
    (mul_le_mul_of_nonneg_right hdh (by positivity)))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply (le_of_mul_le_mul_left (a:= (H:ℝ)) _ hh)
  rw [mul_pow,mul_pow,hs']
  nlinarith only [hsq, mul_nonneg (mul_nonneg hh.le hm.le) (sq_nonneg U)]

/-- The Weyl bound for an incomplete dyadic logarithm sum. For `U ≥ 1`
with `|τ| = U^6`, every block below `100 |τ|` has size `O(U √M)`. -/
theorem logPhase_weyl_block {M b : ℕ} (hM : 1≤M) (hb : b≤2*M)
    {a τ U : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hU : 1≤U) (hτ : |τ| = U^6)
    (hcut : (M:ℝ) ≤ 100*U^6) :
    ‖∑ n ∈ Ioc M b, logPhaseTerm τ a n‖ ≤ 10000*U*√M := by
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have hs := Real.sqrt_pos.mpr hm
  have hs' := Real.sq_sqrt hm.le
  have hu : 0<U := by linarith
  by_cases h : M<b
  · by_cases hlo : U^2≤(M:ℝ)
    · by_cases hhi : (M:ℝ)≤U^4
      · have H := logPhase_weyl_middle (d:=b-M) hM (by omega) ha hU hτ hlo hhi
        rwa [Nat.add_sub_of_le h.le] at H
      · have ht : 0 < |τ| := by rw [hτ]; positivity
        have H := logPhase_second_derivative_bound hM h hb ha ht
        have he : √(|τ|/(9*(M:ℝ)^2)) = U^3/(3*M) := by
          rw [hτ,show U^6=(U^3)^2 by ring, Real.sqrt_div (by positivity),Real.sqrt_sq (by positivity),
            Real.sqrt_mul (by norm_num),Real.sqrt_sq hm.le,show √(9:ℝ)=3 by norm_num]
        rw [he] at H
        have hab : (b:ℝ)≤2*M := by exact_mod_cast hb
        have hup : U^2≤√(M:ℝ) := by
          apply (sq_le_sq₀ (sq_nonneg U) hs.le).mp
          rw [hs']; nlinarith only [le_of_not_ge hhi,show (U^2)^2=U^4 by ring]
        have hsp : √(M:ℝ) ≤ 10*U^3 := by
          apply (sq_le_sq₀ hs.le (by positivity)).mp
          rw [hs']; nlinarith only [hcut,show (10*U^3)^2 = 100*U^6 by ring]
        have h1 : ((b:ℝ)-M)*(U^3/(3*M)) ≤ U*√M := by
          calc _ ≤ (M:ℝ)*(U^3/(3*M)) := by gcongr; linarith
               _ ≤ U^3 := by field_simp; nlinarith only [mul_nonneg hm.le (pow_nonneg hu.le 3)]
               _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hup hu.le]
        have h2 : (U^3/(3*(M:ℝ)))⁻¹ ≤ 30*(U*√M) := by
          rw [inv_div,div_le_iff₀ (by positivity)]
          have hh := mul_le_mul_of_nonneg_right hsp hs.le
          have hh' := mul_le_mul_of_nonneg_right hU (show 0 ≤ √(M:ℝ)*U^3 by positivity)
          nlinarith only [hh,hh',hs']
        exact H.trans (by nlinarith only [h1,h2,mul_nonneg hu.le hs.le])
    · have hsz : √(M:ℝ) ≤ U := by apply (sq_le_sq₀ hs.le hu.le).mp; rw [hs']; exact le_of_not_ge hlo
      have hnorm (n : ℕ) : ‖logPhaseTerm τ a n‖=1 := by simp [logPhaseTerm,Complex.norm_exp]
      calc _ ≤ ∑ n ∈ Ioc M b, ‖logPhaseTerm τ a n‖ := norm_sum_le ..
           _ = (b-M:ℕ) := by simp only [hnorm,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]
           _ ≤ (M:ℝ) := by exact_mod_cast (show b-M ≤ M by omega)
           _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hsz hs.le,hs',mul_nonneg hu.le hs.le]
  · rw [Ioc_eq_empty_of_le (not_lt.mp h),sum_empty,norm_zero]; positivity

end AnalyticNumberTheory.ExponentialSums
