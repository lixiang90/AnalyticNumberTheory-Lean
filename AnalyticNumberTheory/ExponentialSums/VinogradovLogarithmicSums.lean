import AnalyticNumberTheory.ExponentialSums.VinogradovLogBlocks
import AnalyticNumberTheory.ExponentialSums.HigherLogarithmicBlocks

/-!
# Vinogradov's estimate for the logarithmic exponential sum

Uniformly for `1 ≤ N ≤ t` and `N ≤ M ≤ 2N`, the incomplete sum of
`n^(it)` is bounded by a constant times
`N exp(-c (log N)^3/(log t)^2)`, with absolute positive constants.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem logBlock_cast {N M : ℕ} (f : ℝ → ℂ) :
    (∑ n∈Ioc (N:ℤ) M, f n) = ∑ n∈Ioc N M, f n := by
  apply sum_bij' (s:=Ioc (N:ℤ) M) (t:=Ioc N M) (fun (n:ℤ) _ => n.toNat) (fun (n:ℕ) _ => (n:ℤ))
  · intro n hn; obtain ⟨h,h'⟩ := mem_Ioc.mp hn; apply mem_Ioc.mpr; omega
  · intro n hn; obtain ⟨h,h'⟩ := mem_Ioc.mp hn; apply mem_Ioc.mpr; omega
  · intro n hn; have := (mem_Ioc.mp hn).1; omega
  · intro n _; simp
  · intro n hn
    have H : 0≤n := by have := (mem_Ioc.mp hn).1; omega
    congr 1; exact_mod_cast (Int.toNat_of_nonneg H).symm

private theorem logBlock_trivial {N M : ℕ} (hM : M≤2*N) (t : ℝ) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log n)‖ ≤ N := by
  apply (norm_sum_le ..).trans
  simp only [norm_e,sum_const,nsmul_eq_mul,mul_one,Int.card_Ioc]
  exact_mod_cast (show ((M:ℤ)-N).toNat≤N by omega)

private theorem logBlock_fixed_height {N M : ℕ} {t κ C : ℝ} (hN : 0<N)
    (hX : 100≤Real.log (N:ℝ)) (hM : M≤2*N) (hNt : (N:ℝ)≤t) (hT : t≤(N:ℝ)^16)
    (H : ∀ {M b : ℕ} {τ : ℝ}, 1≤M → b≤2*M → |τ| ≤ (M:ℝ)^16 → (M:ℝ) ≤ |τ|^2 →
      ‖∑ n ∈ Ioc M b,e (logPhase τ 0 n)‖ ≤ C*(M:ℝ)^(1-κ)) :
    ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log n)‖ ≤
      C*N*Real.exp (-κ*Real.log N) := by
  have hNr : 0<(N:ℝ) := by positivity
  have ht : 0<t := hNr.trans_le hNt
  have hpi : 1≤2*Real.pi := by linarith only [Real.pi_gt_three]
  have hNbig : 100≤(N:ℝ) := by linarith only [Real.log_le_sub_one_of_pos hNr,hX]
  let τ := t/(2*Real.pi)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hτt : τ≤t := (div_le_self ht.le hpi)
  have hτN : N≤τ^2 := by
    have H' : (N:ℝ)/8≤τ := by
      dsimp [τ]; apply div_le_div₀ ht.le hNt (by positivity) (by linarith only [Real.pi_lt_four])
    have hsq := pow_le_pow_left₀ (by positivity) H' 2
    nlinarith only [hsq,mul_le_mul_of_nonneg_left hNbig hNr.le]
  rw [logBlock_cast (N:=N) (M:=M) (fun x => e ((t/(2*Real.pi))*Real.log x))]
  have Ha := H hN hM (by rw [abs_of_pos hτ]; exact hτt.trans hT)
    (by rw [abs_of_pos hτ]; exact hτN)
  apply (show _ ≤ _ from by simpa [logPhase,τ] using Ha).trans_eq
  rw [Real.rpow_def_of_pos hNr,show Real.log N*(1-κ)=Real.log N+(-κ*Real.log N) by ring,
    Real.exp_add,Real.exp_log hNr]; ring

/-- Vinogradov's logarithmic exponential-sum bound, uniform in the height,
length, and upper endpoint of the dyadic interval. -/
theorem vinogradov_logarithmic_block :
    ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ (N M : ℕ) (t : ℝ),
      1≤N → N≤M → M≤2*N → (N:ℝ)≤t → 16≤t →
      ‖∑ n∈Ioc (N:ℤ) M, e ((t/(2*Real.pi))*Real.log n)‖ ≤
        C*N*Real.exp (-c*(Real.log N)^3/(Real.log t)^2) := by
  obtain ⟨κ,C,hκ,hC,H⟩ := logarithmic_block_power_saving 16 (by norm_num)
  let D := (1000000000000:ℝ)
  let c := min κ (1/D)
  let B := Real.exp 4265200+4
  have hD : 0<D := by norm_num [D]
  have hc : 0<c := lt_min hκ (by positivity)
  have hcD : c≤1/D := min_le_right ..
  have hcκ : c≤κ := min_le_left ..
  have hc1 : c≤1 := hcD.trans (by norm_num [D])
  have hB : 0<B := by dsimp [B]; positivity
  let K := Real.exp 100 + C+B
  have hKC : C≤K := by dsimp [K]; linarith only [hB,Real.exp_pos 100]
  have hKB : B≤K := by dsimp [K]; linarith only [hC,Real.exp_pos 100]
  have hKe : Real.exp 100≤K := by dsimp [K]; linarith only [hC,hB]
  refine ⟨c,hc,K,hC.trans_le hKC,?_⟩
  intro N M t hN hNM hM hNt ht
  let X := Real.log (N:ℝ)
  let T := Real.log t
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hX : 0≤X := Real.log_nonneg (by exact_mod_cast hN)
  have hT : 0<T := Real.log_pos (by linarith)
  have hXT : X≤T := Real.log_le_log hNr hNt
  let u := c*X^3/T^2
  have hu : u≤c*X := by
    apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
    have hsq := pow_le_pow_left₀ hX hXT 2
    nlinarith only [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le hX)]
  change _ ≤ K*N*Real.exp (-c*X^3/T^2)
  rw [show -c*X^3/T^2= -u by dsimp [u]; ring]
  by_cases hbig : 100≤X
  · have hX0 : 0<X := by linarith
    let l := ⌊T/(2*X)⌋₊
    have hq := Nat.floor_le (show 0≤T/(2*X) by positivity)
    have hq' := Nat.lt_floor_add_one (T/(2*X))
    change (l:ℝ)≤T/(2*X) at hq
    change T/(2*X)<(l:ℝ)+1 at hq'
    have hLT : 2*l*X≤T := by linarith only [(le_div_iff₀ (by positivity : 0<2*X)).mp hq]
    have hTL : T≤(2*l+2)*X := by linarith only [(div_lt_iff₀ (by positivity : 0<2*X)).mp hq']
    by_cases hl : 8≤l
    · have hl0 : (0:ℝ)<l := by exact_mod_cast (show 0<l by omega)
      have hu' : u≤X/(D*(l:ℝ)^2) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hT) (by positivity)).mpr
        have hs := pow_le_pow_left₀ (show 0≤2*(l:ℝ)*X by positivity) hLT 2
        have hd := (le_div_iff₀ hD).mp hcD
        nlinarith only [mul_le_mul_of_nonneg_left hs hX,
          mul_le_mul_of_nonneg_right hd (show 0≤X^3*(l:ℝ)^2 by positivity),
          mul_nonneg (pow_nonneg hX 3) (sq_nonneg (l:ℝ))]
      have H' := vinogradov_logarithmic_block_large hN hbig hNM hM (by linarith) hl hLT hTL
      apply H'.trans
      apply mul_le_mul (mul_le_mul_of_nonneg_right hKB hNr.le) _
        (Real.exp_pos _).le (mul_nonneg (hC.trans_le hKC).le hNr.le)
      apply Real.exp_le_exp.mpr; change -X/(D*(l:ℝ)^2)≤-u; rw [neg_div]; exact neg_le_neg hu'
    · have hl' : (l:ℝ)+1≤8 := by exact_mod_cast (show l+1≤8 by omega)
      have hT' : t≤(N:ℝ)^16 := by
        apply (Real.log_le_log_iff (by linarith) (pow_pos hNr 16)).mp
        rw [Real.log_pow]; change T≤(16:ℝ)*X
        linarith only [hTL,mul_le_mul_of_nonneg_right hl' hX]
      apply (logBlock_fixed_height hN hbig hM hNt hT' H).trans
      apply mul_le_mul (mul_le_mul_of_nonneg_right hKC hNr.le) _ (Real.exp_pos _).le
        (mul_nonneg (hC.trans_le hKC).le hNr.le)
      apply Real.exp_le_exp.mpr
      change -κ*X≤-u; linarith only [hu,mul_le_mul_of_nonneg_right hcκ hX]
  · have hh : u≤100 := by linarith only [hu,mul_le_mul_of_nonneg_right hc1 hX,lt_of_not_ge hbig]
    apply (logBlock_trivial hM t).trans
    have hx : 1≤Real.exp 100*Real.exp (-u) := by
      rw [←Real.exp_add,Real.one_le_exp_iff]; linarith
    have h1 := mul_le_mul_of_nonneg_right hKe (Real.exp_pos (-u)).le
    linarith only [mul_le_mul_of_nonneg_right (hx.trans h1) hNr.le]

end AnalyticNumberTheory.ExponentialSums
