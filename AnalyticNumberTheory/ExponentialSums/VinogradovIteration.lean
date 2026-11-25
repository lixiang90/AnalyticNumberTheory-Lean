import AnalyticNumberTheory.ExponentialSums.VinogradovRecursion
import AnalyticNumberTheory.ExponentialSums.VinogradovScale

/-!
# Iteration of the classical Vinogradov mean value estimate

At degree `k`, each step with `k` additional pairs multiplies the
remaining exponent defect by `1−1/k`. Constants are kept explicit in both
the number of pairs and the degree.
-/

noncomputable section
open Real
namespace AnalyticNumberTheory.ExponentialSums

/-- Sum of the degrees in the simultaneous system of power sums. -/
def vinogradovWeight (k : ℕ) : ℝ := (k:ℝ)*(k+1)/2

/-- Height exponent of a mean with defect `δ` from the volume prediction. -/
def vinogradovMeanExponent (s k : ℕ) (δ : ℝ) := 2*(s:ℝ)-vinogradovWeight k+δ

set_option maxHeartbeats 700000 in
private theorem iteration_step {k s M N : ℕ} (hk : 2≤k) (hs : k*k≤s) (hM : k+s≤M)
    (hN : 1≤N) {A C δ : ℝ} (hA : 8*((M:ℝ)+1)*((k:ℝ)+1)≤A) (hC : 0≤C)
    (hδ : 0≤δ) (hδ' : δ≤vinogradovWeight k)
    (H : ∀ Q : ℕ, 1≤Q → (vinogradovSolutionCount s k Q:ℝ)≤C*(Q:ℝ)^(vinogradovMeanExponent s k δ)) :
    (vinogradovSolutionCount (k+s) k N:ℝ) ≤
      (A^(12*M)*C)*(N:ℝ)^(vinogradovMeanExponent (k+s) k ((1-(k:ℝ)⁻¹)*δ)) := by
  obtain ⟨p,hp,hkp,hNp,hpScale,hqScale⟩ := vinogradov_prime_scale hk hN
  let Q := N/p+1
  let t := k+s
  let D := k*(k-1)/2
  let K := vinogradovWeight k
  let a := (k:ℝ)⁻¹
  let w := vinogradovMeanExponent s k δ
  let z := vinogradovMeanExponent t k ((1-a)*δ)
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hM' : (k:ℝ)+s≤M := by exact_mod_cast hM
  have hs' : (k:ℝ)*k≤s := by exact_mod_cast hs
  have hkpos : (0:ℝ)<k := by linarith
  have hAk : (k:ℝ)≤A := by nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  have hAt : (t:ℝ)≤A := by dsimp [t]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  have hA4 : 4*((k:ℝ)+1)≤A := by nlinarith [Nat.cast_nonneg (α:=ℝ) M]
  have hA1 : 1≤A := by linarith
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hq1 : 1≤Q := Nat.succ_pos _
  have htR : (t:ℝ)=(k:ℝ)+s := Nat.cast_add ..
  have hDR : (D:ℝ)=(k:ℝ)*(k-1)/2 := by
    have hd := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)
    have h : (D:ℝ)*2=(k:ℝ)*((k-1:ℕ):ℝ) := by exact_mod_cast hd
    rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one] at h
    linarith
  have hsub : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hK : K=(k:ℝ)*(k+1)/2 := rfl
  have hK' : K≤s := by rw [hK]; nlinarith
  have hw : 0≤w := by change 0≤2*(s:ℝ)-K+δ; linarith
  have hw' : w≤2*s := by change 2*(s:ℝ)-K+δ≤_; change δ≤K at hδ'; linarith
  have hp' := hpScale.trans (mul_le_mul_of_nonneg_right hA4 (by positivity))
  have hq' := hqScale.trans (mul_le_mul_of_nonneg_right (by linarith : 2≤A) (by positivity))
  have hApos : 0<A := by linarith
  have hc₁ : (t:ℝ)^(2*k)*(k.factorial:ℝ)≤A^((3:ℝ)*k) := by
    have hf : (k.factorial:ℝ)≤(k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
    have hb := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg t) hAt (2*k))
      (hf.trans (pow_le_pow_left₀ (Nat.cast_nonneg k) hAk k)) (Nat.cast_nonneg _) (pow_nonneg hApos.le _)
    apply hb.trans_eq
    rw [←pow_add,←Real.rpow_natCast]; congr 1; push_cast; ring
  have hc₂ : 2*((k-1:ℕ):ℝ)^t≤A^((t:ℝ)+1) := by
    rw [Real.rpow_add_one hApos.ne',Real.rpow_natCast,mul_comm]
    apply mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (by rw [hsub]; linarith) _) (by linarith)
      (by norm_num) (pow_nonneg hApos.le _)
  have hz₁ : (k:ℝ)+a*(2*s+D)+(1-a)*w=z := by
    dsimp only [a,w,z,vinogradovMeanExponent,vinogradovWeight]
    rw [htR,hDR]
    field_simp [hkpos.ne']; ring
  have hz₂ : 0+a*((t:ℝ)+(k-1))+(1-a)*(2*k+w)≤z := by
    rw [←hz₁,hDR,htR]
    dsimp only [a]
    field_simp [hkpos.ne']
    nlinarith only [hs',hkR]
  let Z := A^(10*(M:ℝ))*(N:ℝ)^z
  have hb₁ : ((t:ℝ)^(2*k)*k.factorial)*((p:ℝ)^(2*s+D)*(Q:ℝ)^w)*(N:ℝ)^k≤Z := by
    have h := vinogradov_scaled_monomial hn1 hA1 (Nat.cast_nonneg p) (Nat.cast_nonneg Q)
      (by positivity : (0:ℝ)≤2*s+D) hw hp' hq' hc₁
      (by rw [hDR]; nlinarith only [hM',hs',hw',hkR] : 3*(k:ℝ)+(2*s+D)+w≤10*M) hz₁.le
    have he : (2:ℝ)*s+D=((2*s+D:ℕ):ℝ) := by push_cast; ring
    rwa [he,Real.rpow_natCast,Real.rpow_natCast] at h
  have hb₂ : (2*((k-1:ℕ):ℝ)^t)*((p:ℝ)^(t+(k-1))*(Q:ℝ)^((2:ℝ)*k+w))≤Z := by
    have h := vinogradov_scaled_monomial hn1 hA1 (Nat.cast_nonneg p) (Nat.cast_nonneg Q)
      (by rw [htR]; linarith : 0≤(t:ℝ)+(k-1)) (by linarith : 0≤(2:ℝ)*k+w) hp' hq' hc₂
      (by rw [htR]; nlinarith only [hM',hs',hw',hkR] :
        (t:ℝ)+1+((t:ℝ)+(k-1))+(2*k+w)≤10*M) hz₂
    rw [Real.rpow_zero,mul_one] at h
    rw [←hsub,←Nat.cast_add,Real.rpow_natCast] at h
    exact h
  have hbase := vinogradov_recursion_combined hp (by omega : 0<k) (by nlinarith : 0<s) hkp hNp
  have hraw : (vinogradovSolutionCount t k N:ℝ) ≤
      ((t:ℝ)^(2*k)*k.factorial*(p:ℝ)^(2*s+D)*(N:ℝ)^k+
        2*((k-1:ℕ):ℝ)^t*(p:ℝ)^(t+(k-1))*(Q:ℝ)^(2*k))*(vinogradovSolutionCount s k Q:ℝ) := by
    exact_mod_cast hbase
  have htot := hraw.trans (mul_le_mul_of_nonneg_left (H Q hq1) (by positivity))
  have hqr : (Q:ℝ)^(2*(k:ℝ)+w)=(Q:ℝ)^(2*k)*(Q:ℝ)^w := by
    rw [Real.rpow_add (by exact_mod_cast ((by omega : 0<Q)) : (0:ℝ)<Q)]
    rw [show (2:ℝ)*k=((2*k:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast]
  rw [hqr] at hb₂
  have hcp : 2*A^(10*(M:ℝ))≤A^(12*M) := by
    have h₁ : (10:ℝ)*M+1≤(12*M:ℕ) := by push_cast; nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le hA1 h₁
    rw [Real.rpow_add_one hApos.ne',Real.rpow_natCast] at h
    exact (mul_le_mul_of_nonneg_right (by linarith : 2≤A) (Real.rpow_nonneg hApos.le _)).trans
      ((mul_comm ..).le.trans h)
  change (vinogradovSolutionCount t k N:ℝ)≤(A^(12*M)*C)*(N:ℝ)^z
  dsimp only [Z] at hb₁ hb₂
  change (vinogradovSolutionCount t k N:ℝ)≤_* (C*(Q:ℝ)^w) at htot
  nlinarith only [htot,mul_le_mul_of_nonneg_right hb₁ hC,mul_le_mul_of_nonneg_right hb₂ hC,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcp hC) (Real.rpow_nonneg (Nat.cast_nonneg N) z)]

/-- The remaining defect after `τ` prime-conditioning steps. -/
def vinogradovDefect (k τ : ℕ) : ℝ :=
  vinogradovWeight k*(1-(k:ℝ)⁻¹)^τ

private theorem vinogradovDefect_range {k : ℕ} (hk : 2≤k) (τ : ℕ) :
    0≤vinogradovDefect k τ ∧ vinogradovDefect k τ≤vinogradovWeight k := by
  have hk' : 1≤(k:ℝ) := by exact_mod_cast (by omega : 1≤k)
  have hr := sub_nonneg.mpr (inv_le_one_of_one_le₀ hk')
  have hR : 1-(k:ℝ)⁻¹≤1 := sub_le_self 1 (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hw : 0≤vinogradovWeight k := by dsimp [vinogradovWeight]; positivity
  exact ⟨mul_nonneg hw (pow_nonneg hr _),mul_le_of_le_one_right hw (pow_le_one₀ hr hR)⟩

/-- Classical Vinogradov mean value theorem. For `s ≥ k²+kτ`, each
iteration improves the defect by `1−1/k`. The multiplicative constant
is uniform in the length and explicit in the degree and the moment. -/
theorem vinogradov_mean_value_classical {k s τ N : ℕ} (hk : 2≤k)
    (hs : k*k+k*τ≤s) (hN : 1≤N) :
    vinogradovJ s k N ≤
      (8*((s:ℝ)+1)*((k:ℝ)+1))^(12*s*τ)*(N:ℝ)^(vinogradovMeanExponent s k (vinogradovDefect k τ)) := by
  let A := 8*((s:ℝ)+1)*((k:ℝ)+1)
  have hA : 0≤A := by dsimp [A]; positivity
  have hcount (d : ℕ) : ∀ m : ℕ, k*k+k*d≤m → m≤s → ∀ n : ℕ, 1≤n →
      (vinogradovSolutionCount m k n:ℝ)≤A^(12*s*d)*(n:ℝ)^(vinogradovMeanExponent m k (vinogradovDefect k d)) := by
    induction d with
    | zero =>
      intro m _ _ n _
      have hpow : vinogradovMeanExponent m k (vinogradovDefect k 0)=((2*m:ℕ):ℝ) := by
        simp [vinogradovMeanExponent,vinogradovDefect]
      rw [hpow,Real.rpow_natCast,Nat.mul_zero,pow_zero,one_mul]
      exact_mod_cast vinogradovSolutionCount_le_trivial m k n
    | succ d ih =>
      intro m hkm hms n hn
      have hkm' : k*k+k*d≤m-k := by rw [Nat.mul_succ] at hkm; omega
      have hk0 : k*k≤m-k := by omega
      have hm : k+(m-k)=m := by rw [Nat.mul_succ] at hkm; omega
      have hr := vinogradovDefect_range hk d
      have H := iteration_step (M:=s) hk hk0 (hm.le.trans hms) hn (A:=A) le_rfl
        (pow_nonneg hA (12*s*d)) hr.1 hr.2 (ih (m-k) hkm' (by omega))
      rw [hm] at H
      have hδ : vinogradovDefect k (d+1)=(1-(k:ℝ)⁻¹)*vinogradovDefect k d := by
        rw [vinogradovDefect,vinogradovDefect,pow_succ]; ring
      rw [hδ,Nat.mul_succ,pow_add,mul_comm (A^(12*s*d))]
      exact H
  rw [vinogradovJ_eq_card_solutions]
  exact hcount τ s hs le_rfl N hN

end AnalyticNumberTheory.ExponentialSums
