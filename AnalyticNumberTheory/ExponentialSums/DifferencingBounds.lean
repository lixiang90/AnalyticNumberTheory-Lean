import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VanDerCorput

/-!
# Cancellation under repeated van der Corput differencing

A bound uniform over a shorter interval and the positive shifts transfers
to the original sum. The square-root loss can be iterated at any fixed order.
-/

open Real Finset

namespace AnalyticNumberTheory.ExponentialSums

/-- One differencing step transfers a saving of `V²` on the translated
differences to a saving of `V` on the original sum. -/
theorem cancellation_of_forwardDiff (f : ℝ → ℝ) {M H : ℕ} (hH : 1≤H) (hHM : H≤M)
    {V C : ℝ} (hV : 1≤V) (hVH : V^2≤H) (hC : 0≤C)
    (h : ∀ (r b : ℕ), 1≤r → r≤H → b≤2*M →
      ‖∑ n ∈ Ioc M b, e (forwardDiff r f n)‖ ≤ C*(M:ℝ)/V^2)
    (b : ℕ) (hb : b≤2*M) :
    ‖∑ n ∈ Ioc M b, e (f n)‖ ≤ (4+4*C)*(M:ℝ)/V := by
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (by omega : 0<M)
  have hH0 : 0<(H:ℝ) := by exact_mod_cast hH
  have hV0 : 0<V := by linarith
  have hHM' : (H:ℝ)≤M := by exact_mod_cast hHM
  by_cases hmb : M≤b
  · let d := b-M
    have hbd : M+d=b := by dsimp [d]; omega
    have hd : (d:ℝ)≤M := by exact_mod_cast (by dsimp [d]; omega : d≤M)
    let S := ‖∑ n ∈ Ioc M b,e (f n)‖
    let B := C*(M:ℝ)/V^2
    have hB : 0≤B := by dsimp [B]; positivity
    have hsum : ∑ r ∈ Ico 1 H, (1-(r:ℝ)/H)*
        ‖∑ n ∈ Ioc M (b-r),e (forwardDiff r f n)‖ ≤ (H:ℝ)*B := by
      calc _ ≤ ∑ _r ∈ Ico 1 H,B := Finset.sum_le_sum fun r hr =>
                (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self 1 (by positivity))).trans
                  (h r (b-r) (mem_Ico.mp hr).1 (mem_Ico.mp hr).2.le (by omega))
           _ ≤ _ := by
             rw [sum_const,nsmul_eq_mul]
             exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Ico 1 H).card≤H by simp)) hB
    have hdif := vanDerCorput_weyl_differencing f M d H hH
    rw [hbd] at hdif
    let D (r : ℕ) := ‖∑ n ∈ Ioc M (b-r),e (forwardDiff r f n)‖
    have hdif' : (H:ℝ)*S^2 ≤ ((d:ℝ)+H)*(((d:ℝ)+H)+2*∑ r ∈ Ico 1 H,(1-(r:ℝ)/H)*D r) := by
      simpa only [S,D,e,forwardDiff,Nat.cast_add] using hdif
    change ∑ r ∈ Ico 1 H,(1-(r:ℝ)/H)*D r ≤ (H:ℝ)*B at hsum
    have hs : (H:ℝ)*S^2 ≤ (2*M)*(2*M+2*H*B) := by
      apply hdif'.trans
      apply mul_le_mul (by linarith) _ _ (by positivity)
      · linarith
      · refine add_nonneg (by positivity) (mul_nonneg (by norm_num) (sum_nonneg ?_))
        intro i hi
        exact mul_nonneg (sub_nonneg.mpr ((div_le_one hH0).mpr
          (by exact_mod_cast (mem_Ico.mp hi).2.le))) (norm_nonneg _)
    have hsq : S^2 ≤ (4+4*C)*((M:ℝ)/V)^2 := by
      apply (le_of_mul_le_mul_left ?_ hH0 : S^2 ≤ _)
      apply hs.trans
      have he : (H:ℝ)*((4+4*C)*((M:ℝ)/V)^2) =
          4*(M:ℝ)^2*((H:ℝ)/V^2)+4*(M:ℝ)*H*B := by dsimp [B]; field_simp <;> ring
      rw [he]
      have hR := (le_div_iff₀ (sq_pos_of_pos hV0)).2 (by simpa using hVH : 1*V^2≤(H:ℝ))
      nlinarith only [mul_le_mul_of_nonneg_left hR (sq_nonneg (M:ℝ))]
    have hcoef : 4+4*C≤(4+4*C)^2 := by nlinarith [sq_nonneg C]
    have hbig := hsq.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
    change S ≤ _
    apply le_of_sq_le_sq _ (by positivity)
    convert hbig using 1 <;> ring
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,norm_zero]
    positivity

private theorem cancellation_tree (s : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ D≥0, ∀ (f : ℝ → ℝ) (j K : ℕ), j+s=K →
    ∀ (t : Fin j → ℕ) (M H : ℕ) (V : ℝ), (∀ i, 1≤t i ∧ t i≤H) →
    1≤H → H≤M → 1≤V → V^(2^s)≤H →
    (∀ (w : Fin K → ℕ), (∀ i, 1≤w i ∧ w i≤H) → ∀ b : ℕ, b≤2*M →
      ‖∑ n ∈ Ioc M b, e (iterForwardDiff (fun i => (w i:ℝ)) f n)‖ ≤ C*(M:ℝ)/H) →
    ∀ b : ℕ, b≤2*M →
      ‖∑ n ∈ Ioc M b, e (iterForwardDiff (fun i => (t i:ℝ)) f n)‖ ≤ D*(M:ℝ)/V := by
  induction s with
  | zero =>
    refine ⟨C,hC,?_⟩
    intro f j K hj t M H V ht hH hHM hV hVH h b hb
    simp only [Nat.add_zero] at hj
    subst K
    apply (h t ht b hb).trans
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by simpa using hVH)
  | succ s ih =>
    obtain ⟨D,hD,ih⟩ := ih
    refine ⟨4+4*D,by positivity,?_⟩
    intro f j K hj t M H V ht hH hHM hV hVH h b hb
    have hVV : 1≤V^2 := one_le_pow₀ hV
    have hpow : (V^2)^(2^s)≤(H:ℝ) := by
      rw [← pow_mul,show 2*2^s=2^(s+1) by ring]
      exact hVH
    have hVH' : V^2 ≤ (H:ℝ) :=
      (le_self_pow₀ hVV (by positivity : 2^s≠0)).trans hpow
    apply cancellation_of_forwardDiff (iterForwardDiff (fun i => (t i:ℝ)) f) hH hHM hV hVH' hD _ b hb
    intro r b hr hrH hb
    let w : Fin (j+1) → ℕ := Fin.cons r t
    have hw (i : Fin (j+1)) : 1≤w i ∧ w i≤H := Fin.cases ⟨hr,hrH⟩ ht i
    have H' := ih f (j+1) K (by omega) w M H (V^2) hw hH hHM hVV hpow h b hb
    simpa only [w,iterForwardDiff,Fin.cons_zero,Fin.cons_succ] using H'

/-- Savings on all positive tuples of shifts imply cancellation before
differencing. The constant only depends on the order and the leaf bound. -/
theorem iterated_forwardDiff_cancellation (k : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ D≥0, ∀ (f : ℝ → ℝ) (M H : ℕ) (V : ℝ), 1≤H → H≤M → 1≤V → V^(2^k)≤H →
    (∀ (w : Fin k → ℕ), (∀ i, 1≤w i ∧ w i≤H) → ∀ b : ℕ, b≤2*M →
      ‖∑ n ∈ Ioc M b, e (iterForwardDiff (fun i => (w i:ℝ)) f n)‖ ≤ C*(M:ℝ)/H) →
    ∀ b : ℕ, b≤2*M → ‖∑ n ∈ Ioc M b,e (f n)‖ ≤ D*(M:ℝ)/V := by
  obtain ⟨D,hD,h⟩ := cancellation_tree k C hC
  exact ⟨D,hD,fun f M H V hH hHM hV hVH hleaf b hb =>
    h f 0 k (Nat.zero_add k) (fun i => i.elim0) M H V (fun i => i.elim0) hH hHM hV hVH hleaf b hb⟩

end AnalyticNumberTheory.ExponentialSums
