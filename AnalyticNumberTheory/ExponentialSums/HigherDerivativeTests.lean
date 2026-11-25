import AnalyticNumberTheory.ExponentialSums.HigherDerivativeDifferencing

/-!
# The higher derivative test of van der Corput

For a fixed order `k ≥ 2`, the estimate involves the length and the
scale of the absolute value of the `k`-th derivative. It is uniform in
the position of the interval and in both signs of the derivative.
-/

open Real Set Finset
namespace AnalyticNumberTheory.ExponentialSums

private def derivativeSumBound (k : ℕ) (α β : ℝ) : Prop :=
  ∀ {c : ℝ},1≤c → ∃ C≥1, ∀ (F : ℕ→ℝ→ℝ) {a b M : ℕ} {lam : ℝ},
    1≤M → b≤a+M → 0<lam →
    (∀ j<k,∀ t∈Set.Icc (a:ℝ) (b:ℝ),HasDerivAt (F j) (F (j+1) t) t) →
    ContinuousOn (F k) (Set.Icc (a:ℝ) (b:ℝ)) →
    (∀ t∈Set.Icc (a:ℝ) (b:ℝ),lam≤|F k t| ∧ |F k t|≤c*lam) →
    ‖∑ n∈Finset.Ioc a b,e (F 0 n)‖ ≤ C*((M:ℝ)*lam^α+(M:ℝ)^(1-β)*lam^(-α))

private theorem secondDerivativeSumBound : derivativeSumBound 2 (1/2) 1 := by
  intro c hc
  refine ⟨20*c+20,by linarith,?_⟩
  intro F a b M lam hM hm hL hD hC hbound
  by_cases hab : a<b
  · have H := vanDerCorput_second_deriv (f:=F 0) (f':=F 1) (f'':=F 2) hab hL hc
      (hD 0 (by decide)) (hD 1 (by decide)) hC hbound
    change _≤(20*c+20)*(((b:ℝ)-a)*lam^(1/2:ℝ)+lam^(-(1/2):ℝ)) at H
    dsimp only [e]; rw [sub_self,Real.rpow_zero,one_mul]
    apply H.trans; gcongr
    linarith [show (b:ℝ)≤(a:ℝ)+M by exact_mod_cast hm]
  · rw [Finset.Ioc_eq_empty_of_le (not_lt.mp hab),Finset.sum_empty,norm_zero]; positivity

private theorem derivativeSumBound_step {k : ℕ} {α β : ℝ} (hα : 0<α) (hα' : α≤1/2)
    (hβ : 0≤β) (hβ' : β≤1) (h : derivativeSumBound k α β) :
    derivativeSumBound (k+1) (α/(2+2*α)) (β/2) := by
  intro c hc
  obtain ⟨C,hC,H⟩ := h hc
  refine ⟨4+8*C,by linarith,?_⟩
  intro F a b M lam hM hm hL hD hCont hbound
  by_cases hab : a≤b
  · apply higher_derivative_differencing_step hM hab hm hL hα hα' hβ hβ' hC
    intro r hr
    by_cases har : a<b-r
    · have hrb : r≤b := by omega
      have hrr : 0<(r:ℝ) := by exact_mod_cast hr
      let G (j : ℕ) (t : ℝ) := F j (t+r)-F j t
      have hsub {t : ℝ} (ht : t∈Set.Icc (a:ℝ) ((b-r:ℕ):ℝ)) :
          t∈Set.Icc (a:ℝ) (b:ℝ) ∧ t+r∈Set.Icc (a:ℝ) (b:ℝ) := by
        rw [Nat.cast_sub hrb] at ht
        exact ⟨⟨ht.1,by linarith [ht.2]⟩,⟨by linarith [ht.1],by linarith [ht.2]⟩⟩
      have hd (j : ℕ) (hj : j≤k) (t : ℝ) (ht : t∈Set.Icc (a:ℝ) ((b-r:ℕ):ℝ)) :
          HasDerivAt (G j) (G (j+1) t) t := by
        have hz := hsub ht
        simpa only [G,mul_one,Function.comp_def,id_eq,Pi.sub_apply] using (((hD j (by omega) (t+r) hz.2).comp t ((hasDerivAt_id t).add_const (r:ℝ))).fun_sub (hD j (by omega) t hz.1))
      apply H G hM (by omega : b-r≤a+M) (mul_pos hrr hL)
        (fun j hj => hd j hj.le) (fun t ht => (hd k le_rfl t ht).continuousAt.continuousWithinAt)
      intro t ht
      have hz := hsub ht
      have hseg : Set.Icc t (t+r)⊆Set.Icc (a:ℝ) (b:ℝ) := Set.Icc_subset_Icc hz.1.1 hz.2.2
      obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope (F k) (F (k+1)) (show t<t+r by linarith)
        (fun v hv => (hD k (by omega) v (hseg hv)).continuousAt.continuousWithinAt)
        (fun v hv => hD k (by omega) v (hseg ⟨hv.1.le,hv.2.le⟩))
      rw [add_sub_cancel_left] at he
      have hg : G k t = F (k+1) y*r := (eq_div_iff hrr.ne').mp he |>.symm
      obtain ⟨h₁,h₂⟩ := hbound y (hseg ⟨hy.1.le,hy.2.le⟩)
      rw [hg,abs_mul,abs_of_pos hrr]
      exact ⟨by nlinarith only [mul_le_mul_of_nonneg_right h₁ hrr.le],
        by nlinarith only [mul_le_mul_of_nonneg_right h₂ hrr.le]⟩
    · rw [Finset.Ioc_eq_empty_of_le (not_lt.mp har),Finset.sum_empty,norm_zero]; positivity
  · rw [Finset.Ioc_eq_empty_of_le (not_le.mp hab).le,Finset.sum_empty,norm_zero]; positivity

private theorem derivativeSumBound_all (j : ℕ) :
    derivativeSumBound (j+2) (1/((2:ℝ)^(j+2)-2)) ((2:ℝ)⁻¹^j) := by
  induction j with
  | zero =>
    norm_num only [Nat.zero_add,pow_zero,pow_succ,mul_one,one_mul,show (2:ℝ)*2-2=2 by norm_num]
    exact @secondDerivativeSumBound
  | succ j ih =>
    let q := (2:ℝ)^(j+2)
    have hq : 4≤q := by
      dsimp [q]; rw [pow_add]; norm_num; nlinarith only [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)]
    have hq' : 0<q-2 := by linarith
    have ha : 0<1/(q-2) := one_div_pos.mpr hq'
    have ha' : 1/(q-2)≤1/2 := (div_le_div_iff₀ (by linarith) (by norm_num)).mpr (by linarith)
    have hb : (0:ℝ)≤(2:ℝ)⁻¹^j := by positivity
    have hb' : (2:ℝ)⁻¹^j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      (n:=j)
    have H : derivativeSumBound ((j+2)+1) ((1/(q-2))/(2+2*(1/(q-2)))) (((2:ℝ)⁻¹)^j/2) := @derivativeSumBound_step _ _ _ ha ha' hb hb' ih
    have he : (1/(q-2))/(2+2*(1/(q-2)))=1/((2:ℝ)^(j+1+2)-2) := by
      rw [show j+1+2=(j+2)+1 by omega,pow_succ]
      change _=1/(q*2-2)
      apply (div_eq_div_iff (by positivity : 2+2*(1/(q-2))≠0) (by linarith : q*2-2≠0)).mpr
      field_simp [hq'.ne'] <;> ring
    rw [he,show ((2:ℝ)⁻¹)^j/2=((2:ℝ)⁻¹)^(j+1) by rw [pow_succ]; ring] at H
    exact @H

/-- For a `k`-th derivative comparable to `lam`, van der Corput gives
`M lam^(1/(2^k−2)) + M^(1−2^{2−k}) lam^(-1/(2^k−2))`. The functions
`F j` list the derivatives on the closed interval, up to order `k`. -/
theorem vanDerCorput_higher_derivative {k : ℕ} (hk : 2≤k) {c : ℝ} (hc : 1≤c) :
    ∃ C≥1, ∀ (F : ℕ→ℝ→ℝ) {a b M : ℕ} {lam : ℝ},1≤M → b≤a+M → 0<lam →
    (∀ j<k,∀ t∈Set.Icc (a:ℝ) (b:ℝ),HasDerivAt (F j) (F (j+1) t) t) →
    ContinuousOn (F k) (Set.Icc (a:ℝ) (b:ℝ)) →
    (∀ t∈Set.Icc (a:ℝ) (b:ℝ),lam≤|F k t| ∧ |F k t|≤c*lam) →
    ‖∑ n∈Finset.Ioc a b,e (F 0 n)‖ ≤
      C*((M:ℝ)*lam^(1/((2:ℝ)^k-2))+(M:ℝ)^(1-((2:ℝ)⁻¹)^(k-2))*lam^(-(1/((2:ℝ)^k-2)))) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa only [Nat.add_sub_cancel] using derivativeSumBound_all j hc

end AnalyticNumberTheory.ExponentialSums
