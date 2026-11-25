import AnalyticNumberTheory.ExponentialSums.HigherDerivativeTests

/-!
# Exponential sums with monomial phases

Uniform derivative estimates on a fixed dilation of a dyadic interval
give simultaneous control of all its partial sums.
-/

open Real Set Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Coefficient in the `j`-th derivative of the real power function. -/
def fallingPower (s : ℝ) (j : ℕ) : ℝ := ∏ i∈Finset.range j, (s-i)

private theorem monomial_hasDerivAt (A s : ℝ) (j : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun u : ℝ => A*fallingPower s j*u^(s-j))
      (A*fallingPower s (j+1)*t^(s-(j+1:ℕ))) t := by
  convert (Real.hasDerivAt_rpow_const (x:=t) (p:=s-j) (Or.inl ht.ne')).const_mul
    (A*fallingPower s j) using 1
  unfold fallingPower
  rw [Finset.prod_range_succ,Nat.cast_add_one]
  ring_nf

/-- On every integer subinterval of `[D/8,2D]`, the monomial phase
`A t^s` has derivative scale `A D^(s-k)`. The constant depends only
on the order and the exponent. -/
theorem vanDerCorput_monomial {k : ℕ} (hk : 2≤k) {s : ℝ} (hs : s<(k:ℝ))
    (hf : fallingPower s k≠0) :
    ∃ C≥1, ∀ {A D : ℝ} {a b : ℕ},0<A → 1≤D → D/8≤a → (b:ℝ)≤2*D →
      ‖∑ n∈Finset.Ioc a b,e (A*(n:ℝ)^s)‖ ≤
        C*(D*(A*D^(s-k))^(1/((2:ℝ)^k-2))+
          D^(1-((2:ℝ)⁻¹)^(k-2))*(A*D^(s-k))^(-(1/((2:ℝ)^k-2)))) := by
  let q := s-k
  let L := |fallingPower s k| * (2:ℝ)^q
  let U := |fallingPower s k| * ((8:ℝ)⁻¹)^q
  let p := 1/((2:ℝ)^k-2)
  let l := 1-((2:ℝ)⁻¹)^(k-2)
  have hq : q≤0 := sub_nonpos.mpr hs.le
  have hL : 0<L := mul_pos (abs_pos.mpr hf) (by positivity)
  have hl : 0≤l := sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨C,hC,H⟩ := vanDerCorput_higher_derivative hk (le_max_left 1 (U/L))
  let B := max 1 (max (3*L^p) ((3:ℝ)^l*L^(-p)))
  refine ⟨C*B,one_le_mul_of_one_le_of_one_le hC (le_max_left ..),?_⟩
  intro A D a b hA hD ha hb
  have hD' : 0<D := by linarith
  let lam := A*D^q
  have hlam : 0<lam := by dsimp [lam]; positivity
  let F (j : ℕ) (u : ℝ) := A*fallingPower s j*u^(s-j)
  have htpos {t : ℝ} (ht : t∈Set.Icc (a:ℝ) (b:ℝ)) : 0<t := by linarith [ht.1]
  have H' := H F (a:=a) (b:=b) (M:=b+1) (lam:=L*lam) (by omega) (by omega)
    (mul_pos hL hlam) (fun j _ t ht => monomial_hasDerivAt A s j (htpos ht))
    (fun t ht => (monomial_hasDerivAt A s k (htpos ht)).continuousAt.continuousWithinAt) (by
      intro t ht
      have ht' := htpos ht
      have lo := Real.rpow_le_rpow_of_nonpos ht' (show t≤2*D by linarith [ht.2]) hq
      have hi := Real.rpow_le_rpow_of_nonpos (show 0<(8:ℝ)⁻¹*D by positivity)
        (show (8:ℝ)⁻¹*D≤t by linarith [ht.1]) hq
      rw [Real.mul_rpow (by norm_num) hD'.le] at lo hi
      change L*lam≤|A*fallingPower s k*t^q| ∧ _≤max 1 (U/L)*(L*lam)
      rw [abs_mul,abs_mul,abs_of_pos hA,abs_of_nonneg (Real.rpow_nonneg ht'.le _)]
      refine ⟨?_,?_⟩
      · dsimp [L,lam]
        nlinarith only [mul_le_mul_of_nonneg_left lo (mul_nonneg hA.le (abs_nonneg (fallingPower s k)))]
      · calc
          _ ≤ U*lam := by dsimp [U,lam]; nlinarith only [mul_le_mul_of_nonneg_left hi (mul_nonneg hA.le (abs_nonneg (fallingPower s k)))]
          _ = (U/L)*(L*lam) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (mul_pos hL hlam).le)
  have hM : ((b+1:ℕ):ℝ)≤3*D := by rw [Nat.cast_add_one]; linarith
  have hMr := Real.rpow_le_rpow (by positivity) hM hl
  rw [Real.mul_rpow (by norm_num) hD'.le] at hMr
  simp only [F,fallingPower,Finset.range_zero,Finset.prod_empty,mul_one,Nat.cast_zero,sub_zero] at H'
  apply H'.trans
  change C*(_*(L*lam)^p+_*(L*lam)^(-p))≤C*B*(D*lam^p+D^l*lam^(-p))
  rw [Real.mul_rpow hL.le hlam.le,Real.mul_rpow hL.le hlam.le,mul_assoc C B]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rw [mul_add]
  apply add_le_add
  · calc
      _ ≤ (3*D)*(L^p*lam^p) := by gcongr
      _ = (3*L^p)*(D*lam^p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (by positivity)
  · calc
      _ ≤ ((3:ℝ)^l*D^l)*(L^(-p)*lam^(-p)) := by gcongr
      _ = ((3:ℝ)^l*L^(-p))*(D^l*lam^(-p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (by positivity)

end AnalyticNumberTheory.ExponentialSums
