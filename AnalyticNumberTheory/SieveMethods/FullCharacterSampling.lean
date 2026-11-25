import AnalyticNumberTheory.SieveMethods.SparseCharacterSampling
import AnalyticNumberTheory.SieveMethods.BlockSampling

/-!
# Sparse sampling from the first coefficient

The full polynomial is partitioned according to the integer part of the
base-two logarithm of its frequency. The diagonal sampling constants form
an increasing geometric sum, and the shifted-contour contributions form
a decreasing geometric sum.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
namespace AnalyticNumberTheory.SieveMethods

set_option maxHeartbeats 900000 in
/-- A sparse hybrid mean for all coefficients up to a given length. The
family parameter is the modulus for a fixed modulus, and the square of the
largest conductor for a family of primitive characters. -/
theorem full_character_sampling :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D L : ℕ},1≤D →
      CharacterCorrelationFamily F f D → ∀(S : ι→Finset ℂ) {K : ℝ},0≤K →
      (∀i∈F,∀z∈S i,0≤z.im ∧ z.im<L) →
      (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K) →
      ∀(u : ℂ→ℂ),(∀i∈F,∀z∈S i,(u z).re∈Set.Icc (0:ℝ) 1 ∧ (u z).im=z.im) →
      ∀{N : ℕ},1≤N → ∀a : ℕ→ℂ,
      let H := (D:ℝ)*((L:ℝ)+2)
      let R := ∑i∈F,((S i).card:ℝ)
      (∑i∈F,∑z∈S i,‖∑n∈Icc 1 N,a n*f i n*(n:ℂ)^(-u z)‖^2) ≤
        C*(K*N+R*Real.sqrt H*(1+Real.log H)^2)*(∑n∈Icc 1 N,‖a n‖^2) := by
  obtain ⟨C,hC,HC⟩ := sparse_character_dyadic_decay
  refine ⟨10*C,by positivity,?_⟩
  intro ι F f D L hD hF S K hK him hc u hu N hN a
  let H := (D:ℝ)*((L:ℝ)+2)
  let R := ∑i∈F,((S i).card:ℝ)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
    (by linarith [Nat.cast_nonneg (α:=ℝ) L])
  have hl := Real.log_nonneg hH
  let W := F.sigma S
  have hw : (W.card:ℝ)=R := by simp [W,R,card_sigma]
  let J := range (Nat.log 2 N+1)
  let B (j:ℕ) := (Icc 1 N).filter (fun n => Nat.log 2 n=j)
  let E (j:ℕ) := ∑n∈B j,‖a n‖^2
  let U (j:ℕ) := C*(K*(2:ℝ)^j+R*Real.sqrt H*(1+Real.log H)*((2:ℝ)^j)^(-(1/(4+Real.log H))))
  let P (j:ℕ) (p:Σ _ : ι,ℂ) := ∑n∈B j,a n*f p.1 n*(n:ℂ)^(-u p.2)
  have hmap (n) (hn:n∈Icc 1 N) : Nat.log 2 n∈J :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hn).2))
  have he : ∑j∈J,E j=∑n∈Icc 1 N,‖a n‖^2 := sum_fiberwise_of_maps_to hmap _
  have hfull (p:Σ _ : ι,ℂ) : ∑j∈J,P j p=∑n∈Icc 1 N,a n*f p.1 n*(n:ℂ)^(-u p.2) :=
    sum_fiberwise_of_maps_to hmap _
  have hR : 0≤R := hw ▸ Nat.cast_nonneg _
  change _ ≤ (10*C)*(K*N+R*Real.sqrt H*(1+Real.log H)^2)*(∑n∈Icc 1 N,‖a n‖^2)
  rw [← Finset.sum_sigma (s:=F) (t:=S) (f:=fun p => ‖∑n∈Icc 1 N,a n*f p.1 n*(n:ℂ)^(-u p.2)‖^2)]
  change (∑p∈W,_)≤_
  rcases W.eq_empty_or_nonempty with hem|hne
  · rw [hem,sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg _)) (sq_nonneg _)))) (sum_nonneg fun _ _ => sq_nonneg _)
  have hr : 0<R := hw ▸ Nat.cast_pos.mpr hne.card_pos
  have hU (j:ℕ) (_:j∈J) : 0<U j := by
    dsimp only [U]
    exact mul_pos hC (add_pos_of_nonneg_of_pos (mul_nonneg hK (by positivity)) (mul_pos (mul_pos (mul_pos hr (Real.sqrt_pos.mpr (by linarith))) (by linarith)) (Real.rpow_pos_of_pos (by positivity) _)))
  have hb (j:ℕ) (_:j∈J) : (∑p∈W,‖P j p‖^2)≤ U j*E j := by
    have hsub : B j⊆Icc (2^j) (2*2^j) := by
      intro n hn
      obtain ⟨hn,hj⟩ := mem_filter.mp hn
      have hn' := (mem_Icc.mp hn).1
      rw [←hj]
      exact mem_Icc.mpr ⟨Nat.pow_log_le_self 2 (by omega), (by
        simpa [pow_succ,Nat.mul_comm] using (Nat.lt_pow_succ_log_self one_lt_two n).le)⟩
    have h := HC hD hF S hK him hc u hu (Nat.one_le_pow j 2 (by decide)) (B j) hsub a
    simpa only [W,sum_sigma,P,U,E,Nat.cast_pow,Nat.cast_ofNat,H,R] using h
  have hgeom (k:ℕ) : (∑j∈range k,(2:ℝ)^j)=2^k-1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,ih,pow_succ];ring
  have hgeo : (∑j∈J,(2:ℝ)^j)≤2*N := by
    have hh : (2:ℝ)^(Nat.log 2 N)≤N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N≠0)
    rw [show J=range (Nat.log 2 N+1) by rfl,hgeom,pow_succ];linarith
  have hs : (∑j∈J,U j) ≤ (10*C)*(K*N+R*Real.sqrt H*(1+Real.log H)^2) := by
    simp only [U,←mul_sum,sum_add_distrib]
    have hd := dyadic_kernel_decay_sum hH J
    have hbig := mul_le_mul_of_nonneg_left hd (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg H)) (show 0≤1+Real.log H by linarith only [hl]))
    have hsmall := mul_le_mul_of_nonneg_left hgeo hK
    calc _ ≤ C*(K*(2*N)+(R*Real.sqrt H*(1+Real.log H))*(10*(1+Real.log H))) :=
             mul_le_mul_of_nonneg_left (add_le_add hsmall hbig) hC.le
         _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hC.le hK) (Nat.cast_nonneg (α:=ℝ) N)]
  have ha := sampling_sum_of_blocks W J P U E hU hb
  simp_rw [hfull] at ha
  rw [he] at ha
  exact ha.trans (mul_le_mul_of_nonneg_right hs (sum_nonneg fun _ _ => sq_nonneg _))

end AnalyticNumberTheory.SieveMethods
