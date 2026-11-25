import AnalyticNumberTheory.RiemannZeta.HurwitzFourierExpansion

/-!
# The high-frequency tail of the sharp Hurwitz expansion

Beyond twice the stationary frequency the second-order Fourier expansion
is absolutely bounded by a convergent inverse-square tail.
-/
noncomputable section
open Real Complex Filter Set Finset MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem high_integral {s : ℂ} {ω x : ℝ} (hx : 0<x) (hσ : 0<s.re)
    (ht : 0<s.im) (hω : 2*(s.im/x)≤|ω|) :
    ‖∫ u in Ioi x,hurwitzMode (s+2) ω u‖ ≤ x^(-s.re-2)*(8/|ω|) := by
  have hp : 0 < |ω| := lt_of_lt_of_le (by positivity) hω
  have hi := hurwitzMode_integrable_tail (s:=s+2) (by simp; linarith) ω hx
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi x hi (tendsto_id (α:=ℝ))).norm
  filter_upwards [eventually_ge_atTop x] with b hb
  have hg (u : ℝ) (hu : u∈Icc x b) : |ω|/2 ≤ |ω-(s+2).im/u| := by
    have hd := div_le_div_of_nonneg_left ht.le hx hu.1
    have h := abs_sub_abs_le_abs_sub ω (s.im/u)
    rw [abs_of_nonneg (div_nonneg ht.le (hx.trans_le hu.1).le)] at h
    rw [show (s+2).im=s.im by simp]
    linarith
  have H := hurwitzMode_first hx hb (s:=s+2) (by simp; linarith) (by simpa using ht.le)
    (show 0 < |ω|/2 by positivity) hg
  convert H using 1 <;> simp <;> ring

theorem norm_hurwitzCorrectedMode_high {s : ℂ} {a ω x : ℝ} (hx : 0<x)
    (hσ : 0<s.re) (hσ' : s.re<1) (ht : 1≤s.im) (hω : 2*(s.im/x)≤|ω|) :
    ‖hurwitzCorrectedMode a x s ω‖ ≤ 50*(s.im/x)*x^(-s.re)/|ω|^2 := by
  have ht' : 0<s.im := by linarith
  have hp : 0 < |ω| := lt_of_lt_of_le (by positivity) hω
  have hw := abs_pos.mp hp
  have hnorm (z : ℂ) : ‖z‖≤|z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hs : ‖s‖≤2*s.im := by
    apply (hnorm s).trans
    rw [abs_of_pos hσ,abs_of_pos ht']; linarith
  have hs' : ‖s+1‖≤3*s.im := by calc
    ‖s+1‖ ≤ ‖s‖+‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by simp; linarith
  have hi := high_integral hx hσ ht' hω
  have hb : ‖Complex.exp ((ω*(x-a):ℝ)*I)*(x:ℂ)^(-s-1)‖ = x^(-s.re-1) := by
    rw [show -s-1= -(s+1) by ring,←hurwitzShift_mul_mode,norm_mul,norm_hurwitzShift,norm_hurwitzMode _ _ hx]
    simp; ring
  rw [hurwitzCorrectedMode_eq hσ hσ' hw hx,norm_mul,norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hN := norm_sub_le (s*Complex.exp ((ω*(x-a):ℝ)*I)*(x:ℂ)^(-s-1))
    (s*(s+1)*(hurwitzShift a ω*∫ u in Ioi x,hurwitzMode (s+2) ω u))
  rw [mul_assoc s, norm_mul s,hb,norm_mul,norm_mul s,norm_mul (hurwitzShift _ _),norm_hurwitzShift,one_mul] at hN
  rw [mul_assoc s (Complex.exp _)]
  apply (mul_le_mul_of_nonneg_left hN (by positivity)).trans
  have h1 : x^(-s.re-1)=x^(-s.re)/x := by rw [Real.rpow_sub hx,Real.rpow_one]
  have h2 : x^(-s.re-2)=x^(-s.re)/x^2 := by rw [Real.rpow_sub hx,Real.rpow_two]
  calc
    _ ≤ 1/|ω|^2*(2*s.im*x^(-s.re-1)+(2*s.im)*(3*s.im)*(x^(-s.re-2)*(8/|ω|))) := by gcongr
    _ ≤ 1/|ω|^2*(2*s.im*x^(-s.re-1)+(2*s.im)*(3*s.im)*(x^(-s.re-2)*(8/(s.im/x)))) := by
      gcongr; linarith [div_pos ht' hx]
    _ = _ := by rw [h1,h2]; field_simp; ring

/-- Estimate an absolutely convergent remainder from inverse-square
coefficient bounds, telescoping at the first omitted index. -/
theorem norm_sub_sum_le_of_inverse_square {f : ℕ → ℂ} {z : ℂ} (hf : HasSum f z)
    {L : ℕ} (hL : 1≤L) {A : ℝ} (hA : 0≤A)
    (h : ∀ k : ℕ, L≤k → ‖f k‖≤A/((k:ℝ)+1)^2) :
    ‖z-∑ k∈range L,f k‖≤A/L := by
  have hpart (n : ℕ) (hn : L≤n) :
      ‖(∑ k∈range n,f k)-(∑ k∈range L,f k)‖≤A/L-A/n := by
    induction n,hn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [sum_range_succ,add_sub_right_comm]
      have hk' : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
      apply (norm_add_le _ _).trans ((add_le_add ih (h k hk)).trans ?_)
      push_cast
      have H : A/((k:ℝ)+1)^2 ≤ A/k-A/((k:ℝ)+1) := by
        field_simp
        nlinarith
      linarith
  apply le_of_tendsto ((hf.tendsto_sum_nat.sub_const _).norm)
  filter_upwards [eventually_ge_atTop L] with n hn
  exact (hpart n hn).trans (sub_le_self _ (by positivity))

end AnalyticNumberTheory.RiemannZeta
