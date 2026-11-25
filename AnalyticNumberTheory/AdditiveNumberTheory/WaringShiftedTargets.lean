import AnalyticNumberTheory.AdditiveNumberTheory.WaringMajorArcPositivity
import AnalyticNumberTheory.AdditiveNumberTheory.WaringDiminishingRanges

/-!
# Averaging the circle method over representable shifts

Pairing a finite set of shifts with itself converts the minor-arc integral
into a second moment. Every pair whose complementary target is representable
gives a representation of the original target.
-/

open Finset MeasureTheory
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Adjoining two tuples concatenates their lists of powers. -/
theorem waringCount_pos_add {k s m a b : ℕ} (hk : 0<k) (ha : 0<waringCount k s a)
    (hb : 0<waringCount k m b) : 0<waringCount k (s+m) (a+b) := by
  obtain ⟨x,hx⟩ := (waringCount_pos_iff hk).mp ha
  obtain ⟨y,hy⟩ := (waringCount_pos_iff hk).mp hb
  apply (waringCount_pos_iff hk).mpr
  refine ⟨Fin.append x y,?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left,Fin.append_right,hx,hy]

/-- A pair of shifts contributes the phase at the complement of their sum.
The minor-arc contribution of all pairs costs just one factor of the set size. -/
theorem norm_sum_waringMinorContributions_le {k s P N : ℕ} (A : Finset ℕ)
    (hA : ∀ a∈A, ∀ b∈A, a+b≤N) (B T M : ℝ) (hM : 0≤M)
    (hminor : ∀ α∈minorArcsFixed B T, ‖waringSum k P α‖≤M) :
    ‖∑ a∈A, ∑ b∈A, minorArcIntegralFixed (fun α => waringSum k P α ^ s *
      e (-α * ((N-(a+b):ℕ):ℝ))) B T‖ ≤ M^s*A.card := by
  let g (a b : ℕ) (α : ℝ) := waringSum k P α^s*e (-α*((N-(a+b):ℕ):ℝ))
  let S := minorArcsFixed B T
  have hg (a b : ℕ) : IntegrableOn (g a b) S := by
    have H : Continuous (g a b) := ((continuous_genExpSum _ _ _).pow s).mul
      (continuous_e.comp (continuous_neg.mul continuous_const))
    exact H.continuousOn.integrableOn_Icc.mono_set (minorArcsFixed_subset_Icc B T)
  have he (α : ℝ) : ∑ a∈A, ∑ b∈A, g a b α =
      waringSum k P α ^ s * expSum (fun _ => 1) A α ^ 2 * e (-α*(N:ℝ)) := by
    simp only [expSum,one_mul,pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    dsimp [g]
    rw [← e_add, ← e_add, Nat.cast_sub (hA _ ha _ hb),Nat.cast_add]
    congr 2
    ring
  have hbound := norm_minorArcIntegralFixed_mul_pow_e_neg_le_of_bound
    (F:=fun α => waringSum k P α^s) (G:=expSum (fun _ => 1) A)
    ((continuous_genExpSum _ _ _).pow s) (continuous_expSum _ _) (periodic_expSum _ _)
    (pow_nonneg hM s) (fun α hα => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hminor α hα) s) 3 (N:ℤ)
  change ‖∑ a∈A, ∑ b∈A, ∫ α in S, g a b α‖≤_
  simp_rw [← MeasureTheory.integral_finsetSum _ (fun b _ => hg _ b)]
  rw [← MeasureTheory.integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hg a b))]
  simp_rw [he]
  simpa [integral_norm_sq_expSum] using hbound

/-- A major-arc lower bound for each complementary target and cancellation on
the minor arcs imply representability with the shifted variables included. -/
theorem waringCount_pos_of_shift_set {k s m P N : ℕ} (hk : 2≤k) (hP : 3≤P)
    (A : Finset ℕ) (hA : A.Nonempty) (hrep : ∀ a∈A, 0<waringCount k m a)
    (hsize : ∀ a∈A, ∀ b∈A, a+b≤N ∧ N-(a+b)<(P+1)^k)
    {c M : ℝ} (hM : 0≤M)
    (hmaj : ∀ a∈A, ∀ b∈A, c*(P:ℝ)^(s-k) ≤ (waringMajorContribution k s P (N-(a+b))).re)
    (hminor : ∀ α∈minorArcsFixed ((P:ℝ)^(1/10:ℝ)) ((P:ℝ)^((k:ℝ)-1/10)), ‖waringSum k P α‖≤M)
    (hsave : M^s < c*(P:ℝ)^(s-k)*A.card) : 0<waringCount k (s+2*m) N := by
  by_contra! hbad
  have hk0 : 0<k := by omega
  have hzero (a : ℕ) (ha : a∈A) (b : ℕ) (hb : b∈A) : waringCount k s (N-(a+b))=0 := by
    by_contra! h
    have H := waringCount_pos_add hk0 (waringCount_pos_add hk0 (Nat.pos_of_ne_zero h) (hrep a ha)) (hrep b hb)
    have hab := (hsize _ ha _ hb).1
    rw [show s+m+m=s+2*m by omega,show N-(a+b)+a+b=N by omega] at H
    omega
  let U := (P:ℝ)^(1/10:ℝ)
  let V := (P:ℝ)^((k:ℝ)-1/10)
  let J (a b : ℕ) := minorArcIntegralFixed (fun α => waringSum k P α^s*e (-α*((N-(a+b):ℕ):ℝ))) U V
  obtain ⟨hU,hUV,_⟩ := waringArcParameters (by exact_mod_cast (by omega : 2<P) : (2:ℝ)<P) hk
  have hJ (a : ℕ) (ha : a∈A) (b : ℕ) (hb : b∈A) : c*(P:ℝ)^(s-k) ≤ -(J a b).re := by
    have E := waringCount_eq_arcIntegralsFixed hk0 (hsize _ ha _ hb).2 hU hUV (s:=s)
    rw [hzero _ ha _ hb,Nat.cast_zero] at E
    change 0=waringMajorContribution k s P (N-(a+b)) + J a b at E
    exact (hmaj _ ha _ hb).trans_eq (by rw [eq_neg_of_add_eq_zero_left E.symm,Complex.neg_re])
  have hsum := Finset.sum_le_sum (s:=A) (fun a ha => Finset.sum_le_sum (s:=A) (fun b hb => hJ a ha b hb))
  have hn := norm_sum_waringMinorContributions_le (k:=k) (s:=s) (P:=P) A
    (fun a ha b hb => (hsize a ha b hb).1) U V M hM hminor
  change ‖∑ a∈A, ∑ b∈A, J a b‖≤_ at hn
  have hR := (abs_le.mp (Complex.abs_re_le_norm (∑ a∈A, ∑ b∈A, J a b))).1
  simp only [Complex.re_sum] at hR
  simp only [sum_neg_distrib,sum_const,nsmul_eq_mul] at hsum
  have hC : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  nlinarith [mul_lt_mul_of_pos_right hsave hC]

end AnalyticNumberTheory.AdditiveNumberTheory
