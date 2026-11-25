import AnalyticNumberTheory.ExponentialSums.VinogradovMarking
import AnalyticNumberTheory.ExponentialSums.VinogradovSingular
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The prime-step recursion for Vinogradov mean values

Nonsingular solutions are bounded by the marked congruence estimate.
Singular solutions are controlled by the pure moment on a single residue
class. Both contributions shorten the initial interval.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- The total number of pairs bounds every homogeneous solution count. -/
theorem vinogradovSolutionCount_le_trivial (s k N : ℕ) :
    vinogradovSolutionCount s k N≤N^(2*s) := by
  unfold vinogradovSolutionCount
  apply (card_filter_le ..).trans_eq
  simp [card_product,Fintype.card_piFinset_const,pow_add,two_mul]

/-- Increasing the number of pairs by `d` costs at most the trivial
factor `N^(2d)` in the mean. -/
theorem vinogradovSolutionCount_add_le (d s k N : ℕ) :
    vinogradovSolutionCount (d+s) k N≤N^(2*d)*vinogradovSolutionCount s k N := by
  let I := Icc 1 (N:ℤ)
  have hm (t : ℕ) : torusIntegral k (fun α => ‖vinogradovTorusSum k I α‖^(2*t)) =
      (vinogradovSolutionCount t k N:ℝ) :=
    (vinogradov_box_moment_eq I).trans (congrArg Nat.cast (vinogradovCountOn_interval t k N))
  have hcard : I.card=N := by simp [I,Int.card_Icc]
  have hnorm (α : Fin k → ℝ) : ‖vinogradovTorusSum k I α‖≤(N:ℝ) := by
    unfold vinogradovTorusSum torusCharSum
    apply (norm_sum_le ..).trans
    have hu (x : ℤ) : ‖torusChar k (vinogradovCurve k x) α‖=1 := by
      have H := congrArg norm (torusChar_add (vinogradovCurve k x) (-(vinogradovCurve k x)) α)
      simp only [add_neg_cancel,torusChar_zero,norm_one,torusChar_neg,norm_mul,norm_star] at H
      nlinarith only [H,norm_nonneg (torusChar k (vinogradovCurve k x) α)]
    simp [hu,hcard]
  have hc := continuous_torusCharSum I (vinogradovCurve k)
  apply Nat.cast_le (α:=ℝ) |>.mp
  rw [Nat.cast_mul,Nat.cast_pow,←hm,←hm]
  rw [← torusIntegral_const_mul]
  apply torusIntegral_mono k (hc.norm.pow _) (continuous_const.mul (hc.norm.pow _))
  intro α
  change ‖vinogradovTorusSum k I α‖^(2*(d+s))≤(N:ℝ)^(2*d)*‖vinogradovTorusSum k I α‖^(2*s)
  rw [Nat.mul_add,pow_add]
  gcongr
  exact hnorm _

/-- One prime-conditioning step. The two summands bound the nonsingular
and singular systems separately. All constants and lengths are explicit. -/
theorem vinogradov_prime_recursion {k s N p m : ℕ} (hp : p.Prime) (hk : 0<k) (hs : 0<s)
    (hkp : k<p) (hN : N≤m*p^k) :
    vinogradovSolutionCount (k+s) k N ≤
      (k+s)^(2*k)*(p^(2*s)*(N^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovSolutionCount s k (N/p+1)))+
      2*p.choose (k-1)*(k-1)^(k+s)*p^(k+s)*vinogradovSolutionCount (k+s) k (N/p+1) := by
  classical
  let I := Icc 1 (N:ℤ)
  let P := vinogradovTuples (k+s) I
  let S := vinogradovShiftedPairs P (0:Fin k → ℤ)
  let good (z : (Fin (k+s) → ℤ) × (Fin (k+s) → ℤ)) :=
    k≤(univ.image (fun i => (z.1 i:ZMod p))).card ∧ k≤(univ.image (fun i => (z.2 i:ZMod p))).card
  have hm (z) (hz : z∈S) : ((∀ i,z.1 i∈I) ∧ (∀ i,z.2 i∈I)) ∧
      vinogradovMoments k z.1=vinogradovMoments k z.2 := by
    obtain ⟨hx,he⟩ := mem_filter.mp hz
    exact ⟨⟨Fintype.mem_piFinset.mp (mem_product.mp hx).1,Fintype.mem_piFinset.mp (mem_product.mp hx).2⟩,
      by simpa using he⟩
  have hG := vinogradov_nonsingular_marking_le (p:=p) I (S.filter good)
    (fun z hz => (hm _ (mem_filter.mp hz).1).1) (fun z hz => (hm _ (mem_filter.mp hz).1).2)
    (fun z hz => (mem_filter.mp hz).2)
  have hB := vinogradov_singular_interval_le (k:=k) (s:=k+s) (N:=N) hp.pos (by omega) (by omega)
    (S.filter (fun z => ¬good z)) (fun z hz i => ⟨(hm _ (mem_filter.mp hz).1).1.1 i,(hm _ (mem_filter.mp hz).1).1.2 i⟩)
    (fun z hz => (hm _ (mem_filter.mp hz).1).2) (by
      intro z hz
      have h := (mem_filter.mp hz).2
      simpa only [good,not_and_or,not_le] using h)
  rw [←vinogradovCountOn_interval (k+s) k N]
  change S.card≤_
  rw [←card_filter_add_card_filter_not (s:=S) good]
  exact Nat.add_le_add (hG.trans (Nat.mul_le_mul_left _ (vinogradov_marked_card_le hp hk hs hkp hN))) hB

/-- With a prime at least the degree-th root of the interval length,
both contributions reduce to the same shorter mean with fewer variables. -/
theorem vinogradov_recursion_combined {k s N p : ℕ} (hp : p.Prime) (hk : 0<k) (hs : 0<s)
    (hkp : k<p) (hN : N≤p^k) :
    let Q := N/p+1
    vinogradovSolutionCount (k+s) k N ≤
      ((k+s)^(2*k)*k.factorial*p^(2*s+k*(k-1)/2)*N^k+
      2*(k-1)^(k+s)*p^((k+s)+(k-1))*Q^(2*k))*vinogradovSolutionCount s k Q := by
  intro Q
  have H := vinogradov_prime_recursion (m:=1) hp hk hs hkp (by simpa using hN)
  apply H.trans
  simp only [one_pow,mul_one,pow_add,add_mul]
  have hA := vinogradovSolutionCount_add_le k s k Q
  have hB := Nat.choose_le_pow p (k-1)
  have h : 2*p.choose (k-1)*(k-1)^(k+s)*p^(k+s)*vinogradovSolutionCount (k+s) k Q ≤
      (2*p^(k-1)*(k-1)^(k+s)*p^(k+s))*(Q^(2*k)*vinogradovSolutionCount s k Q) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hB) le_rfl) le_rfl) hA
  dsimp only [Q] at h ⊢
  simp only [pow_add] at h
  nlinarith only [h]

end AnalyticNumberTheory.ExponentialSums
