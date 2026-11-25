import AnalyticNumberTheory.SieveMethods.LinearSieveLayers
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Bounding the terminal errors in the linear sieve

Each short branch retains at least half the logarithmic level at every step.
Deeper branches are summable by pair contraction.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The product majorizing the sum of all unsigned subset weights. -/
def sieveBranchProduct (P : Finset ℕ) (g : ℕ → ℝ) (w z : ℝ) : ℝ :=
  ∏p∈sievePrimeWindow P w z,(1+g p)

theorem sieveBranchProduct_nonneg {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀p∈P,0≤g p) (w z : ℝ) :
    0≤sieveBranchProduct P g w z := prod_nonneg (fun p hp => by linarith [hg p (mem_filter.mp hp).1])

theorem sieveBranchProduct_rec (P : Finset ℕ) (g : ℕ → ℝ) (w z : ℝ) :
    sieveBranchProduct P g w z=1+∑p∈sievePrimeWindow P w z,g p*sieveBranchProduct P g w p := by
  rw [sieveBranchProduct,prod_one_add_ordered]; congr 1; apply sum_congr rfl; intro p hp
  rw [sieveBranchProduct,sievePrimeWindow_before hp]

/-- A branch with n large primes retains at least Y/2^n of the
logarithmic level at an admissible node. -/
theorem linearSieve_shallow_layers {P : Finset ℕ} {g : ℕ → ℝ} {w : ℝ}
    (hw : 1<w) (hg : ∀p∈P,0≤g p ∧ g p<1) (n : ℕ) (b : Bool) {z Y : ℝ}
    (hwz : w≤z) (hY : 0<Y) (hu : (if b then (1:ℝ) else 2)≤Y/log z) :
    linearSieveLayer P g w (fun _ Y _ => linearSieveExpWeight P g Y w) n b Y z≤
      sieveBranchProduct P g w z*linearSieveExpWeight P g (Y/2^n) w := by
  let W := sieveEulerBelow P g
  let V := sieveBranchProduct P g w
  have hgp := fun p hp => (hg p hp).1
  have hW := (sieveEulerBelow_pos P (fun p hp => (hg p hp).2) w).le
  have hlw := Real.log_pos hw
  induction n generalizing b z Y with
  | zero =>
    rw [linearSieveLayer,pow_zero,div_one]
    have hV : 1≤V z := Finset.one_le_prod₀ (fun p hp => by linarith [hgp p (mem_filter.mp hp).1])
    exact le_mul_of_one_le_left (mul_nonneg hW (exp_pos _).le) hV
  | succ n ih =>
    let S := sievePrimeWindow P w z
    let T := S.filter (linearSieveAdmits b Y)
    let D := linearSieveExpWeight P g (Y/2^(n+1)) w
    have hD : 0≤D := mul_nonneg hW (exp_pos _).le
    have hnext (p : ℕ) (hp : p∈T) : linearSieveLayer P g w
        (fun _ Y _ => linearSieveExpWeight P g Y w) n (!b) (Y-log p) p≤V p*D := by
      obtain ⟨hp,had⟩ := mem_filter.mp hp
      obtain ⟨hP,hwp,hpz⟩ := mem_filter.mp hp
      have hlp := Real.log_pos (hw.trans_le hwp)
      have hhalf : Y/2≤Y-log p := by
        cases b with
        | false =>
          have ht := hu.trans (div_le_div_of_nonneg_left hY.le hlp (Real.log_le_log (by linarith) hpz.le))
          simp only [Bool.false_eq_true,ite_false] at ht
          linarith [(le_div_iff₀ hlp).mp ht]
        | true => have h₃ := had.resolve_left (by decide); linarith
      obtain ⟨h₁,h₂⟩ := linearSieve_branch_parameter hw hY hp hu had
      apply (ih (!b) hwp h₁ h₂).trans
      apply mul_le_mul_of_nonneg_left _ (sieveBranchProduct_nonneg hgp w p)
      apply mul_le_mul_of_nonneg_left _ hW
      apply exp_le_exp.mpr; apply neg_le_neg; apply div_le_div_of_nonneg_right _ hlw.le
      rw [pow_succ,mul_comm ((2:ℝ)^n),←div_div]
      exact div_le_div_of_nonneg_right hhalf (by positivity)
    have htotal := sieveBranchProduct_rec P g w z
    change V z=1+∑p∈S,g p*V p at htotal
    change (∑p∈T,g p*_)≤V z*D
    calc _ ≤ ∑p∈T,g p*(V p*D) := sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hnext p hp) (hgp p (mem_filter.mp (mem_filter.mp hp).1).1))
         _ ≤ ∑p∈S,g p*(V p*D) := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
           (fun p hp _ => mul_nonneg (hgp p (mem_filter.mp hp).1) (mul_nonneg (sieveBranchProduct_nonneg hgp w p) hD))
         _ = (∑p∈S,g p*V p)*D := by rw [sum_mul]; apply sum_congr rfl; intro p _; ring
         _ ≤ V z*D := mul_le_mul_of_nonneg_right (by linarith only [htotal]) hD

private theorem paired_geometric_tail (m n : ℕ) :
    (∑i∈Finset.Ico (2*m) n,(19/20:ℝ)^(i/2))≤40*(19/20:ℝ)^m := by
  let δ : ℝ := 19/20
  have hδ : 0≤δ := by norm_num [δ]
  have he (k : ℕ) : (∑i∈range (2*k),δ^(i/2))=2*∑j∈range k,δ^j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2*(k+1)=2*k+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ,
        show (2*k+1)/2=k by omega,show (2*k)/2=k by omega]; ring
  have hsum (k : ℕ) : (∑i∈range k,δ^(i/2))≤40 := by
    apply (sum_le_sum_of_subset_of_nonneg (range_mono (show k≤2*k by omega))
      (fun i _ _ => pow_nonneg hδ (i/2))).trans
    rw [he]
    have hh := geom_sum_Ico_le_of_lt_one (m:=0) (n:=k) hδ (show δ<1 by norm_num [δ])
    rw [Nat.Ico_zero_eq_range] at hh
    norm_num [δ] at hh ⊢
    linarith
  rw [Finset.sum_Ico_eq_sum_range]
  change (∑i∈range (n-2*m),δ^((2*m+i)/2))≤40*δ^m
  calc _ = (∑i∈range (n-2*m),δ^(i/2))*δ^m := by
          rw [sum_mul]; apply sum_congr rfl; intro i _; rw [←pow_add]; congr 1; omega
       _ ≤ _ := mul_le_mul_of_nonneg_right (hsum _) (pow_nonneg hδ m)

/-- Total terminal error, separated at twice any chosen number m of prime
pairs. The bound is independent of the total number of generations. -/
theorem linearSieve_terminal_sum {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w z η) (b : Bool)
    (hu : (if b then (1:ℝ) else 2)≤Y/log z) (m N : ℕ) :
    (∑i∈range N,linearSieveLayer P g w (fun _ y _ => linearSieveExpWeight P g y w) i b Y z)≤
      (2*m:ℕ)*sieveBranchProduct P g w z*linearSieveExpWeight P g (Y/2^(2*m)) w+
        2560*(19/20:ℝ)^m*linearSieveExpWeight P g Y z := by
  let G := fun (_ : Bool) (y _ : ℝ) => linearSieveExpWeight P g y w
  let A := fun i => linearSieveLayer P g w G i b Y z
  let E := linearSieveExpWeight P g
  let V := sieveBranchProduct P g w z
  have hW (t : ℝ) := (sieveEulerBelow_pos P (fun p hp => (hg p hp).2) t).le
  have hE (t y : ℝ) : 0≤E y t := mul_nonneg (hW t) (exp_pos _).le
  have hV : 0≤V := sieveBranchProduct_nonneg (fun p hp => (hg p hp).1) w z
  have hfirst (i : ℕ) (hi : i≤2*m) : A i≤V*E (Y/2^(2*m)) w := by
    apply (linearSieve_shallow_layers hw hg i b hwz hY hu).trans
    apply mul_le_mul_of_nonneg_left _ hV
    apply mul_le_mul_of_nonneg_left _ (hW w)
    apply exp_le_exp.mpr; apply neg_le_neg
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hY.le (by positivity) (pow_le_pow_right₀ (by norm_num) hi)) (log_pos hw).le
  have hlast (i : ℕ) : A i≤64*(19/20:ℝ)^(i/2)*E Y z := by
    have hbase (B : Bool) (t : ℝ) (ht : t∈Set.Icc w z) (y : ℝ) (_ : 0<y) (hy : (if B then (1:ℝ) else 2)≤y/log t) :
        G B y t≤2*E y t := by
      apply linearSieve_base_weight hw ht.1 _ (by linarith : η≤1) (fun p hp => (hg p hp).2) (H.restrict ht.2)
      cases B <;> simp_all <;> linarith
    simpa only [show (32:ℝ)*2=64 by norm_num] using
      linearSieve_layer_decay G hw (by norm_num : (0:ℝ)≤2) hη hη' hg H hbase i b (Set.mem_Icc.mpr ⟨hwz,le_rfl⟩) hY hu
  let k := min (2*m) N
  have hkn : k≤N := min_le_right ..
  have hkm : k≤2*m := min_le_left ..
  have htail : (∑i∈Finset.Ico k N,A i)≤2560*(19/20:ℝ)^m*E Y z := by
    by_cases h : 2*m≤N
    · rw [show k=2*m from min_eq_left h]
      apply (sum_le_sum (fun i _ => hlast i)).trans
      calc _ = (∑i∈Finset.Ico (2*m) N,(19/20:ℝ)^(i/2))*(64*E Y z) := by
              rw [sum_mul]; apply sum_congr rfl; intro i _; ring
           _ ≤ (40*(19/20:ℝ)^m)*(64*E Y z) := mul_le_mul_of_nonneg_right (paired_geometric_tail ..) (mul_nonneg (by norm_num) (hE ..))
           _ = _ := by ring
    · rw [show k=N from min_eq_right (not_le.mp h).le,Finset.Ico_self,sum_empty]
      exact mul_nonneg (by positivity) (hE ..)
  change (∑i∈range N,A i)≤_
  rw [←Finset.sum_range_add_sum_Ico A hkn]
  apply add_le_add _ htail
  apply (sum_le_sum (fun i hi => hfirst i ((mem_range.mp hi).le.trans hkm))).trans
  simp only [sum_const,card_range,nsmul_eq_mul]
  change (k:ℝ)*(V*E (Y/2^(2*m)) w)≤(↑(2*m):ℝ)*V*E (Y/2^(2*m)) w
  rw [mul_assoc (↑(2*m):ℝ)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) (mul_nonneg hV (hE ..))

end AnalyticNumberTheory.SieveMethods
