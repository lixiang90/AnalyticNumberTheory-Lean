import AnalyticNumberTheory.SieveMethods.LinearSieveBranches

/-!
# The arithmetic linear sieve with an intermediate cutoff

The Buchstab identity bounds the sifted count between signed Rosser trees.
The error at a node splits into an analytic error, propagated with its local
density, and an arithmetic divisor budget, propagated with coefficient one.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- A positive sign gives the upper estimate, and a negative sign the lower. -/
def linearSieveSign (b : Bool) (x : ℝ) := if b then x else -x

theorem linearSieveSign_le_abs (b : Bool) (x : ℝ) : linearSieveSign b x≤|x| := by
  cases b <;> simp only [linearSieveSign,Bool.false_eq_true,ite_false,Bool.true_eq,ite_true]
  · exact neg_le_abs _
  · exact le_abs_self _

private theorem sign_step {P : Finset ℕ} {w z Y : ℝ} (b : Bool) (A U : ℕ → ℝ) {a t u : ℝ}
    (h : a=t+∑p∈sievePrimeWindow P w z,A p) (hA : ∀p∈sievePrimeWindow P w z,0≤A p) :
    linearSieveSign b (t-(u-∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),U p))≤
      linearSieveSign b (a-u)+∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),
        linearSieveSign (!b) (A p-U p) := by
  cases b with
  | false =>
    have hall : (sievePrimeWindow P w z).filter (linearSieveAdmits false Y)=sievePrimeWindow P w z := by
      ext p; simp [linearSieveAdmits]
    rw [hall]; simp only [linearSieveSign,Bool.false_eq_true,ite_false,Bool.not_false,ite_true,neg_sub,sum_sub_distrib]
    linarith only [h]
  | true =>
    have hs := sum_le_sum_of_subset_of_nonneg (s:=(sievePrimeWindow P w z).filter (linearSieveAdmits true Y))
      (filter_subset ..) (fun p hp _ => hA p hp)
    simp only [linearSieveSign,Bool.true_eq,ite_true,Bool.not_true,Bool.false_eq_true,ite_false,
      neg_sub,sum_sub_distrib]
    linarith only [h,hs]

/-- The sum of the unsigned terminal masses through a prescribed depth. -/
def linearSieveTerminalMass (P : Finset ℕ) (g : ℕ → ℝ) (w : ℝ) (n : ℕ) (b : Bool) (Y z : ℝ) :=
  ∑i∈range (n+1),linearSieveLayer P g w (fun _ y _ => linearSieveExpWeight P g y w) i b Y z

private theorem mass_succ (P : Finset ℕ) (g : ℕ → ℝ) (w : ℝ) (n : ℕ) (b : Bool) (Y z : ℝ) :
    linearSieveTerminalMass P g w (n+1) b Y z=linearSieveExpWeight P g Y w+
      ∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),g p*linearSieveTerminalMass P g w n (!b) (Y-log p) p := by
  unfold linearSieveTerminalMass
  rw [sum_range_succ',add_comm]
  congr 1
  simp only [linearSieveLayer]
  rw [sum_comm]; apply sum_congr rfl; intro p _; rw [mul_sum]

/-- Sifted count compared with its signed large-prime tree. -/
theorem linearSieve_sifted_tree {K : ℝ} (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      ∀ {w Z L : ℝ}, 2≤w → SieveEulerDimensionOne P s.density w K →
      let g := s.density
      let G := fun b y => sieveEulerBelow P g w*linearSieveProfile b (y/log w)
      ∀ (n : ℕ) (b : Bool) {d : ℕ} {Y z : ℝ}, z∈Set.Icc w Z → 0<Y →
        (if b then (1:ℝ) else 2)≤Y/log z → (sievePrimeWindow P w z).card≤n →
        LinearSieveBranch P Z L d Y z →
        linearSieveSign b ((siftedCountOf (sieveMultiple s.A d) (sieveProductBelow P z):ℝ)-
          s.X*g d*linearSieveTree P g w G n b Y z)≤
          s.X*g d*C*linearSieveTerminalMass P g w n b Y z+linearSieveBudget P s.rem L d z := by
  obtain ⟨C,hC,hsmall⟩ := linearSieve_small_branch hK
  refine ⟨C,hC,?_⟩; intro s P hP hX w Z L hw hdim g G n
  let X := fun d => s.X*g d
  let S := fun d t => (siftedCountOf (sieveMultiple s.A d) (sieveProductBelow P t):ℝ)
  let R := linearSieveBudget P s.rem L
  let E := linearSieveExpWeight P g
  let T := linearSieveTree P g w G
  let H := linearSieveTerminalMass P g w
  have hw' : 1<w := by linarith
  induction n with
  | zero =>
    intro b d Y z hz hY hu hn hd
    have hempty : sievePrimeWindow P w z=∅ := card_eq_zero.mp (by omega)
    have hsw := sieve_buchstab_window (sieveMultiple s.A d) hP hz.1
    have hrw := linearSieveBudget_window P s.rem L d hz.1
    simp only [hempty,sum_empty,add_zero] at hsw hrw
    have h₁ : 1≤Y/log z := by cases b <;> simp_all <;> linarith
    have hlz := Real.log_pos (hw'.trans_le hz.1)
    have hyw := (Real.log_le_log (by linarith) hz.1).trans ((one_le_div hlz).mp h₁)
    have hbase := (linearSieveSign_le_abs b _).trans (hsmall s P hP hX hw hz.1 hyw hdim hd b)
    change linearSieveSign b (S d z-X d*G b Y)≤X d*C*H 0 b Y z+R d z
    change S d w=S d z at hsw
    change R d w=R d z at hrw
    rw [←hsw,←hrw]
    simpa only [S,X,G,H,R,linearSieveTerminalMass,Nat.zero_add,sum_range_one,linearSieveLayer,mul_assoc] using hbase
  | succ n ih =>
    intro b d Y z hz hY hu hn hd
    let B := sievePrimeWindow P w z
    let A := B.filter (linearSieveAdmits b Y)
    let U := fun p : ℕ => X (d*p)*T n (!b) (Y-log p) p
    let M := fun p : ℕ => H n (!b) (Y-log p) p
    have h₁ : 1≤Y/log z := by cases b <;> simp_all <;> linarith
    have hyw := (Real.log_le_log (by linarith) hz.1).trans ((one_le_div (Real.log_pos (hw'.trans_le hz.1))).mp h₁)
    have hb := (linearSieveSign_le_abs b _).trans (hsmall s P hP hX hw hz.1 hyw hdim hd b)
    have hmult (p : ℕ) (hp : p∈B) : X (d*p)=X d*g p := by
      have hc := (hd.child hP hz.2 hp).1
      change s.X*s.densityArith (d*p)=s.X*s.density d*s.density p
      rw [s.densityArith_isMultiplicative.map_mul_of_coprime hc]
      change s.X*(s.density d*s.density p)=_; ring
    have hstep : S d w=S d z+∑p∈B,S (d*p) p := by
      convert sieve_buchstab_window (sieveMultiple s.A d) hP hz.1 using 2
      apply sum_congr rfl; intro p hp
      rw [sieveMultiple_coprime (hd.child hP hz.2 hp).1]
    have hchild (p : ℕ) (hp : p∈A) :
        linearSieveSign (!b) (S (d*p) p-U p)≤X (d*p)*C*M p+R (d*p) p := by
      obtain ⟨hp,had⟩ := mem_filter.mp hp
      obtain ⟨hwP,hpar⟩ := linearSieve_branch_parameter hw' hY hp hu had
      have hn' := sievePrimeWindow_card_lt_of_mem hp
      exact ih (!b) ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.le.trans hz.2⟩ hwP hpar (by omega)
        (hd.child hP hz.2 hp).2
    have hs := sign_step (Y:=Y) b (fun p => S (d*p) p) U (u:=X d*G b Y) hstep
      (fun p _ => Nat.cast_nonneg _)
    have hU : X d*T (n+1) b Y z=X d*G b Y-∑p∈A,U p := by
      dsimp only [T,linearSieveTree]; rw [mul_sub,mul_sum]; congr 1
      apply sum_congr rfl; intro p hp
      dsimp only [U]; rw [hmult p (mem_filter.mp hp).1]; ring
    have hM : (∑p∈A,X (d*p)*C*M p)=X d*C*∑p∈A,g p*M p := by
      rw [mul_sum]; apply sum_congr rfl; intro p hp; rw [hmult p (mem_filter.mp hp).1]; ring
    have hbudget : R d w+∑p∈A,R (d*p) p≤R d z := by
      change _ ≤ linearSieveBudget P s.rem L d z
      rw [←linearSieveBudget_window P s.rem L d hz.1]
      apply add_le_add_right
      exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p _ _ => linearSieveBudget_nonneg ..)
    change linearSieveSign b (S d z-X d*T (n+1) b Y z)≤X d*C*H (n+1) b Y z+R d z
    rw [hU]
    apply hs.trans
    have hb' : linearSieveSign b (S d w-X d*G b Y)≤X d*C*E Y w+R d w := by
      change linearSieveSign b (S d w-X d*(sieveEulerBelow P g w*linearSieveProfile b (Y/log w)))≤_
      rw [←mul_assoc]; exact hb
    apply (add_le_add hb' (sum_le_sum hchild)).trans
    change (X d*C*E Y w+R d w)+(∑p∈A,(X (d*p)*C*M p+R (d*p) p))≤X d*C*H (n+1) b Y z+R d z
    rw [sum_add_distrib,hM]
    change _≤X d*C*linearSieveTerminalMass P g w (n+1) b Y z+R d z
    rw [mass_succ]
    change _≤X d*C*(E Y w+∑p∈A,g p*M p)+R d z
    linarith only [hbudget]

end AnalyticNumberTheory.SieveMethods
