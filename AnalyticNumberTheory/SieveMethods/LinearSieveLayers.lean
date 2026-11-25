import AnalyticNumberTheory.SieveMethods.LinearSievePrimeContraction

/-!
# The layers of an admissible Rosser tree

The unsigned mass of each generation propagates the terminal error in the
signed sieve expansion. Lower generations two steps apart form a geometric
majorant. The intermediate upper generation costs one exponential test.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The mass at exactly n prime choices, with a terminal test depending on
the sign, remaining logarithmic level and last prime cutoff. -/
def linearSieveLayer (P : Finset ℕ) (g : ℕ → ℝ) (w : ℝ) (G : Bool → ℝ → ℝ → ℝ) :
    ℕ → Bool → ℝ → ℝ → ℝ
  | 0,b,Y,z => G b Y z
  | n+1,b,Y,z => ∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),
      g p*linearSieveLayer P g w G n (!b) (Y-log p) p

/-- Exponential weight transported by the contraction. -/
def linearSieveExpWeight (P : Finset ℕ) (g : ℕ → ℝ) (Y z : ℝ) : ℝ :=
  sieveEulerBelow P g z*exp (-(Y/log z))

theorem linearSieve_base_weight {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hu : 1≤Y/log z) (hη : η≤1)
    (hg : ∀p∈P,g p<1) (H : SieveEulerApprox P g w z η) :
    linearSieveExpWeight P g Y w≤2*linearSieveExpWeight P g Y z := by
  let r := log z/log w
  let u := Y/log z
  let W := sieveEulerBelow P g
  have hlw := Real.log_pos hw
  have hlz := Real.log_pos (hw.trans_le hwz)
  have hr : 1≤r := (one_le_div hlw).mpr (Real.log_le_log (by linarith) hwz)
  have hur : u*r=Y/log w := by dsimp [u,r]; field_simp
  have hr' : r≤exp (u*(r-1)) := by
    calc r = (r-1)+1 := by ring
         _ ≤ exp (r-1) := Real.add_one_le_exp _
         _ ≤ exp (u*(r-1)) := exp_le_exp.mpr (by nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hr)])
  have hV := (abs_le.mp (H z ⟨hwz,le_rfl⟩ w ⟨le_rfl,hwz⟩)).2
  have hW := (sieveEulerBelow_pos P hg z).le
  have hmaj : W w≤2*W z*r := by
    change W w-W z*r≤η*W z at hV
    nlinarith only [hV,mul_le_mul_of_nonneg_right (hη.trans hr) hW]
  have hshift : r*exp (-(u*r))≤exp (-u) := by
    apply (mul_le_mul_of_nonneg_right hr' (exp_pos _).le).trans_eq
    rw [←Real.exp_add]; congr 1; ring
  change W w*exp (-(Y/log w))≤2*(W z*exp (-u))
  rw [←hur]
  apply (mul_le_mul_of_nonneg_right hmaj (exp_pos _).le).trans
  calc _ = (2*W z)*(r*exp (-(u*r))) := by ring
       _ ≤ (2*W z)*exp (-u) := mul_le_mul_of_nonneg_left hshift (mul_nonneg (by norm_num) hW)
       _ = _ := by ring

private theorem all_lower (P : Finset ℕ) (w z Y : ℝ) :
    (sievePrimeWindow P w z).filter (linearSieveAdmits false Y)=sievePrimeWindow P w z := by
  simp [linearSieveAdmits]

/-- Across either sign the first generation costs at most four times the
exponential weight at the parent. -/
theorem linearSieve_first_layer {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ} (b : Bool)
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hu : 1≤Y/log z) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w z η) :
    (∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),g p*linearSieveExpWeight P g (Y-log p) p)≤
      4*linearSieveExpWeight P g Y z := by
  let S := sievePrimeWindow P w z
  let W := sieveEulerBelow P g
  let u := Y/log z
  have hgp (p : ℕ) (hp : p∈S) := (hg p (mem_filter.mp hp).1).1
  have hW (t : ℝ) := (sieveEulerBelow_pos P (fun p hp => (hg p hp).2) t).le
  have h := sieve_prime_exponential hw hwz hY hη hg H
  have hinv : 1/u≤1 := (div_le_iff₀ (show 0<u from lt_of_lt_of_le zero_lt_one hu)).mpr (by simpa using hu)
  have hcoef : exp 1*(1/u+2*η)≤4 := by
    calc _ ≤ 3*(1+2*(1/10000:ℝ)) := by
              gcongr; linarith [Real.exp_one_lt_d9]
         _ ≤ _ := by norm_num
  calc _ ≤ ∑p∈S,g p*linearSieveExpWeight P g (Y-log p) p :=
         sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p hp _ =>
           mul_nonneg (hgp p hp) (mul_nonneg (hW _) (exp_pos _).le))
       _ = exp 1*∑p∈S,g p*W p*exp (-(Y/log p)) := by
         rw [mul_sum]; apply sum_congr rfl; intro p hp
         have hlp := Real.log_pos (hw.trans_le (mem_filter.mp hp).2.1)
         rw [linearSieveExpWeight,sub_div,div_self hlp.ne',neg_sub,sub_eq_add_neg,Real.exp_add]
         dsimp only [W]; ring
       _ ≤ exp 1*(W z*exp (-u)*(1/u+2*η)) := mul_le_mul_of_nonneg_left h (exp_pos 1).le
       _ = (exp 1*(1/u+2*η))*(W z*exp (-u)) := by ring
       _ ≤ 4*linearSieveExpWeight P g Y z := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (hW z) (exp_pos _).le)

/-- A bound at a lower generation propagates through any number of pairs
of primes. The initial generation can itself have arbitrary depth. -/
theorem linearSieve_lower_layers {P : Finset ℕ} {g : ℕ → ℝ} {w Z η C : ℝ}
    (G : Bool → ℝ → ℝ → ℝ) (k : ℕ) (hw : 1<w) (hC : 0≤C)
    (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w Z η)
    (hbase : ∀ z∈Set.Icc w Z, ∀ Y, 0<Y → 2≤Y/log z →
      linearSieveLayer P g w G k false Y z≤C*linearSieveExpWeight P g Y z) :
    ∀ m : ℕ, ∀ z∈Set.Icc w Z, ∀ Y, 0<Y → 2≤Y/log z →
      linearSieveLayer P g w G (2*m+k) false Y z≤
        ((19/20:ℝ)^m*C)*linearSieveExpWeight P g Y z := by
  intro m; induction m with
  | zero => simpa using hbase
  | succ m ih =>
    intro z hz Y hY hu
    let S := sievePrimeWindow P w z
    let T := fun p : ℕ => (sievePrimeWindow P w p).filter (linearSieveAdmits true (Y-log p))
    let D := (19/20:ℝ)^m*C
    let E := linearSieveExpWeight P g
    have hD : 0≤D := by dsimp [D]; positivity
    have hpstep (p : ℕ) (hp : p∈S) := linearSieve_branch_parameter (b:=false) hw hY hp hu (Or.inl rfl)
    have hpoint (p : ℕ) (hp : p∈S) (q : ℕ) (hq : q∈T p) :
        linearSieveLayer P g w G (2*m+k) false (Y-log p-log q) q≤D*E (Y-log p-log q) q := by
      obtain ⟨hq',had⟩ := mem_filter.mp hq
      obtain ⟨h₁,h₂⟩ := hpstep p hp
      obtain ⟨h₃,h₄⟩ := linearSieve_branch_parameter (b:=true) hw h₁ hq' h₂ had
      obtain ⟨_,hwq,hqp⟩ := mem_filter.mp hq'
      exact ih q ⟨hwq,hqp.le.trans ((mem_filter.mp hp).2.2.le.trans hz.2)⟩ _ h₃ h₄
    rw [show 2*(m+1)+k=(2*m+k+1)+1 by omega,linearSieveLayer,all_lower]
    simp only [Bool.not_false,linearSieveLayer,Bool.not_true]
    calc _ ≤ ∑p∈S,g p*∑q∈T p,g q*(D*E (Y-log p-log q) q) := by
            apply sum_le_sum; intro p hp; apply mul_le_mul_of_nonneg_left _ (hg p (mem_filter.mp hp).1).1
            apply sum_le_sum; intro q hq
            exact mul_le_mul_of_nonneg_left (hpoint p hp q hq) (hg q (mem_filter.mp (mem_filter.mp hq).1).1).1
         _ = D*(∑p∈S,g p*∑q∈T p,g q*E (Y-log p-log q) q) := by
            rw [mul_sum]; apply sum_congr rfl; intro p _
            rw [mul_left_comm D]; congr 1; rw [mul_sum]; apply sum_congr rfl; intro q _; ring
         _ ≤ D*((19/20)*sieveEulerBelow P g z*exp (-(Y/log z))) := by
            apply mul_le_mul_of_nonneg_left _ hD
            simpa only [E,linearSieveExpWeight,mul_assoc] using linearSieve_prime_pair_contraction hw hz.1 hY hu hη hη' hg (H.restrict hz.2)
         _ = _ := by dsimp [D,linearSieveExpWeight]; rw [pow_succ]; ring


private def LayerBound (P : Finset ℕ) (g : ℕ → ℝ) (w Z : ℝ) (G : Bool → ℝ → ℝ → ℝ)
    (n : ℕ) (b : Bool) (C : ℝ) : Prop :=
  ∀ z∈Set.Icc w Z, ∀ Y, 0<Y → (if b then (1:ℝ) else 2)≤Y/log z →
    linearSieveLayer P g w G n b Y z≤C*linearSieveExpWeight P g Y z

private theorem next_layer {P : Finset ℕ} {g : ℕ → ℝ} {w Z η C : ℝ} {G : Bool → ℝ → ℝ → ℝ}
    (b : Bool) {k : ℕ} (hw : 1<w) (hC : 0≤C) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w Z η)
    (hbase : LayerBound P g w Z G k (!b) C) : LayerBound P g w Z G (k+1) b (4*C) := by
  intro z hz Y hY hu
  let S := (sievePrimeWindow P w z).filter (linearSieveAdmits b Y)
  let E := linearSieveExpWeight P g
  change (∑p∈S,g p*linearSieveLayer P g w G k (!b) (Y-log p) p)≤_
  have hu' : 1≤Y/log z := by cases b <;> simp_all <;> linarith
  calc _ ≤ ∑p∈S,g p*(C*E (Y-log p) p) := by
          apply sum_le_sum; intro p hp; obtain ⟨hp,had⟩ := mem_filter.mp hp
          have ⟨h₁,h₂⟩ := linearSieve_branch_parameter hw hY hp hu had
          obtain ⟨hP,hwp,hpz⟩ := mem_filter.mp hp
          exact mul_le_mul_of_nonneg_left (hbase p ⟨hwp,hpz.le.trans hz.2⟩ _ h₁ h₂) (hg p hP).1
       _ = C*∑p∈S,g p*E (Y-log p) p := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring
       _ ≤ C*(4*E Y z) := mul_le_mul_of_nonneg_left (linearSieve_first_layer b hw hz.1 hY hu' hη hη' hg (H.restrict hz.2)) hC
       _ = _ := by ring

/-- At either sign and arbitrary depth n, a terminal exponential error is
bounded by a uniform constant times (19/20) to the power floor(n/2). -/
theorem linearSieve_layer_decay {P : Finset ℕ} {g : ℕ → ℝ} {w Z η C : ℝ}
    (G : Bool → ℝ → ℝ → ℝ) (hw : 1<w) (hC : 0≤C) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w Z η)
    (hbase : ∀ b, ∀ z∈Set.Icc w Z, ∀ Y, 0<Y → (if b then (1:ℝ) else 2)≤Y/log z →
      G b Y z≤C*linearSieveExpWeight P g Y z) (n : ℕ) (b : Bool) {z Y : ℝ}
    (hz : z∈Set.Icc w Z) (hY : 0<Y) (hu : (if b then (1:ℝ) else 2)≤Y/log z) :
    linearSieveLayer P g w G n b Y z≤
      (32*C*(19/20:ℝ)^(n/2))*linearSieveExpWeight P g Y z := by
  let δ : ℝ := 19/20
  have hd : 0<δ := by norm_num [δ]
  have e0 : 0≤linearSieveExpWeight P g Y z :=
    mul_nonneg (sieveEulerBelow_pos P (fun p hp => (hg p hp).2) z).le (exp_pos _).le
  have evenL (m : ℕ) : LayerBound P g w Z G (2*m) false (δ^m*C) := by
    simpa [LayerBound] using linearSieve_lower_layers G 0 hw hC hη hη' hg H (hbase false) m
  have oddL (m : ℕ) : LayerBound P g w Z G (2*m+1) false (δ^m*(4*C)) := by
    apply linearSieve_lower_layers G 1 hw (by positivity) hη hη' hg H _ m
    exact next_layer false hw hC hη hη' hg H (hbase true)
  have oddU (m : ℕ) : LayerBound P g w Z G (2*m+1) true (4*(δ^m*C)) :=
    next_layer true hw (by positivity) hη hη' hg H (evenL m)
  have evenU (m : ℕ) : LayerBound P g w Z G (2*m+1+1) true (4*(δ^m*(4*C))) :=
    next_layer true hw (by positivity) hη hη' hg H (oddL m)
  change _ ≤ (32*C*δ^(n/2))*_
  obtain he|he := Nat.mod_two_eq_zero_or_one n
  · have hn : 2*(n/2)=n := by omega
    cases b
    · have h := evenL (n/2) z hz Y hY hu; rw [hn] at h
      apply h.trans; apply mul_le_mul_of_nonneg_right _ e0
      linarith only [mul_nonneg (pow_nonneg hd.le (n/2)) hC]
    · cases hn' : n/2 with
      | zero =>
        have hn₀ : n=0 := by omega
        subst n; simpa only [linearSieveLayer,Nat.zero_div,pow_zero,mul_one] using
          (hbase true z hz Y hY hu).trans (mul_le_mul_of_nonneg_right (by linarith : C≤32*C) e0)
      | succ m =>
        have hh : 2*m+1+1=n := by omega
        have h := evenU m z hz Y hY hu; rw [hh] at h
        apply h.trans; apply mul_le_mul_of_nonneg_right _ e0
        rw [pow_succ]; dsimp only [δ]
        nlinarith only [mul_nonneg (pow_nonneg (show (0:ℝ)≤19/20 by norm_num) m) hC]
  · have hn : 2*(n/2)+1=n := by omega
    cases b
    · have h := oddL (n/2) z hz Y hY hu; rw [hn] at h
      apply h.trans; apply mul_le_mul_of_nonneg_right _ e0
      linarith only [mul_nonneg (pow_nonneg hd.le (n/2)) hC]
    · have h := oddU (n/2) z hz Y hY hu; rw [hn] at h
      apply h.trans; apply mul_le_mul_of_nonneg_right _ e0
      linarith only [mul_nonneg (pow_nonneg hd.le (n/2)) hC]


end AnalyticNumberTheory.SieveMethods
