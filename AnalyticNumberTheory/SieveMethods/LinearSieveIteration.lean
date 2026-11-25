import AnalyticNumberTheory.SieveMethods.LinearSieveTransition

/-!
# Iteration over the large primes in the linear sieve

At an upper node the next prime must satisfy p³ < exp(Y). A rejected
child contributes zero to the analytic transition because f vanishes up to
two. The finite iteration accumulates the quadrature error by the product
of the factors 1+g(p).
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The primes processed between two strict Euler-product cutoffs. -/
def sievePrimeWindow (P : Finset ℕ) (w z : ℝ) : Finset ℕ :=
  P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)

/-- The beta=2 Rosser branch test at logarithmic level Y. -/
def linearSieveAdmits (b : Bool) (Y : ℝ) (p : ℕ) : Prop := b=false ∨ 3*log p<Y

/-- Finite signed large-prime expansion with arbitrary terminal data at w.
Taking the depth as the cardinality of the window explores every branch. -/
def linearSieveTree (P : Finset ℕ) (g : ℕ → ℝ) (w : ℝ) (G : Bool → ℝ → ℝ) :
    ℕ → Bool → ℝ → ℝ → ℝ
  | 0,b,Y,_ => G b Y
  | n+1,b,Y,z => G b Y-∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),
      g p*linearSieveTree P g w G n (!b) (Y-log p) p

private theorem window_subset {P : Finset ℕ} {w t z : ℝ} (ht : t≤z) :
    sievePrimeWindow P w t ⊆ sievePrimeWindow P w z := by
  intro p hp; obtain ⟨hP,hw,hpt⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hP,hw,hpt.trans_le ht⟩

private theorem window_before {P : Finset ℕ} {w z : ℝ} {p : ℕ} (hp : p∈sievePrimeWindow P w z) :
    sievePrimeWindow P w p=(sievePrimeWindow P w z).filter (fun q => q<p) := by
  ext q; have hpz := (mem_filter.mp hp).2.2
  simp only [sievePrimeWindow,mem_filter,Nat.cast_lt]
  constructor
  · rintro ⟨hP,hw,hqp⟩; exact ⟨⟨hP,hw,(show (q:ℝ)<p by exact_mod_cast hqp).trans hpz⟩,hqp⟩
  · rintro ⟨⟨hP,hw,_⟩,hqp⟩; exact ⟨hP,hw,hqp⟩

theorem sievePrimeWindow_card_lt_of_mem {P : Finset ℕ} {w z : ℝ} {p : ℕ} (hp : p∈sievePrimeWindow P w z) :
    (sievePrimeWindow P w p).card<(sievePrimeWindow P w z).card := by
  apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨window_subset (mem_filter.mp hp).2.2.le,?_⟩)
  intro he
  have hh : p∈sievePrimeWindow P w p := he ▸ hp
  exact lt_irrefl _ (mem_filter.mp hh).2.2

private theorem profile_zero {t : ℝ} (ht : t≤2) : linearSieveProfile false t=0 :=
  (linearSieve_initial ⟨le_max_left ..,max_le (by norm_num) ht⟩).2

theorem linearSieve_branch_parameter {b : Bool} {Y w z : ℝ} {P : Finset ℕ} {p : ℕ}
    (hw : 1<w) (hY : 0<Y) (hp : p∈sievePrimeWindow P w z)
    (ha : (if b then (1:ℝ) else 2)≤Y/log z) (had : linearSieveAdmits b Y p) :
    0<Y-log p ∧ (if !b then (1:ℝ) else 2)≤(Y-log p)/log p := by
  have hw' := (mem_filter.mp hp).2.1
  have hz' := (mem_filter.mp hp).2.2
  have hlp := Real.log_pos (hw.trans_le hw')
  have hratio := ha.trans (div_le_div_of_nonneg_left hY.le hlp (Real.log_le_log (by linarith) hz'.le))
  cases b
  · simp only [Bool.false_eq_true,ite_false] at hratio
    simp only [Bool.not_false,ite_true,le_div_iff₀ hlp] at *
    constructor <;> linarith
  · have h3 := had.resolve_left (by decide)
    simp only [Bool.not_true,Bool.false_eq_true,ite_false,le_div_iff₀ hlp]
    constructor <;> linarith

/-- The one-step formula with exactly the primes admitted by Rosser. -/
theorem linearSieve_admitted_transition (P : Finset ℕ) (g : ℕ → ℝ) (b : Bool) {w z Y D : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hD : 0≤D)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (ha : (if b then (1:ℝ) else 2)≤Y/log z)
    (hV : ∀t∈Set.Icc w z,|sieveEulerBelow P g t-sieveEulerBelow P g z*(log z/log t)|≤D) :
    |sieveEulerBelow P g w*linearSieveProfile b (Y/log w)-
      sieveEulerBelow P g z*linearSieveProfile b (Y/log z)-
      ∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),
        g p*(sieveEulerBelow P g p*linearSieveProfile (!b) ((Y-log p)/log p))|≤
          3*(2*exp eulerMascheroniConstant)*D := by
  have h := linearSieve_prime_transition P g b hw hwz hY hD hg ha hV
  have he : (∑p∈(sievePrimeWindow P w z).filter (linearSieveAdmits b Y),
        g p*(sieveEulerBelow P g p*linearSieveProfile (!b) ((Y-log p)/log p)))=
      ∑p∈sievePrimeWindow P w z,g p*sieveEulerBelow P g p*linearSieveProfile (!b) (Y/log p-1) := by
    rw [sum_filter]; apply sum_congr rfl
    intro p hp
    have hlp := Real.log_pos (hw.trans_le (mem_filter.mp hp).2.1)
    rw [sub_div,div_self hlp.ne']
    by_cases had : linearSieveAdmits b Y p
    · rw [ite_eq_left had]; ring
    · rw [ite_eq_right had]
      have hb : b=true := by cases b <;> simp_all [linearSieveAdmits]
      subst b
      have hle := not_lt.mp (fun hh => had (Or.inr hh))
      rw [show (!true)=false by rfl,profile_zero (by have := (div_le_iff₀ hlp).mpr hle; linarith),mul_zero]
  rw [he]; exact h

/-- Analytic main term after expanding all admissible primes in [w,z).
The whole tree error is bounded by the one-step error times the full
product ∏(1+g), independently of its depth. -/
theorem linearSieve_tree_comparison (P : Finset ℕ) (g : ℕ → ℝ) {w Z D : ℝ}
    (hw : 1<w) (hD : 0≤D) (hg : ∀p∈P,0≤g p ∧ g p<1)
    (hV : ∀ z∈Set.Icc w Z,∀t∈Set.Icc w z,
      |sieveEulerBelow P g t-sieveEulerBelow P g z*(log z/log t)|≤D) :
    let W := sieveEulerBelow P g
    let G := fun b Y => W w*linearSieveProfile b (Y/log w)
    ∀ (n : ℕ) (b : Bool) {z Y : ℝ}, (sievePrimeWindow P w z).card≤n → z∈Set.Icc w Z →
      0<Y → (if b then (1:ℝ) else 2)≤Y/log z →
      |linearSieveTree P g w G n b Y z-W z*linearSieveProfile b (Y/log z)| ≤
        3*(2*exp eulerMascheroniConstant)*D*(∏p∈sievePrimeWindow P w z,(1+g p)) := by
  intro W G
  let E := 3*(2*exp eulerMascheroniConstant)*D
  have hE : 0≤E := by dsimp [E]; positivity
  intro n
  induction n with
  | zero =>
    intro b z Y hn hz hY ha
    have he : sievePrimeWindow P w z=∅ := card_eq_zero.mp (by omega)
    have h := linearSieve_admitted_transition P g b hw hz.1 hY hD hg ha (hV z hz)
    simp [he,linearSieveTree] at h ⊢
    exact h
  | succ n ih =>
    intro b z Y hn hz hY ha
    let S := sievePrimeWindow P w z
    let T := S.filter (linearSieveAdmits b Y)
    let U := fun p : ℕ => W p*linearSieveProfile (!b) ((Y-log p)/log p)
    let H := fun p : ℕ => linearSieveTree P g w G n (!b) (Y-log p) p
    let V := fun p : ℕ => ∏q∈sievePrimeWindow P w p,(1+g q)
    have hV₀ (p : ℕ) : 0≤V p := prod_nonneg (fun q hq => by linarith [(hg q (mem_filter.mp hq).1).1])
    have hi (p : ℕ) (hp : p∈T) : |H p-U p|≤E*V p := by
      obtain ⟨hp,had⟩ := mem_filter.mp hp
      obtain ⟨h₁,h₂⟩ := linearSieve_branch_parameter hw hY hp ha had
      refine ih (!b) (z:=p) (Y:=Y-log p) (by have := sievePrimeWindow_card_lt_of_mem hp; omega) ?_ h₁ h₂
      exact ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.le.trans hz.2⟩
    have he := linearSieve_admitted_transition P g b hw hz.1 hY hD hg ha (hV z hz)
    change |G b Y-W z*linearSieveProfile b (Y/log z)-∑p∈T,g p*U p|≤E at he
    have hsum : |∑p∈T,g p*(H p-U p)|≤E*∑p∈S,g p*V p := by
      apply (Finset.abs_sum_le_sum_abs ..).trans
      rw [mul_sum]
      apply (sum_le_sum (g:=fun p => E*(g p*V p)) _).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p hp _ =>
         mul_nonneg hE (mul_nonneg (hg _ (mem_filter.mp hp).1).1 (hV₀ p))))
      intro p hp; have hgp := (hg p (mem_filter.mp (mem_filter.mp hp).1).1).1
      rw [abs_mul,abs_of_nonneg hgp]
      exact (mul_le_mul_of_nonneg_left (hi p hp) hgp).trans_eq (by ring)
    have hprod : (∏p∈S,(1+g p))=1+∑p∈S,g p*V p := by
      rw [prod_one_add_ordered S g]; congr 1
      apply sum_congr rfl; intro p hp; dsimp only [V]; rw [window_before hp]
    change |(G b Y-∑p∈T,g p*H p)-W z*linearSieveProfile b (Y/log z)|≤E*∏p∈S,(1+g p)
    rw [hprod]; simp_rw [mul_sub] at hsum; rw [sum_sub_distrib] at hsum
    rw [abs_le] at he hsum ⊢
    constructor <;> linarith only [he.1,he.2,hsum.1,hsum.2]

end AnalyticNumberTheory.SieveMethods
