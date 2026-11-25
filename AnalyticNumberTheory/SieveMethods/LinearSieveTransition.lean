import AnalyticNumberTheory.SieveMethods.LinearSieveQuadrature

/-!
# A single transition of the one-dimensional linear sieve

The jump in the finite Euler product when a prime is inserted is exactly
its density times the old product. On the scale log(y)/log(p) the model
measure is constant, and the delay equation identifies the model integral.
-/
noncomputable section
open Set Finset Real MeasureTheory
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- Euler product over the members of P strictly below the real cutoff t. -/
def sieveEulerBelow (P : Finset ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∏ p∈P.filter (fun p : ℕ => (p:ℝ)<t), (1-g p)

theorem sieveEulerBelow_pos (P : Finset ℕ) {g : ℕ → ℝ} (hg : ∀p∈P,g p<1) (t : ℝ) :
    0<sieveEulerBelow P g t :=
  prod_pos (fun p hp => sub_pos.mpr (hg p (mem_filter.mp hp).1))

private theorem cumulative_jump (P : Finset ℕ) (g : ℕ → ℝ) (z : ℝ) :
    (∑p∈P.filter (fun p : ℕ => (p:ℝ)<z),g p*sieveEulerBelow P g p)=1-sieveEulerBelow P g z := by
  let S := P.filter (fun p : ℕ => (p:ℝ)<z)
  have he (p : ℕ) (hp : p∈S) : S.filter (fun q => q<p)=P.filter (fun q : ℕ => (q:ℝ)<p) := by
    ext q
    obtain ⟨_,hpz⟩ := mem_filter.mp hp
    simp only [S,mem_filter,Nat.cast_lt]
    constructor
    · rintro ⟨⟨hq,_⟩,hqp⟩; exact ⟨hq,hqp⟩
    · rintro ⟨hq,hqp⟩
      exact ⟨⟨hq,(show (q:ℝ)<p by exact_mod_cast hqp).trans hpz⟩,hqp⟩
  have hh := prod_one_sub_ordered S g
  have hsum : (∑p∈S,g p*∏q∈S.filter (fun q => q<p),(1-g q))=
      ∑p∈S,g p*sieveEulerBelow P g p := by
    apply sum_congr rfl; intro p hp; rw [he p hp]; rfl
  rw [hsum] at hh
  change (∑p∈S,g p*sieveEulerBelow P g p)=1-∏p∈S,(1-g p)
  linarith only [hh]

/-- The sum of the jumps at the primes in [w,z) telescopes exactly. -/
theorem sieveEulerBelow_sub (P : Finset ℕ) (g : ℕ → ℝ) {w z : ℝ} (hwz : w≤z) :
    (∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p*sieveEulerBelow P g p)=
      sieveEulerBelow P g w-sieveEulerBelow P g z := by
  have h (p : ℕ) : (if (p:ℝ)<z then g p*sieveEulerBelow P g p else 0)=
      (if (p:ℝ)<w then g p*sieveEulerBelow P g p else 0)+
      (if w≤p ∧ (p:ℝ)<z then g p*sieveEulerBelow P g p else 0) := by
    by_cases hp : (p:ℝ)<w
    · simp [hp,hp.trans_le hwz,not_le.mpr hp]
    · simp [hp,not_lt.mp hp]
  have hsum := Finset.sum_congr (s₁:=P) rfl (fun p _ => h p)
  rw [sum_add_distrib,←sum_filter,←sum_filter,←sum_filter,cumulative_jump,cumulative_jump] at hsum
  linarith only [hsum]

/-- Transfer of an Euler-product estimate to prime sums with a monotone test
on the inverse logarithmic scale. D is an absolute error on Euler products. -/
theorem sieve_prime_quadrature (P : Finset ℕ) (g : ℕ → ℝ) {w z Y D M : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hD : 0≤D) (hM : 0≤M)
    (hg : ∀p∈P, 0≤g p ∧ g p<1)
    (hV : ∀t∈Icc w z,|sieveEulerBelow P g t-sieveEulerBelow P g z*(log z/log t)|≤D)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀t∈Icc (Y/log z) (Y/log w), f t∈Icc 0 M)
    (hm : MonotoneOn f (Icc (Y/log z) (Y/log w)) ∨ AntitoneOn f (Icc (Y/log z) (Y/log w))) :
    |(∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p*sieveEulerBelow P g p*f (Y/log p))-
      (sieveEulerBelow P g z/(Y/log z))*(∫t in Icc (Y/log z) (Y/log w), f t)|≤(2*D)*M := by
  let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  let W := sieveEulerBelow P g
  let a := Y/log z
  let b := Y/log w
  let c := W z/a
  let x := fun p : ℕ => Y/log p
  let m := fun p : ℕ => g p*W p
  have hz := hw.trans_le hwz
  have hla := Real.log_pos hw
  have hlz := Real.log_pos hz
  have hlog (p : ℕ) (hp : p∈S) : 0<log p :=
    Real.log_pos (hw.trans_le (mem_filter.mp hp).2.1)
  have hx (p : ℕ) (hp : p∈S) : x p∈Icc a b := by
    obtain ⟨_,h₁,h₂⟩ := mem_filter.mp hp
    exact ⟨div_le_div_of_nonneg_left hY.le (hlog p hp)
      (Real.log_le_log (by linarith) h₂.le),
      div_le_div_of_nonneg_left hY.le hla (Real.log_le_log (by linarith) h₁)⟩
  have hc (t : ℝ) (ht : t∈Icc a b) :
      |(∑p∈S.filter (fun p => x p≤t),m p)-c*(t-a)|≤D := by
    have htpos : 0<t := (div_pos hY hlz).trans_le ht.1
    let v := exp (Y/t)
    have hwv : w≤v := by
      rw [←Real.log_le_iff_le_exp (by linarith)]
      apply (le_div_iff₀ htpos).mpr
      have h := (le_div_iff₀ hla).mp ht.2; linarith
    have hvz : v≤z := by
      rw [←Real.le_log_iff_exp_le (by linarith)]
      apply (div_le_iff₀ htpos).mpr
      have h := (div_le_iff₀ hlz).mp ht.1; linarith
    have hset : S.filter (fun p => x p≤t)=P.filter (fun p : ℕ => v≤p ∧ (p:ℝ)<z) := by
      ext p; simp only [S,mem_filter]
      constructor
      · rintro ⟨⟨hP,hw',hz'⟩,hu⟩
        refine ⟨hP,?_,hz'⟩
        apply (Real.le_log_iff_exp_le (by linarith : (0:ℝ)<p)).mp
        apply (div_le_iff₀ htpos).mpr
        linarith [(div_le_iff₀ (Real.log_pos (hw.trans_le hw'))).mp hu]
      · rintro ⟨hP,hv',hz'⟩
        have hw' := hwv.trans hv'
        refine ⟨⟨hP,hw',hz'⟩,?_⟩
        apply (div_le_iff₀ (Real.log_pos (hw.trans_le hw'))).mpr
        have hh := (Real.le_log_iff_exp_le (by linarith : (0:ℝ)<p)).mpr hv'
        linarith [(div_le_iff₀ htpos).mp hh]
    rw [hset]
    change |(∑p∈P.filter (fun p : ℕ => v≤p ∧ (p:ℝ)<z),g p*sieveEulerBelow P g p)-_|≤D
    rw [sieveEulerBelow_sub P g hvz]
    have hEq : W v-W z-c*(t-a)=W v-W z*(log z/log v) := by
      dsimp only [c,a,v]; rw [Real.log_exp]; field_simp [hY.ne',hlz.ne',htpos.ne']
      <;> ring
    change |W v-W z-c*(t-a)|≤D
    rw [hEq]; exact hV v ⟨hwv,hvz⟩
  apply finite_monotone_quadrature S x m (c:=c) (by positivity) hM _ hx f hf hF hm
  · intro l r hl hlr hr
    exact finite_interval_discrepancy_of_cumulative S x m hD (fun p hp => (hx p hp).1) hc hl hlr hr
  · intro p hp; exact mul_nonneg (hg p (mem_filter.mp hp).1).1 (sieveEulerBelow_pos P (fun q hq => (hg q hq).2) p).le


/-- Extend each profile constantly from its left endpoint at one. -/
def linearSieveProfile (b : Bool) (t : ℝ) := linearSieveFunction b (max 1 t)

theorem continuous_linearSieveProfile (b : Bool) : Continuous (linearSieveProfile b) :=
  (continuousOn_linearSieveFunction b).comp_continuous (continuous_const.max continuous_id)
    (fun _ => mem_Ici.mpr (le_max_left ..))

theorem linearSieveProfile_bounds (b : Bool) (t : ℝ) :
    linearSieveProfile b t∈Icc 0 (2*exp eulerMascheroniConstant) := by
  refine ⟨linearSieveFunction_nonneg b (zero_le_one.trans (le_max_left ..)),?_⟩
  have hupper := strictAntiOn_linearSieveUpper.antitoneOn (mem_Ici.mpr (le_refl (1:ℝ)))
    (mem_Ici.mpr (le_max_left 1 t)) (le_max_left ..)
  rw [linearSieveUpper_eq_of_le_three (show (1:ℝ)∈Set.Icc 1 3 by norm_num),div_one] at hupper
  cases b
  · exact (sub_pos.mp (linearSieve_gap_le_factorial 0 (u:=max 1 t) (by simp)).1).le.trans hupper
  · exact hupper

theorem linearSieveProfile_mono (b : Bool) :
    if b then Antitone (linearSieveProfile b) else Monotone (linearSieveProfile b) := by
  cases b with
  | true =>
    intro x y hxy
    exact strictAntiOn_linearSieveUpper.antitoneOn (mem_Ici.mpr (le_max_left ..)) (mem_Ici.mpr (le_max_left ..)) (max_le_max_left 1 hxy)
  | false =>
    intro x y hxy
    let a := max 1 x
    let c := max 1 y
    have hac : a≤c := max_le_max_left 1 hxy
    have ha₁ : 1≤a := le_max_left ..
    have hc₁ : 1≤c := le_max_left ..
    by_cases ha : 2≤a
    · exact strictMonoOn_linearSieveLower.monotoneOn ha (ha.trans hac) hac
    change linearSieveLower a≤linearSieveLower c
    rw [(linearSieve_initial ⟨ha₁,(not_le.mp ha).le⟩).2]
    exact linearSieveFunction_nonneg false (zero_le_one.trans hc₁)

private theorem profile_integral (b : Bool) {t : ℝ} (ht : (if b then (1:ℝ) else 2)≤t) :
    t*linearSieveProfile b t=(if b then 2*exp eulerMascheroniConstant else 0)+
      ∫v in (2:ℝ)..t,linearSieveProfile (!b) (v-1) := by
  by_cases h : 2≤t
  · rw [linearSieveProfile,max_eq_right (by linarith : 1≤t),linearSieve_integral b h]
    congr 1; apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_le h] at hv
    simp only [linearSieveProfile,max_eq_right (by linarith [hv.1] : 1≤v-1)]
  have hle := (not_le.mp h).le
  have hb : b=true := by cases b <;> simp_all <;> linarith
  subst b; simp only [Bool.true_eq,ite_true] at ht ⊢
  have hseed := linearSieve_initial ⟨ht,hle⟩
  have hzero : (∫v in (2:ℝ)..t,linearSieveProfile false (v-1))=0 := by
    rw [←intervalIntegral.integral_zero (a:=2) (b:=t) (μ:=volume) (E:=ℝ)]
    apply intervalIntegral.integral_congr
    intro v hv; rw [uIcc_of_ge hle] at hv
    exact (linearSieve_initial (show max 1 (v-1)∈Set.Icc 1 2 from
      ⟨le_max_left ..,max_le (by norm_num) (by linarith [hv.2])⟩)).2
  change t*linearSieveUpper (max 1 t)=2*exp eulerMascheroniConstant+_
  rw [max_eq_right ht,hseed.1,show (!true)=false by rfl,hzero,add_zero]
  field_simp [show t≠0 by linarith]

/-- The linear sieve's delay equation integrates between arbitrary
endpoints. For the upper profile its range extends down to 1. -/
theorem linearSieveProfile_integral_from (b : Bool) {a r : ℝ}
    (ha : (if b then (1:ℝ) else 2)≤a) (hr : a≤r) :
    (∫v in a..r,linearSieveProfile (!b) (v-1))=r*linearSieveProfile b r-a*linearSieveProfile b a := by
  rw [profile_integral b (ha.trans hr),profile_integral b ha]
  have H : Continuous (fun t : ℝ => linearSieveProfile (!b) (t-1)) :=
    (continuous_linearSieveProfile _).comp (continuous_id.sub continuous_const)
  linarith only [intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
     (H.intervalIntegrable 2 a) (H.intervalIntegrable a r)]

/-- The prime-sum transition of the one-dimensional linear sieve, with an
absolute error of at most three test-function heights times the Euler
product discrepancy on the sifting interval. -/
theorem linearSieve_prime_transition (P : Finset ℕ) (g : ℕ → ℝ) (b : Bool) {w z Y D : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hD : 0≤D)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (hpar : (if b then (1:ℝ) else 2)≤Y/log z)
    (hV : ∀t∈Icc w z,|sieveEulerBelow P g t-sieveEulerBelow P g z*(log z/log t)|≤D) :
    |sieveEulerBelow P g w*linearSieveProfile b (Y/log w)-
      sieveEulerBelow P g z*linearSieveProfile b (Y/log z)-
      ∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),
        g p*sieveEulerBelow P g p*linearSieveProfile (!b) (Y/log p-1)|≤
          3*(2*exp eulerMascheroniConstant)*D := by
  let a := Y/log z
  let r := Y/log w
  let W := sieveEulerBelow P g
  let M := 2*exp eulerMascheroniConstant
  let f := fun t : ℝ => linearSieveProfile (!b) (t-1)
  have hlw := Real.log_pos hw
  have hlz := Real.log_pos (hw.trans_le hwz)
  have ha : 0<a := div_pos hY hlz
  have har : a≤r := div_le_div_of_nonneg_left hY.le hlw (Real.log_le_log (by linarith) hwz)
  have hm : MonotoneOn f (Icc a r) ∨ AntitoneOn f (Icc a r) := by
    have H := linearSieveProfile_mono (!b)
    cases b
    · exact Or.inr (fun x hx y hy hxy => H (sub_le_sub_right hxy 1))
    · exact Or.inl (fun x hx y hy hxy => H (sub_le_sub_right hxy 1))
  have hq := sieve_prime_quadrature P g hw hwz hY hD (show 0≤M by dsimp [M]; positivity) hg hV f
    ((continuous_linearSieveProfile _).comp (continuous_id.sub continuous_const)) (fun t _ => linearSieveProfile_bounds _ _) hm
  have hint : (∫t in Icc a r,f t)=r*linearSieveProfile b r-a*linearSieveProfile b a := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le har]
    exact linearSieveProfile_integral_from b hpar har
  change |(∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p*W p*f (Y/log p))-
      W z/a*(∫t in Icc a r,f t)|≤2*D*M at hq
  rw [hint] at hq
  have he : W z/a*(r*linearSieveProfile b r-a*linearSieveProfile b a)=
      W z*(log z/log w)*linearSieveProfile b r-W z*linearSieveProfile b a := by
    dsimp [a,r]; field_simp [hlw.ne',hlz.ne',hY.ne'] <;> ring
  rw [he] at hq
  have hprod := mul_le_mul (hV w ⟨le_rfl,hwz⟩) (linearSieveProfile_bounds b r).2
    (linearSieveProfile_bounds b r).1 hD
  rw [←abs_of_nonneg (linearSieveProfile_bounds b r).1,←abs_mul] at hprod
  change |W w*linearSieveProfile b r-W z*linearSieveProfile b a-
    ∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p*W p*f (Y/log p)|≤3*M*D
  change |(W w-W z*(log z/log w))*linearSieveProfile b r|≤D*M at hprod
  rw [abs_le] at hprod hq ⊢
  constructor <;> linarith only [hprod.1,hprod.2,hq.1,hq.2]

end AnalyticNumberTheory.SieveMethods
