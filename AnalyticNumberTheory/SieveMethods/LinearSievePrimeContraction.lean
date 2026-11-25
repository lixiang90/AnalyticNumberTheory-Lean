import AnalyticNumberTheory.SieveMethods.LinearSieveContraction
import AnalyticNumberTheory.SieveMethods.LinearSieveIteration

/-!
# Contraction of pairs of primes in the lower linear sieve

The inverse logarithmic scale makes the Euler-product model measure constant.
Two applications of quadrature transfer the continuous contraction to the
decreasing prime pairs allowed by the Rosser rule.
-/
noncomputable section
open Set Finset Real MeasureTheory
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- Local comparison with the one-dimensional Euler product on every
subinterval, with error measured in units of the product at the right end. -/
def SieveEulerApprox (P : Finset ℕ) (g : ℕ → ℝ) (w z η : ℝ) : Prop :=
  ∀ b∈Set.Icc w z, ∀ a∈Set.Icc w b,
    |sieveEulerBelow P g a-sieveEulerBelow P g b*(log b/log a)|≤η*sieveEulerBelow P g b

theorem SieveEulerApprox.restrict {P : Finset ℕ} {g : ℕ → ℝ} {w z b η : ℝ}
    (H : SieveEulerApprox P g w z η) (hb : b≤z) : SieveEulerApprox P g w b η :=
  fun t ht => H t ⟨ht.1,ht.2.trans hb⟩

private theorem euler_pos {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀p∈P,0≤g p ∧ g p<1) (x : ℝ) :
    0<sieveEulerBelow P g x := sieveEulerBelow_pos P (fun p hp => (hg p hp).2) x

/-- Exponential test function, uniform in both sieve cutoffs. -/
theorem sieve_prime_exponential {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hη : 0≤η) (hg : ∀p∈P,0≤g p ∧ g p<1)
    (H : SieveEulerApprox P g w z η) :
    (∑p∈sievePrimeWindow P w z,g p*sieveEulerBelow P g p*exp (-(Y/log p)))≤
      sieveEulerBelow P g z*exp (-(Y/log z))*(1/(Y/log z)+2*η) := by
  let a := Y/log z
  let b := Y/log w
  let W := sieveEulerBelow P g
  have ha : 0<a := div_pos hY (Real.log_pos (hw.trans_le hwz))
  have hW : 0<W z := euler_pos hg z
  have h := sieve_prime_quadrature P g hw hwz hY (mul_nonneg hη hW.le) (exp_pos (-a)).le hg
    (H z ⟨hwz,le_rfl⟩) (fun t : ℝ => exp (-t)) (Real.continuous_exp.comp continuous_neg)
    (fun t ht => ⟨(exp_pos _).le,exp_le_exp.mpr (neg_le_neg ht.1)⟩)
    (Or.inr (fun _ _ _ _ hxy => exp_le_exp.mpr (neg_le_neg hxy)))
  have hi : (∫t in Set.Icc a b,exp (-t))≤exp (-a) := by
    rw [integral_Icc_eq_integral_Ioc,←integral_exp_neg_Ioi a]
    exact setIntegral_mono_set (integrableOn_exp_neg_Ioi a)
      (Filter.Eventually.of_forall (fun t => (exp_pos (-t)).le)) (Filter.Eventually.of_forall (fun _ ht => ht.1))
  change |(∑p∈sievePrimeWindow P w z,g p*W p*exp (-(Y/log p)))-W z/a*(∫t in Set.Icc a b,exp (-t))|≤_ at h
  change _ ≤ W z*exp (-a)*(1/a+2*η)
  linarith only [(abs_le.mp h).2,mul_le_mul_of_nonneg_left hi (div_nonneg hW.le ha.le),
    show W z*exp (-a)*(1/a+2*η)=W z/a*exp (-a)+(2*(η*W z))*exp (-a) by ring]

private theorem kernel_nonneg {u : ℝ} (hu : 2≤u) : 0≤linearSievePairKernel u :=
  div_nonneg (exp_pos _).le (by linarith)

private theorem kernel_antitone : AntitoneOn linearSievePairKernel (Set.Ici 2) := by
  intro a ha b hb hab
  apply div_le_div₀ (exp_pos _).le (exp_le_exp.mpr (neg_le_neg (max_le_max_left _ (sub_le_sub_right hab 1))))
    (by linarith [mem_Ici.mp ha]) (sub_le_sub_right hab 1)

private theorem kernel_bound {u : ℝ} (hu : 2≤u) : linearSievePairKernel u≤exp 1*exp (-u) := by
  rw [linearSievePairKernel,←Real.exp_add]
  exact (div_le_self (exp_pos _).le (by linarith)).trans
    (exp_le_exp.mpr (by linarith [le_max_right (3:ℝ) (u-1)]))

private theorem sieve_prime_pair_kernel {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hu : 2≤Y/log z) (hη : 0≤η)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w z η) :
    exp 1*(∑p∈sievePrimeWindow P w z,g p*sieveEulerBelow P g p*linearSievePairKernel (Y/log p))≤
      sieveEulerBelow P g z*exp (-(Y/log z))*(73/100+2*exp 1^2*η) := by
  let u := Y/log z
  let r := Y/log w
  let W := sieveEulerBelow P g
  let f := fun t : ℝ => linearSievePairKernel (max 2 t)
  have hze : 0<W z := euler_pos hg z
  have hup : 0<u := by change 0<Y/log z; linarith
  have hext (t : ℝ) (ht : u≤t) : f t=linearSievePairKernel t := by
    dsimp [f]; rw [max_eq_right (hu.trans ht)]
  have hf : Continuous f := by
    change Continuous (fun t : ℝ => exp (-max 3 (max 2 t-1))/(max 2 t-1))
    refine Continuous.div (f:=fun t : ℝ => exp (-max 3 (max 2 t-1))) (g:=fun t : ℝ => max 2 t-1) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro t; linarith [le_max_left (2:ℝ) t]
  have hq := sieve_prime_quadrature P g hw hwz hY (mul_nonneg hη hze.le) (kernel_nonneg hu) hg
    (H z ⟨hwz,le_rfl⟩) f hf (fun t ht => by
      rw [hext t ht.1]; exact ⟨kernel_nonneg (hu.trans ht.1),kernel_antitone hu (hu.trans ht.1) ht.1⟩)
    (Or.inr (fun t ht s hs hts => by
      rw [hext s hs.1,hext t ht.1]; exact kernel_antitone (hu.trans ht.1) (hu.trans hs.1) hts))
  have hi : (∫t in Set.Icc u r,f t)≤∫t in Set.Ioi u,linearSievePairKernel t := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun t (ht : t∈Set.Icc u r) => hext t ht.1),
      integral_Icc_eq_integral_Ioc]
    apply setIntegral_mono_set (linearSievePairKernel_integrable hu) _ (Filter.Eventually.of_forall (fun t (ht : t∈Set.Ioc u r) => ht.1))
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    exact kernel_nonneg (hu.trans ht.le)
  have hs : (∑p∈sievePrimeWindow P w z,g p*W p*f (Y/log p))=
      ∑p∈sievePrimeWindow P w z,g p*W p*linearSievePairKernel (Y/log p) := by
    apply sum_congr rfl; intro p hp
    obtain ⟨_,hwp,hpz⟩ := mem_filter.mp hp
    rw [hext _ (div_le_div_of_nonneg_left hY.le (Real.log_pos (hw.trans_le hwp)) (Real.log_le_log (by linarith) hpz.le))]
  change |(∑p∈sievePrimeWindow P w z,g p*W p*f (Y/log p))-W z/u*(∫t in Set.Icc u r,f t)|≤2*(η*W z)*linearSievePairKernel u at hq
  rw [hs] at hq
  have hmaj := add_le_add (mul_le_mul_of_nonneg_left hi (div_nonneg hze.le hup.le))
    (mul_le_mul_of_nonneg_left (kernel_bound hu) (by positivity : 0≤2*(η*W z)))
  apply (mul_le_mul_of_nonneg_left ((sub_le_iff_le_add'.mp (abs_le.mp hq).2).trans hmaj) (exp_pos 1).le).trans
  change _ ≤ W z*exp (-u)*(73/100+2*exp 1^2*η)
  change exp 1*(W z/u*(∫t in Set.Ioi u,linearSievePairKernel t)+2*(η*W z)*(exp 1*exp (-u)))≤_
  calc _ = W z/u*(exp 1*(∫t in Set.Ioi u,linearSievePairKernel t))+2*η*W z*exp 1^2*exp (-u) := by ring
       _ ≤ W z/u*(73/100*u*exp (-u))+2*η*W z*exp 1^2*exp (-u) :=
         add_le_add_left (mul_le_mul_of_nonneg_left (linearSieve_pair_integral_sharp (u:=u) hu) (div_nonneg hze.le hup.le)) _
       _ = _ := by field_simp [hup.ne'] <;> ring


private theorem clipped_prime_exponential {P : Finset ℕ} {g : ℕ → ℝ} {w b Y η : ℝ}
    (hw : 1<w) (hwb : w≤b) (hY : 0<Y) (hv : 1≤Y/log b) (hη : 0≤η) (hη' : η≤1)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w b η) :
    let v := Y/log b
    (∑p∈(sievePrimeWindow P w b).filter (linearSieveAdmits true Y),
      g p*sieveEulerBelow P g p*exp (-(Y/log p)))≤
        sieveEulerBelow P g b*exp (-max 3 v)*((1+η)/v+8*η) := by
  intro v
  let c := min b (exp (Y/3))
  let W := sieveEulerBelow P g
  have hb : 0<b := by linarith
  have hlb := Real.log_pos (hw.trans_le hwb)
  have hvp : 0<v := div_pos hY hlb
  have hW : 0<W b := euler_pos hg b
  have hset : (sievePrimeWindow P w b).filter (linearSieveAdmits true Y)=sievePrimeWindow P w c := by
    ext p
    simp only [sievePrimeWindow,mem_filter,c,lt_min_iff,linearSieveAdmits,reduceCtorEq,false_or]
    constructor
    · rintro ⟨⟨hP,hwp,hpb⟩,had⟩
      exact ⟨hP,hwp,hpb,(Real.log_lt_iff_lt_exp (by linarith : (0:ℝ)<p)).mp (by linarith)⟩
    · rintro ⟨hP,hwp,hpb,hpc⟩
      exact ⟨⟨hP,hwp,hpb⟩,by linarith [(Real.log_lt_iff_lt_exp (by linarith : (0:ℝ)<p)).mpr hpc]⟩
  rw [hset]
  by_cases hc : w≤c
  · let r := max 3 v
    have hrp : 0<r := by linarith [le_max_left (3:ℝ) v]
    have hlc := Real.log_pos (hw.trans_le hc)
    have hrc : Y/log c=r := by
      by_cases h : b≤exp (Y/3)
      · have hh : 3≤v := (le_div_iff₀ hlb).mpr (by linarith [(Real.log_le_iff_le_exp hb).mpr h])
        simp [c,min_eq_left h,r,max_eq_right hh,v]
      · have hh : v≤3 := (div_le_iff₀ hlb).mpr (by linarith [(Real.le_log_iff_exp_le hb).mpr (not_le.mp h).le])
        dsimp only [c,r]; rw [min_eq_right (not_le.mp h).le,Real.log_exp,max_eq_left hh]
        field_simp
    have hratio : log b/log c=r/v := by rw [←hrc]; dsimp [v]; field_simp
    have hcb : c≤b := min_le_left ..
    have h₁ := sieve_prime_exponential hw hc hY hη hg (H.restrict hcb)
    rw [hrc] at h₁
    have h₂ := (abs_le.mp (H b ⟨hwb,le_rfl⟩ c ⟨hc,hcb⟩)).2
    rw [hratio] at h₂
    have h₃ : W c≤W b*(r/v+η) := by change W c-W b*(r/v)≤η*W b at h₂; linarith
    have hrv : r/v≤3 := (div_le_iff₀ hvp).mpr (max_le (by dsimp only [v]; linarith) (by dsimp only [v]; linarith))
    have hvr : v≤r := le_max_right ..
    have hterm : (r/v+η)*(1/r+2*η)≤(1+η)/v+8*η := by
      have hx : (r/v)*(1/r)=1/v := by field_simp
      have h₄ := mul_le_mul_of_nonneg_right hrv (mul_nonneg (show (0:ℝ)≤2 by norm_num) hη)
      have h₅ := div_le_div_of_nonneg_left hη hvp hvr
      have h₆ := mul_le_mul_of_nonneg_left hη' hη
      nlinarith only [hx,h₄,h₅,h₆,show η*(1/r)=η/r by ring,show (1+η)/v=1/v+η/v by ring]
    apply h₁.trans
    change W c*exp (-r)*(1/r+2*η)≤W b*exp (-r)*((1+η)/v+8*η)
    calc _ ≤ (W b*(r/v+η))*exp (-r)*(1/r+2*η) := by gcongr
         _ = W b*exp (-r)*((r/v+η)*(1/r+2*η)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)
  · have empty : sievePrimeWindow P w c=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp
      obtain ⟨_,hwp,hpc⟩ := mem_filter.mp hp
      exact hc (hwp.trans hpc.le)
    rw [empty,sum_empty]
    exact mul_nonneg (mul_nonneg hW.le (exp_pos _).le) (by positivity)



private theorem shifted_clipped_prime {P : Finset ℕ} {g : ℕ → ℝ} {w b Y η : ℝ}
    (hw : 1<w) (hwb : w≤b) (hu : 2≤Y/log b) (hη : 0≤η) (hη' : η≤1)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w b η) :
    let t := Y/log b
    (∑p∈(sievePrimeWindow P w b).filter (linearSieveAdmits true (Y-log b)),
      g p*sieveEulerBelow P g p*exp (-((Y-log b-log p)/log p)))≤
        exp 1*sieveEulerBelow P g b*((1+η)*linearSievePairKernel t+8*η*exp 1*exp (-t)) := by
  intro t
  let W := sieveEulerBelow P g
  let S := (sievePrimeWindow P w b).filter (linearSieveAdmits true (Y-log b))
  have hlb := Real.log_pos (hw.trans_le hwb)
  have hY : 0<Y-log b := by linarith [(le_div_iff₀ hlb).mp hu]
  have hshift : (Y-log b)/log b=t-1 := by rw [sub_div,div_self hlb.ne']
  have hc := clipped_prime_exponential hw hwb hY (by rw [hshift]; dsimp [t]; linarith) hη hη' hg H
  dsimp only at hc
  rw [hshift] at hc
  have hs : (∑p∈S,g p*W p*exp (-((Y-log b-log p)/log p)))=
      exp 1*∑p∈S,g p*W p*exp (-((Y-log b)/log p)) := by
    rw [mul_sum]; apply sum_congr rfl; intro p hp
    have hlp := Real.log_pos (hw.trans_le (mem_filter.mp (mem_filter.mp hp).1).2.1)
    rw [sub_div (Y-log b),div_self hlp.ne',neg_sub,sub_eq_add_neg,Real.exp_add]; ring
  have hsub : exp (-(max 3 (t-1)))≤exp 1*exp (-t) := by
    rw [←Real.exp_add,Real.exp_le_exp]; linarith [le_max_right (3:ℝ) (t-1)]
  have hrem := mul_le_mul_of_nonneg_left hsub (mul_nonneg (show (0:ℝ)≤8 by norm_num) hη)
  change (∑p∈S,_)≤_
  rw [hs]
  apply (mul_le_mul_of_nonneg_left hc (exp_pos 1).le).trans
  change exp 1*(W b*exp (-(max 3 (t-1)))*((1+η)/(t-1)+8*η))≤_
  calc _ = exp 1*W b*((1+η)*linearSievePairKernel t+8*η*exp (-(max 3 (t-1)))) := by
          unfold linearSievePairKernel; ring
       _ ≤ exp 1*W b*((1+η)*linearSievePairKernel t+8*η*exp 1*exp (-t)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (exp_pos 1).le (euler_pos hg b).le)
          linarith only [hrem]

/-- Uniform contraction of the two successive prime choices allowed from a
lower node. The estimate includes every strictly decreasing admissible pair. -/
theorem linearSieve_prime_pair_contraction_sharp {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hu : 2≤Y/log z) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w z η) :
    (∑p∈sievePrimeWindow P w z,g p*
      ∑q∈(sievePrimeWindow P w p).filter (linearSieveAdmits true (Y-log p)),
        g q*sieveEulerBelow P g q*exp (-((Y-log p-log q)/log q)))≤
      (74/100:ℝ)*sieveEulerBelow P g z*exp (-(Y/log z)) := by
  let S := sievePrimeWindow P w z
  let W := sieveEulerBelow P g
  let u := Y/log z
  let t := fun p : ℕ => Y/log p
  have hE := (exp_pos 1).le
  have hE₂ : exp 1^2≤9 := by
    have hh : exp 1≤3 := by linarith [Real.exp_one_lt_d9]
    simpa only [show (9:ℝ)=3^2 by norm_num] using pow_le_pow_left₀ hE hh 2
  have hW := (euler_pos hg z).le
  have hη₁ : η≤1 := by linarith
  have hpair := sieve_prime_pair_kernel hw hwz hY hu hη hg H
  have hsingle := sieve_prime_exponential hw hwz hY hη hg H
  let A := ∑p∈S,g p*W p*linearSievePairKernel (t p)
  let B := ∑p∈S,g p*W p*exp (-(t p))
  have hiter : (∑p∈S,g p*
      ∑q∈(sievePrimeWindow P w p).filter (linearSieveAdmits true (Y-log p)),
        g q*W q*exp (-((Y-log p-log q)/log q)))≤
          (1+η)*(exp 1*A)+(8*η*exp 1^2)*B := by
    calc _ ≤ ∑p∈S,g p*(exp 1*W p*((1+η)*linearSievePairKernel (t p)+8*η*exp 1*exp (-(t p)))) := by
            apply sum_le_sum; intro p hp
            obtain ⟨hP,hwp,hpz⟩ := mem_filter.mp hp
            apply mul_le_mul_of_nonneg_left _ (hg p hP).1
            exact shifted_clipped_prime hw hwp (hu.trans (div_le_div_of_nonneg_left hY.le
              (Real.log_pos (hw.trans_le hwp)) (Real.log_le_log (by linarith) hpz.le))) hη hη₁ hg (H.restrict hpz.le)
         _ = _ := by
            dsimp only [A,B]; rw [←mul_assoc (1+η),mul_sum,mul_sum,←sum_add_distrib]
            apply sum_congr rfl; intro p _; ring
  change exp 1*A≤W z*exp (-u)*(73/100+2*exp 1^2*η) at hpair
  change B≤W z*exp (-u)*(1/u+2*η) at hsingle
  apply hiter.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hpair (by positivity)) (mul_le_mul_of_nonneg_left hsingle (by positivity))).trans
  have hup : 0<u := div_pos hY (Real.log_pos (hw.trans_le hwz))
  have hinv : 1/u≤1 := (div_le_iff₀ hup).mpr (by change 2≤u at hu; linarith)
  have hsmall : (1+η)*(73/100+2*exp 1^2*η)+(8*η*exp 1^2)*(1/u+2*η)≤74/100 := by
    calc _ ≤ (1+1/10000:ℝ)*(73/100+2*9*(1/10000))+(8*(1/10000)*9)*(1+2*(1/10000)) := by gcongr
         _ ≤ _ := by norm_num
  change _≤74/100*W z*exp (-u)
  convert mul_le_mul_of_nonneg_left hsmall (mul_nonneg hW (exp_pos (-u)).le) using 1 <;> ring


/-- Two successive prime choices contract the weighted remainder by a factor at most 19/20. -/
theorem linearSieve_prime_pair_contraction {P : Finset ℕ} {g : ℕ → ℝ} {w z Y η : ℝ}
    (hw : 1<w) (hwz : w≤z) (hY : 0<Y) (hu : 2≤Y/log z) (hη : 0≤η) (hη' : η≤1/10000)
    (hg : ∀p∈P,0≤g p ∧ g p<1) (H : SieveEulerApprox P g w z η) :
    (∑p∈sievePrimeWindow P w z,g p*
      ∑q∈(sievePrimeWindow P w p).filter (linearSieveAdmits true (Y-log p)),
        g q*sieveEulerBelow P g q*exp (-((Y-log p-log q)/log q)))≤
      (19/20:ℝ)*sieveEulerBelow P g z*exp (-(Y/log z)) := by
  apply (linearSieve_prime_pair_contraction_sharp hw hwz hY hu hη hη' hg H).trans
  have hW := (euler_pos hg z).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hW) (exp_pos _).le

end AnalyticNumberTheory.SieveMethods
