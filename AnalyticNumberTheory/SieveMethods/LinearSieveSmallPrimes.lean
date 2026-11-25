import AnalyticNumberTheory.SieveMethods.LinearSieveArithmetic

/-!
# The small-prime endpoint of the linear sieve

For large logarithmic level the fundamental lemma gives exponential accuracy.
At small level an upper sieve at a reduced cutoff controls the count; the
dimension-one estimate compares its Euler product to the required product.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The upper dimension-one ratio inequality at all subintervals. -/
def SieveEulerDimensionOne (P : Finset ℕ) (g : ℕ → ℝ) (w K : ℝ) : Prop :=
  ∀ b∈Set.Icc 2 w, ∀ a∈Set.Icc 2 b, sieveEulerBelow P g a/sieveEulerBelow P g b≤K*(log b/log a)

/-- The same arithmetic sequence, using the strict prime cutoff attached to P. -/
def SieveData.withPrimeSet (s : SieveData) {P : Finset ℕ} (hP : ∀p∈P,p.Prime) : SieveData :=
  { s with prodPrimes := sieveProductBelow P, prodPrimes_squarefree := sieveProductBelow_squarefree hP }

private theorem withPrimeSet_eulerProd (s : SieveData) {P : Finset ℕ} (hP : ∀p∈P,p.Prime) (w : ℝ) :
    (s.withPrimeSet hP).eulerProd w=sieveEulerBelow P s.density w := by
  change (∏p∈(sieveProductBelow P w).primeFactors, (1-s.density p))=_
  rw [sieveProductBelow_primeFactors hP]; rfl

theorem sieveEulerBelow_window_ratio (P : Finset ℕ) {g : ℕ → ℝ} (hg : ∀p∈P,g p<1) {a b : ℝ} (hab : a≤b) :
    (∏p∈(sievePrimesBelow P b).filter (fun p : ℕ => a≤p),(1-g p)⁻¹)=
      sieveEulerBelow P g a/sieveEulerBelow P g b := by
  let A := sievePrimesBelow P a
  let B := sievePrimesBelow P b
  have hsub : A⊆B := fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans_le hab⟩
  have he : B.filter (fun p : ℕ => a≤p)=B\A := by
    ext p; simp [A,B,sievePrimesBelow]; grind
  change (∏p∈B.filter (fun p : ℕ => a≤p),(1-g p)⁻¹)=(∏p∈A,(1-g p))/(∏p∈B,(1-g p))
  rw [he,Finset.prod_inv_distrib,←Finset.prod_sdiff hsub (f:=fun p : ℕ => 1-g p)]
  have hA : (∏p∈A,(1-g p))≠0 := (sieveEulerBelow_pos P hg a).ne'
  have hAB : (∏p∈B\A,(1-g p))≠0 := (prod_pos (fun p hp => sub_pos.mpr (hg p (mem_filter.mp (mem_sdiff.mp hp).1).1))).ne'
  field_simp

private theorem small_dimension (s : SieveData) {P : Finset ℕ} (hP : ∀p∈P,p.Prime)
    {w b K : ℝ} (hb : b∈Set.Icc 2 w) (h : SieveEulerDimensionOne P s.density w K) :
    (s.withPrimeSet hP).hasDimensionAt b K 1 := by
  intro a ha hab
  change (∏p∈(sieveProductBelow P b).primeFactors.filter (fun p : ℕ => a≤p),(1-s.density p)⁻¹)≤_
  rw [Real.rpow_one,sieveProductBelow_primeFactors hP,sieveEulerBelow_window_ratio P (fun p hp => s.density_lt_one_of_prime (hP p hp)) hab]
  exact h b hb a ⟨ha,hab⟩

private theorem profile_exp_error :
    ∃ C : ℝ, 0<C ∧ ∀b u,1≤u → |linearSieveProfile b u-1|≤C*exp (-u) := by
  let C := 2*exp eulerMascheroniConstant*exp 2*exp (exp 1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro b u hu
  let n := ⌊u-1⌋₊
  have hn : (n:ℝ)≤u-1 := Nat.floor_le (by linarith)
  have hn' : u-1<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hf : 0<(n.factorial:ℝ) := by positivity
  have h := linearSieve_factorial_error b n (u:=u) (by linarith)
  rw [linearSieveProfile,max_eq_right hu]
  apply h.trans
  have he := Real.pow_div_factorial_le_exp (exp 1) (exp_pos 1).le n
  have he' : exp u≤exp 2*(exp 1)^n := by
    rw [←Real.exp_nat_mul,←Real.exp_add]; apply exp_le_exp.mpr; push_cast; linarith
  have hu' : 0<u := by linarith
  have hdiv : exp u/(n.factorial:ℝ)≤exp 2*exp (exp 1) := by
    apply (div_le_div_of_nonneg_right he' hf.le).trans
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left he (exp_pos _).le
  rw [Real.exp_neg,←div_eq_mul_inv,div_le_div_iff₀ (mul_pos hf hu') (exp_pos u)]
  have h₁ := mul_le_mul_of_nonneg_left ((div_le_iff₀ hf).mp hdiv)
    (mul_nonneg (show (0:ℝ)≤2 by norm_num) (exp_pos eulerMascheroniConstant).le)
  have h₂ := le_mul_of_one_le_right (a:=C*(n.factorial:ℝ)) (by dsimp [C]; positivity) hu
  dsimp only [C] at h₂ ⊢; linarith only [h₁,h₂]


/-- Absolute small-prime approximation, with a single remainder sum of strict
level exp(Y), uniformly down to Y = log(w). -/
theorem linearSieve_small_prime_estimate {K : ℝ} (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      ∀ {w Y : ℝ}, 2≤w → log w≤Y → SieveEulerDimensionOne P s.density w K →
      ∀ b, |(siftedCountOf s.A (sieveProductBelow P w):ℝ)-
        s.X*sieveEulerBelow P s.density w*linearSieveProfile b (Y/log w)|≤
        C*s.X*sieveEulerBelow P s.density w*exp (-(Y/log w))+
          ∑e∈(sieveProductBelow P w).divisors.filter (fun e : ℕ => (e:ℝ)<exp Y),|s.rem e| := by
  obtain ⟨V,hfund⟩ := siftedCount_fundamental_lemma hK (show (0:ℝ)≤1 by norm_num)
  obtain ⟨C₀,hC₀,hprofile⟩ := profile_exp_error
  let U := max V (exp 2)
  let B := (1+2*K)*K*U+1
  let C := B*exp U+2*K
  have hKU : 1≤U := (one_le_exp (by norm_num : (0:ℝ)≤2)).trans (le_max_right ..)
  have hUp : 0<U := zero_lt_one.trans_le hKU
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hB : 1≤B := by dsimp only [B]; have := mul_nonneg (mul_nonneg (by linarith : 0≤1+2*K) hKp.le) hUp.le; linarith
  have hC : 0<C := by dsimp only [C]; positivity [zero_lt_one.trans_le hB]
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  intro s P hP hX w Y hw hlev hdim b
  let D := sieveProductBelow P
  let W := sieveEulerBelow P s.density
  let S := fun t : ℝ => (siftedCountOf s.A (D t):ℝ)
  let R := fun t : ℝ => ∑e∈(D t).divisors.filter (fun e : ℕ => (e:ℝ)<exp Y),|s.rem e|
  let v := Y/log w
  have hWp (t : ℝ) : 0<W t := sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) t
  have hlw := log_pos (show 1<w by linarith)
  have hY := hlw.trans_le hlev
  have hv : 1≤v := (one_le_div hlw).mpr hlev
  have hR (t : ℝ) : 0≤R t := sum_nonneg (fun _ _ => abs_nonneg _)
  have hS (t : ℝ) : 0≤S t := Nat.cast_nonneg _
  have hXW := mul_nonneg hX (hWp w).le
  have hdvd {a t : ℝ} (hat : a≤t) : D a∣D t :=
    Finset.prod_dvd_prod_of_subset _ _ _ (fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans_le hat⟩)
  have hRm {a t : ℝ} (hat : a≤t) : R a≤R t := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => abs_nonneg (s.rem p))
    intro e he; obtain ⟨hd,hy⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans (hdvd hat),(sieveProductBelow_squarefree hP t).ne_zero⟩,hy⟩
  have hSm {a t : ℝ} (hat : a≤t) : S t≤S a := by dsimp only [S]; exact_mod_cast siftedCountOf_le_of_dvd (A:=s.A) (hdvd hat)
  have hF {a t : ℝ} (ha : a∈Set.Icc 2 w) (ht : V≤t) (htY : t*log a=Y) :
      |S a-s.X*W a|≤s.X*(2*K*W a*exp (-(t/2)*log t))+R a := by
    have hp (p : ℕ) (hp : p∈((s.withPrimeSet hP).prodPrimes a).primeFactors) : (p:ℝ)≤a := by
      change p∈(sieveProductBelow P a).primeFactors at hp
      rw [sieveProductBelow_primeFactors hP] at hp; exact (mem_filter.mp hp).2.le
    have h := hfund ht ha.1 (s.withPrimeSet hP) hX hp (small_dimension s hP ha hdim)
    have hpow : a^t=exp Y := by rw [Real.rpow_def_of_pos (by linarith [ha.1]),mul_comm,htY]
    rw [withPrimeSet_eulerProd,hpow] at h
    exact h
  have hvY : v*log w=Y := div_mul_cancel₀ _ hlw.ne'
  have herr : |S w-s.X*W w|≤C*(s.X*W w)*exp (-v)+R w := by
    by_cases hl : U≤v
    · have hlog : 2≤log v := (Real.le_log_iff_exp_le (hUp.trans_le hl)).mpr ((le_max_right ..).trans hl)
      have he : exp (-(v/2)*log v)≤exp (-v) := exp_le_exp.mpr (by nlinarith only [mul_nonneg (show 0≤v by linarith) (sub_nonneg.mpr hlog)])
      have h := hF (a:=w) ⟨hw,le_rfl⟩ ((le_max_left ..).trans hl) hvY
      apply h.trans; apply add_le_add_left
      calc s.X*(2*K*W w*exp (-(v/2)*log v))=(2*K)*(s.X*W w)*exp (-(v/2)*log v) := by ring
           _ ≤ C*(s.X*W w)*exp (-v) := by
             gcongr; dsimp [C]; linarith [mul_nonneg (show 0≤B by linarith) (exp_pos U).le]
    · have hm : v≤U := (not_le.mp hl).le
      let a := max 2 (exp (Y/U))
      have haw : a≤w := max_le hw ((Real.le_log_iff_exp_le (by linarith)).mp
        ((div_le_iff₀ hUp).mpr (by linarith [(div_le_iff₀ hlw).mp hm])))
      have ha : 2≤a := le_max_left ..
      have hla := log_pos (show 1<a by linarith)
      have hlog : log w/log a≤U := (div_le_iff₀ hla).mpr (by
        have h := (Real.le_log_iff_exp_le (by linarith : 0<a)).mpr (le_max_right 2 (exp (Y/U)))
        linarith [(div_le_iff₀ hUp).mp h])
      have hWa : W a≤K*U*W w := ((div_le_iff₀ (hWp w)).mp (hdim w ⟨hw,le_rfl⟩ a ⟨ha,haw⟩)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hKp.le) (hWp w).le)
      have hcount : S a≤(1+2*K)*(s.X*W a)+R a := by
        by_cases hc : 2≤exp (Y/U)
        · have halog : U*log a=Y := by rw [show a=exp (Y/U) from max_eq_right hc,log_exp]; field_simp
          have h := (abs_le.mp (hF ⟨ha,haw⟩ (le_max_left ..) halog)).2
          have hexp : exp (-(U/2)*log U)≤1 := Real.exp_le_one_iff.mpr (by
            have := log_nonneg hKU; nlinarith only [mul_nonneg hUp.le this])
          have hh := mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hKp.le) (hWp a).le) hX)
          linarith only [h,hh]
        · have ha₂ : a=2 := max_eq_left (not_le.mp hc).le
          have hset : sievePrimesBelow P a=∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp
            obtain ⟨hp,hh⟩ := mem_filter.mp hp
            rw [ha₂] at hh; exact (not_lt.mpr (show (2:ℝ)≤p by exact_mod_cast (hP p hp).two_le)) hh
          have hDa : D a=1 := by simp only [D,sieveProductBelow,hset,Finset.prod_empty]
          have hWa' : W a=1 := by change (∏p∈sievePrimesBelow P a,(1-s.density p))=1; rw [hset,Finset.prod_empty]
          have hRa : R a=|s.rem 1| := by dsimp only [R]; rw [hDa,Nat.divisors_one,Finset.filter_singleton]; simp [Real.one_lt_exp_iff.mpr hY]
          have hSa : S a=s.X+s.rem 1 := by
            change (siftedCountOf s.A (D a):ℝ)=_
            rw [hDa,siftedCountOf_one]
            simpa [sieveMultiple] using s.card_sieveMultiple_eq 1
          rw [hRa,hSa,hWa',mul_one]
          nlinarith only [le_abs_self (s.rem 1),mul_nonneg hKp.le hX]
      have hraw : |S w-s.X*W w|≤B*(s.X*W w)+R w := by
        have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWa hX) (show 0≤1+2*K by linarith)
        rw [abs_le]; constructor
        · nlinarith only [hS w,hR w,mul_le_mul_of_nonneg_right hB hXW]
        · dsimp only [B]; nlinarith only [hSm haw,hcount,hh,hRm haw,hXW]
      apply hraw.trans; apply add_le_add_left
      rw [mul_right_comm C,←mul_assoc B _]
      have hh : B≤C*exp (-v) := by
        have he : 1≤exp U*exp (-v) := by rw [←Real.exp_add]; apply one_le_exp; linarith
        dsimp only [C]; nlinarith only [mul_le_mul_of_nonneg_left he (show 0≤B by linarith),mul_nonneg hKp.le (exp_pos (-v)).le]
      nlinarith only [mul_le_mul_of_nonneg_right hh hXW]
  have hp := mul_le_mul_of_nonneg_left (hprofile b v hv) hXW
  change |S w-s.X*W w*linearSieveProfile b v|≤(C+C₀)*s.X*W w*exp (-v)+R w
  have he : S w-s.X*W w*linearSieveProfile b v=(S w-s.X*W w)-(s.X*W w)*(linearSieveProfile b v-1) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hXW]; linarith only [herr,hp]


end AnalyticNumberTheory.SieveMethods
