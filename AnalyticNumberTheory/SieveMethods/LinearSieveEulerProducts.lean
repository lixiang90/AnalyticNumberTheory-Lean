import AnalyticNumberTheory.SieveMethods.LinearSieveLogMass

/-!
# Euler product ratios for the dimension-one linear sieve

Partial summation and the convergence of the quadratic logarithmic weight
compare the sieve product to the quotient of logarithms. The upper estimate
depends only on the upper mass discrepancy and the maximum local density.
-/

noncomputable section
open Real Finset
namespace AnalyticNumberTheory.SieveMethods

private theorem log_inverse_factor {x B : ℝ} (hx : 0≤x) (hB : 0<B) (h : x≤1-1/B) :
    0≤ -log (1-x)-x ∧ -log (1-x)-x ≤ B*x^2 := by
  have h₁ : 0<1-x := by linarith [one_div_pos.mpr hB]
  have h₂ := Real.log_le_sub_one_of_pos h₁
  have h₃ := Real.log_le_sub_one_of_pos (inv_pos.mpr h₁)
  rw [Real.log_inv] at h₃
  refine ⟨by linarith,?_⟩
  have hi : (1-x)⁻¹≤B := (inv_le_comm₀ h₁ hB).mpr (by linarith [show B⁻¹=1/B from (one_div B).symm])
  have he : (1-x)⁻¹-1-x=x^2*(1-x)⁻¹ := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg x)]

/-- The logarithm of a ratio of finite sieve products is the sum over the intervening primes. -/
theorem log_sieveEulerBelow_ratio (P : Finset ℕ) (g : ℕ → ℝ) (hg : ∀p∈P, g p<1)
    {w z : ℝ} (hwz : w≤z) :
    log (sieveEulerBelow P g w / sieveEulerBelow P g z) =
      ∑p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z), -log (1-g p) := by
  let S := P.filter (fun p : ℕ => (p:ℝ)<w)
  let T := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  have he : P.filter (fun p : ℕ => (p:ℝ)<z)=S∪T := by
    ext p; simp only [S,T,mem_filter,mem_union]; grind
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hp h
    exact (not_le.mpr (mem_filter.mp hp).2) (mem_filter.mp h).2.1
  have hh (p : ℕ) (hp : p∈P) : (1-g p)≠0 := (sub_pos.mpr (hg p hp)).ne'
  rw [log_div (sieveEulerBelow_pos P hg w).ne' (sieveEulerBelow_pos P hg z).ne']
  simp only [sieveEulerBelow,log_prod (fun p hp => hh p (mem_filter.mp hp).1)]
  rw [he,Finset.sum_union hd,Finset.sum_neg_distrib]
  change (∑ p∈S,_)-((∑p∈S,_)+_) = _
  ring

/-- Upper constant in the comparison of the logarithms of the sieve products. -/
def linearSieveEulerConstant (A B : ℝ) := (A+1)+B*(A+1)*(1+2*(A+1))

private theorem half_le_log_of_two_le {w : ℝ} (hw : 2≤w) : 1/2≤log w := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  rw [Real.log_inv] at h
  have h' := Real.log_le_log (by norm_num : (0:ℝ)<2) hw
  norm_num at h
  linarith

/-- A lower prime-mass discrepancy L costs L/log(w) in the logarithm of the product;
the upper discrepancy contributes independently to the upper bound. -/
theorem sieveEulerBelow_log_ratio_bounds {P : Finset ℕ} {g : ℕ → ℝ} {w z L A B : ℝ}
    (hw : 2≤w) (hz : w≤z) (hP : ∀p∈P, 1≤p)
    (hB : 0<B) (hg : ∀p∈P, 0≤g p ∧ g p≤1-1/B)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    log (sieveEulerBelow P g w / sieveEulerBelow P g z)-log (log z/log w)
      ∈Set.Icc (-(L/log w)) (linearSieveEulerConstant A B/log w) := by
  let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  have hw1 : 1<w := by linarith
  have ha := Real.log_pos hw1
  have hhalf := half_le_log_of_two_le hw
  have hlt (p : ℕ) (hp : p∈P) : g p<1 := by linarith [(hg p hp).2,one_div_pos.mpr hB]
  have hlog := sieve_prime_mass_loglog hw1 hz hP (fun p hp => (hg p hp).1) hL hA H
  have hsum := sieve_prime_mass_invLog_le hw1 hz hP (fun p hp => (hg p hp).1) hL hA H
  have hrem (p : ℕ) (hp : p∈S) : -log (1-g p)-g p∈Set.Icc 0 (B*(A+1)*(g p/log p)) := by
    obtain ⟨hpP,hpw,hpz⟩ := mem_filter.mp hp
    have hx := log_inverse_factor (hg p hpP).1 hB (hg p hpP).2
    have hp0 := log_pos (hw1.trans_le hpw)
    have h₁ := (le_div_iff₀ hp0).mpr (sieve_atom_log_le hw1 hz hP (fun r hr => (hg r hr).1) H hpP hpw hpz)
    refine ⟨hx.1,hx.2.trans ?_⟩
    have h₂ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hB.le (hg p hpP).1)
    calc
      _ = (B*g p)*g p := by ring
      _ ≤ _ := h₂
      _ = _ := by ring
  have h₁ := Finset.sum_nonneg (s:=S) fun p hp => (hrem p hp).1
  have h₂ := Finset.sum_le_sum (s:=S) fun p hp => (hrem p hp).2
  rw [Finset.sum_sub_distrib] at h₁ h₂
  rw [← Finset.mul_sum] at h₂
  rw [log_sieveEulerBelow_ratio P g hlt hz]
  change _≤(∑p∈S,-log (1-g p))-_ ∧ (∑p∈S,-log (1-g p))-_≤_
  change _≤(∑p∈S,g p)-_ ∧ _≤_ at hlog
  constructor
  · linarith [hlog.1]
  · have hinv : (log w)⁻¹≤2 := (inv_le_comm₀ ha (by norm_num : (0:ℝ)<2)).mpr (by linarith)
    have hmass : (∑p∈S,g p/log p)≤(1+2*(A+1))*(log w)⁻¹ := hsum.trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hinv (mul_nonneg (by linarith : 0≤A+1) (inv_nonneg.mpr ha.le))])
    have HH := mul_le_mul_of_nonneg_left hmass (show 0≤B*(A+1) by positivity)
    dsimp only [linearSieveEulerConstant]
    simp only [div_eq_mul_inv] at *
    nlinarith only [h₂,HH,hlog.2]

/-- Restriction of the density hypothesis to a smaller prime interval. -/
theorem SieveLogMassBounds.mono_interval {P : Finset ℕ} {g : ℕ → ℝ} {w z w' z' L A : ℝ}
    (H : SieveLogMassBounds P g w z L A) (hw : w≤w') (hz : z'≤z) :
    SieveLogMassBounds P g w' z' L A :=
  fun u v hu huv hv => H u v (hw.trans hu) huv (hv.trans hz)

private theorem norm_exp_perturbation {x u : ℝ} (hu : 0≤u) (hxu : x≤u) :
    |exp x-1|≤exp u*|x| := by
  have h1 := Real.add_one_le_exp x
  have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at h2
  rcases le_or_gt 0 x with h|h
  · rw [abs_of_nonneg h,abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxu) h]
  · rw [abs_of_neg h,abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr h.le])]
    have hmul := mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.mpr hu) (neg_nonneg.mpr h.le)
    linarith

/-- The upper Euler-product bound uses only the upper mass discrepancy through
its constant. The absolute comparison retains the lower discrepancy linearly. -/
theorem sieveEulerBelow_ratio_comparison {P : Finset ℕ} {g : ℕ → ℝ} {w z L A B : ℝ}
    (hw : 2≤w) (hz : w≤z) (hP : ∀p∈P, 1≤p)
    (hB : 0<B) (hg : ∀p∈P, 0≤g p ∧ g p≤1-1/B)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    let K := linearSieveEulerConstant A B
    sieveEulerBelow P g w / sieveEulerBelow P g z ≤ exp (2*K)*(log z/log w) ∧
    |sieveEulerBelow P g w-sieveEulerBelow P g z*(log z/log w)| ≤
      exp (2*K)*(L+K)*sieveEulerBelow P g z*log z/(log w)^2 := by
  intro K
  let V := sieveEulerBelow P g
  let a := log w
  let b := log z
  let E := log (V w/V z)-log (b/a)
  have hlt (p : ℕ) (hp : p∈P) : g p<1 := by linarith [(hg p hp).2,one_div_pos.mpr hB]
  have hV (t : ℝ) : 0<V t := sieveEulerBelow_pos P hlt t
  have ha : 0<a := log_pos (by linarith)
  have hb : 0<b := log_pos (by linarith)
  have hK : 0≤K := by dsimp [K,linearSieveEulerConstant]; positivity
  have hE : E∈Set.Icc (-(L/a)) (K/a) := sieveEulerBelow_log_ratio_bounds hw hz hP hB hg hL hA H
  have hupper : E≤2*K := hE.2.trans ((div_le_iff₀ ha).mpr (by
    have HH : 1/2≤a := half_le_log_of_two_le hw
    nlinarith only [mul_le_mul_of_nonneg_right HH hK]))
  have hnorm : |E|≤(L+K)/a := abs_le.mpr ⟨by rw [add_div]; linarith [hE.1,div_nonneg hK ha.le],
    by rw [add_div]; linarith [hE.2,div_nonneg hL ha.le]⟩
  have he : exp E=(V w/V z)/(b/a) := by
    dsimp [E]; rw [Real.exp_sub,Real.exp_log (div_pos (hV _) (hV _)),Real.exp_log (div_pos hb ha)]
  constructor
  · have HH := Real.exp_le_exp.mpr hupper
    rw [he,div_le_iff₀ (div_pos hb ha)] at HH
    exact HH
  · have HH := (norm_exp_perturbation (by linarith : 0≤2*K) hupper).trans (mul_le_mul_of_nonneg_left hnorm (exp_pos _).le)
    have hs : V w-V z*(b/a) = (exp E-1)*(V z*(b/a)) := by rw [he]; field_simp [(hV z).ne',ha.ne',hb.ne']
    change |V w-V z*(b/a)|≤_
    rw [hs,abs_mul,abs_of_pos (mul_pos (hV _) (div_pos hb ha))]
    apply (mul_le_mul_of_nonneg_right HH (mul_nonneg (hV _).le (div_nonneg hb.le ha.le))).trans_eq
    change _ = exp (2*K)*(L+K)*V z*b/a^2
    ring

/-- On a whole window the absolute error is controlled by its smallest logarithm. -/
theorem sieveEulerBelow_uniform_comparison {P : Finset ℕ} {g : ℕ → ℝ} {w z L A B : ℝ}
    (hw : 2≤w) (hz : w≤z) (hP : ∀p∈P, 1≤p)
    (hB : 0<B) (hg : ∀p∈P, 0≤g p ∧ g p≤1-1/B)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    let K := linearSieveEulerConstant A B
    ∀ t∈Set.Icc w z, |sieveEulerBelow P g t-sieveEulerBelow P g z*(log z/log t)|≤
      exp (2*K)*(L+K)*sieveEulerBelow P g z*log z/(log w)^2 := by
  intro K t ht
  have Ht := (sieveEulerBelow_ratio_comparison (hw.trans ht.1) ht.2 hP hB hg hL hA (H.mono_interval ht.1 le_rfl)).2
  apply Ht.trans
  have hV := sieveEulerBelow_pos P (g:=g) (fun p hp => by linarith [(hg p hp).2,one_div_pos.mpr hB]) z
  have hK : 0≤K := by dsimp [K,linearSieveEulerConstant]; positivity
  change exp (2*K)*(L+K)*sieveEulerBelow P g z*log z/(log t)^2 ≤ _
  apply div_le_div_of_nonneg_left (by positivity [log_nonneg (by linarith : 1≤z)]) (sq_pos_of_pos (log_pos (by linarith)))
  exact pow_le_pow_left₀ (log_nonneg (by linarith)) (log_le_log (by linarith) ht.1) _

end AnalyticNumberTheory.SieveMethods
