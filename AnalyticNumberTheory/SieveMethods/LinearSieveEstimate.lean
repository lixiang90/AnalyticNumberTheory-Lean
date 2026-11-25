import AnalyticNumberTheory.SieveMethods.LinearSieveComparison
import AnalyticNumberTheory.SieveMethods.LinearSieveEulerProducts

/-!
# A two-cutoff linear sieve estimate

The arithmetic remainder has coefficient one and strict level exp(Y). The
analytic error contains the Euler-product discrepancy, the short branches
and the geometrically summable deep branches.
-/
noncomputable section
open Set Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

private theorem window_eq_filter_below (P : Finset ℕ) (w z : ℝ) :
    sievePrimeWindow P w z=(sievePrimesBelow P z).filter (fun p : ℕ => w≤p) := by
  ext p; simp [sievePrimeWindow,sievePrimesBelow]; grind

theorem sieveBranchProduct_le_ratio {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀p∈P,0≤g p ∧ g p<1)
    {w z : ℝ} (hwz : w≤z) :
    sieveBranchProduct P g w z≤sieveEulerBelow P g w/sieveEulerBelow P g z := by
  rw [←sieveEulerBelow_window_ratio P (fun p hp => (hg p hp).2) hwz,sieveBranchProduct,window_eq_filter_below]
  apply prod_le_prod₀
  · intro p hp; linarith [(hg p (mem_filter.mp (mem_filter.mp hp).1).1).1]
  · intro p hp; have h := hg p (mem_filter.mp (mem_filter.mp hp).1).1
    rw [←one_div,le_div_iff₀ (sub_pos.mpr h.2)]; nlinarith only [sq_nonneg (g p)]

theorem sieveEulerBelow_antitone {P : Finset ℕ} {g : ℕ → ℝ} (hg : ∀p∈P,0≤g p ∧ g p<1) :
    Antitone (sieveEulerBelow P g) := by
  intro w z hwz
  have h := sieveBranchProduct_le_ratio hg hwz
  have hV : 1≤sieveBranchProduct P g w z := Finset.one_le_prod₀ (fun p hp => by linarith [(hg p (mem_filter.mp hp).1).1])
  exact (one_le_div (sieveEulerBelow_pos P (fun p hp => (hg p hp).2) z)).mp (hV.trans h)

private theorem sign_triangle (b : Bool) (a c d : ℝ) : linearSieveSign b (a-d)≤linearSieveSign b (a-c)+|c-d| := by
  cases b <;> simp only [linearSieveSign,Bool.false_eq_true,ite_false,ite_true] <;>
    linarith only [le_abs_self (c-d),neg_le_abs (c-d)]

/-- Finite two-cutoff sieve with the linear-sieve profiles and the ordinary
sum of the absolute arithmetic remainders up to level exp(Y). -/
theorem linearSieve_two_cutoff_sharp {K : ℝ} (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      ∀ {w z Y η : ℝ}, 2≤w → w≤z → 0<Y → 0≤η → η≤1/10000 →
        SieveEulerDimensionOne P s.density z K → SieveEulerApprox P s.density w z η →
        ∀ (m : ℕ) (b : Bool), (if b then (1:ℝ) else 2)≤Y/log z →
        let u := Y/log z
        let r := log z/log w
        let Q := K*r
        let V := sieveEulerBelow P s.density z
        linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-s.X*V*linearSieveProfile b u)≤
          s.X*V*(6*exp eulerMascheroniConstant*η*Q^2+
            C*((2*m:ℕ)*Q^2*exp (-(u*r/3^m))+2560*(74/100:ℝ)^m))+
            ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<exp Y),|s.rem d| := by
  obtain ⟨C,hC,hc⟩ := linearSieve_sifted_tree hK
  refine ⟨C,hC,?_⟩; intro s P hP hX w z Y η hw hwz hY hη hη' H HA m b hu u r Q V
  let g := s.density
  let W := sieveEulerBelow P g
  let G := fun b y => W w*linearSieveProfile b (y/log w)
  let n := (sievePrimeWindow P w z).card
  let T := linearSieveTree P g w G n b Y z
  let B := sieveBranchProduct P g w z
  let E := exp (-(u*r/3^m))
  let R := ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<exp Y),|s.rem d|
  have hg (p : ℕ) (hp : p∈P) : 0≤g p ∧ g p<1 := ⟨s.density_nonneg_of_prime (hP p hp),s.density_lt_one_of_prime (hP p hp)⟩
  have hW (a : ℝ) : 0<W a := sieveEulerBelow_pos P (fun p hp => (hg p hp).2) a
  have hw' : 1<w := by linarith
  have hzw : 2≤z := hw.trans hwz
  have hQ : 0≤Q := mul_nonneg (by linarith) (div_nonneg (log_pos (hw'.trans_le hwz)).le (log_pos hw').le)
  have hratio : W w/W z≤Q := H z ⟨hzw,le_rfl⟩ w ⟨hw,hwz⟩
  have hWw := (div_le_iff₀ (hW z)).mp hratio
  have hB : B≤Q := (sieveBranchProduct_le_ratio hg hwz).trans hratio
  have hWB : W w*B≤W z*Q^2 := (mul_le_mul hWw hB (sieveBranchProduct_nonneg (fun p hp => (hg p hp).1) w z) (mul_nonneg hQ (hW z).le)).trans_eq (by ring)
  have hH : SieveEulerDimensionOne P g w K := fun t ht => H t ⟨ht.1,ht.2.trans hwz⟩
  have hD (a : ℝ) (ha : a∈Set.Icc w z) (t : ℝ) (ht : t∈Set.Icc w a) :
      |W t-W a*(log a/log t)|≤η*W w :=
    (HA a ha t ht).trans (mul_le_mul_of_nonneg_left (sieveEulerBelow_antitone hg ha.1) hη)
  have ht := linearSieve_tree_comparison P g hw' (mul_nonneg hη (hW w).le) hg hD n b (le_refl _) ⟨hwz,le_rfl⟩ hY hu
  change |T-W z*linearSieveProfile b u|≤3*(2*exp eulerMascheroniConstant)*(η*W w)*B at ht
  have hc' := hc s P hP hX hw hH n b (d:=1) (Y:=Y) (z:=z) ⟨hwz,le_rfl⟩ hY hu le_rfl (L:=Y)
    ⟨one_dvd _,Nat.coprime_one_left _,by simp⟩
  have hS : sieveMultiple s.A 1=s.A := by ext p; simp [sieveMultiple]
  rw [hS,s.density_one,mul_one,linearSieveBudget_divisors hP] at hc'
  simp only [one_mul] at hc'
  have htail := linearSieve_terminal_sum_sharp hw' hwz hY hη hη' hg HA b hu m (n+1)
  have hExp : exp (-(Y/3^m/log w))=E := by
    dsimp only [E,r,u]; congr 2
    field_simp [(log_pos (hw'.trans_le hwz)).ne',(log_pos hw').ne'] <;> ring
  have hE : 0≤E := (exp_pos _).le
  have hunit : exp (-u)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hY.le (log_pos (hw'.trans_le hwz)).le))
  have hM : linearSieveTerminalMass P g w n b Y z≤
      W z*((2*m:ℕ)*Q^2*E+2560*(74/100:ℝ)^m) := by
    apply htail.trans
    simp only [linearSieveExpWeight,hExp]
    change (2*m:ℕ)*B*(W w*E)+2560*(74/100:ℝ)^m*(W z*exp (-u))≤_
    have h₁ := mul_le_mul_of_nonneg_right hWB (mul_nonneg (Nat.cast_nonneg (α:=ℝ) (2*m)) hE)
    have h₂ := mul_le_mul_of_nonneg_left hunit (mul_nonneg (by positivity : 0≤2560*(74/100:ℝ)^m) (hW z).le)
    nlinarith only [h₁,h₂]
  have ht' : |s.X*T-s.X*(W z*linearSieveProfile b u)|≤s.X*W z*(6*exp eulerMascheroniConstant*η*Q^2) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hX]
    apply mul_le_mul_of_nonneg_left ht hX |>.trans
    have h := mul_le_mul_of_nonneg_left hWB (mul_nonneg (mul_nonneg (mul_nonneg hX (by norm_num : (0:ℝ)≤6)) (exp_pos eulerMascheroniConstant).le) hη)
    nlinarith only [h]
  change linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-s.X*T)≤s.X*C*linearSieveTerminalMass P g w n b Y z+R at hc'
  change linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-s.X*W z*linearSieveProfile b u)≤_
  rw [mul_assoc s.X]
  apply (sign_triangle b _ (s.X*T) _).trans
  apply (add_le_add hc' ht').trans
  have h := mul_le_mul_of_nonneg_left hM (mul_nonneg hX hC.le)
  change _ ≤ s.X*W z*(6*exp eulerMascheroniConstant*η*Q^2+C*((2*m:ℕ)*Q^2*E+2560*(74/100:ℝ)^m))+R
  linarith only [h]

theorem linearSieve_two_cutoff {K : ℝ} (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) → 0≤s.X →
      ∀ {w z Y η : ℝ}, 2≤w → w≤z → 0<Y → 0≤η → η≤1/10000 →
        SieveEulerDimensionOne P s.density z K → SieveEulerApprox P s.density w z η →
        ∀ (m : ℕ) (b : Bool), (if b then (1:ℝ) else 2)≤Y/log z →
        let u := Y/log z
        let r := log z/log w
        let Q := K*r
        let V := sieveEulerBelow P s.density z
        linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-s.X*V*linearSieveProfile b u)≤
          s.X*V*(6*exp eulerMascheroniConstant*η*Q^2+
            C*((2*m:ℕ)*Q^2*exp (-(u*r/2^(2*m)))+2560*(19/20:ℝ)^m))+
            ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<exp Y),|s.rem d| := by
  obtain ⟨C,hC,H⟩ := linearSieve_two_cutoff_sharp hK
  refine ⟨C,hC,?_⟩
  intro s P hP hX w z Y η hw hwz hY hη hη' hdim happrox m b hu u r Q V
  have hV : 0≤V := (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le
  have hu' : 0≤u := div_nonneg hY.le (Real.log_nonneg (by linarith))
  have hr : 0≤r := div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by linarith))
  apply (H s P hP hX hw hwz hY hη hη' hdim happrox m b hu).trans
  change _ ≤ s.X*V*(6*exp eulerMascheroniConstant*η*Q^2+
    C*((2*m:ℕ)*Q^2*exp (-(u*r/2^(2*m)))+2560*(19/20:ℝ)^m))+_
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX hV)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg (α:=ℝ) (2*m)) (sq_nonneg Q))
    apply exp_le_exp.mpr; apply neg_le_neg
    apply div_le_div_of_nonneg_left (mul_nonneg hu' hr) (by positivity)
    simpa only [pow_mul] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) (by norm_num : (3:ℝ)≤2^2) m
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num : (74/100:ℝ)≤19/20) m) (by norm_num)

end AnalyticNumberTheory.SieveMethods
