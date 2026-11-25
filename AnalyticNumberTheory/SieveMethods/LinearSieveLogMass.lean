import AnalyticNumberTheory.SieveMethods.LinearSieveTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Abel estimates for the logarithmic prime mass

On the logarithmic scale the dimension-one sieve hypothesis compares the
mass g(p) log p with Lebesgue measure. The two error constants remain separate
when the mass is tested against the inverse first and second powers.
-/

noncomputable section
open Real MeasureTheory Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- Upper and lower discrepancies of the prime mass on half-open intervals. -/
def SieveLogMassBounds (P : Finset ℕ) (g : ℕ → ℝ) (w z L A : ℝ) : Prop :=
  ∀ u v : ℝ, w≤u → u≤v → v≤z →
    (∑ p∈P.filter (fun p : ℕ => u≤p ∧ (p:ℝ)<v), g p*Real.log p) - Real.log (v/u)
      ∈ Set.Icc (-L) A

private theorem log_cutoff_filter (P : Finset ℕ) (hp : ∀p∈P, 0<p) (l r : ℝ) :
    P.filter (fun p : ℕ => l≤log p ∧ log p<r) =
      P.filter (fun p : ℕ => exp l≤p ∧ (p:ℝ)<exp r) := by
  ext p
  by_cases h : p∈P
  · have hpos : (0:ℝ)<p := by exact_mod_cast hp p h
    simp only [Finset.mem_filter,Real.le_log_iff_exp_le hpos,Real.log_lt_iff_lt_exp hpos]
  · simp [h]

private theorem log_mass_closed {P : Finset ℕ} {g : ℕ → ℝ} {w z L A : ℝ}
    (hw : 1<w) (hz : w≤z) (hP : ∀p∈P, 1≤p) (hg : ∀p∈P, 0≤g p)
    (H : SieveLogMassBounds P g w z L A) {l r : ℝ} (hl : log w≤l) (hlr : l≤r) (hr : r≤log z) :
    let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
    (∑ p∈S.filter (fun p : ℕ => log p∈Set.Icc l r),g p*log p)-(r-l)∈Set.Icc (-L) (A+1) := by
  intro S
  let B (l r : ℝ) := P.filter (fun p : ℕ => l≤log p ∧ log p<r)
  have hwindow (u v : ℝ) (hu : log w≤u) (huv : u≤v) (hv : v≤log z) :
      (∑ p∈B u v,g p*log p)-(v-u)∈Set.Icc (-L) A := by
    have h := H (exp u) (exp v) ((Real.log_le_iff_le_exp (by linarith)).mp hu)
      (Real.exp_le_exp.mpr huv) ((Real.le_log_iff_exp_le (by linarith)).mp hv)
    rw [Real.log_div (exp_pos _).ne' (exp_pos _).ne',Real.log_exp,Real.log_exp] at h
    simpa only [B,log_cutoff_filter P hP] using h
  let U := S.filter (fun p : ℕ => log p∈Set.Icc l r)
  have hlo : B l r ⊆ U := by
    intro p hp
    obtain ⟨hp,hlp,hpr⟩ := Finset.mem_filter.mp hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hP p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp,
      (Real.log_le_log_iff (by linarith) hp0).mp (hl.trans hlp),
      (Real.log_lt_log_iff hp0 (by linarith)).mp (hpr.trans_le hr)⟩,hlp,hpr.le⟩
  let v := min (r+1) (log z)
  have hrv : r≤v := le_min (by linarith) hr
  have hhi : U ⊆ B l v := by
    intro p hp
    obtain ⟨hp,hlp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hpw,hpz⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hlp,lt_min (by linarith) (Real.log_lt_log (by linarith) hpz)⟩
  have hmass (p : ℕ) (hp : p∈P) : 0≤g p*log p :=
    mul_nonneg (hg p hp) (Real.log_nonneg (by exact_mod_cast hP p hp))
  have h₁ := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => g p*log p) hlo
    (fun p hp _ => hmass p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
  have h₂ := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => g p*log p) hhi
    (fun p hp _ => hmass p (Finset.mem_filter.mp hp).1)
  change _≤(∑ p∈U,g p*log p)-(r-l) ∧ (∑ p∈U,g p*log p)-(r-l)≤_
  constructor
  · linarith [(hwindow l r hl hlr hr).1]
  · linarith [(hwindow l v hl (hlr.trans hrv) (min_le_right ..)).2,
      show v≤r+1 from min_le_left ..]

/-- Partial summation against an inverse power on the logarithmic scale. -/
theorem sieve_mass_inverse_moment (j : ℕ) {P : Finset ℕ} {g : ℕ → ℝ} {w z L A : ℝ}
    (hw : 1<w) (hz : w≤z) (hP : ∀p∈P, 1≤p) (hg : ∀p∈P, 0≤g p)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    (∑ p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p*log p*(log p)⁻¹^j)-
      (∫ x in log w..log z, x⁻¹^j) ∈Set.Icc (-(L*(log w)⁻¹^j)) ((A+1)*(log w)⁻¹^j) := by
  let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  let a := log w
  let b := log z
  have ha : 0<a := log_pos hw
  have hab : a≤b := log_le_log (by linarith) hz
  let f (x : ℝ) := (max a x)⁻¹^j
  have hf : Continuous f := ((continuous_const.max continuous_id).inv₀ (fun x => (ha.trans_le (le_max_left ..)).ne')).pow j
  have hx (p : ℕ) (hp : p∈S) : log p∈Set.Icc a b := by
    obtain ⟨_,hpw,hpz⟩ := Finset.mem_filter.mp hp
    exact ⟨log_le_log (by linarith) hpw, log_le_log (by linarith) hpz.le⟩
  have he (x : ℝ) (h : x∈Set.Icc a b) : f x=x⁻¹^j := by simp [f,max_eq_right h.1]
  have hmono : AntitoneOn f (Set.Icc a b) := fun x hx y hy hxy => by
    rw [he x hx,he y hy]; exact pow_le_pow_left₀ (by positivity [ha.trans_le hy.1]) (inv_anti₀ (ha.trans_le hx.1) hxy) _
  have hres := finite_monotone_quadrature_one_sided S (fun p : ℕ => log p) (fun p => g p*log p)
    (c:=1) hL (by linarith : 0≤A+1) (pow_nonneg (inv_nonneg.mpr ha.le) j)
    (fun p hp => mul_nonneg (hg p (Finset.mem_filter.mp hp).1) (ha.le.trans (hx p hp).1)) hx f hf
    (fun x h => ⟨by rw [he _ h]; positivity [ha.trans_le h.1],by rw [he _ h]; exact pow_le_pow_left₀ (by positivity [ha.trans_le h.1]) (inv_anti₀ ha h.1) j⟩)
    (.inr hmono) (fun l r hl hlr hr => by simpa only [one_mul] using log_mass_closed hw hz hP hg H hl hlr hr)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,one_mul] at hres
  have hsum : (∑ p∈S,g p*log p*f (log p))=∑p∈S,g p*log p*(log p)⁻¹^j :=
    Finset.sum_congr rfl fun p hp => by rw [he _ (hx p hp)]
  rwa [hsum] at hres

/-- Inverse-logarithm partial summation with separate errors on the two sides. -/
theorem sieve_prime_mass_loglog {P : Finset ℕ} {g : ℕ → ℝ} {w z L A : ℝ}
    (hw : 1<w) (hz : w≤z) (hP : ∀p∈P, 1≤p) (hg : ∀p∈P, 0≤g p)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    (∑ p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p)-log (log z/log w)
      ∈Set.Icc (-(L/log w)) ((A+1)/log w) := by
  let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  have hres := sieve_mass_inverse_moment 1 hw hz hP hg hL hA H
  have hsum : (∑p∈S,g p*log p*(log p)⁻¹)=∑p∈S,g p := by
    apply Finset.sum_congr rfl; intro p hp
    rw [mul_assoc,mul_inv_cancel₀ (log_pos (hw.trans_le (Finset.mem_filter.mp hp).2.1)).ne',mul_one]
  simp only [pow_one,integral_inv_of_pos (log_pos hw) (log_pos (hw.trans_le hz))] at hres
  change (∑p∈S,_) - _ ∈ _ at hres
  simpa only [hsum,div_eq_mul_inv] using hres

/-- The quadratic logarithmic weight has an integrable tail, uniformly in the upper endpoint. -/
theorem sieve_prime_mass_invLog_le {P : Finset ℕ} {g : ℕ → ℝ} {w z L A : ℝ}
    (hw : 1<w) (hz : w≤z) (hP : ∀p∈P, 1≤p) (hg : ∀p∈P, 0≤g p)
    (hL : 0≤L) (hA : 0≤A) (H : SieveLogMassBounds P g w z L A) :
    (∑ p∈P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z),g p/log p) ≤
      (log w)⁻¹+(A+1)*(log w)⁻¹^2 := by
  let S := P.filter (fun p : ℕ => w≤p ∧ (p:ℝ)<z)
  have hres := (sieve_mass_inverse_moment 2 hw hz hP hg hL hA H).2
  have hsum : (∑p∈S,g p*log p*(log p)⁻¹^2)=∑p∈S,g p/log p := by
    apply Finset.sum_congr rfl; intro p hp
    field_simp [(log_pos (hw.trans_le (Finset.mem_filter.mp hp).2.1)).ne']
  have h₁ := log_pos hw
  have h₂ := log_pos (hw.trans_le hz)
  have hab := Real.log_le_log (by linarith : 0<w) hz
  have hI : (∫ x in log w..log z, x⁻¹^2)=(log w)⁻¹-(log z)⁻¹ := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=log w) (b:=log z) (f:=fun x : ℝ => -x⁻¹)
      (f':=fun x => x⁻¹^2) (fun x hx => by
        have hx0 : 0<x := h₁.trans_le ((Set.uIcc_of_le hab ▸ hx).1)
        convert (hasDerivAt_inv hx0.ne').neg using 1 <;> simp [inv_pow]) (by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_id.inv₀ (fun x hx => (h₁.trans_le ((Set.uIcc_of_le hab ▸ hx).1)).ne')).pow 2)
    linarith
  change (∑p∈S,_)-_≤_ at hres
  rw [hsum,hI] at hres
  linarith [inv_pos.mpr h₂]

/-- A single atom is controlled by the upper discrepancy on intervals of unit logarithmic length. -/
theorem sieve_atom_log_le {P : Finset ℕ} {g : ℕ → ℝ} {w z L A : ℝ}
    (hw : 1<w) (hz : w≤z) (hP : ∀p∈P, 1≤p) (hg : ∀p∈P, 0≤g p)
    (H : SieveLogMassBounds P g w z L A) {p : ℕ} (hp : p∈P) (hpw : w≤p) (hpz : (p:ℝ)<z) :
    g p*log p≤A+1 := by
  have hx : log w≤log p := log_le_log (by linarith) hpw
  have hy : log p≤log z := log_le_log (by linarith) hpz.le
  have h := (log_mass_closed hw hz hP hg H hx le_rfl hy).2
  simp only [sub_self,sub_zero] at h
  apply le_trans _ h
  apply Finset.single_le_sum (fun i hi => mul_nonneg (hg i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
    (log_nonneg (by exact_mod_cast hP i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)))
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp,hpw,hpz⟩,le_rfl,le_rfl⟩

end AnalyticNumberTheory.SieveMethods
