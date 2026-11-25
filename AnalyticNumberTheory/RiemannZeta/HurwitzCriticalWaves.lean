import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalModel
import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalDiagonal
import AnalyticNumberTheory.AnalyticTools.MovingPolynomialEnergy

/-!
# Direct and reciprocal waves in the shifted zeta polynomial

The direct frequencies are m+a, and the reciprocal frequencies are m+1.
The squared amplitudes produce the shifted and ordinary harmonic sums.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- A false index labels a direct term; a true index labels a reciprocal term. -/
def hurwitzWaveFrequency (a : ℝ) (i : Bool×ℕ) : ℝ := i.2+if i.1 then 1 else a

def hurwitzWavePhase (a : ℝ) (i : Bool×ℕ) (t : ℝ) : ℝ :=
  let r := hurwitzWaveFrequency a i
  if i.1 then -(hardyPhase t-t*Real.log r)-2*Real.pi*r*a else hardyPhase t-t*Real.log r

def hurwitzWave (a : ℝ) (i : Bool×ℕ) (t : ℝ) : ℂ :=
  (((Real.sqrt (hurwitzWaveFrequency a i))⁻¹:ℝ):ℂ)*Complex.exp ((hurwitzWavePhase a i t:ℂ)*I)

def hurwitzWaveEntry (a : ℝ) (i : Bool×ℕ) := 2*Real.pi*(hurwitzWaveFrequency a i)^2

def hurwitzWaveIndices (N : ℕ) : Finset (Bool×ℕ) := (Finset.univ : Finset Bool) ×ˢ (Finset.range N : Finset ℕ)

def hurwitzWaveSum (a : ℝ) (N : ℕ) (t : ℝ) :=
  ∑i∈hurwitzWaveIndices N,enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t

theorem hurwitzWaveFrequency_pos {a : ℝ} (ha : 0<a) (i : Bool×ℕ) : 0<hurwitzWaveFrequency a i := by
  obtain ⟨b,n⟩ := i;cases b <;>simp [hurwitzWaveFrequency] <;>positivity

theorem continuous_hurwitzWave (a : ℝ) (i : Bool×ℕ) : Continuous (hurwitzWave a i) := by
  have h : Continuous hardyPhase := (((Real.continuous_mul_log.sub (continuous_const.mul continuous_id)).div_const 2).sub continuous_const)
  unfold hurwitzWave hurwitzWavePhase;split_ifs <;>fun_prop

theorem norm_hurwitzWave (a : ℝ) (i : Bool×ℕ) (t : ℝ) :
    ‖hurwitzWave a i t‖=(Real.sqrt (hurwitzWaveFrequency a i))⁻¹ := by
  rw [hurwitzWave,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),Complex.norm_exp_ofReal_mul_I,mul_one]

theorem hurwitzWaveEntry_le_iff {a t : ℝ} (ha : 0<a) (ht : 0≤t) (i : Bool×ℕ) :
    hurwitzWaveEntry a i≤t ↔ hurwitzWaveFrequency a i≤Real.sqrt (t/(2*Real.pi)) := by
  rw [Real.le_sqrt (hurwitzWaveFrequency_pos ha i).le (by positivity),le_div_iff₀ (by positivity : 0<2*Real.pi),mul_comm]
  rfl

private theorem sum_wave_cutoff {E : Type*} [AddCommMonoid E] (p : Bool×ℕ→E)
    {a t : ℝ} (ha : a∈Ioc (0:ℝ) 1) (ht : 0≤t)
    (hx : 1≤Real.sqrt (t/(2*Real.pi))) {N : ℕ} (hN : ⌊Real.sqrt (t/(2*Real.pi))⌋₊+1≤N) :
    let x := Real.sqrt (t/(2*Real.pi))
    (∑i∈hurwitzWaveIndices N,if hurwitzWaveEntry a i≤t then p i else 0)=
      (∑m∈range (⌊x-a⌋₊+1),p (false,m))+(∑m∈range ⌊x⌋₊,p (true,m)) := by
  intro x
  change ⌊x⌋₊+1≤N at hN
  rw [hurwitzWaveIndices,Finset.sum_product (Finset.univ : Finset Bool) (Finset.range N) (fun i => if hurwitzWaveEntry a i≤t then p i else 0),Fintype.sum_bool]
  have hD : ((range N).filter (fun m => hurwitzWaveEntry a (false,m)≤t))=range (⌊x-a⌋₊+1) := by
    ext m
    simp only [mem_filter,Finset.mem_range,hurwitzWaveEntry_le_iff ha.1 ht,hurwitzWaveFrequency,Bool.false_eq_true,ite_false]
    have hf := Nat.le_floor_iff (n:=m) (show 0≤x-a by linarith [ha.2])
    have h := Nat.floor_mono (show x-a≤x by linarith [ha.1])
    change (m<N ∧ (m:ℝ)+a≤x) ↔ m<⌊x-a⌋₊+1
    constructor
    · intro hm;have h₀ : m≤⌊x-a⌋₊ := hf.mpr (by linarith [hm.2]);omega
    · intro hm;have h₁ : m≤⌊x-a⌋₊ := by omega
      have h₂ := hf.mp h₁;exact ⟨by omega,by linarith⟩
  have hU : ((range N).filter (fun m => hurwitzWaveEntry a (true,m)≤t))=range ⌊x⌋₊ := by
    ext m
    simp only [mem_filter,Finset.mem_range,hurwitzWaveEntry_le_iff ha.1 ht,hurwitzWaveFrequency,ite_true]
    change (m<N ∧ (m:ℝ)+1≤x) ↔ m<⌊x⌋₊
    have hf : m+1≤⌊x⌋₊ ↔ (m:ℝ)+1≤x := by rw [Nat.le_floor_iff (by linarith : 0≤x)];norm_cast
    rw [←hf];omega
  simp_rw [←sum_filter,hD,hU]
  apply add_comm

/-- The two elementary wave families recover the original rotated
Dirichlet polynomials, including the exact entry time of every term. -/
theorem hurwitzWaveSum_eq {a t : ℝ} (ha : a∈Ioc (0:ℝ) 1) (ht : 0≤t)
    (hx : 1≤Real.sqrt (t/(2*Real.pi))) {N : ℕ} (hN : ⌊Real.sqrt (t/(2*Real.pi))⌋₊+1≤N) :
    let x := Real.sqrt (t/(2*Real.pi))
    let s := (1/2:ℂ)+(t:ℂ)*I
    let E := Complex.exp ((hardyPhase t:ℂ)*I)
    hurwitzWaveSum a N t=E*hurwitzDirectSum a x s+conj E*hurwitzReciprocalPoly a ⌊x⌋₊ s := by
  intro x s E
  rw [hurwitzWaveSum]
  change (∑i∈hurwitzWaveIndices N,if hurwitzWaveEntry a i≤t then hurwitzWave a i t else 0)=_
  rw [sum_wave_cutoff (fun i => hurwitzWave a i t) ha ht hx hN,hurwitzDirectSum,←Nat.range_succ_eq_Icc_zero,
    hurwitzReciprocalPoly,mul_sum,mul_sum]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl;intro m _
    have hp : 0<(m:ℝ)+a := by linarith [Nat.cast_nonneg (α:=ℝ) m,ha.1]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_add,critical_monomial_eq hp]
    simp only [hurwitzWave,hurwitzWavePhase,hurwitzWaveFrequency,Bool.false_eq_true,ite_false]
    dsimp only [E]
    rw [mul_left_comm,←Complex.exp_add];congr 2;push_cast;ring
  · apply sum_congr rfl;intro m _
    have hp : 0<(m:ℝ)+1 := by positivity
    have he : s-1= -((1/2:ℂ)+(-t:ℝ)*I) := by dsimp [s];push_cast;ring
    rw [show (m:ℂ)+1=(((m:ℝ)+1:ℝ):ℂ) by push_cast;rfl,he,critical_monomial_eq hp]
    simp only [hurwitzWave,hurwitzWavePhase,hurwitzWaveFrequency,ite_true,hurwitzShift,hurwitzOmega,E,←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I]
    rw [show ∀w z v k:ℂ,Complex.exp w*(Complex.exp z*(k*Complex.exp v))=k*Complex.exp (w+z+v) by
      intros;rw [Complex.exp_add,Complex.exp_add];ring]
    congr 2;push_cast;ring

/-- Sum of the squared amplitudes of the active waves. -/
theorem hurwitzWaveSum_diagonal {a t : ℝ} (ha : a∈Ioc (0:ℝ) 1) (ht : 0≤t)
    (hx : 1≤Real.sqrt (t/(2*Real.pi))) {N : ℕ} (hN : ⌊Real.sqrt (t/(2*Real.pi))⌋₊+1≤N) :
    (∑i∈hurwitzWaveIndices N,‖enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t‖^2)=
      hurwitzCriticalDiagonal a t := by
  have h (i) : ‖enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t‖^2=
      if hurwitzWaveEntry a i≤t then 1/hurwitzWaveFrequency a i else 0 := by
    change ‖if hurwitzWaveEntry a i≤t then hurwitzWave a i t else 0‖^2=_
    split_ifs
    · rw [norm_hurwitzWave,inv_pow,Real.sq_sqrt (hurwitzWaveFrequency_pos ha.1 i).le,one_div]
    · simp
  simp_rw [h]
  rw [sum_wave_cutoff (fun i => 1/hurwitzWaveFrequency a i) ha ht hx hN]
  simp only [hurwitzCriticalDiagonal,hurwitzWaveFrequency,Bool.false_eq_true,ite_false,ite_true,harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,one_div,Nat.cast_add,Nat.cast_one]

end AnalyticNumberTheory.RiemannZeta
