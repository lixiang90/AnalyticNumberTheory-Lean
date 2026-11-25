import AnalyticNumberTheory.DirichletLFunctions.PrimitiveCriticalPolynomial
import AnalyticNumberTheory.RiemannZeta.WeightedHardyEnergy

/-!
# Moving waves of a primitive Dirichlet character

The two families have conjugate character coefficients. A common scaling
by sqrt(q) reconciles their cutoffs with the Hardy phase.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

def primitiveWaveWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (i : Bool×ℕ) :=
  if i.1 then primitiveHardyMultiplier χ*conj (χ (i.2:ZMod q)) else χ (i.2:ZMod q)

theorem norm_primitiveWaveWeight {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (i : Bool×ℕ) :
    ‖primitiveWaveWeight χ i‖=‖χ (i.2:ZMod q)‖ := by
  unfold primitiveWaveWeight;split_ifs
  · rw [norm_mul,norm_primitiveHardyMultiplier hχ,Complex.norm_conj,one_mul]
  · rfl

theorem scaledHardyEntry_iff {q : ℕ} [NeZero q] {t : ℝ} (ht : 0≤t) (n : ℕ) :
    scaledHardyEntry (Real.sqrt q) n≤t ↔ n≤primitiveCriticalLength q t := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  rw [primitiveCriticalLength,Nat.le_floor_iff (Real.sqrt_nonneg _),Real.le_sqrt (Nat.cast_nonneg _) (by positivity),
    le_div_iff₀ (by positivity : 0<2*Real.pi),scaledHardyEntry,div_pow,Real.sq_sqrt hq.le,
    ←mul_div_assoc,div_le_iff₀ hq]
  constructor <;>intro h <;>linarith

private theorem wave_terms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 0<n) (t : ℝ) :
    let s := (1/2:ℂ)+t*I
    let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
    let z := R*(χ n*(n:ℂ)^(-s))
    weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) (false,n) t=z ∧
    weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) (true,n) t=primitiveHardyMultiplier χ*conj z := by
  intro s R z
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hn' := Nat.cast_pos (α:=ℝ).mpr hn
  have he : scaledHardyAngle (Real.sqrt q) n t=primitiveHardyPhase q t-t*Real.log n := by
    rw [scaledHardyAngle,primitiveHardyPhase,Real.log_div hn'.ne' (Real.sqrt_pos.mpr hq).ne',Real.log_sqrt hq.le];ring
  have hdir : weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) (false,n) t=z := by
    dsimp only [weightedHardyWave,primitiveWaveWeight,z,R]
    simp only [Bool.false_eq_true,ite_false,Circle.coe_exp]
    rw [←Complex.ofReal_natCast,critical_monomial_eq hn',he]
    push_cast;rw [sub_mul,Complex.exp_sub,div_eq_mul_inv,←Complex.exp_neg]
    rw [show -(↑t*Complex.log (n:ℂ)*I)=I*(-Complex.log (n:ℂ))*↑t by ring]
    ring
  refine ⟨hdir,?_⟩
  rw [←hdir]
  simp only [weightedHardyWave,primitiveWaveWeight,Bool.false_eq_true,ite_false,ite_true,map_mul,←Complex.exp_conj,
    Complex.conj_ofReal,Complex.conj_I]
  push_cast;rw [show ∀w:ℂ,w*(-I)= -w*I by intro;ring];ring

private theorem cutoff_sums {E : Type*} [AddCommMonoid E] {q : ℕ} [NeZero q] {t : ℝ} (ht : 0≤t)
    {N : ℕ} (hN : primitiveCriticalLength q t≤N) (f : Bool×ℕ→E) :
    (∑i∈scaledWaveIndex N,if scaledHardyEntry (Real.sqrt q) i.2≤t then f i else 0)=
      (∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f (false,n))+
      ∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f (true,n) := by
  rw [scaledWaveIndex,sum_product (f:=fun i => if scaledHardyEntry (Real.sqrt q) i.2≤t then f i else 0),Fintype.sum_bool]
  have H : ((Finset.Icc 1 N).filter (fun n=>scaledHardyEntry (Real.sqrt q) n≤t))=Finset.Icc 1 (primitiveCriticalLength q t) := by
    ext n;simp only [mem_filter,Finset.mem_Icc,scaledHardyEntry_iff ht];omega
  simp_rw [←sum_filter,H];apply add_comm

theorem weightedHardyPolynomial_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0≤t)
    {N : ℕ} (hN : primitiveCriticalLength q t≤N) :
    weightedHardyPolynomial (Real.sqrt q) (primitiveWaveWeight χ) N t=
      primitiveCriticalPolynomial χ (primitiveCriticalLength q t) t := by
  let s := (1/2:ℂ)+t*I
  let R := (Circle.exp (primitiveHardyPhase q t):ℂ)
  let f := fun n : ℕ => R*(χ n*(n:ℂ)^(-s))
  change (∑i∈scaledWaveIndex N,if scaledHardyEntry (Real.sqrt q) i.2≤t then weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) i t else 0)=_
  rw [cutoff_sums ht hN]
  have h (n : ℕ) (hn : n∈Finset.Icc 1 (primitiveCriticalLength q t)) := wave_terms χ (Finset.mem_Icc.mp hn).1 t
  have h₁ : (∑n∈Finset.Icc 1 (primitiveCriticalLength q t),weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) (false,n) t)=
      ∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f n := sum_congr rfl (fun n hn => (h n hn).1)
  have h₂ : (∑n∈Finset.Icc 1 (primitiveCriticalLength q t),weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) (true,n) t)=
      ∑n∈Finset.Icc 1 (primitiveCriticalLength q t),primitiveHardyMultiplier χ*conj (f n) := sum_congr rfl (fun n hn => (h n hn).2)
  have hf : primitiveRotatedPoly χ (primitiveCriticalLength q t) t=∑n∈Finset.Icc 1 (primitiveCriticalLength q t),f n := by
    rw [primitiveRotatedPoly,dirichletPoly,mul_sum]
  rw [h₁,h₂,primitiveCriticalPolynomial,hf,map_sum,mul_sum]

def primitiveCriticalDiagonal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :=
  2*∑n∈Finset.Icc 1 (primitiveCriticalLength q t),‖χ n‖^2/(n:ℝ)

theorem weightedHardyDiagonal_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {t : ℝ} (ht : 0≤t) {N : ℕ} (hN : primitiveCriticalLength q t≤N) :
    weightedHardyDiagonal (Real.sqrt q) (primitiveWaveWeight χ) N t=primitiveCriticalDiagonal χ t := by
  have h (i : Bool×ℕ) : ‖enteredWave (scaledHardyEntry (Real.sqrt q) i.2) (weightedHardyWave (Real.sqrt q) (primitiveWaveWeight χ) i) t‖^2=
      if scaledHardyEntry (Real.sqrt q) i.2≤t then ‖χ i.2‖^2/(i.2:ℝ) else 0 := by
    change ‖if scaledHardyEntry (Real.sqrt q) i.2≤t then _ else 0‖^2=_
    split_ifs
    · rw [norm_weightedHardyWave,norm_primitiveWaveWeight hχ,mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _),div_eq_mul_inv]
    · simp
  unfold weightedHardyDiagonal;simp_rw [h]
  rw [cutoff_sums ht hN,primitiveCriticalDiagonal];ring

end AnalyticNumberTheory.DirichletLFunctions
