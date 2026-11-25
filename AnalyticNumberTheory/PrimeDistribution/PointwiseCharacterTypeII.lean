import AnalyticNumberTheory.PrimeDistribution.PointwiseDetectorMoments
import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import AnalyticNumberTheory.PrimeDistribution.SparseMollifierMean
import AnalyticNumberTheory.PrimeDistribution.SparseDetectorIntegral

/-!
# Character zero detection from pointwise bounds on the critical line

The kernel has enough decay to use the pointwise bound at shifted
heights. No fourth moment of the L-family is required in this estimate.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory Filter
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- A pointwise critical-line bound and the sparse Möbius second moment
give a quadratic count for the integral detector. -/
theorem pointwise_character_typeII_count {a b B C : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b)
    (hB : 0<B) (hC : 0<C) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*} {F : Finset ι} (q : ι→ℕ) [∀i,NeZero (q i)]
      (χ : (i:ι)→DirichletCharacter ℂ (q i)) (S : ι→Finset ℂ) {L X : ℕ} {H K V : ℝ},
    1≤L → 1≤X → 1≤H → 0≤K → 0≤V → (∀i∈F,(q i:ℝ)*((L:ℝ)+2)≤H) →
    SparseCharacterBound F (fun i n => χ i n) L H C →
    (∀i∈F,∀z∈S i,0≤z.im ∧ z.im<L) →
    (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K) →
    ∀ f : ι→ℝ→ℝ,(∀i∈F,Continuous (f i)) → (∀i∈F,∀t,0≤f i t) →
    (∀i∈F,∀t,f i t≤B*((q i:ℝ)*(|t|+2))^a*(1+Real.log ((q i:ℝ)*(|t|+2)))^b) →
    (∀i∈F,∀z∈S i,∀ᶠ U : ℝ in atTop,
      V≤∫ t in -U..U,1/(1+|t-z.im|)^6*f i t*
        ‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖) →
    let R := ∑i∈F,((S i).card:ℝ)
    R*V^2≤D*H^(2*a)*(1+Real.log H)^(2*b)*(K*X+R*Real.sqrt H*(1+Real.log H))*(1+Real.log X)^2 := by
  obtain ⟨E,hE,HE⟩ := translated_conductor_growth ha hb
  refine ⟨π^2*(B*E)^2*8*C,by positivity,?_⟩
  intro ι F q _ χ S L X H K V hL hX hH hK hV hq hm him hc f hf hf₀ hLfun hdet
  let ℓ := 1+Real.log H
  have hℓ : 0<ℓ := by dsimp [ℓ];linarith [Real.log_nonneg hH]
  let A := B*E*(H^a*ℓ^b)
  have hA : 0≤A := mul_nonneg (mul_nonneg hB.le hE.le) (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hH) _) (Real.rpow_nonneg hℓ.le _))
  have hlocal (i) (hi:i∈F) (z) (hz:z∈S i) (t:ℝ) : f i t≤A*Real.sqrt (1+|t-z.im|) := by
    let w := 1+|t-z.im|
    have hw : 1≤w := by dsimp [w];linarith [abs_nonneg (t-z.im)]
    have hqi : (1:ℝ)≤q i := by exact_mod_cast (NeZero.one_le : 1≤q i)
    have hp : 1≤(q i:ℝ)*(|t|+2) := one_le_mul_of_one_le_of_one_le hqi (by linarith [abs_nonneg t])
    have htime := him i hi z hz
    have hlo : |t|≤|t-z.im|+z.im := by
      simpa only [sub_add_cancel,abs_of_nonneg htime.1] using abs_add_le (t-z.im) z.im
    have hP : (q i:ℝ)*(|t|+2)≤H*w := by
      apply le_trans _ (mul_le_mul_of_nonneg_right (hq i hi) (zero_le_one.trans hw))
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      dsimp [w];nlinarith only [hlo,htime.2,abs_nonneg (t-z.im),mul_nonneg (Nat.cast_nonneg (α:=ℝ) L) (abs_nonneg (t-z.im))]
    have h := mul_le_mul_of_nonneg_left (HE hp hH hw hP) hB.le
    exact (hLfun i hi t).trans (by dsimp only [A,ℓ,w] at *;convert h using 1 <;>ring)
  let g (i : ι) (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖
  have hg (i) : Continuous (g i) := ( (differentiable_dirichletPoly _ X).continuous.comp
    (show Continuous (fun t:ℝ => (1/2:ℂ)+t*I) by fun_prop)).norm
  let R := ∑i∈F,((S i).card:ℝ)
  have hR : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  let B₂ := 8*C*(K*X+R*Real.sqrt H*ℓ)*(1+Real.log X)^2
  have hB₂ : 0≤B₂ := mul_nonneg (mul_nonneg (by positivity) (add_nonneg (mul_nonneg hK (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg H)) hℓ.le))) (sq_nonneg _)
  have hmean (n : ℕ) := sparse_detector_second_mean F S (R:=(2:ℝ)^n*L) (Nat.cast_nonneg (α:=ℝ) L) (by positivity) hB₂
    (fun i hi z hz => ⟨(him i hi z hz).1,(him i hi z hz).2.le⟩) g (fun i _ => hg i)
    (fun v => sparse_mollifier_second_mean hm hH hC.le hX hK S him hc v)
  have h := count_from_pointwise_detector F S hL hA (mul_nonneg pi_pos.le hB₂) hV f g hf hf₀
    (fun i _ => hg i) hlocal hmean hdet
  apply h.trans_eq
  dsimp only [A,B₂,ℓ,R]
  rw [show 2*a=a*2 by ring,show 2*b=b*2 by ring,
    Real.rpow_mul (zero_le_one.trans hH),Real.rpow_mul hℓ.le,Real.rpow_two,Real.rpow_two]
  ring

end AnalyticNumberTheory.PrimeDistribution
