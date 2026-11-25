import AnalyticNumberTheory.PrimeDistribution.InghamFamilyBounds
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityBalance
import AnalyticNumberTheory.SieveMethods.SparseCharacterSampling

/-!
# Inputs for Montgomery's mean density theorem

Up to real part four fifths the Ingham exponent is already sufficient.
For the sparse estimate above four fifths, the family can be indexed by
its members so that the positive modulus of each character is available.
-/
noncomputable section
open Finset Complex Real MeasureTheory
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Reindexing a sparse mean by actual members of its finite index set
preserves its correlation parameter, sample count, and constant. -/
theorem SparseCharacterBound.attach {ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {L : ℕ} {H C : ℝ}
    (h : SparseCharacterBound F f L H C) :
    SparseCharacterBound F.attach (fun i n => f i.val n) L H C := by
  intro S K hK him hc u hu M hM a
  let A (i : ι) : Finset ℂ := if hi : i∈F then S ⟨i,hi⟩ else ∅
  have he (i : F) : A i.val=S i := by simp [A,i.property]
  have H' := h A hK (by
    intro i hi
    simpa only [he ⟨i,hi⟩] using him ⟨i,hi⟩ (mem_attach _ _)) (by
    intro i hi
    simpa only [he ⟨i,hi⟩] using hc ⟨i,hi⟩ (mem_attach _ _)) u (by
    intro i hi
    simpa only [he ⟨i,hi⟩] using hu ⟨i,hi⟩ (mem_attach _ _)) hM a
  have hsum := sum_attach F (fun i => ∑z∈A i,‖∑n∈Icc M (2*M),a n*f i n*(n:ℂ)^(-u z)‖^2)
  have hcard := sum_attach F (fun i => ((A i).card:ℝ))
  rw [←hsum,←hcard] at H'
  simpa only [he] using H'

end AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution
open AnalyticNumberTheory.SieveMethods

/-- On the left part of the strip the full character group satisfies
Montgomery's exponent with just eight logarithms. -/
theorem modulusDensityCount_montgomery_left :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (1/2:ℝ) (4/5) → 2≤T →
      (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*T)^(montgomeryExponent σ)*(Real.log ((q:ℝ)*T))^8 := by
  obtain ⟨C,hC,H⟩ := modulusDensityCount_ingham_log_eight
  refine ⟨C,hC,?_⟩;intro q _ σ T hσ hT
  have hs := inghamExponent_le_montgomeryExponent (by linarith [hσ.1]) hσ.2
  have hx : 1≤(q:ℝ)*T := one_le_mul_of_one_le_of_one_le (by exact_mod_cast NeZero.pos q) (by linarith)
  exact (H (q:=q) ⟨hσ.1,by linarith [hσ.2]⟩ hT).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hs) hC.le) (by positivity))

/-- The left-hand part of Montgomery's density estimate for all primitive
conductors, with the principal character and both signs of the height. -/
theorem primitive_conductors_montgomery_left :
    ∃ C : ℝ,0<C ∧ ∀ {Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (1/2:ℝ) (4/5) → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤
        C*((Q:ℝ)^2*T)^(montgomeryExponent σ)*(Real.log ((Q:ℝ)*T))^8 := by
  obtain ⟨C,hC,H⟩ := primitive_conductors_ingham_log_eight
  refine ⟨C,hC,?_⟩;intro Q σ T hQ hσ hT
  have hs := inghamExponent_le_montgomeryExponent (by linarith [hσ.1]) hσ.2
  have hx : 1≤(Q:ℝ)^2*T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast hQ)) (by linarith)
  exact (H hQ ⟨hσ.1,by linarith [hσ.2]⟩ hT).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hs) hC.le) (by positivity))

/-- The primitive family on the dependent index set used in strip-zero counts. -/
theorem primitive_sparse_mean_attach :
    ∃ C : ℝ,0<C ∧ ∀(Q L : ℕ),1≤Q →
      SparseCharacterBound (primitiveCharacterFamily Q).attach (fun p n => p.val.2 n) L
        ((Q:ℝ)^2*((L:ℝ)+2)) C := by
  obtain ⟨C,hC,_,H⟩ := sparse_character_family_mean
  exact ⟨C,hC,fun Q L hQ => (H Q L hQ).attach⟩

end AnalyticNumberTheory.PrimeDistribution
