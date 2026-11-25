import AnalyticNumberTheory.DirichletSeries.VerticalOrder

/-!
# The sparse hybrid mean-square bound for a character family

A family is indexed by a finite set F, and the heights in each unit
interval have occupancy at most K for each character. The parameter H
combines the maximal correlation modulus and the height window.
-/
open Real Complex Finset
namespace AnalyticNumberTheory.SieveMethods

/-- A uniform dyadic mean square for sparse samples of character polynomials.
The imaginary part of the exponent is prescribed by the sample, while its
real part can vary over the whole closed unit interval. -/
def SparseCharacterBound {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (L : ℕ) (H C : ℝ) : Prop :=
  ∀(S : ι→Finset ℂ) {K : ℝ}, 0≤K →
  (∀i∈F,∀z∈S i,0≤z.im ∧ z.im<L) →
  (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K) →
  ∀(u : ℂ→ℂ),(∀i∈F,∀z∈S i,(u z).re∈Set.Icc (0:ℝ) 1 ∧ (u z).im=z.im) →
  ∀{M : ℕ},1≤M → ∀a : ℕ→ℂ,
  (∑i∈F,∑z∈S i,‖∑n∈Icc M (2*M),a n*f i n*(n:ℂ)^(-u z)‖^2) ≤
    C*(K*M+(∑i∈F,((S i).card:ℝ))*Real.sqrt H*(1+Real.log H))*(∑n∈Icc M (2*M),‖a n‖^2)

/-- Existence of a positive sparse hybrid mean-square constant. -/
def SparseCharacterMean {ι : Type*} (F : Finset ι) (f : ι→ℕ→ℂ) (L : ℕ) (H : ℝ) : Prop :=
  ∃ C : ℝ, 0<C ∧ SparseCharacterBound F f L H C

end AnalyticNumberTheory.SieveMethods
