import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The first logarithmic moment of an Euler product

When every local factor has mass one, its logarithmic moment contributes
additively to the global moment. The square-zero extension encodes the product
rule, so only absolute summability of the coefficients and their first moment
is needed.
-/

open Filter Real Finset TrivSqZeroExt
open scoped Topology
namespace AnalyticNumberTheory.DirichletSeries

private def logPair (x y : ℝ) : TrivSqZeroExt ℝ ℝ := (x,y)

@[simp] private theorem logPair_fst (x y : ℝ) : (logPair x y).fst=x := rfl
@[simp] private theorem logPair_snd (x y : ℝ) : (logPair x y).snd=y := rfl

private theorem hasSum_log_pair {α : Type*} {a b : α → ℝ} {x y : ℝ}
    (ha : HasSum a x) (hb : HasSum b y) :
    HasSum (fun n => logPair (a n) (b n)) (logPair x y) := by
  have hp (a b : ℝ) : (inl a + inr b : TrivSqZeroExt ℝ ℝ)=logPair a b := by apply TrivSqZeroExt.ext <;> simp
  simpa only [hp] using (hasSum_inl ℝ ha).add (hasSum_inr ℝ hb)

private theorem prod_log_pair {α : Type*} (S : Finset α) (b : α → ℝ) :
    (∏ p∈S, logPair 1 (b p))=logPair 1 (∑p∈S,b p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sum_empty,prod_empty]; apply TrivSqZeroExt.ext <;> simp
  | insert p S hp ih =>
    rw [prod_insert hp,sum_insert hp,ih]
    apply TrivSqZeroExt.ext
    · simp
    · simp [op_smul_eq_smul,add_comm]

/-- Sum the local logarithmic moments when every local Euler factor has mass one. -/
theorem hasSum_euler_log_moment {f : ℕ→ℝ} {b : Nat.Primes→ℝ} (h₀ : f 0=0) (h₁ : f 1=1)
    (hm : ∀ {m n : ℕ}, m.Coprime n → f (m*n)=f m*f n)
    (h : Summable fun n => |f n|) (hlog : Summable fun n : ℕ => |f n*log n|)
    (hlocal : ∀p : Nat.Primes, HasSum (fun j : ℕ => f (p.val^j)) 1 ∧
      HasSum (fun j : ℕ => f (p.val^j)*log (p.val^j:ℕ)) (b p)) :
    HasSum b (∑' n : ℕ, f n*log n) := by
  let F (n : ℕ) : TrivSqZeroExt ℝ ℝ := logPair (f n) (f n*log n)
  have H : Summable (fun n => ‖F n‖) := by simpa [F,TrivSqZeroExt.norm_def,Real.norm_eq_abs] using h.add hlog
  have H₀ : F 0=0 := by apply TrivSqZeroExt.ext <;> simp [F,h₀]
  have H₁ : F 1=1 := by apply TrivSqZeroExt.ext <;> simp [F,h₁]
  have Hm {m n : ℕ} (hc : m.Coprime n) : F (m*n)=F m*F n := by
    by_cases hm' : m=0
    · simp [hm',H₀]
    by_cases hn' : n=0
    · simp [hn',H₀]
    apply TrivSqZeroExt.ext
    · simp [F,hm hc]
    · simp [F,hm hc,Real.log_mul (by exact_mod_cast hm' : (m:ℝ)≠0) (by exact_mod_cast hn' : (n:ℝ)≠0),op_smul_eq_smul,smul_eq_mul]; ring
  have E := EulerProduct.eulerProduct_hasProd H₁ (fun {_ _} hc => Hm hc) H H₀
  have hf (p : Nat.Primes) : (∑' j : ℕ, F (p.val^j))=logPair 1 (b p) :=
    (hasSum_log_pair (hlocal p).1 (hlocal p).2).tsum_eq
  simp_rw [hf] at E
  have hsum := hasSum_snd ℝ H.of_norm.hasSum
  change Tendsto (fun S : Finset Nat.Primes => ∏p∈S, logPair 1 (b p)) atTop (𝓝 (∑' n : ℕ,F n)) at E
  have Hlim := TrivSqZeroExt.continuous_snd.continuousAt.tendsto.comp E
  change Tendsto (fun S : Finset Nat.Primes => ∑p∈S,b p) atTop _
  rw [show (∑' n : ℕ,f n*log n)=snd (∑' n : ℕ,F n) from hsum.tsum_eq]
  exact Hlim.congr' (Eventually.of_forall fun S => by
    change snd (∏ p∈S, logPair 1 (b p))=_
    rw [prod_log_pair,logPair_snd])

end AnalyticNumberTheory.DirichletSeries
