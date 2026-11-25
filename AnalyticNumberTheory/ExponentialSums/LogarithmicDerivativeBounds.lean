import AnalyticNumberTheory.ExponentialSums.LogPhaseDifferences
import AnalyticNumberTheory.ExponentialSums.HigherDerivativeTests

/-!
# Higher derivative bounds for shifted logarithmic sums

The first and second terms from the derivative test are written in
logarithmic coordinates. At the point where the second becomes larger,
the test of the preceding order already yields the desired estimate.
-/

open Real Complex Finset
namespace AnalyticNumberTheory.ExponentialSums

private noncomputable def logPhaseJet (τ a : ℝ) : ℕ → ℝ → ℝ
  | 0 => logPhase τ a
  | 1 => fun u => τ/(u+a)
  | j+2 => logSecondDerivative τ a j

private theorem logPhaseJet_deriv {τ a u : ℝ} (hu : 0<u+a) (j : ℕ) :
    HasDerivAt (logPhaseJet τ a j) (logPhaseJet τ a (j+1) u) u := by
  match j with
  | 0 => exact logPhase_deriv τ a hu
  | 1 => simpa [logPhaseJet,logSecondDerivative] using logPhase_second τ a hu
  | n+2 => exact logSecondDerivative_hasDerivAt hu n

private noncomputable def firstLogExponent (k : ℕ) (x y : ℝ) :=
  x+(y-k*x)/((2:ℝ)^k-2)

private noncomputable def secondLogExponent (k : ℕ) (x y : ℝ) :=
  x-4/(2:ℝ)^k*x-(y-k*x)/((2:ℝ)^k-2)

private theorem log_block_two_terms (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ {M b : ℕ} {a t : ℝ},1≤M → b≤2*M →
      a∈Set.Icc (0:ℝ) 1 → 0 < |t| →
      ‖∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n)‖ ≤
        C*(Real.exp (firstLogExponent (j+2) (Real.log M) (Real.log |t|))+
          Real.exp (secondLogExponent (j+2) (Real.log M) (Real.log |t|))) := by
  let k := j+2
  let B := ((j+1).factorial:ℝ)/(2*π*3^k)
  let α := 1/((2:ℝ)^k-2)
  let β := ((2:ℝ)⁻¹)^j
  have hB : 0<B := by dsimp [B]; positivity
  have h3 : 1≤(3:ℝ)^k := one_le_pow₀ (by norm_num)
  obtain ⟨D,hD,H⟩ := vanDerCorput_higher_derivative (k:=k) (by dsimp [k]; omega) h3
  refine ⟨D*(B^α+B^(-α)),by positivity,?_⟩
  intro M b a t hM hb ha ht
  let m := (M:ℝ)
  have hm : 1≤m := by dsimp [m]; exact_mod_cast hM
  have hm₀ := zero_lt_one.trans_le hm
  let τ := -t/(2*π)
  let lam := B*|t|/m^k
  have hlam : 0<lam := by dsimp [lam]; positivity
  have hτ : |τ|=|t|/(2*π) := by simp [τ,abs_div,abs_of_pos (by positivity : 0<2*π)]
  have hx {u : ℝ} (hu : u∈Set.Icc (M:ℝ) b) : m≤u+a ∧ u+a≤3*m := by
    have hbu : (b:ℝ)≤2*m := by dsimp [m]; exact_mod_cast hb
    constructor <;> linarith only [hu.1,hu.2,ha.1,ha.2,hm,hbu]
  have hjet := H (logPhaseJet τ a) hM (by omega : b≤M+M) hlam
    (fun l _ u hu => logPhaseJet_deriv (hm₀.trans_le (hx hu).1) l)
    (fun u hu => (logPhaseJet_deriv (τ:=τ) (hm₀.trans_le (hx hu).1) k).continuousAt.continuousWithinAt)
    (by
      intro u hu
      obtain ⟨hl,hh⟩ := hx hu
      have hpos := hm₀.trans_le hl
      change lam≤|(-1:ℝ)^(j+1)*τ*((j+1).factorial:ℝ)/(u+a)^k| ∧
        |(-1:ℝ)^(j+1)*τ*((j+1).factorial:ℝ)/(u+a)^k|≤3^k*lam
      simp only [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,hτ,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _),abs_of_pos hpos]
      have hl' := pow_le_pow_left₀ hm₀.le hl k
      have hh' := pow_le_pow_left₀ hpos.le hh k
      rw [mul_pow] at hh'
      let A := |t|/(2*π)*((j+1).factorial:ℝ)
      have hA : 0≤A := by dsimp [A]; positivity
      have he : lam=A/(3^k*m^k) := by dsimp [lam,B,A]; ring
      change lam≤A/(u+a)^k ∧ A/(u+a)^k≤3^k*lam
      rw [he,show (3:ℝ)^k*(A/(3^k*m^k))=A/m^k by field_simp]
      exact ⟨div_le_div_of_nonneg_left hA (by positivity) hh',
        div_le_div_of_nonneg_left hA (by positivity) hl'⟩)
  let x := Real.log m
  let y := Real.log |t|
  have hlog : Real.log lam=Real.log B+(y-k*x) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_mul hB.ne' ht.ne',Real.log_pow]; ring
  have hβ : β=4/(2:ℝ)^k := by
    dsimp [β,k]; rw [inv_pow,pow_add]; norm_num; ring
  have e₁ : m*lam^α = B^α*Real.exp (firstLogExponent k x y) := by
    rw [Real.rpow_def_of_pos hlam,Real.rpow_def_of_pos hB,hlog,
      show m=Real.exp x from (Real.exp_log hm₀).symm,←Real.exp_add,←Real.exp_add]
    congr 1; dsimp only [firstLogExponent,α]; ring
  have e₂ : m^(1-β)*lam^(-α) = B^(-α)*Real.exp (secondLogExponent k x y) := by
    rw [Real.rpow_def_of_pos hm₀,Real.rpow_def_of_pos hlam,Real.rpow_def_of_pos hB,hlog,←Real.exp_add,←Real.exp_add]
    congr 1; change x*(1-β)+_=_
    rw [hβ]; dsimp only [secondLogExponent,α]; ring
  change ‖∑ n∈Ioc M b,e (logPhase τ a n)‖≤_
  change ‖∑ n∈Ioc M b,e (logPhase τ a n)‖≤D*(m*lam^α + m^(1-β)*lam^(-α)) at hjet
  apply hjet.trans
  rw [e₁,e₂,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  let U := Real.exp (firstLogExponent k x y)
  let V := Real.exp (secondLogExponent k x y)
  change B^α*U+B^(-α)*V≤(B^α+B^(-α))*(U+V)
  nlinarith only [show 0≤B^α*V by positivity,show 0≤B^(-α)*U by positivity]

private theorem first_le_next {k : ℕ} (hk : 2≤k) {x y : ℝ}
    (h : firstLogExponent (k+1) x y≤secondLogExponent (k+1) x y) :
    firstLogExponent k x y≤firstLogExponent (k+1) x y := by
  let Q := (2:ℝ)^k
  have hQ : 4≤Q := (by norm_num : (4:ℝ)=2^2).le.trans ( pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk)
  have hd : 0<Q-2 := by linarith
  have he : firstLogExponent k x y-firstLogExponent (k+1) x y =
      Q/(2*(Q-2))*(firstLogExponent (k+1) x y-secondLogExponent (k+1) x y) := by
    dsimp [firstLogExponent,secondLogExponent,Q]
    rw [pow_succ]
    push_cast
    change x+(y-k*x)/(Q-2)-(x+(y-(k+1)*x)/(Q*2-2))=_
    have h2 : Q*2-2≠0 := by linarith
    change _=Q/(2*(Q-2))*((x+(y-(k+1)*x)/(Q*2-2))-(x-4/(Q*2)*x-(y-(k+1)*x)/(Q*2-2)))
    field_simp [hd.ne',h2,show Q≠0 by linarith]
    ring_nf
    field_simp [show -1+Q≠0 by linarith] <;> ring
  exact sub_nonpos.mp (he ▸ mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h))

private theorem logarithmic_block_exp (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ {M b : ℕ} {a t : ℝ},1≤M → b≤2*M →
      a∈Set.Icc (0:ℝ) 1 → (M:ℝ)≤|t| →
      ‖∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n)‖ ≤
        C*Real.exp (firstLogExponent (j+2) (Real.log M) (Real.log |t|)) := by
  induction j with
  | zero =>
    obtain ⟨D,hD,H⟩ := log_block_two_terms 0
    refine ⟨2*D,by positivity,?_⟩
    intro M b a t hM hb ha ht
    have hm : (0:ℝ)<M := by exact_mod_cast hM
    have h := H hM hb ha (hm.trans_le ht)
    have hE : secondLogExponent 2 (Real.log M) (Real.log |t|)≤firstLogExponent 2 (Real.log M) (Real.log |t|) := by
      dsimp [secondLogExponent,firstLogExponent]
      have hlog := Real.log_le_log hm ht
      norm_num at *; linarith only [hlog]
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hD.le])
  | succ j ih =>
    obtain ⟨D,hD,H⟩ := log_block_two_terms (j+1)
    obtain ⟨C,hC,HS⟩ := ih
    refine ⟨C+2*D,by positivity,?_⟩
    intro M b a t hM hb ha ht
    have hm : (0:ℝ)<M := by exact_mod_cast hM
    let x := Real.log M
    let y := Real.log |t|
    let U := firstLogExponent (j+1+2) x y
    let V := secondLogExponent (j+1+2) x y
    change ‖_‖≤(C+2*D)*Real.exp U
    by_cases hUV : V≤U
    · apply (H hM hb ha (hm.trans_le ht)).trans
      change D*(Real.exp U+Real.exp V)≤_
      nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hUV) hD.le,
        show 0≤C*Real.exp U by positivity]
    · have he := first_le_next (k:=j+2) (by omega) (x:=x) (y:=y) (le_of_not_ge hUV)
      have hh := HS hM hb ha ht
      apply hh.trans
      nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC.le,
        show 0≤D*Real.exp U by positivity]

/-- The order-`k` estimate on each incomplete logarithmic block. The
constant depends only on the derivative order, uniformly in the shift. -/
theorem logPhase_higher_order_block {k : ℕ} (hk : 2≤k) :
    ∃ C : ℝ,0<C ∧ ∀ {M b : ℕ} {a t : ℝ},1≤M → b≤2*M →
      a∈Set.Icc (0:ℝ) 1 → (M:ℝ)≤|t| →
      ‖∑ n∈Ioc M b,e (logPhase (-t/(2*π)) a n)‖ ≤
        C*|t|^(1/((2:ℝ)^k-2))*(M:ℝ)^(1-k/((2:ℝ)^k-2)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨C,hC,H⟩ := logarithmic_block_exp j
  refine ⟨C,hC,?_⟩
  intro M b a t hM hb ha ht
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  apply (H hM hb ha ht).trans_eq
  rw [Real.rpow_def_of_pos (hm.trans_le ht),Real.rpow_def_of_pos hm,mul_assoc,←Real.exp_add]
  congr 2
  dsimp only [firstLogExponent]; ring

end AnalyticNumberTheory.ExponentialSums
