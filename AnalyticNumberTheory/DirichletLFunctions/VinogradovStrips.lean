import AnalyticNumberTheory.RiemannZeta.HurwitzVinogradovStrips
import AnalyticNumberTheory.DirichletLFunctions.VinogradovGrowth
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Dirichlet L-functions in near-one strips

Estimating the first period by a power integral gives a bound uniform in
the height, modulus, and character. All conductor dependence is contained
in the factor `q^(R/(log |Im s|)^(2/3))`.
-/

open Complex Real Finset
open AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The sum of the initial power weights in a strip of width `δ`. -/
theorem first_period_power_sum_le {q : ℕ} (hq : 1≤q) {δ σ : ℝ} (hδ : 0<δ)
    (hσ : 0≤σ) (hstrip : 1-δ≤σ) :
    ∑ n∈Icc 1 q,(n:ℝ)^(-σ)≤(q:ℝ)^δ*(1+1/δ) := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hq₀ : 0<(q:ℝ) := zero_lt_one.trans_le hq'
  by_cases hd : δ≤1
  · let f (u : ℝ) := u^(δ-1)
    have hanti : AntitoneOn f (Set.Icc (1:ℝ) q) := fun u hu v _ huv =>
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hu.1) huv (by linarith)
    have hi := AntitoneOn.sum_le_integral_Ico (a:=1) (b:=q) hq (by simpa using hanti)
    have he : (∑ n∈Icc 1 q,f n)=1+∑ n∈Ico 1 q,f (n+1:ℕ) := by
      have hr : Icc 1 q=insert 1 (Icc 2 q) := by
        ext n; simp only [mem_Icc,mem_insert]; omega
      rw [hr,sum_insert (by simp)]
      have hf : f 1=1 := by simp [f]
      simp only [Nat.cast_one,hf]
      congr 1
      refine sum_bij' (fun n _ => n-1) (fun n _ => n+1) ?_ ?_ ?_ ?_ ?_
      · intro n hn; simp only [mem_Icc,mem_Ico] at hn ⊢; omega
      · intro n hn; simp only [mem_Icc,mem_Ico] at hn ⊢; omega
      · intro n hn; have := (mem_Icc.mp hn).1; omega
      · intro n _; omega
      · intro n hn; rw [Nat.sub_add_cancel (by have := (mem_Icc.mp hn).1; omega)]
    have hInt : (∫ x in (1:ℝ)..q,f x)=((q:ℝ)^δ-1)/δ := by
      dsimp only [f]
      rw [integral_rpow (Or.inl (by linarith : -1<δ-1)),show δ-1+1=δ by ring,Real.one_rpow]
    rw [Nat.cast_one,hInt] at hi
    calc _ ≤ ∑ n∈Icc 1 q,f n := by
                apply sum_le_sum; intro n hn
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_Icc.mp hn).1)
                linarith only [hstrip]
         _ ≤ 1+((q:ℝ)^δ-1)/δ := by rw [he]; gcongr
         _ ≤ _ := by
              have hh := Real.one_le_rpow hq' hδ.le
              rw [mul_add,mul_one,mul_one_div]
              linarith only [hh,show ((q:ℝ)^δ-1)/δ≤(q:ℝ)^δ/δ by gcongr; linarith]
  · calc _ ≤ ∑ _n∈Icc 1 q,(1:ℝ) := by
                apply sum_le_sum; intro n hn
                exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (mem_Icc.mp hn).1) (neg_nonpos.mpr hσ)
         _ = (q:ℝ) := by simp
         _ ≤ (q:ℝ)^δ := by simpa using Real.rpow_le_rpow_of_exponent_le hq' (le_of_not_ge hd)
         _ ≤ _ := le_mul_of_one_le_right (by positivity) (by have := one_div_pos.mpr hδ; linarith)

/-- Conductor-uniform near-one growth of Dirichlet L-functions for every
fixed positive strip multiplier `R`. -/
theorem LFunction_vinogradov_near_one {R : ℝ} (hR : 0<R) :
    ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {s : ℂ},0<s.re → 2≤|s.im| → 1-R/(Real.log |s.im|)^(2/3:ℝ)≤s.re →
      ‖χ.LFunction s‖≤D*(q:ℝ)^(R/(Real.log |s.im|)^(2/3:ℝ))*(Real.log |s.im|)^(2/3:ℝ) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_near_one hR.le
  let B := (Real.log 2)^(2/3:ℝ)
  have hB : 0<B := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨C+1/R+1/B,by positivity,?_⟩
  intro q _ χ s hσ ht hstrip
  let L := (Real.log |s.im|)^(2/3:ℝ)
  have hlog := Real.log_pos (by linarith : 1 < |s.im|)
  have hL : 0<L := Real.rpow_pos_of_pos hlog _
  have hBL : B≤L := Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) ht) (by norm_num)
  have hq : 1≤q := Nat.pos_of_ne_zero (NeZero.ne _)
  have h := periodicLFunction_le_of_regular_hurwitz χ (norm_char_le_one χ) s (fun a ha => H ha hσ ht hstrip)
  have hinit := first_period_power_sum_le hq (div_pos hR hL) hσ.le hstrip
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq : (1:ℝ)≤q) (show 1-s.re≤R/L by linarith only [hstrip])
  apply h.trans
  apply (add_le_add hinit (mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*L))).trans
  have he : 1/(R/L)=L/R := by field_simp
  change (q:ℝ)^(R/L)*(1+1/(R/L))+(q:ℝ)^(R/L)*(C*L)≤(C+1/R+1/B)*(q:ℝ)^(R/L)*L
  rw [he]
  have h1 : 1≤L/B := (le_div_iff₀ hB).mpr (by simpa)
  calc _ = (q:ℝ)^(R/L)*(1+L/R+C*L) := by ring
       _ ≤ (q:ℝ)^(R/L)*(L/B+L/R+C*L) := by gcongr
       _ = _ := by ring

/-- Enlarging the near-one strip by a two-thirds power of the iterated
logarithm gives the corresponding bound uniform in the modulus. -/
theorem LFunction_vinogradov_loglog_strip :
    ∃ K : ℝ,0<K ∧ ∀ {R : ℝ},0<R → ∃ D : ℝ,0<D ∧ ∀ {q : ℕ} [NeZero q]
      (χ : DirichletCharacter ℂ q) {s : ℂ},0<s.re → 10≤|s.im| →
      let L := Real.log |s.im|
      let δ := R*(Real.log L)^(2/3:ℝ)/L^(2/3:ℝ)
      1-δ≤s.re → ‖χ.LFunction s‖≤D*(q:ℝ)^δ*L^(2/3+K*R^(3/2:ℝ):ℝ) := by
  obtain ⟨K,hK,C,hC,H⟩ := hurwitzZeta_sub_initial_loglog_strip
  refine ⟨K,hK,?_⟩
  intro R hR
  let B := (Real.log (Real.log 10))^(2/3:ℝ)
  have h₁ : 1<Real.log 10 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hB : 0<B := Real.rpow_pos_of_pos (Real.log_pos h₁) _
  refine ⟨C+1+1/(R*B),by positivity,?_⟩
  intro q _ χ s hσ ht
  let L := Real.log |s.im|
  let U := L^(2/3:ℝ)
  let V := L^(2/3+K*R^(3/2:ℝ):ℝ)
  let A := (Real.log L)^(2/3:ℝ)
  let δ := R*A/U
  change 1-δ≤s.re → ‖χ.LFunction s‖≤(C+1+1/(R*B))*(q:ℝ)^δ*V
  intro hstrip
  have hL : Real.log 10≤L := Real.log_le_log (by norm_num) ht
  have hL' := h₁.trans_le hL
  have hU : 1≤U := Real.one_le_rpow hL'.le (by norm_num)
  have hUV : U≤V := Real.rpow_le_rpow_of_exponent_le hL'.le (by have := mul_pos hK (Real.rpow_pos_of_pos hR (3/2:ℝ)); linarith)
  have hBA : B≤A := Real.rpow_le_rpow (Real.log_nonneg h₁.le) (Real.log_le_log (by linarith) hL) (by norm_num)
  have hA := hB.trans_le hBA
  have hU₀ := zero_lt_one.trans_le hU
  have hδ : 0<δ := div_pos (mul_pos hR hA) hU₀
  have heT : Real.exp 1≤|s.im| := by linarith [Real.exp_one_lt_d9]
  have h := periodicLFunction_le_of_regular_hurwitz χ (norm_char_le_one χ) s
    (fun a ha => H hR.le ha hσ heT hstrip)
  have hq : 1≤q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hinit := first_period_power_sum_le hq hδ hσ.le hstrip
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq : (1:ℝ)≤q) (show 1-s.re≤δ by linarith)
  have hrec : 1/δ≤V/(R*B) := by
    rw [show 1/δ=U/(R*A) by dsimp [δ]; field_simp]
    exact div_le_div₀ (by positivity) hUV (mul_pos hR hB) (mul_le_mul_of_nonneg_left hBA hR.le)
  apply h.trans
  apply (add_le_add hinit (mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*V))).trans
  change (q:ℝ)^δ*(1+1/δ)+(q:ℝ)^δ*(C*V)≤_
  calc _ = (q:ℝ)^δ*(1+1/δ+C*V) := by ring
       _ ≤ (q:ℝ)^δ*(V+V/(R*B)+C*V) := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hU.trans hUV) hrec) le_rfl) (by positivity)
       _ = _ := by ring

end AnalyticNumberTheory.DirichletLFunctions
