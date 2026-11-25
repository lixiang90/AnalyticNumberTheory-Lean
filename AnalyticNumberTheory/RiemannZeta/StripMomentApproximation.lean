import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.AnalyticTools.Summation.Abel

/-!
# Effective estimates for the long polynomial in a vertical strip

On a dyadic interval one can take the polynomial length comparable to
the height. The pointwise error and the trivial polynomial bound then
control the difference of the squared moduli.
-/
open Real Complex Finset MeasureTheory Set
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

/-- A uniform upper bound for partial sums of n^(-p), for fixed 0<p<1. -/
theorem sum_nat_neg_rpow_strip_bound {p : ℝ} (hp : 0<p) (hp' : p<1) :
    ∃ C : ℝ,0<C ∧ ∀ {N : ℕ},1≤N →
      (∑n∈Finset.Icc 1 N,(n:ℝ)^(-p))≤C*(N:ℝ)^(1-p) := by
  refine ⟨1/(1-p)+|powerSumConstant p|+1,by positivity,?_⟩
  intro N hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have h := abs_sum_rpow_neg_sub_le_of_pos hp hp'.ne hn
  rw [Nat.floor_natCast] at h
  have h₁ := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr hp.le)
  have h₂ := Real.one_le_rpow hn (sub_nonneg.mpr hp'.le)
  have h₃ := mul_le_mul_of_nonneg_left h₂ (abs_nonneg (powerSumConstant p))
  simp only [div_eq_mul_inv] at h ⊢
  linarith only [(abs_le.mp h).2,h₁,h₂,h₃,le_abs_self (powerSumConstant p)]

/-- Tail of the diagonal series at an explicit finite cutoff. -/
theorem abs_zeta_diagonal_tail_le {p : ℝ} (hp : 1<p) {N : ℕ} (hN : 1≤N) :
    |(∑n∈Finset.Icc 1 N,(n:ℝ)^(-p))-(riemannZeta (p:ℂ)).re|≤
      (1+1/(p-1))*(N:ℝ)^(1-p) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have h := abs_sum_rpow_neg_sub_le_of_pos (by linarith : 0<p) hp.ne' hn
  rw [Nat.floor_natCast,(powerSumConstant_eq_tsum_and_zeta hp).2] at h
  let S := ∑n∈Finset.Icc 1 N,(n:ℝ)^(-p)
  let Z := (riemannZeta (p:ℂ)).re
  let A := (N:ℝ)^(1-p)
  have hA : 0≤A := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcmp : (N:ℝ)^(-p)≤A := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  change |S-(A/(1-p)+Z)|≤_ at h
  change |S-Z|≤_*A
  calc |S-Z| = |(S-(A/(1-p)+Z))+A/(1-p)| := by congr 1;ring
       _ ≤ |S-(A/(1-p)+Z)|+|A/(1-p)| := abs_add_le ..
       _ ≤ A+A/(p-1) := by
         rw [abs_div,abs_of_nonneg hA,abs_of_nonpos (by linarith : 1-p≤0),neg_sub]
         linarith
       _ = _ := by ring

/-- The size of a long polynomial and of its approximation error on a
dyadic interval; both constants depend only on the fixed real part. -/
theorem strip_long_polynomial_bounds {σ : ℝ} (hσ : 0<σ) (hσ' : σ<1) :
    ∃ C : ℝ,0<C ∧ ∀ {N : ℕ} {t : ℝ}, 1≤N → 1≤t → (N:ℝ)/2≤t → t≤2*N →
    let s := (σ:ℂ)+(t:ℂ)*I
    let P := dirichletPoly (fun _ => 1) N s
    ‖riemannZeta s-P‖≤C*(N:ℝ)^(-σ) ∧ ‖P‖≤C*(N:ℝ)^(1-σ) ∧ ‖riemannZeta s‖≤2*C*(N:ℝ)^(1-σ) := by
  obtain ⟨K,hK,H⟩ := riemannZeta_approx_dirichletPoly_sub_bound (by norm_num : (0:ℝ)<2)
    (by linarith [Real.two_le_pi] : (2:ℝ)<2*Real.pi)
  obtain ⟨D,hD,h⟩ := sum_nat_neg_rpow_strip_bound hσ hσ'
  let C := 2+K+D
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro N t hN ht hNt htN s P
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hp : 0<(N:ℝ) := by linarith
  have H' := H hN hσ (by rwa [abs_of_pos (by linarith : 0<t)]) (by rwa [abs_of_pos (by linarith : 0<t)])
  have hpow : (N:ℝ)^(1-σ)=N*(N:ℝ)^(-σ) := by rw [sub_eq_add_neg,Real.rpow_add hp,Real.rpow_one]
  have he : ‖riemannZeta s-P‖≤C*(N:ℝ)^(-σ) := by
    rw [abs_of_pos (by linarith : 0<t),hpow] at H'
    have hd : (N:ℝ)*(N:ℝ)^(-σ)/t≤2*(N:ℝ)^(-σ) := (div_le_iff₀ (by linarith)).mpr
      (by nlinarith only [mul_le_mul_of_nonneg_right hNt (Real.rpow_nonneg hp.le (-σ))])
    dsimp only [s,P,C];linarith only [H',hd,mul_nonneg hD.le (Real.rpow_nonneg hp.le (-σ))]
  have hpoly : ‖P‖≤C*(N:ℝ)^(1-σ) := by
    change ‖∑n∈Finset.Icc 1 N,(1:ℂ)*(n:ℂ)^(-s)‖≤_
    apply (norm_sum_le ..).trans
    simp only [one_mul]
    have hh : (∑n∈Finset.Icc 1 N,‖(n:ℂ)^(-s)‖)=∑n∈Finset.Icc 1 N,(n:ℝ)^(-σ) := by
      apply sum_congr rfl
      intro n hn';rw [Complex.norm_natCast_cpow_of_pos (mem_Icc.mp hn').1];simp [s]
    rw [hh];apply (h hN).trans;apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
    dsimp [C];linarith
  refine ⟨he,hpoly,?_⟩
  have hcmp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (by linarith : -σ≤1-σ)) hC.le
  linarith only [norm_sub_norm_le (riemannZeta s) P,he,hpoly,hcmp]

/-- Polynomial growth of zeta sufficient to integrate the relative
Stirling error in the reflected moment. -/
theorem norm_riemannZeta_strip_height {σ : ℝ} (hσ : 0<σ) (hσ' : σ<1) :
    ∃ C : ℝ,0<C ∧ ∀ {t : ℝ},1≤t → ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖≤C*t^(1-σ) := by
  obtain ⟨C,hC,h⟩ := strip_long_polynomial_bounds hσ hσ'
  refine ⟨2*C*2^(1-σ),by positivity,?_⟩
  intro t ht
  let N := ⌊t⌋₊+1
  have hNt : (N:ℝ)≤2*t := by dsimp [N];push_cast;linarith [Nat.floor_le (by linarith : 0≤t)]
  have htN : t≤(N:ℝ) := by dsimp [N];push_cast;linarith [Nat.lt_floor_add_one t]
  have hh := (h (N:=N) (by dsimp [N];omega) ht (by linarith) (by linarith)).2.2
  apply hh.trans
  rw [mul_assoc (2*C),←Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by linarith : 0≤t)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hNt (by linarith)) (by positivity)

end AnalyticNumberTheory.RiemannZeta
