import AnalyticNumberTheory.RiemannZeta.HurwitzGeometricContours
import AnalyticNumberTheory.RiemannZeta.HurwitzFourierExpansion

/-!
# Summing the rotated tails at a half-integer cutoff

On each of the upper and lower contours the Fourier oscillations form a
geometric progression. The identity gives the exact combined contribution
of all frequencies above any given cutoff.
-/
noncomputable section
open Real Complex MeasureTheory Filter Finset Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem half_grid_exp (m : ℕ) {k : ℝ} (hk : k=1 ∨ k= -1) :
    Complex.exp (2*Real.pi*(k:ℂ)*((m:ℂ)+1/2)*I)= -1 := by
  have h : Complex.exp (2*Real.pi*((m:ℂ)+1/2)*I)= -1 := by
    rw [show 2*Real.pi*((m:ℂ)+1/2)*I=(m:ℂ)*(2*Real.pi*I)+Real.pi*I by ring,
      Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,Complex.exp_pi_mul_I,one_mul]
  rcases hk with rfl|rfl
  · simpa using h
  · rw [show 2*Real.pi*((-1:ℝ):ℂ)*((m:ℂ)+1/2)*I= -(2*Real.pi*((m:ℂ)+1/2)*I) by push_cast;ring,
      Complex.exp_neg,h];norm_num

/-- Factorization of each mode at the half-integer crossing. -/
theorem shiftedRayMode_eq_geometric (s : ℂ) (a b : ℝ) (m n : ℕ) (hb : b=a+m+1/2)
    {k : ℝ} (hk : k=1 ∨ k= -1) (v : ℝ) :
    hurwitzShift a (2*Real.pi*k*n)*fourierPowerMode s (2*Real.pi*k*n) (hurwitzRay b k v) =
      (hurwitzRay b k v)^(-s)*(hurwitzRayRatio k v)^n := by
  let z := hurwitzRay b k v
  have hk2 : (k:ℂ)^2=1 := by rcases hk with rfl|rfl <;> norm_num
  have hbase : Complex.exp (2*Real.pi*(k:ℂ)*(z-a)*I)=hurwitzRayRatio k v := by
    have he : 2*Real.pi*(k:ℂ)*(z-a)*I=2*Real.pi*k*((m:ℂ)+1/2)*I+
        ((2*Real.pi*v:ℝ):ℂ)*(-1+k*I) := by
      dsimp [z,hurwitzRay];rw [hb];push_cast;ring_nf;simp [I_sq,hk2];ring
    rw [he,Complex.exp_add,half_grid_exp m hk,hurwitzRayRatio,neg_one_mul]
  rw [hurwitzShift,fourierPowerMode,←mul_assoc,←Complex.exp_add,←hbase,←Complex.exp_nat_mul]
  change _*z^(-s)=z^(-s)*_
  rw [mul_comm];congr 2;push_cast;ring

/-- Geometric kernel for all frequencies strictly above q. -/
def hurwitzGeometricTail (s : ℂ) (b k : ℝ) (q : ℕ) :=
  (1+(k:ℂ)*I)*∫ v in Ioi (0:ℝ), (hurwitzRay b k v)^(-s)*(hurwitzRayRatio k v)^(q+1)/(1-hurwitzRayRatio k v)

theorem tendsto_hurwitz_shifted_tails {s : ℂ} (hσ : 0<s.re) (hσ' : s.re<1) {a b : ℝ}
    (m q : ℕ) (hb : b=a+m+1/2) (hb' : 0<b) {k : ℝ} (hk : k=1 ∨ k= -1) :
    Tendsto (fun N : ℕ => ∑ j∈range N,hurwitzShift a (k*hurwitzOmega (q+j))*hurwitzTail s (k*hurwitzOmega (q+j)) b)
      atTop (𝓝 (hurwitzGeometricTail s b k q)) := by
  let d : ℂ := 1+(k:ℂ)*I
  let z (v : ℝ) := hurwitzRay b k v
  have hω (j : ℕ) : k*hurwitzOmega (q+j)*k>0 := by
    rcases hk with rfl|rfl <;> simpa using hurwitzOmega_pos (q+j)
  have hω' : 0<2*Real.pi*k*k := by rcases hk with rfl|rfl <;> simp [Real.pi_pos]
  have hpow : AEStronglyMeasurable (fun v : ℝ => (z v)^(-s)) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.cpow_const (by unfold z hurwitzRay;fun_prop)
    intro v hv;left;dsimp only [z];rw [hurwitzRay_re];linarith [mem_Ioi.mp hv]
  have hInt : IntegrableOn (fun v : ℝ => ‖(z v)^(-s)‖*Real.exp (-2*Real.pi*v)) (Ioi 0) := by
    apply (integrable_fourierPowerMode_ray hσ.le hb' hω').norm.congr
    filter_upwards with v
    rw [fourierPowerMode,norm_mul,Complex.norm_exp,mul_I_re,im_ofReal_mul,hurwitzRay_im]
    dsimp [z];rw [mul_comm];congr 2;rcases hk with rfl|rfl <;> ring
  have H := (tendsto_hurwitzRay_geometric_integral k q hpow hInt).const_mul d
  apply H.congr'
  filter_upwards with N
  have he (j : ℕ) : k*hurwitzOmega (q+j)=2*Real.pi*k*(q+j+1:ℕ) := by unfold hurwitzOmega;push_cast;ring
  have ht (j : ℕ) : IntegrableOn (fun v : ℝ => hurwitzShift a (k*hurwitzOmega (q+j))*fourierPowerMode s (k*hurwitzOmega (q+j)) (z v)) (Ioi 0) :=
    (integrable_fourierPowerMode_ray hσ.le hb' (hω j)).const_mul _
  calc
    _ = d*∫ v in Ioi (0:ℝ),∑ j∈range N,hurwitzShift a (k*hurwitzOmega (q+j))*fourierPowerMode s (k*hurwitzOmega (q+j)) (z v) := by
      congr 1;apply integral_congr_ae
      filter_upwards with v
      dsimp only [z]
      simp_rw [he,shiftedRayMode_eq_geometric s a b m _ hb hk]
      rw [mul_sum];apply sum_congr rfl;intro j _
      rw [mul_assoc,←pow_add];congr 2;omega
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => ht j),mul_sum]
      apply sum_congr rfl;intro j _
      rw [hurwitzTail_eq_ray hσ hσ' hb' (hω j),integral_const_mul];ring
end AnalyticNumberTheory.RiemannZeta
