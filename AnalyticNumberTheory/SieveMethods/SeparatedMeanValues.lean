import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-!
# Mean squares at separated real frequencies

Integrating the off-diagonal terms produces one Hilbert form at each
endpoint. No arithmetic condition on the frequencies is needed.
-/

open Complex Real Finset MeasureTheory
open scoped Classical
namespace AnalyticNumberTheory.SieveMethods

private noncomputable def phase (x t : ℝ) : ℂ := Complex.exp (I*(x:ℂ)*t)

private theorem phase_pair (x y t : ℝ) :
    phase x t*star (phase y t) = phase (x-y) t := by
  simp only [phase,Complex.star_def,← Complex.exp_conj,map_mul,Complex.conj_I,Complex.conj_ofReal,← Complex.exp_add]
  congr 1; push_cast; ring

private theorem phase_norm (x t : ℝ) : ‖phase x t‖ = 1 := by simp [phase,Complex.norm_exp]

private theorem phase_deriv (x t : ℝ) : HasDerivAt (phase x) (phase x t*(I*(x:ℂ))) t := by
  change HasDerivAt (fun u : ℝ => Complex.exp (I*(x:ℂ)*u)) _ t
  simpa [phase] using (Complex.ofRealCLM.hasDerivAt (x:=t)).const_mul (I*(x:ℂ)) |>.cexp

/-- Montgomery–Vaughan mean value inequality for arbitrary separated
real frequencies. The error is uniform in both endpoints. -/
theorem separated_frequency_mean_square {ι : Type*} (S : Finset ι) (x : ι → ℝ) (c : ι → ℂ)
    {δ : ℝ} (hδ : 0<δ) (hsep : ∀ i∈S, ∀ j∈S, i≠j → δ≤|x i - x j|) (a b : ℝ) :
    |(∫ t in a..b, ‖∑ i ∈ S, c i*Complex.exp (I*(x i:ℂ)*t)‖^2)-
      (b-a)*(∑ i ∈ S, ‖c i‖^2)| ≤ 2*π*δ⁻¹*(∑ i ∈ S, ‖c i‖^2) := by
  classical
  let v (i : ι) (t : ℝ) := c i*phase (x i) t
  let A (i j : ι) (t : ℝ) := v i t*star (v j t)
  let D := ∑ i ∈ S, ‖c i‖^2
  let B (t : ℝ) := ∑ i ∈ S, ∑ j ∈ S, if i=j then (0:ℂ) else A i j t/((x i-x j:ℝ):ℂ)
  let F (t : ℝ) := ∑ i ∈ S, ∑ j ∈ S, if i=j then (t:ℂ)*(‖c i‖^2:ℝ) else -I*(A i j t/((x i-x j:ℝ):ℂ))
  have hA (i j : ι) (t : ℝ) : A i j t = c i*star (c j)*phase (x i-x j) t := by
    simp only [A,v,star_mul,← phase_pair]
    ring
  have hn (z : ℂ) : z*star z = ((‖z‖^2:ℝ):ℂ) := by rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have hdiag (i : ι) (t : ℝ) : A i i t = ((‖c i‖^2:ℝ):ℂ) := by
    rw [hA,sub_self]; simp only [phase,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one]; exact hn _
  have hterm (i) (hi : i∈S) (j) (hj : j∈S) (t : ℝ) :
      HasDerivAt (fun u : ℝ => if i=j then (u:ℂ)*(‖c i‖^2:ℝ) else -I*(A i j u/((x i-x j:ℝ):ℂ))) (A i j t) t := by
    by_cases he : i=j
    · subst j; simp only [ite_true,hdiag]; convert (Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const ((‖c i‖^2:ℝ):ℂ) using 1 <;> push_cast <;> simp
    · have hd : x i-x j ≠ 0 := by intro h; have hh := hsep i hi j hj he; rw [h,abs_zero] at hh; linarith
      have hd' : ((x i-x j:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
      simp only [he,ite_false,hA]
      convert ((((phase_deriv (x i-x j) t).const_mul (c i*star (c j))).div_const ((x i-x j:ℝ):ℂ)).const_mul (-I)) using 1
      field_simp
      ring_nf
      simp [Complex.I_sq]
  have hnorm (t : ℝ) : ((‖∑ i ∈ S, v i t‖^2:ℝ):ℂ) = ∑ i ∈ S, ∑ j ∈ S, A i j t := by
    rw [← hn,star_sum,Finset.sum_mul]
    exact sum_congr rfl fun i _ => Finset.mul_sum ..
  have hderiv (t : ℝ) : HasDerivAt F ((‖∑ i ∈ S, v i t‖^2:ℝ):ℂ) t := by
    rw [hnorm]; exact HasDerivAt.fun_sum fun i hi => HasDerivAt.fun_sum fun j hj => hterm i hi j hj t
  have hc : Continuous (fun t : ℝ => ((‖∑ i ∈ S, v i t‖^2:ℝ):ℂ)) := by
    dsimp only [v,phase]; fun_prop
  have hin := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b) (fun t _ => hderiv t) (hc.intervalIntegrable ..)
  rw [intervalIntegral.integral_ofReal] at hin
  have hF (t : ℝ) : F t = (t:ℂ)*(D:ℂ)-I*B t := by
    have hi (i j : ι) : (if i=j then (t:ℂ)*(‖c i‖^2:ℝ) else -I*(A i j t/((x i-x j:ℝ):ℂ))) =
        (if i=j then (t:ℂ)*(‖c i‖^2:ℝ) else 0)- I*(if i=j then 0 else A i j t/((x i-x j:ℝ):ℂ)) := by
      split_ifs <;> ring
    simp only [F,B,D,hi,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq,Complex.ofReal_sum]
    congr 1
    exact (sum_congr rfl (fun i hi => if_pos hi)).trans (Finset.mul_sum ..).symm
  have hB (t : ℝ) : ‖B t‖ ≤ π*δ⁻¹*D := by
    have h := hilbert_inequality_separated S x hδ hsep (fun i => v i t)
    simpa only [B,A,v,norm_mul,phase_norm,mul_one,D] using h
  let J := ∫ t in a..b, ‖∑ i ∈ S, v i t‖^2
  have he : ((J-(b-a)*D:ℝ):ℂ) = -I*(B b-B a) := by
    push_cast; change (J:ℂ)-_ = _
    change (J:ℂ) = _ at hin
    rw [hin,hF,hF]; ring
  change |J-(b-a)*D| ≤ _
  rw [← Real.norm_eq_abs,← Complex.norm_real,he,norm_mul,norm_neg,Complex.norm_I,one_mul]
  linarith only [norm_sub_le (B b) (B a),hB b,hB a]

end AnalyticNumberTheory.SieveMethods
