import AnalyticNumberTheory.RiemannZeta.HurwitzCorrectionOscillation

/-!
# The first correction against the complete finite Hurwitz polynomial

The first direct frequency is isolated. Two frequencies adjacent to the
saddle are estimated by the length of the block; the remaining frequencies
contribute the summable logarithmic spacing kernel.
-/
noncomputable section
open Real Complex Finset MeasureTheory Set
open scoped ComplexConjugate Interval
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem square_weight {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i : Bool×ℕ)
    {k : ℕ} (hk : 1≤k) (hk' : k≤ i.2+1) (hi : 1≤ i.2) :
    (Real.sqrt (hurwitzWaveFrequency a i))⁻¹≤2*(Real.sqrt k)⁻¹ := by
  have hm : (1:ℝ)≤ i.2 := by exact_mod_cast hi
  have hkm : (k:ℝ)≤(i.2:ℝ)+1 := by exact_mod_cast hk'
  have H := Real.sqrt_le_sqrt (show (k:ℝ)≤4*hurwitzWaveFrequency a i by linarith [(hurwitzWaveFrequency_mem ha i).1])
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at H
  rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr (hurwitzWaveFrequency_pos ha.1 _))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))]
  linarith only [H]

private def blockCost (a C : ℝ) (j m : ℕ) :=
  (if m=0 then C*(Real.sqrt a)⁻¹ else 0)+(if m+1=j then C else 0)+(if m=j then C else 0)+
    C*criticalCosineGap j (m+1)

private theorem norm_clipped_wave_correction : ∃ C : ℝ,0<C ∧ ∀ {a u b c : ℝ} {j : ℕ} (i : Bool×ℕ),
    a∈Ioc (0:ℝ) 1 → 2≤j → b≤c → hardyCutoff j≤b → c≤hardyCutoff (j+1) → |(j:ℝ)-u|≤1 →
    (∀t∈Icc b c,2*hardySaddleRoot t-u-j∈Icc (0:ℝ) 2) →
    ‖∫t in b..c,conj (enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t)*
        hurwitzCorrectionAmplitude j u (hardySaddleRoot t)‖ ≤ blockCost a C j i.2 := by
  obtain ⟨D,hD,H⟩ := hurwitz_correction_wave_nonstationary
  obtain ⟨E,hE,J⟩ := hurwitzCorrectionAmplitude_height_bounds
  let C := D/Real.log 2+48*E+D
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hC : 0<C := by dsimp [C];positivity
  have hCD : D≤C := by dsimp [C];linarith [div_pos hD hlog]
  have hCE : 48*E≤C := by dsimp [C];linarith [div_pos hD hlog]
  have hCL : D/Real.log 2≤C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro a u b c j i ha hj hbc hb hc hju harg
  let G := fun t => hurwitzCorrectionAmplitude j u (hardySaddleRoot t)
  let r := hurwitzWaveFrequency a i
  let k := i.2+1
  let v := max b (hurwitzWaveEntry a i)
  have he (t : ℝ) : conj (enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t)*G t=
      enteredWave (hurwitzWaveEntry a i) (fun t => conj (hurwitzWave a i t)*G t) t := by
    change conj (if _ then _ else _)*_=if _ then _ else _
    split_ifs <;>simp
  change ‖∫ t in b..c,conj (enteredWave _ _ t)*G t‖≤_
  simp_rw [he];rw [integral_enteredWave hbc]
  have hgap : 0≤criticalCosineGap j k := by unfold criticalCosineGap;split_ifs <;>positivity
  have hcost : 0≤blockCost a C j i.2 := by unfold blockCost;split_ifs <;>positivity
  by_cases hv : v≤c
  swap
  · rw [min_eq_left (le_of_not_ge hv),intervalIntegral.integral_same,norm_zero];exact hcost
  rw [min_eq_right hv]
  have hvb : b≤v := le_max_left ..
  have hj₁ : 1≤j := by omega
  have hjr : (2:ℝ)≤j := by exact_mod_cast hj
  have hjp : 0<(j:ℝ) := by linarith
  have hr := hurwitzWaveFrequency_pos ha.1 i
  have hp : 0<b := (hardyCutoff_pos hj₁).trans_le hb
  have hx {t : ℝ} (ht : t∈Icc v c) : (j:ℝ)≤hardySaddleRoot t :=
    (hardySaddleRoot_mem (show t∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨hb.trans (hvb.trans ht.1),ht.2.trans hc⟩)).1
  have harg' (t : ℝ) (ht : t∈Icc v c) := harg t ⟨hvb.trans ht.1,ht.2⟩
  have hw (t : ℝ) (ht : t∈Icc v c) : ‖G t‖≤E*(j:ℝ)^(-(1/2:ℝ)) := by
    have h := (J (hp.trans_le (hvb.trans ht.1)) (by linarith [hx ht] : 1≤hardySaddleRoot t) hju (harg' t ht)).1
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hjp (hx ht) (by norm_num)) hE.le)
  by_cases hfar : k<j
  · have hfreq : r≤(k:ℝ) := by simpa [k,r] using (hurwitzWaveFrequency_mem ha i).2
    have hkj : (k:ℝ)<j := by exact_mod_cast hfar
    have hsep := H i ha hj₁ (hfreq.trans_lt hkj) hv (hb.trans hvb) hc hju harg'
    have hlg : 0<Real.log j-Real.log k := sub_pos.mpr (Real.log_lt_log (Nat.cast_pos.mpr (Nat.succ_pos _)) hkj)
    have hlg' : Real.log j-Real.log k≤Real.log j-Real.log r := sub_le_sub_left (Real.log_le_log hr hfreq) _
    by_cases hm : i.2=0
    · have h₁ : (k:ℝ)=1 := by simp [k,hm]
      have hL : Real.log 2≤Real.log j-Real.log r := by rw [h₁,Real.log_one,sub_zero] at hlg';exact (Real.log_le_log (by norm_num) hjr).trans hlg'
      have hri : a≤r := by
        obtain ⟨d,m⟩ := i;cases d <;>dsimp [hurwitzWaveFrequency,r] <;>linarith [Nat.cast_nonneg (α:=ℝ) m,ha.2]
      have hA := inv_anti₀ (Real.sqrt_pos.mpr ha.1) (Real.sqrt_le_sqrt hri)
      have hJ : (j:ℝ)^(-(1/2:ℝ))≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have hle : D*(j:ℝ)^(-(1/2:ℝ))*(Real.sqrt r)⁻¹/(Real.log j-Real.log r)≤
          C*(Real.sqrt a)⁻¹ := by
        apply (div_le_div₀ (by positivity : 0≤D*1*(Real.sqrt a)⁻¹)
          (mul_le_mul (mul_le_mul_of_nonneg_left hJ hD.le) hA (by positivity) (by positivity)) hlog hL).trans
        calc D*1*(Real.sqrt a)⁻¹/Real.log 2 = (D/Real.log 2)*(Real.sqrt a)⁻¹ := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_right hCL (by positivity)
      apply (hsep.trans hle).trans
      unfold blockCost;rw [if_pos hm]
      split_ifs <;>linarith only [mul_nonneg hC.le hgap,hC.le]
    · have hm' := Nat.one_le_iff_ne_zero.mpr hm
      have hA := square_weight ha i (k:=k) (Nat.succ_pos _) le_rfl hm'
      have hle : D*(j:ℝ)^(-(1/2:ℝ))*(Real.sqrt r)⁻¹/(Real.log j-Real.log r)≤C*criticalCosineGap j k := by
        rw [criticalCosineGap,if_neg (Ne.symm (Nat.ne_of_lt hfar)),
          abs_of_neg (sub_neg.mpr (Real.log_lt_log (Nat.cast_pos.mpr (Nat.succ_pos _)) hkj)),neg_sub,
          Real.rpow_neg (Nat.cast_nonneg k),←Real.sqrt_eq_rpow]
        apply (div_le_div₀ (by positivity : 0≤D*(j:ℝ)^(-(1/2:ℝ))*(2*(Real.sqrt k)⁻¹))
          (mul_le_mul_of_nonneg_left hA (by positivity)) hlg hlg').trans
        calc _ = D*(2*(j:ℝ)^(-(1/2:ℝ))*(Real.sqrt k)⁻¹/(Real.log j-Real.log k)) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)
      apply (hsep.trans hle).trans
      unfold blockCost;split_ifs <;>linarith only [hC.le,mul_nonneg hC.le (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  · have hentry : hurwitzWaveEntry a i≤c := (le_max_right ..).trans hv
    have hcpos : 0<c := hp.trans_le hbc
    have hbnd := (hurwitzWaveEntry_le_iff ha.1 hcpos.le i).mp hentry
    have hfreq : r≤(j:ℝ)+1 := hbnd.trans (hardySaddleRoot_mem (show c∈Icc (hardyCutoff j) (hardyCutoff (j+1)) from ⟨hb.trans hbc,hc⟩)).2
    have hm : i.2≤j := by
      have h := (hurwitzWaveFrequency_mem ha i).1.trans_le hfreq
      have h' : i.2<j+1 := by exact_mod_cast h
      omega
    have hkj : j≤k := Nat.le_of_not_gt hfar
    have hm₁ : 1≤ i.2 := by dsimp [k] at hkj;omega
    have hA := square_weight ha i hj₁ hkj hm₁
    have hJ := intervalIntegral.norm_integral_le_of_norm_le_const (a:=v) (b:=c)
      (C:=(2*(Real.sqrt j)⁻¹)*(E*(j:ℝ)^(-(1/2:ℝ)))) (f:=fun t => conj (hurwitzWave a i t)*G t) (fun t ht=>by
        rw [uIoc_of_le hv] at ht;rw [norm_mul,Complex.norm_conj,norm_hurwitzWave]
        exact mul_le_mul hA (hw t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity))
    rw [abs_of_nonneg (sub_nonneg.mpr hv)] at hJ
    have hlen : c-v≤24*(j:ℝ) := (sub_le_sub hc (hb.trans hvb)).trans (hardyCutoff_step_length hj₁)
    apply (hJ.trans (mul_le_mul_of_nonneg_left hlen (by positivity))).trans
    rw [Real.rpow_neg hjp.le,←Real.sqrt_eq_rpow]
    have hnum : 2*(Real.sqrt j)⁻¹*(E*(Real.sqrt j)⁻¹)*(24*(j:ℝ))=48*E := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hjp)];nlinarith only [Real.sq_sqrt hjp.le]
    rw [hnum]
    apply hCE.trans
    have hh : i.2+1=j ∨ i.2=j := by dsimp [k] at hkj;omega
    rcases hh with h|h <;>unfold blockCost <;>rw [if_pos h] <;>split_ifs <;>
      linarith only [mul_nonneg hC.le hgap,hC.le,mul_nonneg hC.le (inv_nonneg.mpr (Real.sqrt_nonneg a))]

private theorem sum_succ (N : ℕ) (f : ℕ→ℝ) :
    (∑m∈range N,f (m+1))=∑m∈Finset.Icc 1 N,f m := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]

/-- Oscillatory cross term for the entire polynomial on a partial pair of
cutoff intervals. A uniform constant suffices for every shift and length. -/
theorem hurwitz_correction_polynomial_block : ∃ C : ℝ,0<C ∧ ∀ {a u b c : ℝ} {j : ℕ} (N : ℕ),
    a∈Ioc (0:ℝ) 1 → 2≤j → b≤c → hardyCutoff j≤b → c≤hardyCutoff (j+1) → |(j:ℝ)-u|≤1 →
    (∀t∈Icc b c,2*hardySaddleRoot t-u-j∈Icc (0:ℝ) 2) →
    ‖∫t in b..c,conj (hurwitzWaveSum a N t)*hurwitzCorrectionAmplitude j u (hardySaddleRoot t)‖ ≤
      C*((Real.sqrt a)⁻¹+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n) := by
  obtain ⟨C,hC,H⟩ := norm_clipped_wave_correction
  refine ⟨2*C,by positivity,?_⟩
  intro a u b c j N ha hj hbc hb hc hju harg
  let g := fun t => hurwitzCorrectionAmplitude j u (hardySaddleRoot t)
  let f := fun (i : Bool×ℕ) t => conj (enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t)*g t
  have hG : ContinuousOn g (uIcc b c) := by
    rw [uIcc_of_le hbc]
    intro t ht
    have hp := (hardyCutoff_pos (by omega : 0<j)).trans_le (hb.trans ht.1)
    have hx := hardySaddleRoot_pos hp
    have hh := (differentiableOn_hurwitzCorrectionAmplitude (j:ℝ) u _ hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact (hh.continuousAt.comp (f:=hardySaddleRoot) (hardySaddleRoot_hasDerivAt hp).continuousAt).continuousWithinAt
  have hi (i : Bool×ℕ) : IntervalIntegrable (f i) volume b c := by
    have he (t : ℝ) : conj (enteredWave (hurwitzWaveEntry a i) (hurwitzWave a i) t)=
        enteredWave (hurwitzWaveEntry a i) (fun t=>conj (hurwitzWave a i t)) t := by
      change conj (if _ then _ else _)=if _ then _ else _;split_ifs <;>simp
    dsimp only [f];simp_rw [he]
    exact (enteredWave_intervalIntegrable _ (Complex.continuous_conj.comp (continuous_hurwitzWave a i)) _ _).mul_continuousOn hG
  have he (t : ℝ) : conj (hurwitzWaveSum a N t)*g t=∑i∈hurwitzWaveIndices N,f i t := by
    rw [hurwitzWaveSum,map_sum,sum_mul]
  change ‖∫t in b..c,conj (hurwitzWaveSum a N t)*g t‖≤_
  simp_rw [he];rw [intervalIntegral.integral_finsetSum (f:=f) (fun i _ => hi i)]
  apply (norm_sum_le ..).trans
  apply (sum_le_sum (fun i _ => H i ha hj hbc hb hc hju harg)).trans
  rw [hurwitzWaveIndices,sum_product (f:=fun i : Bool×ℕ => blockCost a C j i.2),Fintype.sum_bool]
  have hsum : (∑m∈range N,blockCost a C j m)≤C*((Real.sqrt a)⁻¹+2+∑n∈Finset.Icc 1 N,criticalCosineGap j n) := by
    have hsel (m : ℕ) : m+1=j ↔ m=j-1 := by omega
    simp only [blockCost,hsel,sum_add_distrib,sum_ite_eq',←mul_sum]
    rw [sum_succ N (criticalCosineGap j)]
    split_ifs <;>linarith only [hC.le,mul_nonneg hC.le (inv_nonneg.mpr (Real.sqrt_nonneg a))]
  dsimp;linarith only [hsum]

end AnalyticNumberTheory.RiemannZeta
