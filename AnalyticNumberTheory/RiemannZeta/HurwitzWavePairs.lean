import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalWaves
import AnalyticNumberTheory.RiemannZeta.ShiftedHardyKernels
import AnalyticNumberTheory.RiemannZeta.CriticalCosineOffDiagonal

/-!
# Integrated pairs of shifted critical-line waves

For distinct unit cells the logarithmic spacing survives an arbitrary
shift by a factor of at least a. The direct and reciprocal waves in the
same cell have a doubled Hardy phase with a possible stationary endpoint.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped ComplexConjugate Interval
namespace AnalyticNumberTheory.RiemannZeta

private def phaseExp (f : ℝ→ℝ) (t : ℝ) := Complex.exp ((f t:ℂ)*I)

private theorem norm_integral_neg_phase (f : ℝ→ℝ) (u v : ℝ) :
    ‖∫t in u..v,phaseExp (fun t => -f t) t‖=‖∫t in u..v,phaseExp f t‖ := by
  have h (t : ℝ) : phaseExp (fun t => -f t) t=conj (phaseExp f t) := by
    rw [phaseExp,phaseExp,←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I];push_cast;ring_nf
  simp_rw [h];rw [intervalIntegral.intervalIntegral_conj,Complex.norm_conj]

private theorem integral_pair_factor (a : ℝ) (i j : Bool×ℕ) (u v : ℝ) :
    let r := hurwitzWaveFrequency a i
    let s := hurwitzWaveFrequency a j
    ‖∫t in u..v,hurwitzWave a i t*conj (hurwitzWave a j t)‖=
      (Real.sqrt r)⁻¹*(Real.sqrt s)⁻¹*‖∫t in u..v,phaseExp (fun t => hurwitzWavePhase a i t-hurwitzWavePhase a j t) t‖ := by
  intro r s
  have h (t : ℝ) : hurwitzWave a i t*conj (hurwitzWave a j t)=
      ((((Real.sqrt r)⁻¹*(Real.sqrt s)⁻¹:ℝ):ℂ))*phaseExp (fun t => hurwitzWavePhase a i t-hurwitzWavePhase a j t) t := by
    dsimp only [hurwitzWave,phaseExp,r,s]
    rw [map_mul,←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    rw [sub_mul,Complex.exp_sub,div_eq_mul_inv,←Complex.exp_neg,show ∀z:ℂ,z*(-I)= -(z*I) by intro;ring]
    ring
  simp_rw [h];rw [intervalIntegral.integral_const_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

private theorem phase_difference_bound {a : ℝ} (i j : Bool×ℕ) (hi : 0<hurwitzWaveFrequency a i)
    (hj : 0<hurwitzWaveFrequency a j) {u v : ℝ} (hu : 0<u) (huv : u≤v)
    (hiu : hurwitzWaveEntry a i≤u) (hju : hurwitzWaveEntry a j≤u) (hij : i≠j)
    (hfreq : i.2≠j.2 → hurwitzWaveFrequency a i≠hurwitzWaveFrequency a j) :
    ‖∫t in u..v,phaseExp (fun t => hurwitzWavePhase a i t-hurwitzWavePhase a j t) t‖≤
      if i.2=j.2 then 8*Real.sqrt v else 4/|Real.log (hurwitzWaveFrequency a j)-Real.log (hurwitzWaveFrequency a i)| := by
  let r := hurwitzWaveFrequency a i
  let s := hurwitzWaveFrequency a j
  let d := Real.log s-Real.log r
  have hd (h : i.2≠j.2) : d≠0 := sub_ne_zero.mpr (fun he => hfreq h ((Real.log_injOn_pos hj hi he).symm))
  have hcross (w : ℝ) :
      ‖∫t in u..v,phaseExp (shiftedHardyPhase r s w) t‖ ≤ if i.2=j.2 then 8*Real.sqrt v else 4/|d| := by
    split_ifs with h
    · exact norm_integral_shiftedHardyPhase_le_sqrt r s w hu huv
    · exact norm_integral_shiftedHardyPhase_of_ne hi hj (hfreq h) w hiu hju huv
  have lin (h : i.2≠j.2) (w : ℝ) :
      ‖∫t in u..v,phaseExp (fun t => t*d+w) t‖ ≤ if i.2=j.2 then 8*Real.sqrt v else 4/|d| := by
    rw [if_neg h];exact norm_integral_linear_phase (hd h) w huv
  change _ ≤ if i.2=j.2 then 8*Real.sqrt v else 4/|d|
  obtain ⟨b,m⟩ := i;obtain ⟨c,n⟩ := j
  cases b <;>cases c
  · have h : m≠n := fun e => hij (by rw [e])
    have he : (fun t => hurwitzWavePhase a (false,m) t-hurwitzWavePhase a (false,n) t)=(fun t => t*d+0) := by
      funext t;dsimp [hurwitzWavePhase,r,s,d];ring
    rw [he];exact lin h 0
  · have he : (fun t => hurwitzWavePhase a (false,m) t-hurwitzWavePhase a (true,n) t)=shiftedHardyPhase r s (2*Real.pi*s*a) := by
      funext t;dsimp [hurwitzWavePhase,r,s,shiftedHardyPhase];ring
    rw [he];exact hcross _
  · let w := 2*Real.pi*r*a
    have he : (fun t => hurwitzWavePhase a (true,m) t-hurwitzWavePhase a (false,n) t)=(fun t => -shiftedHardyPhase r s w t) := by
      funext t;dsimp [hurwitzWavePhase,r,s,shiftedHardyPhase,w];ring
    rw [he,norm_integral_neg_phase];exact hcross w
  · have h : m≠n := fun e => hij (by rw [e])
    let w := 2*Real.pi*(r-s)*a
    have he : (fun t => hurwitzWavePhase a (true,m) t-hurwitzWavePhase a (true,n) t)=(fun t => -(t*d+w)) := by
      funext t;dsimp [hurwitzWavePhase,r,s,d,w];ring
    rw [he,norm_integral_neg_phase];exact lin h w

private theorem freq_range {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i : Bool×ℕ) :
    let k := (i.2:ℝ)+1
    k-1+a≤hurwitzWaveFrequency a i ∧ hurwitzWaveFrequency a i≤k ∧ a*k≤hurwitzWaveFrequency a i := by
  intro k
  obtain ⟨b,m⟩ := i;cases b <;>dsimp [hurwitzWaveFrequency,k] <;>refine ⟨?_,?_,?_⟩
  all_goals nlinarith [ha.2,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sub_nonneg.mpr ha.2)]

private theorem freq_gap {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i j : Bool×ℕ) (hne : i.2≠j.2) :
    a*|Real.log (j.2+1:ℕ)-Real.log (i.2+1:ℕ)|≤|Real.log (hurwitzWaveFrequency a j)-Real.log (hurwitzWaveFrequency a i)| := by
  have h {i j : Bool×ℕ} (hij : i.2<j.2) : a*(Real.log (j.2+1:ℕ)-Real.log (i.2+1:ℕ))≤
      Real.log (hurwitzWaveFrequency a j)-Real.log (hurwitzWaveFrequency a i) :=
    shifted_log_gap_lower ha (Nat.succ_pos _) (Nat.succ_lt_succ hij) (hurwitzWaveFrequency_pos ha.1 _)
      (by simpa using (freq_range ha i).2.1) (by simpa using (freq_range ha j).1)
  rcases lt_or_gt_of_ne hne with hh|hh
  · have hx := Real.log_lt_log (Nat.cast_pos.mpr (Nat.succ_pos i.2)) (Nat.cast_lt.mpr (Nat.succ_lt_succ hh))
    rw [abs_of_pos (sub_pos.mpr hx)];exact (h hh).trans (le_abs_self _)
  · rw [abs_sub_comm,abs_sub_comm (Real.log (hurwitzWaveFrequency a j))]
    have hx := Real.log_lt_log (Nat.cast_pos.mpr (Nat.succ_pos j.2)) (Nat.cast_lt.mpr (Nat.succ_lt_succ hh))
    rw [abs_of_pos (sub_pos.mpr hx)];exact (h hh).trans (le_abs_self _)

private theorem inv_sqrt_freq {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i : Bool×ℕ) :
    (Real.sqrt (hurwitzWaveFrequency a i))⁻¹≤a⁻¹*(Real.sqrt (i.2+1:ℕ))⁻¹ := by
  have hr := (freq_range ha i).2.2
  have hk : 0<(↑(i.2+1):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have h := Real.sqrt_le_sqrt (show a^2*(↑(i.2+1):ℝ)≤hurwitzWaveFrequency a i by
    push_cast;exact (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)] : a^2≤a) (by positivity)).trans hr)
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ha.1.le] at h
  simpa only [mul_inv_rev,mul_comm] using inv_anti₀ (mul_pos ha.1 (Real.sqrt_pos.mpr hk)) h

/-- Pairwise absolute cost for the shifted moment, including the possible
stationary terms in a common unit cell. -/
theorem hurwitz_wave_pair_bound {a : ℝ} (ha : a∈Ioc (0:ℝ) 1) (i j : Bool×ℕ) (hij : i≠j)
    {u v : ℝ} (hu : 0<u) (huv : u≤v) (hiu : hurwitzWaveEntry a i≤u) (hju : hurwitzWaveEntry a j≤u) :
    ‖∫t in u..v,hurwitzWave a i t*conj (hurwitzWave a j t)‖≤
      (if i.2=j.2 then 8*Real.sqrt v*a⁻¹^2*((i.2+1:ℕ):ℝ)⁻¹ else 0)+
        2*a⁻¹^3*criticalCosineGap (i.2+1) (j.2+1) := by
  let k := i.2+1
  let l := j.2+1
  let r := hurwitzWaveFrequency a i
  let s := hurwitzWaveFrequency a j
  let g := |Real.log (l:ℝ)-Real.log k|
  have ha' := ha.1
  have hk₀ : 0<(k:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hl₀ : 0<(l:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hg (h : i.2≠j.2) : 0<g := abs_pos.mpr (sub_ne_zero.mpr (fun e => h (by
    have hh := Real.log_injOn_pos (Set.mem_Ioi.mpr hl₀) (Set.mem_Ioi.mpr hk₀) e
    exact Nat.succ.inj (Nat.cast_inj.mp hh).symm)))
  have hgap (h : i.2≠j.2) : a*g≤|Real.log s-Real.log r| := freq_gap ha i j h
  have hfreq (h : i.2≠j.2) : r≠s := by
    intro he;have H := hgap h;rw [he,sub_self,abs_zero] at H;exact (not_lt_of_ge H) (mul_pos ha.1 (hg h))
  have H := phase_difference_bound i j (hurwitzWaveFrequency_pos ha.1 _) (hurwitzWaveFrequency_pos ha.1 _) hu huv hiu hju hij hfreq
  rw [integral_pair_factor]
  have H' := mul_le_mul (inv_sqrt_freq ha i) (inv_sqrt_freq ha j) (by positivity) (by positivity)
  apply (mul_le_mul H' H (norm_nonneg _) (by positivity)).trans
  by_cases he : i.2=j.2
  · simp only [he,ite_true,criticalCosineGap,mul_zero,add_zero]
    rw [show ∀z:ℝ,(a⁻¹*z⁻¹)*(a⁻¹*z⁻¹)=a⁻¹^2*(z^2)⁻¹ by intro z;ring,Real.sq_sqrt (Nat.cast_nonneg _)]
    ring_nf
    exact le_rfl
  · have hk : i.2+1≠j.2+1 := fun h => he (Nat.succ.inj h)
    simp only [if_neg he,zero_add,criticalCosineGap,if_neg hk]
    change _≤2*a⁻¹^3*(2*(k:ℝ)^(-(1/2:ℝ))*(l:ℝ)^(-(1/2:ℝ))/g)
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
    have he₁ := div_le_div_of_nonneg_left (by norm_num : 0≤(4:ℝ)) (mul_pos ha.1 (hg he)) (hgap he)
    apply (mul_le_mul_of_nonneg_left he₁ (by positivity : 0≤(a⁻¹*(Real.sqrt (k:ℝ))⁻¹)*(a⁻¹*(Real.sqrt (l:ℝ))⁻¹))).trans_eq
    ring

end AnalyticNumberTheory.RiemannZeta
