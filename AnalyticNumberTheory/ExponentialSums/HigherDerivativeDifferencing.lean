import AnalyticNumberTheory.ExponentialSums.VanDerCorput
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# Differencing estimates for the higher derivative test

The positive and negative powers of the shift must be averaged separately.
This produces the two terms in the classical higher derivative estimate.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem differencing_frequency_sums {H : ℕ} (hH : 1≤H) {lam α : ℝ}
    (hlam : 0<lam) (hα : 0≤α) (hα' : α≤1/2) :
    (∑ r∈Ico 1 H,((r:ℝ)*lam)^α) ≤ H*((H:ℝ)*lam)^α ∧
    (∑ r∈Ico 1 H,((r:ℝ)*lam)^(-α)) ≤ 2*H*((H:ℝ)*lam)^(-α) := by
  have hH' : 0<(H:ℝ) := by exact_mod_cast hH
  have hsub : Ico 1 H⊆Icc 1 H := fun r hr => mem_Icc.mpr ⟨(mem_Ico.mp hr).1,(mem_Ico.mp hr).2.le⟩
  constructor
  · calc
      _ ≤ ∑ _r∈Ico 1 H,((H:ℝ)*lam)^α := by
        apply sum_le_sum; intro r hr; gcongr; exact (mem_Ico.mp hr).2.le
      _ ≤ _ := by
        rw [sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Ico 1 H).card≤H by simp)) (by positivity)
  · let Z := ((H:ℝ)*lam)^(-α)
    have hZ : 0≤Z := by dsimp [Z]; positivity
    have hweight {r : ℕ} (hr : r∈Ico 1 H) : ((r:ℝ)*lam)^(-α)≤Z*Real.sqrt H*(Real.sqrt r)⁻¹ := by
      have hr' : 0<(r:ℝ) := by exact_mod_cast (mem_Ico.mp hr).1
      have hrH : (r:ℝ)≤H := by exact_mod_cast (mem_Ico.mp hr).2.le
      have hx : 1≤(H:ℝ)/r := (one_le_div hr').mpr hrH
      have he : ((r:ℝ)*lam)^(-α)=Z*((H:ℝ)/r)^α := by
        dsimp [Z]
        rw [Real.mul_rpow hr'.le hlam.le,Real.mul_rpow hH'.le hlam.le,Real.div_rpow hH'.le hr'.le,
          Real.rpow_neg hr'.le,Real.rpow_neg hH'.le]
        field_simp
      rw [he]
      apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hα') hZ).trans_eq
      rw [←Real.sqrt_eq_rpow,Real.sqrt_div hH'.le]; ring
    calc
      _ ≤ ∑ r∈Ico 1 H,Z*Real.sqrt H*(Real.sqrt r)⁻¹ := sum_le_sum fun _ hr => hweight hr
      _ ≤ ∑ r∈Icc 1 H,Z*Real.sqrt H*(Real.sqrt r)⁻¹ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ Z*Real.sqrt H*(2*Real.sqrt H) := by
        rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (AnalyticTools.Summation.sum_Icc_inv_sqrt_le H) (by positivity)
      _ = _ := by change _=2*(H:ℝ)*Z; nlinarith only [congrArg (fun z : ℝ => Z*z) (Real.sq_sqrt (Nat.cast_nonneg H))]

private theorem differencing_two_power_square {f : ℝ→ℝ} {a b M H : ℕ}
    (hab : a≤b) (hM : b≤a+M) (hH : 1≤H) (hHM : H≤M)
    {lam α D C : ℝ} (hlam : 0<lam) (hα : 0≤α) (hα' : α≤1/2) (hD : 0≤D) (hC : 0≤C)
    (h : ∀ r∈Ico 1 H,‖∑ n∈Ioc a (b-r),e (f ((n:ℝ)+r)-f n)‖ ≤
      C*((M:ℝ)*((r:ℝ)*lam)^α+D*((r:ℝ)*lam)^(-α))) :
    ‖∑ n∈Ioc a b,e (f n)‖^2 ≤ 4*(M:ℝ)^2/H+
      4*M*C*((M:ℝ)*((H:ℝ)*lam)^α+2*D*((H:ℝ)*lam)^(-α)) := by
  let S := ‖∑ n∈Ioc a b,e (f n)‖
  let s (r : ℕ) := ‖∑ n∈Ioc a (b-r),e (f ((n:ℝ)+r)-f n)‖
  let P := ((H:ℝ)*lam)^α
  let Q := ((H:ℝ)*lam)^(-α)
  have hP : 0≤P := by dsimp [P]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hH' : 0<(H:ℝ) := by exact_mod_cast hH
  have hm' : (H:ℝ)≤M := by exact_mod_cast hHM
  have ⟨hu,hv⟩ := differencing_frequency_sums hH hlam hα hα'
  have hsum : (∑ r∈Ico 1 H,(1-(r:ℝ)/H)*s r) ≤ C*((M:ℝ)*(H*P)+D*(2*H*Q)) := by
    calc
      _ ≤ ∑ r∈Ico 1 H,C*((M:ℝ)*((r:ℝ)*lam)^α+D*((r:ℝ)*lam)^(-α)) := by
        apply sum_le_sum; intro r hr
        exact (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self 1 (by positivity))).trans (h r hr)
      _ ≤ _ := by
        rw [←mul_sum,sum_add_distrib,←mul_sum,←mul_sum]
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hu (by positivity)) (mul_le_mul_of_nonneg_left hv hD)) hC
  have hnon : 0≤∑ r∈Ico 1 H,(1-(r:ℝ)/H)*s r := sum_nonneg (fun r hr => mul_nonneg
    (sub_nonneg.mpr ((div_le_one hH').mpr (by exact_mod_cast (mem_Ico.mp hr).2.le))) (norm_nonneg _))
  have hdif := vanDerCorput_weyl_differencing f a (b-a) H hH
  have hba : a+(b-a)=b := by omega
  rw [hba] at hdif
  have h' : (H:ℝ)*S^2 ≤ ((b-a:ℕ)+H:ℝ)*(((b-a:ℕ)+H:ℝ)+2*∑ r∈Ico 1 H,(1-(r:ℝ)/H)*s r) := by
    simpa only [S,s,e,Nat.cast_add] using hdif
  have hlen : ((b-a:ℕ):ℝ)≤M := by exact_mod_cast (show b-a≤M by omega)
  have hh := h'.trans (mul_le_mul (by linarith : ((b-a:ℕ)+H:ℝ)≤2*M)
    (show ((b-a:ℕ)+H:ℝ)+2*∑ r∈Ico 1 H,(1-(r:ℝ)/H)*s r ≤ 2*M+2*(C*((M:ℝ)*(H*P)+D*(2*H*Q))) by linarith)
    (by positivity) (by positivity))
  change S^2 ≤ 4*(M:ℝ)^2/H+4*M*C*((M:ℝ)*P+2*D*Q)
  apply le_of_mul_le_mul_left (a:=(H:ℝ)) _ hH'
  apply hh.trans_eq
  field_simp; ring

/-- One higher derivative step. A two-term estimate for each positive
difference yields the classical new exponents `α/(2+2α)` and `β/2`. -/
theorem higher_derivative_differencing_step {f : ℝ→ℝ} {a b M : ℕ} (hM : 1≤M)
    (hab : a≤b) (hMb : b≤a+M) {lam α β C : ℝ} (hlam : 0<lam)
    (hα : 0<α) (hα' : α≤1/2) (hβ : 0≤β) (hβ' : β≤1) (hC : 1≤C)
    (h : ∀ r : ℕ, 1≤r → ‖∑ n∈Ioc a (b-r),e (f ((n:ℝ)+r)-f n)‖ ≤
      C*((M:ℝ)*((r:ℝ)*lam)^α+(M:ℝ)^(1-β)*((r:ℝ)*lam)^(-α))) :
    let p := α/(2+2*α)
    ‖∑ n∈Ioc a b,e (f n)‖ ≤
      (4+8*C)*((M:ℝ)*lam^p+(M:ℝ)^(1-β/2)*lam^(-p)) := by
  let m : ℝ := M
  let p := α/(2+2*α)
  let u := lam^p
  let T := lam^(-2*p)
  let D := m^(1-β)
  let A := m*u
  let B := m^(1-β/2)*lam^(-p)
  let k := 4+8*C
  let S := ‖∑ n∈Ioc a b,e (f n)‖
  have hm : 1≤m := by dsimp [m]; exact_mod_cast hM
  have hm' : 0<m := by linarith
  have hu : 0<u := Real.rpow_pos_of_pos hlam _
  have hT : 0<T := Real.rpow_pos_of_pos hlam _
  have hD : 1≤D := Real.one_le_rpow hm (by linarith)
  have hA : 0≤A := mul_nonneg hm'.le hu.le
  have hB : 0≤B := by dsimp [B]; positivity
  have hk : 1≤k := by dsimp [k]; linarith
  have hS : 0≤S := norm_nonneg _
  have htriv : S≤m := by
    apply (norm_sum_le _ _).trans
    simp only [norm_e,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]
    dsimp [m]; exact_mod_cast (show b-a≤M by omega)
  have huT : u^2=T⁻¹ := by
    dsimp [u,T]; rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hlam.le,←Real.rpow_neg hlam.le]
    congr 1; push_cast; ring
  have hAsq : A^2=m^2/T := by dsimp [A]; rw [mul_pow,huT]; ring
  have hBsq : B^2=m*D*T := by
    dsimp [B,D,T]; rw [mul_pow,←Real.rpow_natCast _ 2,←Real.rpow_mul hm'.le,
      ←Real.rpow_natCast _ 2,←Real.rpow_mul hlam.le]
    have he : (1-β/2)*((2:ℕ):ℝ) = 1+(1-β) := by push_cast; ring
    rw [he,Real.rpow_add hm',Real.rpow_one]
    congr 2; push_cast; ring
  have hmain : (lam*T)^α=T⁻¹ := by
    dsimp [T]
    rw [show lam*lam^(-2*p)=lam^(1+ -2*p) by rw [Real.rpow_add hlam,Real.rpow_one],
      ←Real.rpow_mul hlam.le,←Real.rpow_neg hlam.le]
    congr 1; dsimp [p]; field_simp; ring
  have hmain' : (lam*T)^(-α)=T := by rw [Real.rpow_neg (by positivity),hmain,inv_inv]
  have h_mono : A+B≤k*(A+B) := le_mul_of_one_le_left (add_nonneg hA hB) hk
  change S≤k*(A+B)
  by_cases hlo : T≤1
  · have hu2 : 1≤u^2 := by rw [huT]; exact one_le_inv_iff₀.mpr ⟨hT,hlo⟩
    have hu1 : 1≤u := by by_contra! h'; nlinarith only [mul_pos (sub_pos.mpr h') (show 0<1+u by linarith),hu2]
    exact htriv.trans ((le_mul_of_one_le_right hm'.le hu1).trans ((le_add_of_nonneg_right hB).trans h_mono))
  by_cases hhi : m≤T
  · have hB' : m≤B := by
      apply le_of_sq_le_sq _ hB
      rw [hBsq]
      calc m^2 = m*1*m := by ring
           _ ≤ _ := by gcongr
    exact htriv.trans (hB'.trans ((le_add_of_nonneg_left hA).trans h_mono))
  let H := ⌈T⌉₊
  have hH : 1≤H := Nat.ceil_pos.mpr hT
  have hHM : H≤M := Nat.ceil_le.mpr (not_le.mp hhi).le
  have hTH : T≤(H:ℝ) := Nat.le_ceil _
  have hH' : 0<(H:ℝ) := hT.trans_le hTH
  have hHT : (H:ℝ)≤2*T := by dsimp [H]; linarith [Nat.ceil_lt_add_one hT.le]
  have Hz : ((H:ℝ)*lam)^α ≤ 2*T⁻¹ := by
    calc
      _ ≤ (2*(lam*T))^α := Real.rpow_le_rpow (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_right hHT hlam.le]) hα.le
      _ = (2:ℝ)^α*T⁻¹ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),hmain]
      _ ≤ _ := mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith : α≤1)).trans_eq (Real.rpow_one _)) (by positivity)
  have Hq : ((H:ℝ)*lam)^(-α)≤T := by
    rw [←hmain']; apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_right hTH hlam.le]) (by linarith)
  have Hav := differencing_two_power_square hab hMb hH hHM hlam hα.le hα' (zero_le_one.trans hD) (zero_le_one.trans hC)
    (fun r hr => h r (mem_Ico.mp hr).1)
  have hd : 4*m^2/H≤4*m^2/T := div_le_div_of_nonneg_left (by positivity) hT hTH
  have hs : S^2≤4*m^2/T+4*m*C*(m*(2*T⁻¹)+2*D*T) := by
    apply Hav.trans; apply add_le_add hd
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left Hz hm'.le) (mul_le_mul_of_nonneg_left Hq (by linarith))
  have hs' : S^2≤(4+8*C)*A^2+(8*C)*B^2 := by
    rw [hAsq,hBsq]; apply hs.trans_eq; ring
  have hbound : S^2≤k*(A+B)^2 := by
    apply hs'.trans; dsimp [k]
    nlinarith only [mul_nonneg (by linarith : 0≤4+8*C) (mul_nonneg hA hB),sq_nonneg B]
  have hk' : k≤k^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (zero_le_one.trans hk)]
  apply le_of_sq_le_sq _ (mul_nonneg (zero_le_one.trans hk) (add_nonneg hA hB))
  rw [mul_pow]; exact hbound.trans (mul_le_mul_of_nonneg_right hk' (sq_nonneg _))

end AnalyticNumberTheory.ExponentialSums
