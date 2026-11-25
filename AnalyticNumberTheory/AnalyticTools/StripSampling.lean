import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-!
# Sampling a holomorphic family in a strip

A unit-interval Sobolev inequality in both coordinates turns bounds on
the mean squares of two derivatives into a sampling estimate. Each
family member has a separate set of sampling points.
-/
noncomputable section
open Finset MeasureTheory Complex
open scoped Classical Topology
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AnalyticTools

private theorem sobolev_square_unit {f g : ℝ → ℂ} {a x : ℝ} (hx : x ∈ Set.Icc a (a+1))
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : Continuous g) :
    ‖f x‖^2 ≤ ∫ t in a..a+1, (2*‖f t‖^2 + ‖g t‖^2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  let F (t : ℝ) := (f t)^2
  let G (t : ℝ) := 2 * f t * g t
  have hFG (t : ℝ) : HasDerivAt F (G t) t := by
    change HasDerivAt (fun u => f u ^ 2) (2*f t*g t) t
    convert (hf t).mul (hf t) using 1
    · ext u; simp [pow_two]
    · ring
  have hG : Continuous G := (continuous_const.mul hfc).mul hg
  have hh := gallagher_sobolev_pointwise (by linarith : a<a+1) hx (fun t _ => hFG t) hG.continuousOn
  simp only [F,G,norm_pow,add_sub_cancel_left,inv_one,one_mul,norm_mul,Complex.norm_ofNat] at hh
  apply hh.trans
  rw [← intervalIntegral.integral_add (f:=fun t => ‖f t‖^2) (g:=fun t => 2*‖f t‖*‖g t‖) ((hfc.norm.pow 2).intervalIntegrable ..)
    (((continuous_const.mul hfc.norm).mul hg.norm).intervalIntegrable ..)]
  apply intervalIntegral.integral_mono_on (by linarith)
    (((hfc.norm.pow 2).add ((continuous_const.mul hfc.norm).mul hg.norm)).intervalIntegrable ..)
    (((continuous_const.mul (hfc.norm.pow 2)).add (hg.norm.pow 2)).intervalIntegrable ..)
  intro t _
  change ‖f t‖^2 + 2*‖f t‖*‖g t‖ ≤ 2*‖f t‖^2+‖g t‖^2
  nlinarith [sq_nonneg (‖f t‖-‖g t‖)]

private lemma sampling_vertical_integrals {S : Finset ℂ} {L : ℕ} {K : ℝ}
    (hL : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < L)
    (hmult : ∀ j < L, ((S.filter (fun z => ⌊z.im⌋₊ = j)).card : ℝ) ≤ K)
    (P : ℕ → ℝ → ℂ) (k : ℕ) (hdt : ∀t, HasDerivAt (P k) (I*P (k+1) t) t)
    (hcont : ∀j, Continuous (P j)) :
    ∑ z ∈ S, ‖P k z.im‖^2 ≤ K *
      (2*(∫ t in (0:ℝ)..L, ‖P k t‖^2) + ∫ t in (0:ℝ)..L, ‖P (k+1) t‖^2) := by
  let f := fun t => 2*‖P k t‖^2 + ‖P (k+1) t‖^2
  have hfc : Continuous f := (continuous_const.mul ((hcont _).norm.pow 2)).add ((hcont _).norm.pow 2)
  have hf0 (t : ℝ) : 0 ≤ f t := by dsimp only [f]; positivity
  have hmap (z : ℂ) (hz : z ∈ S) : ⌊z.im⌋₊ ∈ range L := mem_range.mpr ((Nat.floor_lt (hL z hz).1).mpr (hL z hz).2)
  rw [← sum_fiberwise_of_maps_to hmap]
  have hblock (j : ℕ) (hj : j ∈ range L) :
      ∑ z ∈ S.filter (fun z => ⌊z.im⌋₊=j), ‖P k z.im‖^2 ≤ K*∫ t in (j:ℝ)..(j+1:ℕ), f t := by
    let W := S.filter (fun z => ⌊z.im⌋₊=j)
    have hzbd (z : ℂ) (hz : z ∈ W) : ‖P k z.im‖^2 ≤ ∫ t in (j:ℝ)..(j+1:ℕ), f t := by
      have hz' := (hL _ (mem_filter.mp hz).1).1
      have hj' := (mem_filter.mp hz).2
      have hplace : z.im ∈ Set.Icc (j:ℝ) (j+1) := ⟨hj' ▸ Nat.floor_le hz', by
        simpa only [hj'] using (Nat.lt_floor_add_one z.im).le⟩
      have hs := sobolev_square_unit hplace (hdt)
        (continuous_const.mul (hcont (k+1)))
      simpa [f, norm_mul] using hs
    apply (sum_le_sum hzbd).trans
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hmult j (mem_range.mp hj))
      (intervalIntegral.integral_nonneg (by exact_mod_cast Nat.le_succ j) (fun t _ => hf0 t))
  apply (sum_le_sum hblock).trans
  rw [← mul_sum, intervalIntegral.sum_integral_adjacent_intervals (a:=fun j : ℕ => (j:ℝ)) (fun _ _ => hfc.intervalIntegrable ..)]
  simp only [Nat.cast_zero]
  change K * (∫ t in (0:ℝ)..L, 2*‖P k t‖^2 + ‖P (k+1) t‖^2) ≤ _
  rw [intervalIntegral.integral_add (f:=fun t => 2*‖P k t‖^2) (g:=fun t => ‖P (k+1) t‖^2) ((continuous_const.mul ((hcont _).norm.pow 2)).intervalIntegrable ..)
    (((hcont _).norm.pow 2).intervalIntegrable ..), intervalIntegral.integral_const_mul]

/-- Sampling on a strip of width one. The derivative identities describe
changes in the real and imaginary directions. -/
theorem strip_family_sampling {ι : Type*} (F : Finset ι) (S : ι→Finset ℂ) (P : ι→ℕ→ℝ→ℝ→ℂ)
    {L : ℕ} {K B σ : ℝ} (hK : 0≤K)
    (hre : ∀ p∈F,∀z∈S p,z.re∈Set.Icc σ (σ+1))
    (hL : ∀p∈F,∀z∈S p,0≤z.im ∧ z.im<L)
    (hmult : ∀p∈F,∀j<L,(((S p).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K)
    (hr : ∀p k t,Continuous fun u => P p k u t) (htC : ∀p k u,Continuous (P p k u))
    (hR : ∀p u t,HasDerivAt (fun v => P p 0 v t) (P p 1 u t) u)
    (hT : ∀p k u t,HasDerivAt (P p k u) (I*P p (k+1) u t) t)
    (hmean : ∀u∈Set.Icc σ (σ+1),∀k≤2,∑p∈F, (∫ t in (0:ℝ)..L,‖P p k u t‖^2) ≤B) :
    ∑p∈F,∑z∈S p,‖P p 0 z.re z.im‖^2≤9*K*B := by
  let f (p : ι) (z : ℂ) (u : ℝ) := 2*‖P p 0 u z.im‖^2 + ‖P p 1 u z.im‖^2
  have hfc (p : ι) (z : ℂ) : Continuous (f p z) :=
    (continuous_const.mul ((hr p _ _).norm.pow 2)).add ((hr p _ _).norm.pow 2)
  have hfcs (p : ι) : Continuous fun u => ∑ z ∈ S p, f p z u :=
    continuous_finsetSum _ fun z _ => hfc p z
  have hz (p : ι) (hp : p ∈ F) (z : ℂ) (hz : z ∈ S p) :
      ‖P p 0 z.re z.im‖^2 ≤ ∫ r in σ..σ+1, f p z r := by
    exact sobolev_square_unit (f:=fun u => P p 0 u z.im) (g:=fun u => P p 1 u z.im) (hre p hp z hz) (fun u => hR p u z.im) (hr p 1 z.im)
  have hswap (p : ι) : (∑ z ∈ S p, ∫ r in σ..σ+1, f p z r) =
      ∫ r in σ..σ+1, ∑ z ∈ S p, f p z r :=
    (intervalIntegral.integral_finsetSum (fun z _ => (hfc p z).intervalIntegrable ..)).symm
  have hvert (t : ℝ) (ht : t ∈ Set.Icc σ (σ+1)) (k : ℕ) (hk : k ≤ 1) :
      ∑ p ∈ F, ∑ z ∈ S p, ‖P p k t z.im‖^2 ≤ 3*K*B := by
    apply (sum_le_sum fun p hp => sampling_vertical_integrals (hL p hp) (hmult p hp) (fun j => P p j t) k (hT p k t) (fun j => htC p j t)).trans
    rw [←mul_sum, sum_add_distrib, ←mul_sum]
    have h1 := hmean t ht k (by omega)
    have h2 := hmean t ht (k+1) (by omega)
    calc
      _ ≤ K*(2*B+B) := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤2)) h2) hK
      _ = _ := by ring
  apply (sum_le_sum fun p hp => sum_le_sum (hz p hp)).trans
  simp_rw [hswap]
  rw [← intervalIntegral.integral_finsetSum (fun p _ => (hfcs p).intervalIntegrable ..)]
  calc
    _ ≤ ∫ _r in σ..σ+1, 9*K*B := by
      apply intervalIntegral.integral_mono_on (by linarith) ((continuous_finsetSum _ (fun p _ => hfcs p)).intervalIntegrable ..)
        (continuous_const.intervalIntegrable ..)
      intro t ht
      simp only [f,sum_add_distrib,← mul_sum]
      linarith only [hvert t ht 0 (by decide), hvert t ht 1 (by decide)]
    _ = _ := by simp

end AnalyticNumberTheory.AnalyticTools
