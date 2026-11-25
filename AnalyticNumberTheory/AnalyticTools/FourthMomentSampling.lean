import AnalyticNumberTheory.SieveMethods.LargeSieve

/-!
# Sampling fourth moments at separated ordinates

Gallagher's inequality on centered disjoint intervals gives a sampling
bound in terms of the fourth moments of the function and its derivative.
The free positive parameter balances their different sizes.
-/

open Real Complex Finset Set MeasureTheory
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.AnalyticTools

/-- Integrals on disjoint centered windows are dominated by a single
integral over the containing interval. Equality of distances is allowed. -/
theorem sum_integral_separated_windows_le {ι : Type*} (S : Finset ι) (t : ι→ℝ)
    {w a b : ℝ} (hw : 0<w) (hab : a≤b)
    (hsep : ∀ i∈S,∀ j∈S,i≠j → w≤|t i-t j|)
    (hin : ∀ i∈S,a≤t i-w/2 ∧ t i+w/2≤b)
    {g : ℝ→ℝ} (hg : Continuous g) (hpos : ∀ x,0≤g x) :
    (∑ i∈S,∫ x in (t i-w/2)..(t i+w/2),g x) ≤ ∫ x in a..b,g x := by
  let U (i : ι) := Ioc (t i-w/2) (t i+w/2)
  have hu (i : ι) : t i-w/2≤t i+w/2 := by linarith
  have hdis : Set.Pairwise (↑S) (fun i j => Disjoint (U i) (U j)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain h|h := le_abs.mp (hsep i hi j hj hij)
    · linarith only [h,hxi.1,hxj.2]
    · linarith only [h,hxj.1,hxi.2]
  simp_rw [intervalIntegral.integral_of_le (hu _)]
  rw [intervalIntegral.integral_of_le hab,←integral_biUnion_finset S (s:=U) (fun _ _ => measurableSet_Ioc) hdis
    (fun i _ => (hg.integrableOn_Icc (μ:=volume) (a:=t i-w/2) (b:=t i+w/2)).mono_set Ioc_subset_Icc_self)]
  apply setIntegral_mono_set ((hg.integrableOn_Icc (μ:=volume)).mono_set Ioc_subset_Icc_self)
    (ae_of_all _ hpos)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨hi',hx'⟩ := mem_iUnion.mp hi
  exact ⟨(hin i hi').1.trans_lt hx'.1,hx'.2.trans (hin i hi').2⟩

/-- Weighted Young inequality for the product in the derivative of the
fourth power. -/
theorem twice_cube_mul_le_fourth {a b L : ℝ} (ha : 0≤a) (hb : 0≤b) (hL : 0<L) :
    2*a^3*b≤3*L*a^4+(L^3)⁻¹*b^4 := by
  have h := mul_nonneg (sq_nonneg (b-L*a)) (show 0≤b^2+2*(L*a)*b+3*(L*a)^2 by positivity)
  field_simp
  nlinarith only [h,mul_nonneg (pow_nonneg (mul_nonneg hL.le ha) 3) hb]

/-- Sampling fourth powers of a differentiable function. The interval
length `w` may be any lower bound for the separation. -/
theorem sum_fourth_separated_le {ι : Type*} (S : Finset ι) (t : ι→ℝ)
    {w a b L : ℝ} (hw : 0<w) (hab : a≤b) (hL : 0<L)
    (hsep : ∀ i∈S,∀ j∈S,i≠j → w≤|t i-t j|)
    (hin : ∀ i∈S,a≤t i-w/2 ∧ t i+w/2≤b)
    {f g : ℝ→ℂ} (hf : ∀ x,HasDerivAt f (g x) x) (hg : Continuous g) :
    (∑ i∈S,‖f (t i)‖^4)≤(w⁻¹+3*L)*(∫ u in a..b,‖f u‖^4)+
      (L^3)⁻¹*(∫ u in a..b,‖g u‖^4) := by
  let F (x : ℝ) := ‖f x‖^4
  let G (x : ℝ) := ‖g x‖^4
  have cf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hF : Continuous F := cf.norm.pow 4
  have hG : Continuous G := hg.norm.pow 4
  let p (x : ℝ) := f x^2
  let d (x : ℝ) := 2*f x*g x
  have hd (x : ℝ) : HasDerivAt p (d x) x := by simpa [p,d,Pi.pow_def] using (hf x).pow 2
  have hc : Continuous d := (continuous_const.mul cf).mul hg
  have hpoint (i : ι) :
      ‖f (t i)‖^4≤(w⁻¹+3*L)*(∫ u in (t i-w/2)..(t i+w/2),F u)+
        (L^3)⁻¹*(∫ u in (t i-w/2)..(t i+w/2),G u) := by
    let c := t i-w/2
    let e := t i+w/2
    have hce : c≤e := by dsimp [c,e];linarith
    have H := gallagher_sobolev_sq_midpoint (x:=t i) hw (fun x _ => hd x) hc.continuousOn
    have hp (x : ℝ) : ‖p x‖^2=F x := by dsimp [p,F];rw [norm_pow,←pow_mul]
    simp_rw [hp] at H
    have hmix (x : ℝ) : ‖p x‖*‖d x‖≤3*L*F x+(L^3)⁻¹*G x := by
      simp only [p,d,F,G,norm_pow,norm_mul,Complex.norm_two]
      apply le_trans _ (twice_cube_mul_le_fourth (a:=‖f x‖) (b:=‖g x‖) (norm_nonneg _) (norm_nonneg _) hL)
      exact le_of_eq (by ring)
    have hu := intervalIntegral.integral_mono_on hce (((cf.pow 2).norm.mul hc.norm).intervalIntegrable («μ»:=volume) c e)
      (((continuous_const.mul hF).add (continuous_const.mul hG)).intervalIntegrable ..) (fun x _ => hmix x)
    change (∫ x in c..e, ‖p x‖*‖d x‖)≤∫ x in c..e,3*L*F x+(L^3)⁻¹*G x at hu
    rw [intervalIntegral.integral_add ((hF.intervalIntegrable ..).const_mul _) ((hG.intervalIntegrable ..).const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hu
    change F (t i)≤w⁻¹*(∫ x in c..e,F x)+(∫ x in c..e,‖p x‖*‖d x‖) at H
    change F (t i)≤(w⁻¹+3*L)*(∫ x in c..e,F x)+(L^3)⁻¹*∫ x in c..e,G x
    linarith only [H,hu]
  have hsum := Finset.sum_le_sum (s:=S) (fun i _ => hpoint i)
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hsum
  apply hsum.trans
  exact add_le_add (mul_le_mul_of_nonneg_left (sum_integral_separated_windows_le S t hw hab hsep hin hF (fun _ => by dsimp [F];positivity)) (by positivity))
    (mul_le_mul_of_nonneg_left (sum_integral_separated_windows_le S t hw hab hsep hin hG (fun _ => by dsimp [G];positivity)) (by positivity))

end AnalyticNumberTheory.AnalyticTools
