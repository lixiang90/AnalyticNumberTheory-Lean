import AnalyticNumberTheory.AnalyticTools.MordellIntegral

/-!
# Trigonometric evaluation of the Mordell integral

The undivided identity holds even when the cosine in the classical
denominator vanishes. The integral therefore specifies the continuous
extension of the quotient.
-/
noncomputable section
open Real Complex Filter Set
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

private def phase (x : ℝ) : ℂ := Complex.exp ((Real.pi*x:ℝ)*I)

private theorem phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  unfold phase;rw [←Complex.exp_add];congr 1;push_cast;ring

private theorem phase_two : phase 2=1 := by
  unfold phase;convert Complex.exp_two_pi_mul_I using 1;push_cast;ring

private theorem phase_neg_half : phase (-(1/2))= -I := by
  unfold phase;convert Complex.exp_neg_pi_div_two_mul_I using 1;push_cast;ring

private theorem phase_cos (x : ℝ) :
    2*((Real.cos (Real.pi*x):ℝ):ℂ)=phase x+phase (-x) := by
  rw [Complex.ofReal_cos,Complex.cos];dsimp [phase];push_cast;ring_nf

/-- Multiplication by the cosine clears both removable singularities. -/
theorem cos_mul_mordellIntegral (c : ℝ) :
    (Real.cos (Real.pi*c):ℂ)*mordellIntegral c Real.pi =
      2*Real.pi*Complex.exp (((Real.pi*(c^2/2-5/8):ℝ):ℂ)*I)*
        (Real.cos (Real.pi*(c^2/2-c-1/8)):ℂ) := by
  let a := c^2/2-c-1/8
  let b := c^2/2-5/8
  let d := 1/4+(c-1)^2
  have h := mordellIntegral_equation c
  have he : Complex.exp (2*Real.pi*I*c)=phase (2*c) := by unfold phase;congr 1;push_cast;ring
  have hd : Complex.exp (I*Real.pi/4+I*Real.pi*((c-1:ℝ):ℂ)^2)=phase d := by
    unfold phase d;congr 1;push_cast;ring
  rw [he,hd] at h
  have hc : 2*phase c*(Real.cos (Real.pi*c):ℂ)=1+phase (2*c) := by
    rw [mul_right_comm,phase_cos,add_mul,←phase_add,←phase_add]
    rw [show -c+c=0 by ring,show c+c=2*c by ring];simp [phase,add_comm]
  have hp : phase (c+b+a)=phase (2*c)*phase d := by
    rw [←phase_add,show 2*c+d=(c+b+a)+2 by dsimp [a,b,d];ring,phase_add (c+b+a) 2,phase_two,mul_one]
  have hm : phase (c+b+ -a)=phase (2*c)*(-I) := by
    rw [←phase_neg_half,←phase_add];congr 1;dsimp [a,b];ring
  have hmain : 2*phase c*(2*Real.pi*phase b*(Real.cos (Real.pi*a):ℂ))=
      phase (2*c)*(2*Real.pi*phase d-2*Real.pi*I) := by
    calc
      _ = (Real.pi:ℂ)*phase (c+b)*(2*(Real.cos (Real.pi*a):ℂ))*2 := by rw [phase_add];ring
      _ = 2*Real.pi*(phase (c+b+a)+phase (c+b+ -a)) := by rw [phase_cos,phase_add (c+b) a,phase_add (c+b) (-a)];ring
      _ = _ := by rw [hp,hm];ring
  apply mul_left_cancel₀ (show (2:ℂ)*phase c≠0 by apply mul_ne_zero (by norm_num);exact Complex.exp_ne_zero _)
  change 2*phase c*((Real.cos (Real.pi*c):ℂ)*mordellIntegral c Real.pi) =
    2*phase c*(2*Real.pi*phase b*(Real.cos (Real.pi*a):ℂ))
  rw [←mul_assoc,hc,hmain,h]

/-- Away from the zeros of the denominator this is the usual closed
form of the translated Gaussian contour integral. -/
theorem mordellIntegral_eq_cos_quotient {c : ℝ} (hc : Real.cos (Real.pi*c)≠0) :
    mordellIntegral c Real.pi =
      2*Real.pi*Complex.exp (((Real.pi*(c^2/2-5/8):ℝ):ℂ)*I)*
        ((Real.cos (Real.pi*(c^2/2-c-1/8))/Real.cos (Real.pi*c):ℝ):ℂ) := by
  apply mul_left_cancel₀ (show ((Real.cos (Real.pi*c):ℝ):ℂ)≠0 by exact_mod_cast hc)
  rw [cos_mul_mordellIntegral,Complex.ofReal_div]
  have hn : ((Real.cos (Real.pi*c):ℝ):ℂ)≠0 := by exact_mod_cast hc
  rw [mul_comm ((Real.cos (Real.pi*c):ℝ):ℂ)]
  simp only [mul_assoc,div_mul_cancel₀ _ hn]

end AnalyticNumberTheory.AnalyticTools
