import AnalyticNumberTheory.RiemannZeta.ZeroCounting
import AnalyticNumberTheory.RiemannZeta.ZeroFreeRegion
import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "ζ 函数的零点计数与无零区域" =>
%%%
tag := "zeta-zeros"
file := "zeta-zeros"
%%%

{index}[Riemann–von Mangoldt 公式]设 $`N(T)` 按重数计入临界带中所有满足 $`0<\operatorname{Im}(\rho)\le T` 的零点。辐角原理把这个整数与边界上的辐角变化联系起来。Gamma 因子的 Stirling 展开给出光滑主项，在 $`T\ge2` 时有

$$`N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e}+\frac78+O(\log T).`

{docstring riemannVonMangoldt_asymptotic}

{index}[无零区域]计数控制零点的总数，无零区域则限制它们能靠实部一多近。存在 $`c>0` 使 $`\sigma\ge 1-c/\log(|t|+2)` 的区域没有零点。取素数计数的积分路径时，这条边界决定了能将路径向左移动的距离。

{docstring riemannZeta_zero_free_region}

# 用 Dirichlet 多项式探测零点
%%%
file := "zero-detection"
tag := "zero-detection"
%%%

用截断的 Möbius 级数乘以 ζ 函数的有限 Dirichlet 近似。除常数项外，乘积中 $`n\le N` 的系数全部抵消。对于充分大的 $`N`，若 $`\rho` 是零点、$`\Re\rho\ge3/4` 且 $`N\le |\Im\rho|\le 2N`，则剩下的多项式在 $`\rho` 处的模至少为 $`1/2`。这将计数这些零点的问题转化为估计多项式取大值的次数。

{docstring AnalyticNumberTheory.PrimeDistribution.zetaDetector_large_at_zero}
