import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions
import AnalyticNumberTheory.RiemannZeta.IntegratedArgument
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

# ζ 函数辐角的一次积分
%%%
tag := "integrated-zeta-argument"
file := "integrated-argument"
%%%

{index}[辐角的一次积分]在零点计数公式中，$`S(t)` 记录 ζ 函数沿折线的辐角变化除以 $`\pi` 的值，在零点高度取右极限。逐点估计 $`S(t)=O(\log t)` 只能直接给出积分的 $`O(T\log T)` 上界。实际上，正负变化相互抵消，$`S_1(T)=\int_0^T S(t)\,dt` 满足

$$`|S_1(T)|\le C\log T\qquad(T\ge8).`

{docstring integratedArgument_abs_le_log}

为看出抵消，引入水平积分 $`P(t)=\int_{1/2}^2\log|\zeta(\sigma+it)|\,d\sigma`。从 ζ 函数中逐一提出局部零点因子后，$`P` 在零点高度仍连续，且 $`P(t)=O(\log t)`。避开零点高度时，$`P'(t)=\pi S(t)-\arg\zeta(2+it)`。有限高度带只有有限个零点高度，因此可以跨过它们积分。

{docstring zeta_horizontalLogMean_bound}

{docstring hasDerivAt_zeta_horizontalLogMean}

在实部二的直线上，Euler 乘积的对数有绝对收敛的 Dirichlet 级数。再除一次对数得到有界原函数，故任意区间上 $`\arg\zeta(2+it)` 的积分绝对值至多为 $`\pi^2/(3\log2)`。这给出 $`S_1` 在两个高度间的精确增量公式。

{docstring abs_integral_arg_riemannZeta_two_le}

{docstring integratedArgument_increment}

# 分离 ζ 对数导数的全部极点
%%%
tag := "centered-zeta-partial-fractions"
file := "centered-partial-fractions"
%%%

{index}[对数导数的部分分式展开]对一个非零位置 $`\omega`，先从 $`1/(s-\omega)` 减去它在原点的值，得到

$$`K_\omega(s)=\frac1{s-\omega}+\frac1\omega
              =\frac{s}{\omega(s-\omega)}.`

这样每个分式在 $`s=0` 消失。当 $`|\omega|\ge 2|s|` 时，它的模至多是 $`2|s|/|\omega|^2`。因此临界带内非平凡零点的倒平方和就足以保证绝对收敛。在原点附近，各项可以使用同一个可求和的上界。

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.centeredPole_eq}

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.norm_centeredPole_le}

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.tendsto_tsum_centeredPole_zero}

在 $`s\ne 1` 且 $`\zeta(s)\ne0` 时，完整公式为

$$`-\frac{\zeta'}{\zeta}(s)=-\log(2\pi)+K_1(s)
       -\sum_{\rho}K_{\rho}(s)-\sum_{k=1}^\infty K_{-2k}(s).`

每个非平凡零点按解析重数重复，负偶整数各出现一次。$`s=1` 是 ζ 的极点，在负对数导数中留数为 $`+1`；每个零点则贡献其重数的负值。取 $`s=0`，两个无穷级数与 $`K_1` 都消失，所以常数恰是 $`-\log(2\pi)`。

{docstring ZetaZeroEnumeration.summable_centered}

{docstring summable_centered_trivialZetaZero}

{docstring neg_logDeriv_riemannZeta_zero}

{docstring exists_centered_logDeriv_riemannZeta}
