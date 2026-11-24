import AnalyticNumberTheory.RiemannZeta.CriticalMeanSquare
import AnalyticNumberTheory.DirichletLFunctions.CriticalCorrelations
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "ζ 与 Dirichlet L 函数在临界线上的二阶矩" =>
%%%
tag := "critical-second-moment"
file := "critical-second-moment"
%%%

{index}[ζ 函数的二阶矩]在临界线 $`s=1/2+it` 上，ζ 函数的均方随高度按对数增长，并且主项系数恰好为一。

$$`\int_1^T |\zeta(1/2+it)|^2\,dt\sim T\log T.`

{docstring mean_sq_riemannZeta_half_asymptotic}

取长为 $`\lfloor T\rfloor+1` 的 Dirichlet 多项式近似 ζ。两者之差的平方在 $`[1,T]` 上积分，再除以 $`T`，所得误差有一个绝对常数上界。

{docstring mean_sq_zeta_sub_long_dirichletPoly_half}

为了从{ref "dirichlet-polynomials"}[Dirichlet 多项式均值定理]读出主项，把多项式在 $`M=\lfloor T/\sqrt{\log T}\rfloor+1` 处截短。对角项给出调和和 $`\sum_{m\le M}1/m\sim\log T`。在均值定理中，非对角项相对于对角项的误差受 $`2\pi M/T` 控制。删掉的长多项式尾段，其系数平方和至多为 $`O(\sqrt{\log T})`。最后对两次近似分别使用平方可积函数的三角不等式，便可把短多项式的主项传回 ζ 函数。

# 周期系数与 Dirichlet 特征
%%%
tag := "periodic-second-moment"
file := "periodic-coefficients"
%%%

若 Dirichlet 级数的系数 $`a(n)` 以 $`q` 为周期且模不超过一，临界线均方除以 $`T\log T` 后的极限为一个周期内的系数平方平均值。证明先把多项式按剩余类拆为 Hurwitz ζ 函数的有限近似，再用同一个均方准则提取对角项。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_periodicLFunction_half}

对固定模数 $`q` 的 Dirichlet 特征，平方权在可逆剩余类上等于一，在其余类上等于零。因此极限是 $`\varphi(q)/q`。这个系数也适用于非原始特征，此处使用的是系数序列给定的模数。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_LFunction_half}

只在一个剩余类上取系数一，还能提取有理移位的 Hurwitz ζ 函数。计入周期分解中的尺度因子后，它的均方主项系数为一。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_hurwitzZeta_rational_half}

用复极化恒等式可以同时比较两个任意复周期序列 $`a,b`。把临界线上的乘积 $`L_a(s)\overline{L_b(s)}` 积分并除以 $`T\log T`，极限为 $`q^{-1}\sum_{r\bmod q}a(r)\overline{b(r)}`。因此，同一模数的两个不同特征在这个均值下正交。

{docstring AnalyticNumberTheory.DirichletLFunctions.mixed_mean_periodicLFunctions}

{docstring AnalyticNumberTheory.DirichletLFunctions.mixed_mean_LFunctions_of_ne}
