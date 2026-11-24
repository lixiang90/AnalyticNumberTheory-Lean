import AnalyticNumberTheory.RiemannZeta.CriticalMeanSquare
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "ζ 函数在临界线上的二阶矩" =>
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
