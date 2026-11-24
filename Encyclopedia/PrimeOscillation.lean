import AnalyticNumberTheory.PrimeDistribution.Oscillation
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "素数定理误差与 Möbius 和的振荡" =>
%%%
tag := "prime-oscillation"
file := "prime-oscillation"
%%%

{index}[振荡定理]{ref "prime-counting"}[素数定理]给出 $`\psi(x)\sim x`。ζ 的非平凡零点还限制余项可以有多小。存在常数 $`c>0`，使得在任意给定截点之后，既能找到 $`\psi(x)-x\ge c\sqrt{x}` 的点，也能找到 $`\psi(x)-x\le-c\sqrt{x}` 的点。这就是 $`\psi(x)-x=\Omega_\pm(\sqrt x)` 的量词含义。

{docstring psi_sub_id_omega_half}

更一般地，一个实部为 $`\beta` 的非平凡零点就能给出 $`x^\beta` 尺度上的正负振荡。证明通过 Mellin 变换联系误差和零点。若某一侧最终始终太小，会得到一个最终非负的函数，其 Mellin 变换在实轴上的解析性质与非实奇点矛盾。

{docstring psi_sub_id_omega_plus_minus_of_zero}

相同的方法可以研究 $`M(x)=\sum_{n\le x}\mu(n)`。其 Dirichlet 级数和 ζ 函数的倒数相连，临界带中的零点在倒数中变成极点。无条件地，$`M(x)` 在平方根尺度上也有两个方向的振荡。

{docstring mertensM_omega_half}
