import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "原特征的 L 函数方程" =>
%%%
tag := "dirichlet-functional-equation"
file := "dirichlet-functional-equation"
%%%

{index}[Dirichlet L 函数]设 $`\chi` 是模 $`q` 的原特征。对 $`L(s,\chi)` 补上由特征奇偶性决定的 Gamma 因子，可将 $`1-s` 处的值与共轭特征在 $`s` 处的值联系起来。Lean 采用的补全函数将模数幂单独列出，因此下式右端显式含有 $`q^{s-1/2}`。

{docstring completedLFunction_one_sub_primitive}

归一化 Gauss 和给出的根数决定相位。它的模为一，所以对函数方程两边取绝对值时，根数这一项消失。

{docstring norm_rootNumber_primitive}
