import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "黎曼 ξ 函数与临界线" =>
%%%
tag := "riemann-xi"
file := "riemann-xi"
%%%

{index}[黎曼 ξ 函数]将 $`\zeta(s)` 与 Gamma 因子配成整函数 $`\xi(s)` 后，函数方程成为关于 $`s\mapsto 1-s` 的对称关系。按本库的归一化，$`\xi(0)=\xi(1)=1/2`。

{docstring xi_one_sub}

取 $`s=1/2+it`，此时 $`1-s=\overline{s}`。再用 $`\xi(\overline{s})=\overline{\xi(s)}`，可知临界线上每一点的函数值都为实数。

{docstring xi_half_add_mul_I_im}
