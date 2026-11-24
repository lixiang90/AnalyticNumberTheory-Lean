import AnalyticNumberTheory.AdditiveNumberTheory.Waring
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "圆法与 Waring 表示数" =>
%%%
tag := "waring"
file := "waring"
%%%

{index}[Waring 问题]用 $`R_{k,s}(n)` 表示方程 $`x_1^k+\cdots+x_s^k=n` 的非负整数有序解数。设 $`k>0`，选择满足 $`n<(P+1)^k` 的截点。只要有一个坐标大于 $`P`，它的幂就已经超过目标，所以这个截断保留全部解。

取 $`S(\alpha)=\sum_{x=0}^{P} e(\alpha x^k)`。展开 $`S(\alpha)^s` 后，每个元组给出一个整数频率。乘以 $`e(-n\alpha)` 并积过一个周期，频率为零的项各贡献一，其余项的积分为零。

{docstring integral_waringSum_pow}

例如 $`n=5,k=2,s=2` 时，取 $`P=2` 即可，两个解分别是 $`(1,2)` 与 $`(2,1)`。对于四个平方，Lagrange 定理保证每个非负整数的表示数都为正。

{docstring waringCount_four_squares_pos}

在解析估计中，可把同一个积分分成靠近小分母有理数的主弧和其余的次弧。分割本身给出精确等式，估计这两部分才涉及误差项。

{docstring waringCount_eq_arcIntegrals}
