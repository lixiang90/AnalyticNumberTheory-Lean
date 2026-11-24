import AnalyticNumberTheory.DirichletSeries.Perron
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletSeries

#doc (Manual) "Perron 反演与截断端点" =>
%%%
tag := "perron-inversion"
file := "perron-inversion"
%%%

{index}[Perron 公式]设 $`c>0`。将 $`y^z/z` 沿直线段 $`z=c+it,\ -T\le t\le T` 积分，并乘以 $`1/(2\pi i)`，可以从 $`y` 的大小读出一个阶跃函数。随着 $`T` 趋于无穷，极限在 $`0<y<1` 时为零，在 $`y>1` 时为一，在 $`y=1` 时为二分之一。

{docstring tendsto_perronKernel}

取 $`y=x/n`，就能从 Dirichlet 级数中选出 $`n<x` 的系数。若要得到平滑的部分和，可以把分母换成 $`z(z+1)\cdots(z+k)`，同时把分子换成 $`x^{z+k}`。此时 $`a_n` 的权重为 $`(x-n)^k/k!`，而 $`n=x` 的权重在 $`k\ge1` 时为零。

{docstring riesz_perron_formula}
