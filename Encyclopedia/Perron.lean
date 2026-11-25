import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.DirichletSeries.LogPerronTruncation
import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary
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

# 对数平滑与有限高度
%%%
tag := "logarithmic-perron"
file := "logarithmic-smoothing"
%%%

在 $`s=\sigma+it`、$`\sigma>0` 上，把 Perron 核的分母取为 $`s^2`。沿整条直线积分，得到实变量 $`v` 的正部

$$`\frac{1}{2\pi}\int_{\mathbb R}\frac{e^{(\sigma+it)v}}{(\sigma+it)^2}\,dt
  =\max(v,0).`

这是函数 $`v\mapsto v` 在正半轴上的 Laplace 反演。零延拓在原点连续，所以 $`v=0` 处的值也是零。被积函数的模为 $`e^{\sigma v}/(\sigma^2+t^2)`。

{docstring integral_logPerronKernel}

令 $`F(s)=\sum a_n e^{-\lambda_n s}`，并且 $`M_\sigma=\sum |a_n|e^{-\sigma\lambda_n}<\infty`。逐项使用核公式，每个指数的权重都是 $`(u-\lambda_n)_+`。即使纵线正好落在绝对收敛域的边界，只要 $`M_\sigma` 有限，这个推导仍然成立。

{docstring DirichletFrequency.logPerron_formula}

若只积分到高度 $`-T\le t\le T`，两端尾积分中分别使用 $`(\sigma^2+t^2)^{-1}\le t^{-2}`，归一化后的总误差至多为 $`M_\sigma e^{\sigma u}/(\pi T)`。

{docstring DirichletFrequency.norm_truncated_logPerron_sub_sum_le}

对普通 Dirichlet 级数，取 $`u=\log x`、$`\lambda_n=\log n` 后得到

$$`\sum_{n\le x}a_n\log(x/n)=\frac{1}{2\pi}\int_{\mathbb R}
   F(\sigma+it)\frac{x^{\sigma+it}}{(\sigma+it)^2}\,dt.`

{docstring logWeightedSum_eq_perron}

权重 $`\log(x/n)` 也等于 $`\int_n^x dt/t`。交换有限求和与积分就得到系数部分和的积分表示。比较两个截点 $`0<x\le y` 的平滑和时，所有 $`n\le x` 的项共同多出 $`\log(y/x)`，余项只含 $`x<n\le y` 的系数。

{docstring logWeightedSum_eq_integral}

{docstring logWeightedSum_sub_eq_short_sum}
