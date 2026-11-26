import AnalyticNumberTheory.DirichletSeries.HalfIntegerPerron
import AnalyticNumberTheory.DirichletSeries.PerronRectangle
import AnalyticNumberTheory.DirichletSeries.SharpPerron
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.DirichletSeries.LogPerronTruncation
import AnalyticNumberTheory.DirichletSeries.LogPerronOrdinary
import AnalyticNumberTheory.DirichletSeries.LogPerronPolynomials
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

# 任意阶的对数权与 Riesz 权
%%%
tag := "higher-perron-means"
file := "higher-perron-means"
%%%

设 $`k\ge1` 是整数，$`s=\sigma+it` 且 $`\sigma>0`。在{ref "logarithmic-perron"}[一阶对数平滑]中，$`s^2` 给出一次权。将分母换成 $`s^{k+1}`，得到正部的 $`k` 次幂

$$`\frac1{2\pi}\int_{\mathbb R}\frac{e^{sv}}{s^{k+1}}\,dt
=\frac{(\max(v,0))^k}{k!}.`

这是正半轴上 $`v^k/k!` 的 Laplace 反演。$`k\ge1` 使零延拓在原点连续，而且积分沿整条直线绝对收敛。

{docstring integrable_powerLogPerronKernel}

{docstring integral_powerLogPerronKernel}

令 $`A(s)=\sum_n a_n e^{-\lambda_n s}` 在选定的直线上绝对收敛。每一项的指数因子把核的自变量从 $`u` 平移到 $`u-\lambda_n`。若反演所得的权 $`w(v)` 在 $`v<0` 时消失，积分便只留下有限和 $`\sum_{\lambda_n\le u}a_n w(u-\lambda_n)`。

{docstring DirichletFrequency.smoothedPerron_formula}

对重复因子 $`s^{k+1}` 和连续平移的因子 $`s(s+1)\cdots(s+k)`，令 $`v=u-\lambda_n\ge0`。它们分别给出

$$`w_{\log}(v)=\frac{v^k}{k!},\qquad
w_{\mathrm R}(v)=\frac{(1-e^{-v})^k}{k!}.`

两种权在截点 $`\lambda_n=u` 都取零。这两个公式都允许积分线位于实际绝对收敛的边界。

{docstring DirichletFrequency.powerLogPerron_formula}

{docstring DirichletFrequency.rieszPerron_formula}

对于普通 Dirichlet 级数，取 $`u=\log x` 和 $`\lambda_n=\log n`，两种权分别变成 $`(\log(x/n))^k/k!` 与 $`(1-n/x)^k/k!`。例如在 $`x=4`、$`k=2` 时，$`n=1` 的两种权分别是 $`(\log 4)^2/2` 和 $`9/32`。

{docstring powerLogWeightedSum_eq_perron}

# 带线性增长的分子与积分移线
%%%
tag := "log-perron-contour-shift"
file := "contour-shift"
%%%

设 $`0<a\le b`，$`F` 在竖直带 $`a\le\Re s\le b` 上全纯。对实数 $`x>0`，记

$$`\mathcal P_\sigma(F;x)=\frac{1}{2\pi}\int_{\mathbb R}
 F(\sigma+it)\frac{x^{\sigma+it}}{(\sigma+it)^2}\,dt.`

若两侧的被积函数绝对可积，且带内 $`|F(s)|\le C(1+|s|)`，则 $`\mathcal P_a(F;x)=\mathcal P_b(F;x)`。证明先在高度 $`\pm T` 之间闭合矩形。水平边长固定，分母给出的 $`T^{-2}` 抵消分子的一次增长，两条水平边的积分便随 $`T\to\infty` 消失。

{docstring AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.integral_verticalLine_eq_of_boundary_decay}

{docstring logPerronIntegral_shift}

若右边界上的 $`F` 是一条绝对收敛的 Dirichlet 级数，这个等式把它的有限对数加权和延续到左边界。{ref "critical-character-perron-inversion"}[非主特征的临界线反演]给出了一个例子。

{docstring logWeightedSum_eq_of_logPerronContinuation}

对有限多项式 $`P(s)=\sum_{n\in S}a_n n^{-s}`，每项满足 $`x^s n^{-s}=(x/n)^s`。于是只要相应的积分绝对可积，就有
$`\mathcal P_\sigma(PF;x)=\sum_{n\in S}a_n\mathcal P_\sigma(F;x/n)`。
令 $`F=1`，每项便获得权重 $`\max(\log(x/n),0)`，包括 $`x=n` 时的零值。

{docstring logPerronIntegral_finset_mul}

{docstring logPerronIntegral_finset}

# 对称截断恢复带半权的部分和
%%%
tag := "sharp-perron-partial-sums"
file := "sharp-perron-partial-sums"
%%%

设普通 Dirichlet 级数 $`F(s)=\sum_{n\ge1}a_n n^{-s}` 在 $`c>0` 这条线上绝对收敛。固定 $`x>0`，沿这条直线把 $`F(s)x^s/s` 积分到高度 $`\pm T`。当 $`T` 趋于无穷时，极限是 $`\sum_{1\le n<x}a_n`，若 $`x` 恰是正整数，再加上 $`a_x/2`。

{docstring midpointPartialSum}

{docstring tendsto_dirichletContourIntegral_midpointPartialSum}

对固定 $`x,c`，误差满足 $`|E(T)|\le C/T`。常数由三部分组成：远离 $`x` 的项用绝对收敛控制，靠近 $`x` 的有限项保留各自的 $`|\log(x/n)|`，当 $`n=x` 时直接使用核在 $`1` 处的估计。把 $`F` 取为 $`\log\zeta`，就得到{ref "riemann-counting-mellin"}[Riemann 半权素数幂计数的反演]。

{docstring norm_dirichletContourIntegral_sub_midpointPartialSum_le}

# 半整数截断与矩形移线
%%%
tag := "perron-half-integer-rectangles"
file := "half-integer-rectangles"
%%%

当 $`x=N+1/2` 时，最近的整数与 $`x` 相距半个单位。设 $`|a_n|\le A` 对 $`n\le 2x` 成立。在 $`1<c\le2` 的积分线上，逐项累加距离的倒数，靠近 $`x` 的项对截断误差的总贡献为 $`O(Ax\log(2x)/T)`。远处各项由 $`\sum |a_n|n^{-c}` 控制。

{docstring perron_halfInteger_error_le}

若级数在整个矩形上有全纯延拓，先把积分左移到 $`\sigma_0>0`。设左边的函数界为 $`B_v`，上下边的函数界为 $`B_h`。左边的积分贡献至多为 $`(\sqrt{2}/\pi)B_v x^{\sigma_0}\log(1+T/\sigma_0)`，两条水平边合起来至多为 $`(c-\sigma_0)B_h x^c/(\pi T)`。

{docstring norm_dirichletContourIntegral_le_of_rectangle}
