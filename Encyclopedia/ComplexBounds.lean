import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.WeightedArgumentPrinciple
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HorizontalLogMean
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.Jensen
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.HadamardThreeCircles
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

#doc (Manual) "圆盘上的零点计数与增长估计" =>
%%%
tag := "complex-bounds"
file := "complex-bounds"
%%%

{index}[Jensen 公式]设 $`f` 在半径 $`R` 的闭圆盘邻域内解析，且 $`f(z_0)\ne0`。Jensen 公式把边界上 $`\log|f|` 的圆周平均写成中心值与零点贡献之和。一个重数为 $`m` 的内点零点 $`\rho` 贡献 $`m\log(R/|\rho-z_0|)`。

{docstring jensen_formula}

若只数半径 $`r<R` 内的零点，每个零点贡献至少 $`\log(R/r)`。已知外圆上的模不超过 $`M`，便可用 $`(\log M-\log|f(z_0)|)/\log(R/r)` 控制其中互异零点的个数。

{docstring finset_card_zeros_le_sub_log_div_log}

另一种局部估计从对数导数中逐项扣除附近零点的极点。Landau 引理用边界上 $`|f(z)/f(z_0)|` 的上界控制余项。这一步见于{ref "primes-in-progressions"}[素数分布的无零矩形]的证明。

{docstring landau_logDeriv_center_le}

若已知内外两个同心圆上的最大模，Hadamard 三圆定理还给出中间圆上的界。正最大模的对数关于半径的对数具有凸性。

{docstring hadamard_three_circles_log_convex}

# 穿过零点的水平对数积分
%%%
tag := "horizontal-logarithmic-mean"
file := "horizontal-logarithmic-mean"
%%%

在圆盘内分解全纯函数的零点，对数模可写成有限个 $`m_\rho\log|z-\rho|` 的和，加上无零点因子的对数模。Jensen 公式用圆周上的增长控制这些重数之和。

{docstring AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.disk_log_norm_factorization}

单个核在穿过 $`\rho` 时有对数奇性，但沿有限水平线段可积。随高度移动线段，积分在穿过零点时仍连续。在实部从二分之一到二的线段上，将这一点逐个应用于圆盘中的零点，就得到全纯函数对数模积分的连续性。

{docstring AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.continuous_integral_horizontalLogKernel}

{docstring AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.continuousAt_horizontalLogMean}

# 矩形上的加权辐角原理
%%%
tag := "weighted-argument-principle"
file := "weighted-argument-principle"
%%%

{index}[加权辐角原理]设 $`f,g` 为整函数，矩形 $`R` 的边界上 $`f` 处处非零。沿边界按逆时针方向积分，可得

$$`\frac{1}{2\pi i}\int_{\partial R}g(s)\frac{f'(s)}{f(s)}\,ds
 =\sum_{\rho\in R^\circ,\,f(\rho)=0}m_\rho\,g(\rho).`

其中 $`m_\rho` 是解析零点阶数。取 $`g=1` 时，积分数出内部零点的总重数；取 $`g(s)=s` 时，积分给出计重数的零点之和。

{docstring weighted_argument_principle_rect_entire}

证明先从 $`f` 中提出有限乘积 $`\prod_\rho(s-\rho)^{m_\rho}`。剩余因子在闭矩形上处处非零，其对数导数乘以 $`g` 后的边界积分为零。对其余各项 $`m_\rho g(s)/(s-\rho)` 使用柯西积分公式即可。

{docstring factor_entire_finite_zeros}
