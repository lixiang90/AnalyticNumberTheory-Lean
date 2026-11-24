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
