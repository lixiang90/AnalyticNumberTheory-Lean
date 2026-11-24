import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.TuranPowerSums
import AnalyticNumberTheory.DirichletLFunctions.TuranZeroDetection
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "Turán 幂和与零点检测" =>
%%%
tag := "turan-power-sums"
file := "turan-power-sums"
%%%

{index}[Turán 幂和]设有 $`N` 个复数 $`z_j`，各带一个非负整数权 $`b_j`。若至少一个模最大的数有正权，且最大模 $`R>0`，那么对任意自然数 $`M`，在 $`M<k\le M+N` 内总有一个幂次满足

$$`\left|\sum_j b_j z_j^k\right|\ge e^{-M-10N-2} R^k.`

例如，两个数 $`1,-1` 取相同权时，所有奇数次幂和都等于零，紧接着的偶数次幂和却是权之和。定理把这类结论推广到任意复相位，并给出一个长度只依赖于项数的区间。

{docstring turan_high_power_sum_scaled}

{index}[零点检测]在点 $`1+\eta+it` 附近，$`L'/L` 的高阶导数可以展开为到零点的距离倒数的幂和。若半径 $`2\eta` 的圆盘中有零点，且 $`0<\eta\le1/1024`、$`Y\ge q(|t|+2)`、$`\eta\log Y\ge1`，那么只要 $`M\ge C(1+\eta\log Y)`，就有 $`M<k\le2M` 使第 $`k-1` 阶导数除以 $`(k-1)!` 后的模至少为 $`(64\eta)^{-k}`。这里 $`C` 是绝对常数，特征可以是任意非主特征。

{docstring LFunction_turan_zero_detector}
