import AnalyticNumberTheory.RiemannZeta.HardyTheorem
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "Hardy 定理与临界线上的零点" =>
%%%
tag := "hardy-critical-zeros"
file := "hardy-critical-zeros"
%%%

{index}[Hardy 定理]存在任意高的正实数 $`t` 使 $`\zeta(1/2+it)=0`。库中证明了一个带区间的结论。对每个充分大的 $`T`，区间 $`[T,2T]` 中至少有一个这样的纵坐标。

{docstring eventually_exists_critical_zero_dyadic}

{docstring hardy_critical_zeros_infinite}

Hardy 函数 $`Z(t)` 是把 ζ 函数乘以一个模为一的相位后得到的实值函数。因此 $`|Z(t)|=|\zeta(1/2+it)|`。在区间 $`[T,2T]` 上，不取绝对值的一阶积分是 $`O(T^{3/4})`，而绝对值积分对于充分大的 $`T` 至少是 $`T/2`。

{docstring integral_hardyZ_dyadic_isBigO}

{docstring eventually_half_le_integral_abs_hardyZ}

若区间中没有零点，连续实函数 $`Z` 在整个区间保持同号。此时积分的绝对值必须等于绝对值的积分，这与上面两个估计矛盾。{ref "critical-second-moment"}[二阶矩公式]则给出了同一条直线上幅值的平方均值。
