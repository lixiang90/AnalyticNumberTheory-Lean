import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools.Summation

#doc (Manual) "Abel 分部求和与调和数" =>
%%%
tag := "abel-summation"
file := "abel-summation"
%%%

{index}[Abel 分部求和]给定实数 $`x\ge 1`，记 $`H_{\lfloor x\rfloor}=\sum_{1\le n\le x}1/n`。把计数函数 $`\lfloor t\rfloor=t-\{t\}` 代入 Abel 分部求和公式，连续部分给出 $`\log x`，小数部分留下一个可积的余项。

{docstring sum_inv_abel_formula}

从 $`1` 积到无穷远，余项产生 Euler 常数 $`\gamma`。截断在 $`x` 处时，调和数与 $`\log x+\gamma` 的距离至多为 $`1/x`。这个误差界对非整数端点同样成立。

{docstring abs_sum_inv_sub_log_sub_gamma_le}
