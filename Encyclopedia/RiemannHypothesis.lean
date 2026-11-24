import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "黎曼猜想的等价命题" =>
%%%
tag := "riemann-hypothesis"
file := "riemann-hypothesis"
%%%

{index}[黎曼猜想]黎曼猜想断言 ζ 函数的每个非平凡零点都在 $`\Re s=1/2` 上。{ref "hardy-critical-zeros"}[Hardy 定理]给出了临界线上无穷多个零点。要得到黎曼猜想，还需排除临界带里偏离这条线的所有零点。函数方程的对称性说明，只需考虑临界线右侧。

{docstring riemannHypothesisProp_iff_ne_zero_of_half_lt_re}

令 $`M(x)=\sum_{n\le x}\mu(n)`。对每个 $`\varepsilon>0` 有 $`M(x)=O_\varepsilon(x^{1/2+\varepsilon})`，这一组算术估计与黎曼猜想等价。Möbius 函数的 Dirichlet 级数在绝对收敛半平面等于 $`1/\zeta(s)`，而分部求和把 $`M(x)` 的增长界转为级数收敛区域的信息。

{docstring riemannHypothesisProp_iff_mertensM_isBigO}

黎曼猜想还蕴含 Lindelöf 猜想，即 ζ 函数在临界线上满足任意正幂的增长上界。下面的 Lean 声明显式接受黎曼猜想作为前提。

{docstring riemannHypothesisProp_implies_lindelof}
