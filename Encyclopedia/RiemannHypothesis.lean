import AnalyticNumberTheory.RiemannZeta.LogarithmUnderRH
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

# ζ 函数的对数分支
%%%
tag := "rh-zeta-logarithm"
file := "zeta-logarithm"
%%%

{index}[ζ 函数的对数分支]在 $`\Re s>1`，Euler 乘积确定了 $`\log\zeta(s)` 的一个分支。向左延拓时，先消去 $`s=1` 的单极点，令
$$`\zeta_1(s)=(s-1)\zeta(s),\qquad \zeta_1(1)=1.`
黎曼猜想等价于 $`\zeta_1` 在整个半平面 $`\Re s>1/2` 上有全纯对数。正向推论使用了单连通域上无零点全纯函数的对数存在定理。反过来，复指数处处非零，所以这个对数的存在性排除了临界线右侧的非平凡零点。

{docstring riemannHypothesisProp_iff_exists_regularizedLog}

{docstring AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.exists_holomorphic_logarithm}

用 $`G(2)=\log\zeta(2)` 唯一确定 $`\zeta_1` 的全纯对数 $`G`。在实区间 $`[1,2]` 上，$`\zeta_1` 取正实值，故 $`G(1)=0`。

{docstring regularizedLogZeta}

{docstring regularizedLogZeta_one}

从半平面中删去实轴上的 $`(1/2,1]` 后，$`s-1` 的主值对数全纯。因此
$$`L(s)=G(s)-\operatorname{Log}(s-1)`
满足 $`e^{L(s)}=\zeta(s)` 及 $`L'(s)=\zeta'(s)/\zeta(s)`，并在 $`\Re s>1` 上与 Euler 乘积给出的分支一致。趋近 $`s=1` 时有 $`L(s)+\operatorname{Log}(s-1)\to 0`，这也确定了对数奇点的常数项。

{docstring slitLogZeta}

{docstring hasDerivAt_slitLogZeta}

{docstring slitLogZeta_eq_logZeta}

{docstring tendsto_slitLogZeta_add_log_at_one}
