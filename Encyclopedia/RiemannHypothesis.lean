import AnalyticNumberTheory.RiemannZeta.MoebiusDirichletSeries
import AnalyticNumberTheory.RiemannZeta.OneLineUnderRH
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

另一个算术等价命题来自素数计数。{ref "von-koch-error"}[von Koch 判别法]表明，黎曼猜想等价于 $`\psi(x)-x=O(\sqrt{x}(\log x)^2)`。

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

# 临界线右侧的对数增长界
%%%
tag := "rh-logarithmic-growth"
file := "logarithmic-growth"
%%%

{index}[Littlewood 对数估计]设黎曼猜想成立，取定 $`1/2<\sigma_0\le1` 和 $`\varepsilon>0`。设 $`L(s)` 是从 Euler 乘积延拓来的{ref "rh-zeta-logarithm"}[对数分支]。对所有 $`s=\sigma+it` 满足 $`\sigma_0\le\sigma\le1`、$`|t|\ge2`，有
$$`|L(\sigma+it)|\le C_{\sigma_0,\varepsilon}(\log |t|)^{2-2\sigma+\varepsilon}.`
这个估计中的常数对整条闭带一致。越接近 $`\sigma=1`，允许的对数幂次越小。

{docstring norm_slitLogZeta_le_log_rpow}

证明在同心圆上比较 $`L` 的大小。内圆完全落在 $`\Re s\ge a>1` 内。这里 Dirichlet 级数的系数 $`\Lambda(n)/\log n` 非负，所以 $`|L(s)|\le\log\zeta(a)`。在外圆上，$`\Re L(s)=\log|\zeta(s)|`；Borel–Carathéodory 定理把实部的上界转化为整个对数的上界 $`O(\log |t|)`。

{docstring norm_logZeta_le_log_norm_riemannZeta}

{docstring norm_slitLogZeta_on_closedBall}

取小量 $`\delta>0`，令圆心为 $`r+1+\delta+it`，内外圆半径分别为 $`r` 和 $`r+1/2`。点 $`\sigma+it` 到圆心的距离是 $`r+a`，其中 $`a=1+\delta-\sigma`。Hadamard 三圆定理给出对数幂次
$$`\frac{\log(1+a/r)}{\log(1+1/(2r))}\le 2a+\frac{a}{r}.`
选取足够小的 $`\delta` 和足够大的 $`r` 就得到所需的指数。

固定 $`\sigma_0>1/2` 后，可以取 $`\varepsilon` 使整条带上的指数严格小于一。因此 $`L(s)=o(\log|t|)`，而 $`\zeta(s)=e^{L(s)}` 及其倒数对任意 $`\eta>0` 在充分大高度均至多为 $`|t|^\eta`。

{docstring norm_slitLogZeta_le_mul_log_of_large_height}

{docstring norm_riemannZeta_and_inv_le_rpow_of_large_height}

# 直线 Re s = 1 上的 Littlewood 估计
%%%
tag := "rh-littlewood-one-line"
file := "littlewood-one-line"
%%%

{index}[Littlewood 在实部一上的估计]在 $`\sigma=1` 处，{ref "rh-logarithmic-growth"}[对数幂估计]对每个固定的 $`\varepsilon>0` 给出 $`O_\varepsilon((\log|t|)^\varepsilon)`。假设黎曼猜想，沿高度 $`t` 的一段短水平线积分，可以保留更精确的主项系数。对充分大的 $`|t|`，Euler 乘积延拓来的分支满足
$$`|\log\zeta(1+it)|\le \log\log\log|t|+A.`

{docstring norm_slitLogZeta_one_le_log_log_log}

令 $`m=\log\log|t|`、$`\delta=1/m`。在 $`\Re s\ge1+\delta`，非负的 von Mangoldt 系数给出 $`|\zeta'(s)/\zeta(s)|\ll1/\delta`。在圆心 $`2+it`、半径 $`5/4` 的圆上，Cauchy 导数估计给出 $`O(\log|t|)`。应用三圆定理，在 $`|\Re s-1|\le\delta` 内得到
$$`\left|\frac{\zeta'(s)}{\zeta(s)}\right|\ll\log\log|t|.`

{docstring norm_logDeriv_riemannZeta_near_one_of_rh}

从 $`1+\delta+it` 到 $`1+it` 的距离恰好为 $`1/m`，所以对数在这段路上只变化 $`O(1)`。右端的 Euler 级数给出 $`|\log\zeta(1+\delta+it)|\le\log\zeta(1+\delta)\le\log(2/\delta)`。这就得到上面的三重对数估计。分别对 $`\Re\log\zeta` 和它的相反数取指数，得到
$$`|\zeta(1+it)|\ll\log\log|t|,\qquad |1/\zeta(1+it)|\ll\log\log|t|.`

{docstring norm_riemannZeta_one_and_inv_le_log_log}

# Möbius 级数的普通收敛
%%%
tag := "rh-moebius-series"
file := "moebius-series"
%%%

{index}[Möbius 级数]按自然次序取部分和 $`F_N(s)=\sum_{n\le N}\mu(n)n^{-s}`。黎曼猜想成立的充要条件是，对每个 $`\Re s>1/2`，数列 $`F_N(s)` 都收敛。等价地，该级数的普通收敛横坐标恰好等于 $`1/2`。

{docstring riemannHypothesisProp_iff_moebiusDirichletConverges}

{docstring riemannHypothesisProp_iff_moebiusAbscissa_eq_half}

记 $`F` 为收敛半平面中的和函数。由 Euler 乘积和解析延拓，整个开收敛半平面中都有 $`F(s)((s-1)\zeta(s))=s-1`，其中括号内的函数在 $`s=1` 处取值 $`1`。如果非平凡零点落在这个开半平面内，等式两侧在该点矛盾。因此每个非平凡零点的实部都给出收敛横坐标的下界，{ref "hardy-critical-zeros"}[Hardy 定理]使这个下界至少为 $`1/2`。

{docstring moebiusDirichletSum_mul_zetaOne}

在黎曼猜想下，$`\Re s>1/2` 时的极限是 $`1/\zeta(s)` 的全纯延拓，在极点 $`s=1` 处极限为零。在 $`1/2<\Re s\le1` 的带内，这是条件收敛。绝对收敛半平面仍为 $`\Re s>1`。

{docstring tendsto_moebiusDirichletPartialSum_of_rh}

{docstring moebiusDirichletSeries_conditionally_convergent_of_rh}
