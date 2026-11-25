import AnalyticNumberTheory.DirichletLFunctions.AllHeightWeyl
import AnalyticNumberTheory.DirichletLFunctions.NarrowLogarithmicStrips
import AnalyticNumberTheory.DirichletLFunctions.CriticalConductorBound
import AnalyticNumberTheory.DirichletLFunctions.DerivativeStrips
import AnalyticNumberTheory.DirichletLFunctions.VinogradovStrips
import AnalyticNumberTheory.DirichletLFunctions.WeylBound
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.ExponentialSums

#doc (Manual) "Hurwitz ζ 函数与 Dirichlet L 函数的 Weyl 界" =>
%%%
tag := "weyl-subconvexity"
file := "weyl-subconvexity"
%%%

{index}[Weyl 次凸界]在临界线 $`s=1/2+it` 上，黎曼 ζ 函数满足

$$`|\zeta(1/2+it)|\ll |t|^{1/6}(1+\log |t|),\qquad |t|\ge2\pi.`

由临界带两边的估计作凸性插值，所得高度指数为 $`1/4+\varepsilon`。这里的 $`1/6` 来自有限 Dirichlet 和中相位的相消。

{docstring riemannZeta_weyl_bound}

{index}[Hurwitz ζ 函数]对任意实移位 $`0<a\le1`，Hurwitz ζ 函数满足同一估计，只需在右侧另加 $`a^{-1/2}`。这一项正是级数首项 $`a^{-s}` 的模，余下部分的常数与移位无关。

{docstring hurwitzZeta_weyl_bound}

直接从函数中减去首项后，其余部分在整个移位区间上一致满足同一个 Weyl 界。

{docstring hurwitzZeta_sub_initial_weyl_bound}

将有限和按 $`M<n\le2M` 分段，考察对数相位 $`\tau\log(n+a)`，其中 $`\tau=-t/(2\pi)`。在中等长度的块上，取约 $`M/|\tau|^{1/3}` 个平均平移，前向差的二阶导数大小约为 $`|\tau|r/M^3`。用{ref "exponential-sums"}[van der Corput 方法]估计这些差分，再用分部求和乘回 $`(n+a)^{-1/2}`，每块贡献 $`O(|t|^{1/6})`。块的个数给出最后的对数因子。

{docstring logPhase_weyl_block}

若 $`\chi` 是模 $`q` 的 Dirichlet 特征，把级数按剩余类拆成 Hurwitz ζ 函数之和，可以得到在模数和高度上一致的界

$$`|L(1/2+it,\chi)|\ll \sqrt q\,|t|^{1/6}(1+\log |t|).`

对固定模数，这就给出了高度方向的 Weyl 指数。证明同样适用于模不超过一的周期系数。

{docstring LFunction_weyl_bound}

{docstring periodicLFunction_weyl_bound}

# 靠近一线的 Vinogradov 阶估计
%%%
tag := "vinogradov-hurwitz-growth"
file := "vinogradov-hurwitz-growth"
%%%

取 $`s=\sigma+it`、$`T=|t|\ge2` 和 $`L=\log T`。从 Hurwitz ζ 中扣掉首项以后，对一切 $`0<a\le1` 和 $`\sigma>0` 有一致估计

$$`|\zeta(s,a)-a^{-s}|\le D L^{2/3}\exp\!\bigl(K\max(1-\sigma,0)^{3/2}L\bigr).`

三次指数衰减列的求和给出 $`L^{2/3}`。因此在 $`\sigma\ge1-RL^{-2/3}` 的带内，指数因子能被只依赖 $`R` 的常数控制。

{docstring hurwitzZeta_sub_initial_vinogradov_bound}

{docstring hurwitzZeta_sub_initial_near_one}

在任意模数 $`q` 下，对周期系数扣去首个完整周期，再按剩余类应用上述一致界。对所有 Dirichlet 特征，在同一带内得到 $`|L(s,\chi)|\ll_R q^{R/L^{2/3}}L^{2/3}`，其中 $`R>0`。

{docstring periodicLFunction_sub_first_period_vinogradov}

{docstring LFunction_vinogradov_near_one}

取整数 $`k\ge2`。在 $`\sigma>0` 且 $`\sigma\ge1-k/(2^k-2)` 的带内，导数估计给出高度指数 $`1/(2^k-2)`，并带有因子 $`1+\log T`。Hurwitz 形式扣除首项，其常数对阶数和移位都一致。

{docstring hurwitzZeta_sub_initial_derivative_strips}

{docstring LFunction_derivative_strips}

在更宽的带内，令 $`\delta=R(\log L/L)^{2/3}`。对固定的 $`R>0` 和 $`T\ge10`，若 $`\sigma\ge1-\delta`，则 $`|L(s,\chi)|\ll_R q^\delta L^{2/3+K R^{3/2}}`，其中 $`K` 是绝对常数。

{docstring LFunction_vinogradov_loglog_strip}

固定 $`T=|t|\ge10`、$`L=\log T`。若带宽为 $`\delta=(\log L)^2/L`，则正则化的 Hurwitz ζ 函数满足 $`O(L^{2/3})`，Dirichlet L 函数满足 $`O(q^\delta L)`。若改取 $`\delta=R\log L/L`，在临界带内，后者满足 $`O_R(q^\delta L/\log L)`。

{docstring hurwitzZeta_sub_initial_log_squared_strip}

{docstring LFunction_log_over_loglog_strip}

有限阶导数估计也能延伸至低高度和虚轴。令 $`T_* = 2+|t|`，将极点贡献写为 $`16T_*^{1-\sigma}/(|1-\sigma|+|t|)`，则在 $`s\ne1` 时，余下部分的界对导数阶数与实移位都一致。

{docstring hurwitzZeta_sub_initial_derivative_strips_all_heights}

{docstring LFunction_derivative_strips_all_heights}

# 临界线上的模数与高度
%%%
tag := "critical-conductor-bound"
file := "critical-conductor-bound"
%%%

{index}[联合凸性界]设 $`\chi` 是任意模 $`q\ge1` 的 Dirichlet 特征。在整条临界线上同时保留模数与高度的依赖，可得

$$`|L(1/2+it,\chi)|\le C\bigl(q(1+|t|)\bigr)^{1/4}\qquad(t\in\mathbb R).`

这里 $`C` 是绝对常数。特别地，中心值满足 $`|L(1/2,\chi)|\ll q^{1/4}`。另一方面，若固定模数而让高度增大，Weyl 估计给出更小的高度指数。取 $`T_*=2+|t|`，覆盖全部高度的结论为

$$`|\zeta(1/2+it,a)-a^{-1/2-it}|\ll T_*^{1/6}(1+\log T_*),\qquad |L(1/2+it,\chi)|\ll q^{1/2}T_*^{1/6}(1+\log T_*).`

第一式的常数对 $`0<a\le1` 一致。第二式来自按模 $`q` 的剩余类分组，并估计第一周期的有限和。

{docstring norm_LFunction_critical_conductor_quarter}

{docstring hurwitzZeta_sub_initial_weyl_all_heights}

{docstring LFunction_weyl_all_heights}

## 平滑函数方程给出的长度

对本原特征，完备函数的对称函数方程把中心值写成两个 Gaussian 积分，分别含 $`\chi` 与其共轭特征。令 $`X=\sqrt{q(1+|t|)}`。把 Mellin 变量写成 $`w=c+iv`，除去中心的 Γ 因子后，权函数的模至多为 $`C_c X^c e^{-v^2/2}`。上界对特征的两种奇偶性均成立。

{docstring completedL_gaussian_functional_equation}

{docstring norm_characterGaussianKernel_le}

在 $`c=3/4` 的线上，Dirichlet 级数截于 $`N=\lceil X\rceil` 后的尾和是 $`O(N^{-1/4})`。将前 $`N` 项的积分移到 $`c=-1/4`，原点的留数给出中心多项式，大小是 $`O(\sqrt N)`。负线上的多项式是 $`O(N^{3/4})`。这样正线尾和、留数和负线积分都至多为 $`O(\sqrt X)`，正好得到四分之一次幂。非原始特征通过本原导子处的函数和有限个 Euler 因子得到同一上界。

{docstring characterGaussianMean_polynomial_shift}

{docstring norm_LFunction_primitive_critical_quarter}
