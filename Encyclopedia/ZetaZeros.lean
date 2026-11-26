import AnalyticNumberTheory.PrimeDistribution.ShiftedMangoldtMean
import AnalyticNumberTheory.PrimeDistribution.ZeroTailAsymptotic
import AnalyticNumberTheory.RiemannZeta.PoissonZeroAsymptotic
import AnalyticNumberTheory.RiemannZeta.LogDerivativeLeft
import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions
import AnalyticNumberTheory.RiemannZeta.IntegratedArgument
import AnalyticNumberTheory.RiemannZeta.ZeroCounting
import AnalyticNumberTheory.RiemannZeta.ZeroFreeRegion
import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "ζ 函数的零点计数与无零区域" =>
%%%
tag := "zeta-zeros"
file := "zeta-zeros"
%%%

{index}[Riemann–von Mangoldt 公式]设 $`N(T)` 按重数计入临界带中所有满足 $`0<\operatorname{Im}(\rho)\le T` 的零点。辐角原理把这个整数与边界上的辐角变化联系起来。Gamma 因子的 Stirling 展开给出光滑主项，在 $`T\ge2` 时有

$$`N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e}+\frac78+O(\log T).`

{docstring riemannVonMangoldt_asymptotic}

{index}[无零区域]计数控制零点的总数，无零区域则限制它们能靠实部一多近。存在 $`c>0` 使 $`\sigma\ge 1-c/\log(|t|+2)` 的区域没有零点。取素数计数的积分路径时，这条边界决定了能将路径向左移动的距离。

{docstring riemannZeta_zero_free_region}

# 用 Dirichlet 多项式探测零点
%%%
file := "zero-detection"
tag := "zero-detection"
%%%

用截断的 Möbius 级数乘以 ζ 函数的有限 Dirichlet 近似。除常数项外，乘积中 $`n\le N` 的系数全部抵消。对于充分大的 $`N`，若 $`\rho` 是零点、$`\Re\rho\ge3/4` 且 $`N\le |\Im\rho|\le 2N`，则剩下的多项式在 $`\rho` 处的模至少为 $`1/2`。这将计数这些零点的问题转化为估计多项式取大值的次数。

{docstring AnalyticNumberTheory.PrimeDistribution.zetaDetector_large_at_zero}

# ζ 函数辐角的一次积分
%%%
tag := "integrated-zeta-argument"
file := "integrated-argument"
%%%

{index}[辐角的一次积分]在零点计数公式中，$`S(t)` 记录 ζ 函数沿折线的辐角变化除以 $`\pi` 的值，在零点高度取右极限。逐点估计 $`S(t)=O(\log t)` 只能直接给出积分的 $`O(T\log T)` 上界。实际上，正负变化相互抵消，$`S_1(T)=\int_0^T S(t)\,dt` 满足

$$`|S_1(T)|\le C\log T\qquad(T\ge8).`

{docstring integratedArgument_abs_le_log}

为看出抵消，引入水平积分 $`P(t)=\int_{1/2}^2\log|\zeta(\sigma+it)|\,d\sigma`。从 ζ 函数中逐一提出局部零点因子后，$`P` 在零点高度仍连续，且 $`P(t)=O(\log t)`。避开零点高度时，$`P'(t)=\pi S(t)-\arg\zeta(2+it)`。有限高度带只有有限个零点高度，因此可以跨过它们积分。

{docstring zeta_horizontalLogMean_bound}

{docstring hasDerivAt_zeta_horizontalLogMean}

在实部二的直线上，Euler 乘积的对数有绝对收敛的 Dirichlet 级数。再除一次对数得到有界原函数，故任意区间上 $`\arg\zeta(2+it)` 的积分绝对值至多为 $`\pi^2/(3\log2)`。这给出 $`S_1` 在两个高度间的精确增量公式。

{docstring abs_integral_arg_riemannZeta_two_le}

{docstring integratedArgument_increment}

# 分离 ζ 对数导数的全部极点
%%%
tag := "centered-zeta-partial-fractions"
file := "centered-partial-fractions"
%%%

{index}[对数导数的部分分式展开]对一个非零位置 $`\omega`，先从 $`1/(s-\omega)` 减去它在原点的值，得到

$$`K_\omega(s)=\frac1{s-\omega}+\frac1\omega
              =\frac{s}{\omega(s-\omega)}.`

这样每个分式在 $`s=0` 消失。当 $`|\omega|\ge 2|s|` 时，它的模至多是 $`2|s|/|\omega|^2`。因此临界带内非平凡零点的倒平方和就足以保证绝对收敛。在原点附近，各项可以使用同一个可求和的上界。

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.centeredPole_eq}

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.norm_centeredPole_le}

{docstring AnalyticNumberTheory.AnalyticTools.EntireFunctions.tendsto_tsum_centeredPole_zero}

在 $`s\ne 1` 且 $`\zeta(s)\ne0` 时，完整公式为

$$`-\frac{\zeta'}{\zeta}(s)=-\log(2\pi)+K_1(s)
       -\sum_{\rho}K_{\rho}(s)-\sum_{k=1}^\infty K_{-2k}(s).`

每个非平凡零点按解析重数重复，负偶整数各出现一次。$`s=1` 是 ζ 的极点，在负对数导数中留数为 $`+1`；每个零点则贡献其重数的负值。取 $`s=0`，两个无穷级数与 $`K_1` 都消失，所以常数恰是 $`-\log(2\pi)`。

{docstring ZetaZeroEnumeration.summable_centered}

{docstring summable_centered_trivialZetaZero}

{docstring neg_logDeriv_riemannZeta_zero}

{docstring exists_centered_logDeriv_riemannZeta}

# Selberg 平滑公式
%%%
tag := "selberg-log-derivative"
file := "selberg-explicit-formula"
%%%

{index}[Selberg 平滑公式]取 $`x>1`。给 $`n\le x` 的系数以权重一，给 $`x<n\le x^2` 的系数以权重 $`\log(x^2/n)/\log x`，其余系数的权重为零。记这些权重为 $`w_x(n)`。以 $`x=2` 为例，$`n=2` 的权重是一，$`n=3` 的权重是 $`\log(4/3)/\log2`，$`n=4` 的权重是零。这个有限和可以从两个截断处的{ref "integrated-explicit-formula"}[对数加权和]相减得到。

{docstring AnalyticNumberTheory.DirichletSeries.logTaperedSum_eq_difference}

取 $`s\ne 1` 且 $`\zeta(s)\ne0`。将{ref "centered-zeta-partial-fractions"}[对数导数的部分分式展开]平移到 $`s`，新中心处的常数就是 $`-\zeta'(s)/\zeta(s)`。对平移后的展开作 Laplace 反演，得到系数 $`\Lambda(n)n^{-s}` 的对数加权和。

{docstring neg_logDeriv_riemannZeta_translate}

{docstring AnalyticNumberTheory.PrimeDistribution.logWeightedSum_shifted_vonMangoldt}

写 $`K_x(z)=(x^{2z}-x^z)/(z^2\log x)`。在 $`x` 和 $`x^2` 处取差、除以 $`\log x`，便得到
$$`-\frac{\zeta'}{\zeta}(s)=\sum_{n\le x^2}\frac{\Lambda(n)w_x(n)}{n^s}
-K_x(1-s)+\sum_\rho K_x(\rho-s)+\sum_{m\ge1}K_x(-2m-s).`
其中 $`\rho` 遍历所有非平凡零点，按重数计入。两个零点级数都绝对收敛。这个恒等式无需假设黎曼猜想。

{docstring AnalyticNumberTheory.PrimeDistribution.selberg_logDeriv_explicit_formula}

{docstring AnalyticNumberTheory.PrimeDistribution.summable_selberg_zero_slopes}

# 临界线上的 Poisson 零点和
%%%
tag := "critical-line-poisson-mass"
file := "poisson-zero-sum"
%%%

{index}[Poisson 零点和]设黎曼猜想成立，写 $`s=\sigma+it`、$`\delta=\sigma-\tfrac12`。每个零点 $`\rho=\tfrac12+i\gamma` 对 $`\Re(1/(s-\rho))` 的贡献为 $`\delta/(\delta^2+(t-\gamma)^2)`。将这些项按重数相加，记为 $`F(s)`。当 $`\delta>0` 时各项都为正。满足 $`|t-\gamma|\le\delta` 的每个零点至少贡献 $`1/(2\delta)`。

{docstring ZetaZeroEnumeration.poissonMass}

在 $`s\ne 0` 且 $`\xi(s)\ne0` 处有 $`F(s)=\Re(\xi'/\xi)(s)`。证明对 ξ 的 Hadamard 展开取实部，并减去它在 $`1/2` 处的值。泛函方程 $`\xi(s)=\xi(1-s)` 给出 $`\xi'(1/2)=0`，而每个零点在该处的上述贡献也为零。这样便确定了展开中的实常数。

{docstring deriv_xi_half}

{docstring ZetaZeroEnumeration.re_logDeriv_xi_eq_poissonMass}

把 ξ 的 Gamma 因子展开，可得
$$`F(s)=\Re\frac{\zeta'}{\zeta}(s)+\frac12\log\frac{|t|}{2\pi}
+O\!\left(\frac1{|t|}\right).`
这一余项对 $`0<\sigma\le2`、$`|t|\ge2` 内所有满足 $`\zeta(s)\ne0` 的点一致。即使 $`s` 接近零点，误差常数也相同。这里用到的 Gamma 估计是有界竖直带上 $`\Re\psi(z)=\log|\Im z|+O(1/|\Im z|)`，其中 $`\psi=\Gamma'/\Gamma`。

{docstring poissonMass_sub_re_logDeriv_estimate}

{docstring AnalyticNumberTheory.AnalyticTools.Gamma.abs_re_digamma_sub_log_height_le}

# ζ 对数导数在左半平面的增长
%%%
tag := "zeta-left-log-derivative"
file := "left-log-derivative"
%%%

{index}[ζ 对数导数的反射]记 $`D=\zeta'/\zeta`，$`\psi_\Gamma=\Gamma'/\Gamma`。实无穷位的因子为
$`\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)`。对其取对数导数，再对完成的 ζ 函数使用函数方程，就得到在 $`\Re s<0` 且避开负偶整数时成立的反射公式

$$`D(s)=\log\pi-D(1-s)-\tfrac12\psi_\Gamma(s/2)-\tfrac12\psi_\Gamma((1-s)/2).`

{docstring AnalyticNumberTheory.AnalyticTools.Gamma.logDeriv_gammaReal}

{docstring logDeriv_zeta_reflect_gamma}

在 $`\Re s\le-1/2` 内，反射点满足 $`\Re(1-s)\ge3/2`，此时 $`D(1-s)` 由绝对收敛的 von Mangoldt 级数一致控制。若 $`s` 与所有非正偶整数的距离至少为 $`d>0`，则存在同一个绝对常数 $`C`，使得

$$`|D(s)|\le d^{-1}+5\log(|s|+3)+C.`

{docstring norm_logDeriv_zeta_left_le_inv_add_log}

取 $`|\Im s|\ge1` 时可用 $`d=1`。取 $`\Re s=-1,-3,-5,\ldots` 时也可用 $`d=1`，即使 $`\Im s=0`。这些水平线和竖线可用作往左移动 Perron 积分时的矩形边界。

{docstring norm_logDeriv_zeta_left_edges}

# 正纵坐标的平方倒数尾和
%%%
tag := "positive-zero-reciprocal-tail"
file := "reciprocal-square-tail"
%%%

记 $`\rho=\beta+i\gamma`，每个非平凡零点按重数计。正纵坐标超过 $`T\ge2` 的零点满足精确的分部求和公式

$$`\sum_{\gamma>T}\frac{1}{\gamma^2}
=\int_T^\infty \frac{2(N(u)-N(T))}{u^3}\,du.`

对于 $`\gamma>T`，单个零点对积分的贡献是从 $`u=\gamma` 起累积的，恰为 $`1/\gamma^2`。这个写法也适用于 $`T` 本身是零点纵坐标的情形。

{docstring AnalyticNumberTheory.PrimeDistribution.positiveZeroReciprocalSquareTail_eq_integral}

将 Riemann–von Mangoldt 公式代入，得到

$$`\sum_{\gamma>T}\frac{1}{\gamma^2}
=\frac{\log(T/(2\pi))+1}{2\pi T}
+O\!\left(\frac{\log T}{T^2}\right).`

{docstring AnalyticNumberTheory.PrimeDistribution.positiveZeroReciprocalSquareTail_two_term}

计入所有 $`\gamma=T` 的零点，只会增加该高度的总重数除以 $`T^2`。单位高度区间的零点计数为 $`O(\log T)`，所以两项展开和误差界都保留。取首项就得到 $`\sum_{\gamma\ge T}\gamma^{-2}=(\log T)/(2\pi T)+O(1/T)`。

{docstring AnalyticNumberTheory.PrimeDistribution.tsum_positiveZero_div_im_sq_two_term}

{docstring AnalyticNumberTheory.PrimeDistribution.tsum_positiveZero_div_im_sq_main_term}
