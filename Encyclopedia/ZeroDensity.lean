import AnalyticNumberTheory.PrimeDistribution.ShortIntervalEstimates
import AnalyticNumberTheory.PrimeDistribution.ZetaLogFreeDensity
import AnalyticNumberTheory.PrimeDistribution.Hoheisel
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "ζ 函数的零密度估计与短区间素数" =>
%%%
tag := "zero-density"
file := "zero-density"
%%%

{index}[零密度估计]令 $`N(\sigma,T)` 计入满足 $`\sigma\le\Re\rho<1`、$`0<\Im\rho\le T` 的不同 ζ 零点。若 $`1/2\le\sigma\le1`、$`T\ge2`，有

$$`N(\sigma,T)\ll T^{4(1-\sigma)}(\log T)^{11}.`

当 $`\sigma>3/4` 时，右端的高度幂次小于一。证明用{ref "zero-detection"}[截断 Möbius 多项式]把零点转成 Dirichlet 多项式的大值，再在单位高度区间取样。若每个零点按重数计入，库中给出的界多一个对数因子。

{docstring zeta_zeroDensity}

{docstring zeta_zeroDensity_with_multiplicity}

若只需要一个绝对指数，可以消去对数因子。把正、负高度的非平凡零点一并按重数计入，在 $`0\le\sigma\le1`、$`T\ge0` 上得到

$$`N_{\mathrm{sym}}(\sigma,T)\le C(T+2)^{A(1-\sigma)}.`

这里的 $`A,C>0` 是绝对常数。直接对 ζ 的高阶对数导数使用 Turán 幂和，处理模一主特征，再把有界高度的零点并入常数。

{docstring zetaDensityCount_log_free}

{index}[短区间素数]截断显式公式把 $`\psi(x+h)-\psi(x)` 与零点的贡献联系起来。对于 $`h=x^\theta` 和 $`3/4<\theta<1`，下述结论仍使用声明中的加强无零区假设。零密度估计与截断显式公式两项已由库中的定理给出。

在两个端点分别截断显式公式。每个零点对差值的贡献可由 $`h x^{\Re\rho-1}` 乘以其重数控制。截断高度 $`2\le T\le x` 可自由选择，以平衡零点和与截断误差。

{docstring psi_interval_zero_sum_bound}

{docstring psi_shortInterval_of_superLogZeroFree}

另一个无条件范围直接来自带误差项的{ref "prime-counting"}[素数定理]。存在 $`d>0`，取 $`h=x\exp(-d\sqrt{\log x})` 时，$`\psi(x+h)-\psi(x)` 与 $`\vartheta(x+h)-\vartheta(x)` 都渐近于 $`h`。

{docstring chebyshev_expShortInterval}

# Hoheisel 定理与幂长短区间
%%%
tag := "hoheisel-prime-intervals"
file := "hoheisel"
%%%

{index}[Hoheisel 定理]存在一个固定指数 $`1/2<\theta_0<1`，使对每个固定的 $`\theta_0\le\theta<1`，当 $`x` 充分大时，

$$`\pi(x+x^\theta)-\pi(x)\ge \frac{x^\theta}{8\log x}.`

因此每个这样的区间 $`(x,x+x^\theta]` 都含有素数。证明先由无对数损失的零密度估计和经典无零区得到 $`\psi(x+x^\theta)-\psi(x)\ge x^\theta/2`，再估计高次素数幂的贡献，从对数权转回素数个数。

{docstring hoheisel_primes_in_power_intervals}

若已有无零区宽度 $`\delta(t)` 满足 $`\delta(t)\log t\to\infty`，同一方法可使零点和趋于零，从而把素数个数的下界改进为渐近式 $`\pi(x+x^\theta)-\pi(x)\sim x^\theta/\log x`。这个推论允许宽度随高度非单调变化。

{docstring hoheisel_prime_asymptotic_of_improving_width}

# Dirichlet 特征族的零点
%%%
tag := "dirichlet-family-density"
file := "character-families"
%%%

令 $`Y=Q(T+2)`，其中 $`Q\ge1`、$`T\ge0`。把模数不超过 $`Q` 的所有原始非主特征放在一起，统计各自 $`L` 函数在 $`\sigma\le\Re\rho<1`、$`|\Im\rho|\le T` 的零点。对 $`3/4\le\sigma\le1`，不同零点按每个特征分别计数后，总数至多为

$$`C(1+\log Y)^{10}Y^{16(1-\sigma)}.`

常数 $`C` 与模数上限、高度和实部截点无关。共轭特征把负纵坐标的零点映到正纵坐标，实零点也计入这个估计。

{docstring dirichlet_family_zeroDensity}

按重数计数时，对每个零点再用局部零点个数控制其重数，得到幂次为十一的对数因子。结合全临界带内的粗计数，这个带重数的上界适用于 $`0\le\sigma\le1`。若 $`(1-\sigma)\log Y\ge\log(1+\log Y)`，还可把对数因子吸收到幂中，得到 $`CY^{27(1-\sigma)}`。

{docstring primitiveFamilyZeroCount_le}

{docstring primitiveFamilyZeroCount_le_of_log_gap}

{index}[无对数损失的零密度定理]使用{ref "turan-power-sums"}[Turán 幂和]与{ref "prime-hybrid-sieve"}[素数支撑的混合大筛]，可以把带重数的估计写为

$$`\sum_{q\le Q}\ \sum_{\substack{\chi\bmod q\\\chi\ \mathrm{primitive,\ nonprincipal}}}N_\chi(\sigma,T)
\le C\,[Q(T+2)]^{A(1-\sigma)}.`

这里 $`Q\ge1`、$`T\ge0`、$`0\le\sigma\le1`。常数 $`C,A>0` 绝对，计数同时覆盖正负高度。这种形式在 $`\sigma` 逼近一时尤其重要，因为当 $`(1-\sigma)\log(Q(T+2))` 有界时，右侧仍然有界。

{docstring primitiveFamilyZeroCount_log_free}
