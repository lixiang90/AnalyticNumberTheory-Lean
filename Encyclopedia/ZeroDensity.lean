import AnalyticNumberTheory.PrimeDistribution.ShortIntervalEstimates
import AnalyticNumberTheory.PrimeDistribution.ZetaLogFreeDensity
import AnalyticNumberTheory.PrimeDistribution.HoheiselLittlewood
import AnalyticNumberTheory.PrimeDistribution.HuxleyDensity
import AnalyticNumberTheory.PrimeDistribution.ConsecutivePrimeGaps
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

# Ingham 零密度定理
%%%
tag := "ingham-zeta-density"
file := "ingham"
%%%

{index}[Ingham 零密度定理]对 $`1/2\le\sigma\le1` 与 $`T\ge2`，正高度上不同零点的个数满足

$$`N(\sigma,T)\ll T^{3(1-\sigma)/(2-\sigma)}(\log T)^{11}.`

隐常数与 $`\sigma,T` 无关。高度的幂次在 $`\sigma=1/2` 时为一，而对每个固定的 $`1/2<\sigma<1` 都严格小于一。例如 $`\sigma=3/4` 时为 $`3/5`。若按重数计入每个零点，相同的高度幂次配上十二次对数幂。

{docstring ingham_zeroDensity}

{docstring ingham_zeroDensity_with_multiplicity}

证明把高度分为 $`[X,2X]`。在每个零点对截断的 Möbius 多项式使用 Riesz 核，移线到实部 $`1/2`。这样，每个零点都对应于一个有限 Dirichlet 多项式的大值，或一个临界线积分的大值。前者用离散均值估计控制，后者用{ref "critical-fourth-moment"}[ζ 的四阶矩]和 Möbius 多项式的均方共同控制。取截点 $`Y=X^{3/(4-2\sigma)}` 后，两项给出同一个高度幂次。

如果再假设加强的无零区，则对每个固定的 $`2/3<\theta<1` 都有 $`\pi(x+x^\theta)-\pi(x)\sim x^\theta/\log x`。这个明确的指数范围使用下述声明里的无零区假设。下节给出指数充分接近一时的无条件结论。

{docstring primePi_shortInterval_two_thirds_of_superLogZeroFree}

# Huxley 零密度定理
%%%
tag := "huxley-zeta-density"
file := "huxley"
%%%

{index}[Huxley 零密度定理]设 $`1/2\le\sigma\le1`、$`T\ge2`。以 $`N^*(\sigma,T)` 计入 $`\sigma\le\Re\rho<1`、$`0<\Im\rho\le T` 的 ζ 零点，每个零点计其重数。Huxley 的经典估计为

$$`N^*(\sigma,T)\ll T^{12(1-\sigma)/5}(\log T)^{28}.`

{docstring huxley_zeroDensity_classical}

高度幂次在 $`\sigma=3/4` 时和{ref "ingham-zeta-density"}[Ingham 的估计]相同，都是 $`3/5`。在 $`3/4<\sigma<1` 时 Huxley 的幂次更小。例如当 $`\sigma=9/10` 时，两者分别为 $`6/25` 与 $`3/11`。

在 $`[T,2T]` 上对 $`\sigma\ge3/4` 取平滑长度 $`Y=T^{6/5}`、Möbius 多项式长度 $`X=\lfloor T^{1/2+6(1-\sigma)/5}\rfloor`。有限多项式由大值估计控制，移到临界线的积分由 ζ 的四阶矩及 Möbius 多项式的大值分布控制。将各段相加后，库中的证明对不同零点给出二十二次对数幂，计入重数给出二十三次。两种形式均可直接引用。

{docstring huxley_zeroDensity_distinct}

{docstring huxley_zeroDensity_with_multiplicity}

若进一步给定加强的无零区，则对每个固定的 $`7/12<\theta<1` 得到素数计数渐近式 $`\pi(x+x^\theta)-\pi(x)\sim x^\theta/\log x`。阈值由 $`1-1/(12/5)=7/12` 给出。

{docstring huxley_primePi_shortInterval_of_superLogZeroFree}

# Hoheisel 定理与幂长短区间
%%%
tag := "hoheisel-prime-intervals"
file := "hoheisel"
%%%

{index}[Hoheisel 定理]存在一个固定指数 $`1/2<\theta_0<1`，使对每个固定的 $`\theta_0\le\theta<1`，当 $`x` 充分大时，

$$`\pi(x+x^\theta)-\pi(x)\ge \frac{x^\theta}{8\log x}.`

因此每个这样的区间 $`(x,x+x^\theta]` 都含有素数。证明先由无对数损失的零密度估计和经典无零区得到 $`\psi(x+x^\theta)-\psi(x)\ge x^\theta/2`，再估计高次素数幂的贡献，从对数权转回素数个数。

{docstring hoheisel_primes_in_power_intervals}

进一步结合{ref "littlewood-zero-free"}[Littlewood 无零区]，上述计数具有无条件的精确主项。存在固定的 $`1/2<\theta_0<1`，对每个 $`\theta_0\le\theta<1` 都有

$$`\pi(x+x^\theta)-\pi(x)\sim\frac{x^\theta}{\log x}.`

{docstring hoheisel_prime_asymptotic}

同一区间上的 von Mangoldt 权重和与素数对数权重和都渐近于区间长度 $`x^\theta`。

{docstring hoheisel_chebyshev_asymptotic}

证明也提供一个可复用的接口。只需无零区宽度 $`\delta(t)` 满足 $`\delta(t)\log t\to\infty`，即可压低显式公式中的零点贡献。宽度可以随高度非单调变化。

{docstring hoheisel_prime_asymptotic_of_improving_width}

设 $`p_n` 是按递增顺序排列的素数。把区间的左端点取为 $`p_n`，便得到 $`p_{n+1}-p_n=O(p_n^\theta)`。若 $`\theta_0<\theta<1`，可先对介于 $`\theta_0` 与 $`\theta` 之间的指数应用此界，得到 $`p_{n+1}-p_n=o(p_n^\theta)`。

{docstring hoheisel_prime_gap_littleO}

还有一个整次幂的推论。存在整数 $`k_0\ge2`，对每个固定的 $`k\ge k_0` 和所有充分大的 $`n`，开区间 $`(n^k,(n+1)^k)` 中都有素数。这里的 $`k_0` 来自 $`k(1-\theta_0)\ge1`。

{docstring hoheisel_primes_between_powers}

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
