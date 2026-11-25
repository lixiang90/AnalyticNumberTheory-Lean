import AnalyticNumberTheory.PrimeDistribution.FixedModulusIngham
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyIngham
import AnalyticNumberTheory.DirichletLFunctions.FamilyDensityCounts
import AnalyticNumberTheory.PrimeDistribution.PrincipalCharacterDensity
import AnalyticNumberTheory.PrimeDistribution.CharacterDetectorWindow
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeI
import AnalyticNumberTheory.PrimeDistribution.CharacterInghamTypeII
import AnalyticNumberTheory.PrimeDistribution.ShortIntervalEstimates
import AnalyticNumberTheory.PrimeDistribution.ZetaLogFreeDensity
import AnalyticNumberTheory.PrimeDistribution.HoheiselLittlewood
import AnalyticNumberTheory.PrimeDistribution.HuxleyPrimeIntervals
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

$$`N(\sigma,T)\ll T^{3(1-\sigma)/(2-\sigma)}(\log T)^7.`

隐常数与 $`\sigma,T` 无关。高度的幂次在 $`\sigma=1/2` 时为一，在 $`\sigma=3/4` 时为 $`3/5`。若计入每个零点的重数，同一高度幂次配上八次对数幂。

{docstring ingham_zeroDensity_log_seven}

{docstring ingham_zeroDensity_with_multiplicity_log_eight}

{index}[主特征的零点计数]任意正模数的主特征满足 $`L(s,\chi_0)=\zeta(s)\prod_{p\mid q}(1-p^{-s})`。附加因子的零点都在虚轴上。因此在 $`\Re s\ge\sigma>0`，主特征保留 ζ 零点的重数。再用共轭对称性及 ζ 在实区间 $`(0,1)` 上无零点，双侧高度计数恰是正高度计数的两倍。取高度规模 $`T+2`，所得八次对数幂估计对所有 $`T\ge0` 成立，常数与模数无关。

{docstring characterDensityCount_principal_eq_twice}

{docstring principal_character_ingham_density}

证明把高度分为 $`[X,2X]`。在每个零点对截断的 Möbius 多项式使用 Riesz 核，移线到实部 $`1/2`。这样，每个零点都对应于一个有限 Dirichlet 多项式的大值，或一个临界线积分的大值。前者用离散均值估计控制，后者用{ref "critical-fourth-moment"}[ζ 的四阶矩]和 Möbius 多项式的均方共同控制。取截点 $`Y=X^{3/(4-2\sigma)}` 后，两项给出同一个高度幂次。

结合{ref "vinogradov-korobov-zero-free"}[Vinogradov–Korobov 无零区]，对每个固定的 $`2/3<\theta<1` 都有 $`\pi(x+x^\theta)-\pi(x)\sim x^\theta/\log x`。下述声明也适用于其他满足同一宽度条件的无零区。

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

将 Huxley 密度定理与{ref "vinogradov-korobov-zero-free"}[Vinogradov–Korobov 无零区]合用，对每个固定的 $`7/12<\theta<1` 得到素数计数渐近式 $`\pi(x+x^\theta)-\pi(x)\sim x^\theta/\log x`。阈值由 $`1-1/(12/5)=7/12` 给出。

{docstring huxley_primePi_shortInterval}

{docstring huxley_primePi_shortInterval_of_superLogZeroFree}

对接近临界指数的区间也有定量推论。固定 $`a>1`。当 $`x` 充分大且

$$`h\ge x^{7/12}\exp\!\bigl((\log x)^{2/3}(\log\log x)^{a+1/3}\bigr)`

时，存在 $`c,C>0` 使 $`|\psi(x+h)-\psi(x)-h|\le Ch\exp(-c(\log\log x)^a)`。这个估计对满足下界的所有实数 $`h` 一致，包括 $`h>x`。

{docstring huxley_psi_interval}

{docstring huxley_psi_interval_of_vinogradovKorobov}

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

# 按导子分组与非主特征零点的检测
%%%
tag := "character-mellin-zero-detection"
file := "character-mellin-zero-detection"
%%%

对模 $`q` 的特征 $`\chi`，令 $`N_\chi(\sigma,T)` 表示满足 $`0<\Re\rho<1`、$`\Re\rho\ge\sigma` 和 $`|\Im\rho|\le T` 的零点数，每个零点按解析重数计入。若 $`\chi` 由导子 $`d` 上的原始特征 $`\psi` 诱导，则在开临界带内，从 $`L(s,\psi)` 到 $`L(s,\chi)` 增加的有限个 Euler 因子均非零。因此两个函数在该带内的零点及其重数相同。将全部特征按导子重排，得到

$$`\sum_{\chi\bmod q}N_\chi(\sigma,T)
 =\sum_{d\mid q}\sum_{\substack{\psi\bmod d\\\psi\ \mathrm{primitive}}}N_\psi(\sigma,T).`

{docstring AnalyticNumberTheory.DirichletLFunctions.modulusDensityCount_eq_sum_primitive}

{docstring AnalyticNumberTheory.DirichletLFunctions.modulusDensityCount_trivial}

对非主特征，取 $`M_X(s,\chi)=\sum_{n\le X}\mu(n)\chi(n)n^{-s}`。乘积 $`L(s,\chi)M_X(s,\chi)` 的 Dirichlet 系数在 $`2\le n\le X` 上消失。对乘积使用六阶 Riesz 权 $`(1-n/Y)^6` 后，将积分线移到 $`\Re w=1/2-\Re\rho`。分母在 $`w=0` 的零点由 $`L(\rho,\chi)=0` 抵消。这个论证也适用于非主特征的实零点。

{docstring character_riesz_inversion}

{docstring character_mellin_dichotomy}

对 $`X\ge1`、$`Y\ge16` 和 $`1/2<\Re\rho<1`，检测器给出两个可能。有限多项式在零点处的模至少为 $`1/4`，或移线后归一化积分的模至少为 $`1/4`。前者用特征多项式的混合均方控制。后者在同一高度窗口上使用加权 Hölder 不等式，将其化为 $`L` 函数的四阶矩和 $`M_X` 的二阶矩。核随纵坐标差以六次幂衰减，使这个窗口可以扩大而保持统一的估计。

{docstring character_ingham_typeI_count}

{docstring character_ingham_typeII_count}

# 固定模数的 Ingham 零密度界
%%%
tag := "fixed-modulus-ingham-density"
file := "fixed-modulus-ingham-density"
%%%

取 $`q\ge1`、$`T\ge2` 和 $`1/2\le\sigma\le1`。记 $`e(\sigma)=3(1-\sigma)/(2-\sigma)`。模 $`q` 的全部特征满足

$$`\sum_{\chi\bmod q} N_\chi(\sigma,T)
  \ll (qT)^{e(\sigma)}\bigl(\log(qT)\bigr)^9.`

这里的常数与 $`q,T,\sigma` 无关。总数包括主特征、非原始特征和实零点，每个零点按重数计入。非主特征的证明把{ref "character-mellin-zero-detection"}[两种零点检测结果]分别求和。取与 $`qT` 同阶的整数 $`X` 和 $`Y=X^{3/(4-2\sigma)}` 后，两个上界中的幂次相同。靠近 $`\sigma=1/2` 时，以单位高度区间的计数控制全部零点。主特征的贡献则通过导子一的特征归结到 $`\zeta` 的零点。

{docstring modulusDensityCount_ingham}

# 按原始导子求和的 Ingham 零密度界
%%%
tag := "primitive-family-ingham-density"
file := "primitive-family-ingham-density"
%%%

对每个导子 $`q\le Q` 的原始特征求和，{ref "character-family-critical-fourth"}[临界线第四矩]与原始特征混合大筛共同给出尺度 $`Q^2T`。设 $`Q\ge1`、$`T\ge2`、$`1/2\le\sigma\le1`。每个零点按解析重数计入，纵坐标从 $`-T` 到 $`T`，则

$$`\sum_{1\le q\le Q}\ \sum_{\chi\bmod q}^{*}N_\chi(\sigma,T)
  \ll (Q^2T)^{3(1-\sigma)/(2-\sigma)}\bigl(\log(QT)\bigr)^9.`

{docstring primitive_conductors_ingham_density}

原始特征族在复共轭下保持不变，因此正、负高度可在同一个估计中处理。有限族中唯一的原始主特征具有导子一，其 $`L` 函数是 Riemann ζ 函数。把它单独计入，可将总数精确拆为模一的零点数与原始非主特征的带重数零点数。这一拆分也适用于 $`Q=1`。

{docstring primitive_density_sum_eq_principal_add}

{docstring primitiveFamilyZeroCount_ingham}
