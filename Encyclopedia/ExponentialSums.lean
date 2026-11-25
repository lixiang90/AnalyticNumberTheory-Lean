import AnalyticNumberTheory.ExponentialSums.HigherDerivativeTests
import AnalyticNumberTheory.ExponentialSums.ReciprocalRealBlocks
import AnalyticNumberTheory.ExponentialSums.SharpPoissonSummation
import AnalyticNumberTheory.ExponentialSums.ReciprocalTransform
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue
import AnalyticNumberTheory.ExponentialSums.PrimeLinearSums
import AnalyticNumberTheory.ExponentialSums.PrimeDensityWeights
import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeSums
import AnalyticNumberTheory.ExponentialSums.PrimeContourDenominators
import AnalyticNumberTheory.PrimeDistribution.FixedModulusPolynomialMoments
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ExponentialSums

#doc (Manual) "从几何级数到 Weyl 和" =>
%%%
tag := "exponential-sums"
file := "exponential-sums"
%%%

{index}[Weyl 和]写 $`e(t)=\exp(2\pi i t)`。在线性相位下，相邻项之比恒为 $`e(\alpha)`。当 $`\alpha` 不是整数时，等比求和与平凡估计一起给出下式，其中 $`\|\alpha\|` 表示到最近整数的距离。

{docstring norm_sum_Ioc_e_le_min}

对于 $`S_k(\alpha)=\sum_{1\le n\le N}e(\alpha n^k)`，Hua 引理估计整个周期上的高次矩。以 $`k=2` 为例，对任意 $`\varepsilon>0`，四次矩为 $`O_{\varepsilon}(N^{2+\varepsilon})`。均值界允许某些 $`\alpha` 处的和很大，例如整数频率处所有项都等于一。

{docstring hua_lemma}

# 线性素数指数和的权重
%%%
tag := "linear-prime-exponential-sums"
file := "linear-prime-sums"
%%%

写 $`e(t)=\exp(2\pi it)`。同一频率 $`\alpha` 给出三个不同的有限和

$$`\Psi_\alpha(x)=\sum_{n\le x}\Lambda(n)e(\alpha n),\qquad
   \Theta_\alpha(x)=\sum_{p\le x}(\log p)e(\alpha p),\qquad
   P_\alpha(x)=\sum_{p\le x}e(\alpha p).`

前两个和相差的项全来自高次素数幂。逐项取模就有 $`|\Psi_\alpha(x)-\Theta_\alpha(x)|\le\psi(x)-\vartheta(x)`。对 $`x>1`，每个 $`p\le x` 还满足 $`1-\log p/\log x\ge0`，这给出去掉对数权重时的点态误差。

{docstring norm_primeExpSum_sub_logPrimeExpSum_le}

{docstring norm_unweightedPrimeExpSum_sub_div_log_le}

当 $`|\,\alpha-a/q\,|\le q^{-2}`、$`(a,q)=1` 且 $`x\ge2` 时，令

$$`V(x,q)=xq^{-1/2}+x^{4/5}+\sqrt{xq}.`

{index}[Vaughan 恒等式]把 von Mangoldt 加权和分解为可以分别估计的双线性和，给出 $`|\Psi_\alpha(x)|\le 10000 V(x,q)\log^4 x`。再用高次素数幂的总权重界，可得 $`|\Theta_\alpha(x)|\le 10016 V(x,q)\log^4 x`。

{docstring vinogradov_prime_exp_sum_bound}

{docstring logPrimeExpSum_vaughan_bound}

对无权和，从 $`\lceil\sqrt x\rceil` 处分开求和。小素数的贡献至多为 $`2\sqrt x`。在剩余部分对单调权 $`1/\log p` 使用 Abel 求和，若截至 $`x` 的对数加权部分和的模都不超过 $`H`，这一部分至多为 $`4H/\log x`。这一步保留了 $`q` 的依赖，并把 $`\log^4 x` 降为 $`\log^3 x`。

{docstring AnalyticNumberTheory.PrimeDistribution.norm_sum_primes_le_sqrt_add_of_log_bound}

{docstring unweightedPrimeExpSum_vaughan_bound}

若 $`0<Q\le x^{2/5}` 且 $`Q\le q\le x/Q`，则 $`V(x,q)\le 3x/\sqrt Q`。例如取 $`Q=x^{2/5}`，所有 $`x^{2/5}\le q\le x^{3/5}` 都给出 $`P_\alpha(x)\ll x^{4/5}\log^3 x`。

{docstring prime_exp_sums_balanced_bound}

# 从特征平均到有理频率
%%%
tag := "rational-prime-sums-density"
file := "rational-prime-sums"
%%%

取 $`(a,q)=1`。在可逆剩余类上展开 $`e(an/q)`，特征 $`\chi` 的系数绝对值至多为 $`\sqrt{\operatorname{cond}(\chi)}/\varphi(q)\le\sqrt q/\varphi(q)`。不可逆剩余类上只有素数底数整除 $`q` 的素数幂有贡献，其总权重至多为 $`(\log q/\log2)\log y`。

{docstring norm_primeExpSum_le_character_mean}

在{ref "fixed-modulus-character-means"}[固定模数的特征平均]中乘入这个 Gauss 系数界，再用 $`q/\varphi(q)\le6(1+\log q)`。对于 $`x\ge4`、$`1\le q\le x` 和任意 $`0\le y\le x`，这给出

$$`\left|\sum_{n\le y}\Lambda(n)e(an/q)\right|
 \ll \left(\frac{x}{\sqrt q}+x^{4/5}q^{1/10}+\sqrt{xq}\right)(1+\log x)^{11}.`

在这里，中间的 $`q^{1/10}` 来自零点平均中的 $`q^{3/5}` 与 Gauss 系数中的 $`q^{-1/2}`。整数分子可以为负，改变频率的符号会把整个素数和变为其复共轭。

{docstring primeExpSum_rational_zero_density}

# 从有理逼近到实频率
%%%
tag := "density-real-prime-frequencies"
file := "prime-frequency-approximation"
%%%

给定既约分数 $`a/q`，设 $`|\alpha-a/q|\le q^{-2}`。若 $`x|\alpha-a/q|\le2`，对{ref "rational-prime-sums-density"}[有理频率的估计]作一次 Abel 求和，就能控制实频率 $`\alpha`。频率移动 $`\beta` 至多使部分和界增加因子 $`1+2\pi x|\beta|`。

{docstring norm_primeExpSum_shift_of_bound}

当 $`x|\alpha-a/q|>2` 时，以 $`x/q` 为分母上限重新作 Dirichlet 逼近。两个不同既约分数的间距至少是其分母乘积的倒数。由此得到第二个分数 $`b/r`，满足

$$`\frac q2<r\le\frac{x}{q},\qquad x|\alpha-b/r|<2.`

{docstring AnalyticNumberTheory.AdditiveNumberTheory.exists_narrow_rational_approximation}

将 $`r\le x/q` 代入有理频率估计，原来的中间项至多为 $`x^{4/5}(x/q)^{1/10}=x^{9/10}q^{-1/10}`。合并宽、窄两种情形，令

$$`W(x,q)=\frac{x}{\sqrt q}+x^{4/5}q^{1/10}+\sqrt{xq}+\frac{x^{9/10}}{q^{1/10}}.`

于是 $`x\ge4` 时，对每个 $`0\le y\le x` 都有 $`|\Psi_\alpha(y)|\ll W(x,q)(1+\log x)^{11}`。

{docstring primeExpSum_zero_density}

去掉高次素数幂得到素数对数加权和的同一上界，再用{ref "linear-prime-exponential-sums"}[分部求和去掉素数对数]，无权和节省一个对数因子。当 $`0<Q\le x^{1/4}` 且 $`Q\le q\le x/Q`，四项都不超过 $`x/\sqrt Q`。在这个区间，三种素数和共享分母节省 $`Q^{-1/2}`。

{docstring logPrimeExpSum_zero_density}

{docstring unweightedPrimeExpSum_zero_density}

{docstring densityPrimeScale_le_of_denominator_range}

{docstring prime_sums_zero_density_balanced}

# 有理频率处的平滑素数和
%%%
tag := "logarithmic-prime-character-sums"
file := "smoothed-prime-sums"
%%%

在{ref "linear-prime-exponential-sums"}[von Mangoldt 指数和]中加入 $`\log(x/n)`，记所得的和为 $`S_1(\alpha,x)`。在有理频率 $`\alpha=a/q`，指数相位在每个剩余类上恒定。对可逆剩余类用 Dirichlet 特征展开，得到系数 $`\tau(\overline\chi,a)/\varphi(q)`。对每个特征，相应的平滑和在 $`\sigma>1` 时等于

$$`\frac1{2\pi}\int_{\mathbb R}
    \frac{-L'(\sigma+it,\chi)}{L(\sigma+it,\chi)}
    \frac{x^{\sigma+it}}{(\sigma+it)^2}\,dt.`

这条等式由{ref "logarithmic-perron"}[对数平滑的 Perron 公式]给出，对本原和非本原特征都成立。

{docstring logSmoothedPsiChar_eq_logDeriv_integral}

不可逆剩余类中有贡献的项是素数底数整除 $`q` 的素数幂。截至 $`t`，它们的总权重至多为 $`(\log q/\log 2)\log t`。从 $`1` 到 $`x` 对此界关于 $`dt/t` 积分，得到平滑特征展开的总误差至多为 $`\log q\,(\log x)^2/(2\log 2)`。

{docstring norm_logSmoothedPrimeExpSum_sub_characters}

从 $`x` 移到 $`y>x` 时，原有各项的权重全都增加 $`\log(y/x)`。因此 $`S_1(\alpha,y)-S_1(\alpha,x)` 的主项是 $`\log(y/x)\Psi_\alpha(x)`，近似误差只取决于短区间 $`(x,y]` 的 von Mangoldt 质量，至多为 $`\log(y/x)(\psi(y)-\psi(x))`。

{docstring norm_logSmoothedPrimeExpSum_difference}

# 素数权与 Möbius 权的短特征多项式
%%%
tag := "short-prime-polynomial-moments"
file := "short-polynomial-moments"
%%%

设 $`s=1/2+it`，记 $`P_a(s,\chi)=\sum_{n\le N}a_n\chi(n)n^{-s}`。平方后的多项式长为 $`N^2`，其中 $`k` 的系数是所有 $`uv=k`、$`u,v\le N` 的 $`a_ua_v` 之和。把{ref "critical-pointwise-character-means"}[固定模数特征均方]用在这个平方上，即可对任意给定的高度估计四阶矩。

{docstring AnalyticNumberTheory.DirichletLFunctions.critical_polynomial_fourth_energy}

当 $`|a_n|\le1` 时，平方系数的模至多为 $`d(k)`。利用{ref "divisor-power-means"}[除数函数的调和二阶矩]可得
$`\sum_{\chi\bmod q}|P_a(s,\chi)|^4\le(q+N^2)(1+\log(N^2))^4`。
对 $`a_n=\mu(n)`，相应的二阶矩至多为 $`(q+N)(1+\log N)`。

{docstring AnalyticNumberTheory.DirichletLFunctions.bounded_critical_polynomial_fourth}

{docstring AnalyticNumberTheory.PrimeDistribution.fixed_modulus_mobius_polynomial_moments}

取 $`a_n=\Lambda(n)`。由 $`\sum_{u\mid k}\Lambda(u)=\log k`，平方系数 $`b_k` 至多为 $`(\log N)\log k`。再按乘积把 $`\sum b_k/k` 拆回 $`(\sum_{n\le N}\Lambda(n)/n)^2`，Mertens 第一估计便给出 $`\sum b_k^2/k\ll(1+\log N)^4`。因此二阶矩与四阶矩分别至多为 $`O((q+N)(1+\log N)^2)` 和 $`O((q+N^2)(1+\log N)^4)`，两个常数对模数和高度一致。

{docstring AnalyticNumberTheory.PrimeDistribution.norm_factorPairWeight_vonMangoldt_le}

{docstring AnalyticNumberTheory.PrimeDistribution.vonMangoldt_square_harmonic_energy}

{docstring AnalyticNumberTheory.PrimeDistribution.fixed_modulus_vonMangoldt_polynomial_moments}

# 平滑素数和的两条积分线
%%%
tag := "prime-two-contours"
file := "two-contours"
%%%

设 $`\chi` 是模 $`q\ge2` 的非主特征，$`X=\lfloor x\rfloor`。在系数上把 Möbius 函数截于 $`U`，把 von Mangoldt 函数截于 $`V\ge1`。记相应的短特征多项式为 $`M_U` 和 $`P_V`，再记截短系数的 Dirichlet 卷积所给出的多项式为 $`I_{U,V}`。它的长度至多为 $`UV`。临界线上的分子为

$$`E(s)=P_V(s)-M_U(s)L'(s,\chi)-I_{U,V}(s)L(s,\chi).`

{docstring primeContourRegularPart}

右侧积分线上的分子 $`B(s)` 由两个有限尾段相乘得到。第一段的系数为 $`\sum_{d\mid m,\,d>U}\mu(d)`，范围为 $`U<m\le X/V`。第二段的系数为 $`\Lambda(k)`，范围为 $`V<k\le X`。两段都带同一个特征的权。对数 Perron 核在 $`mk>x` 时取逆所得权重为零，故这个矩形范围精确给出原来的双曲线和。

{docstring primeContourTailPart}

用{ref "log-perron-contour-shift"}[归一化积分] $`\mathcal P_\sigma` 表示，两条积分线给出的恒等式是

$$`\sum_{n\le x}\Lambda(n)\chi(n)\log(x/n)
=\mathcal P_{1/2}(E;x)+\mathcal P_1(B;x).`

{docstring logSmoothedPsiChar_two_contours}

证明对 Vaughan 的系数恒等式使用有限求和，再对每一项应用{ref "critical-character-perron-inversion"}[非主特征的临界线反演]和有限多项式乘法公式。等式对所有正实 $`x` 成立，两项均绝对可积。

{docstring AnalyticNumberTheory.DirichletLFunctions.logPerron_intervalCharacter_product}

在 $`\Re s=1` 上，$`|x^s|=x`，而 $`(2\pi)^{-1}\int_{\mathbb R}(1+t^2)^{-1}\,dt=1/2`，因此尾项的特征平均带有精确因子 $`x/2`。分别对两个因子应用{ref "fixed-modulus-tail-energy"}[剩余类尾和估计]。Möbius 尾段的系数由 $`d(m)` 控制，素数尾段使用 Mertens 的带权估计。

{docstring typeII_tail_polynomial_energy}

{docstring vonMangoldt_tail_polynomial_energy}

{docstring primeContourTail_integral_mean}

# 平滑素数特征和的固定模数平均
%%%
tag := "smoothed-prime-character-mean"
file := "smoothed-character-mean"
%%%

设 $`2\le q\le x`，写 $`L=1+\log x`。在{ref "prime-two-contours"}[双直线分解]中取相等的整数截断 $`A`。临界线上的短多项式长度依次为 $`A,A,A^2`。若 $`A^2\le x`，记 $`R=\sqrt q+A`，则三个多项式在特征群上的平方和开根后分别至多为 $`4RL,RL,RL^2`。这些界在每个实高度上成立。

{docstring primeContour_short_scale}

在临界线上对每个乘积使用 Cauchy 不等式，再把 $`L(s,\chi)` 和 $`L'(s,\chi)` 的{ref "critical-pointwise-character-means"}[特征均方]关于 $`dt/|s|^2` 积分，得到左侧积分的绝对值之和。右侧积分则使用尾段的剩余类估计。两侧的上界分别为

$$`C\sqrt x\sqrt q\,(\sqrt q+A)L^3,\qquad
2x(q/A+L)L^3.`

{docstring primeContourRegular_integral_mean}

{docstring primeContourTail_balanced}

取 $`Y=(xq)^{1/4}` 和 $`A=\lfloor Y\rfloor`。由 $`Y/2\le A\le Y` 和 $`\sqrt q\le Y`，两侧依赖截断的项都至多为常数倍的 $`(xq)^{3/4}L^3`。因此平滑特征和 $`\psi_1(x,\chi)=\sum_{n\le x}\chi(n)\Lambda(n)\log(x/n)` 满足

$$`\sum_{\chi\bmod q,\ \chi\ne\chi_0}|\psi_1(x,\chi)|
\ll xL^4+(xq)^{3/4}L^3.`

{docstring exists_primeContour_cutoff}

{docstring logSmoothedPsiChar_nonprincipal_mean}

# 平滑素数指数和的有理频率界
%%%
tag := "smoothed-rational-prime-bound"
file := "smoothed-rational-bound"
%%%

把 Chebyshev 的初等估计 $`|\psi(t,\chi)|\le(\log 4+4)t` 从 $`1` 到 $`x` 关于 $`dt/t` 积分，即得 $`|\psi_1(x,\chi)|\le(\log 4+4)(x-1)`。将此界用于主特征后，{ref "smoothed-prime-character-mean"}[固定模数平均]也适用于整个特征群。模数为一时只有主特征。

{docstring norm_logSmoothedPsiChar_le}

{docstring logSmoothedPsiChar_mean}

在{ref "logarithmic-prime-character-sums"}[有理频率的特征展开]中，每个既约分子对应的 Gauss 系数绝对值至多为 $`\sqrt q/\varphi(q)`。结合 $`q/\varphi(q)\le6(1+\log q)`，对每个 $`1\le q\le x`、每个与 $`q` 互素的整数 $`a`，得到

$$`\left|\sum_{n\le x}\Lambda(n)e(an/q)\log(x/n)\right|
\ll \frac{x}{\sqrt q}(1+\log x)^5
+x^{3/4}q^{1/4}(1+\log x)^4.`

第一项随分母增大而减小，第二项随分母增大而增加。两个端点 $`q=1`、$`q=x` 均包含在估计中。

{docstring norm_logSmoothedPrimeExpSum_le_character_mean}

{docstring logSmoothedPrimeExpSum_rational_contour}

# 用对数平滑和恢复截断素数和
%%%
tag := "prime-log-desmoothing"
file := "logarithmic-desmoothing"
%%%

写 $`S(\alpha,x)=\sum_{n\le x}\Lambda(n)e(\alpha n)`，用 $`S_1` 表示再乘 $`\log(x/n)` 后的和。设 $`1\le x<y`。两个平滑和相减，所有 $`n\le x` 的项都得到同一个因子 $`\log(y/x)`。除以它后，余项至多为 $`\psi(y)-\psi(x)`。区间 $`(x,y]` 中每项的 von Mangoldt 权重至多为 $`\log y`，其中的整数个数至多为 $`y-x+1`。

{docstring AnalyticNumberTheory.PrimeDistribution.psi_sub_le_length_mul_log}

{docstring norm_primeExpSum_le_logSmoothed_difference}

假定 $`[x,2x]` 上的每个平滑和的模都不超过 $`M`，且 $`M\ge L=1+\log x`。取 $`H=\sqrt{xM/L}`。当 $`H<x` 时选 $`y=x+H`，于是 $`\log(y/x)\ge H/(2x)`。两种误差分别来自端点的平滑和与短区间的素数幂，均为 $`O(\sqrt{xLM})`。当 $`H\ge x` 时，Chebyshev 的初等上界已足够。对任意实频率，最终得到 $`|S(\alpha,x)|\le8\sqrt{xLM}`。

{docstring norm_primeExpSum_le_of_logSmoothed_bound}

# 有理频率的截断素数和
%%%
tag := "sharp-rational-contour"
file := "sharp-rational-contour"
%%%

对既约分数 $`a/q`，记{ref "smoothed-rational-prime-bound"}[平滑和的两项上界]为 $`T(x,q)`，省略绝对常数。端点从 $`x` 移到 $`[x,2x]` 内的任意点，$`T` 最多增大 $`64` 倍。因而可把同一个上界代入{ref "prime-log-desmoothing"}[有限差分估计]。

{docstring primeContourSmoothedScale_le_double}

由 $`\sqrt{u+v}\le\sqrt u+\sqrt v`，$`\sqrt{x(1+\log x)\,T(x,q)}` 展开为两项上界。对 $`1\le q\le x`，写 $`L=1+\log x`，得到

$$`\left|\sum_{n\le x}\Lambda(n)e(an/q)\right|
\ll \frac{x}{q^{1/4}}L^3 + x^{7/8}q^{1/8}L^{5/2}.`

{docstring sqrt_primeContourSmoothedScale_le}

{docstring primeExpSum_rational_contour}

若 $`1\le Q\le q^2` 且 $`qQ\le x`，则 $`q^{-1/2}\le Q^{-1/4}`，且 $`x^{3/4}q^{1/4}\le xQ^{-1/4}`。平滑和由此节省因子 $`Q^{-1/4}`，去掉平滑权重后的和节省 $`Q^{-1/8}`。

{docstring primeContourScales_le_of_denominator_range}

{docstring primeExpSums_rational_contour_balanced}

# 有限 Poisson 求和与倒数相位
%%%
tag := "poisson-reciprocal-phase"
file := "reciprocal-phase"
%%%

{index}[有限 Poisson 求和]设整数端点为 $`a<b`，相位导数单调且取值在 $`[\alpha,\beta]` 内。下面的定理在声明所列的延长区间上要求导数界。它把 $`\sum_{a<n\le b}e(f(n))` 化成有限多个积分 $`\int_a^b e(f(t)-mt)\,dt`。只需保留 $`\lfloor\alpha\rfloor-1\le m\le\lceil\beta\rceil+1`，总误差至多为 $`64(1+\log(2+\beta-\alpha))`。

{docstring vanDerCorput_poisson_sharp}

对 $`e(A/t+vt)`，驻点 $`t=\sqrt{A/v}` 落在 $`[a,b]` 内恰对应于 $`A/b^2\le v\le A/a^2`。以 $`r=\sqrt{A/v}` 和 $`w=(t-r)/\sqrt{t}` 代换后，相位恰为 $`2vr+vw^2`。由 Fresnel 积分 $`\int_0^\infty e(w^2)\,dw=(1+i)/4`，可读出驻相主项

$$`\frac{1+i}{2}\, A^{1/4}v^{-3/4}e(2\sqrt{Av}).`

当 $`0<a\le b\le2a` 且 $`A>0`，形式化估计同时控制两端点的截断误差，允许驻点与端点重合。

{docstring AnalyticNumberTheory.AnalyticTools.tendsto_integral_fresnel_half}

{docstring reciprocal_transform_integral}

把有限 Poisson 求和与驻相估计合用，就得到倒数相位的离散变换。整数 $`a<n\le b` 对应半开频率区间 $`A/b^2<m\le A/a^2`。当 $`1\le a\le b\le2^J a` 时，余项至多为
$`249J(1+\sqrt{b^3/A})(1+\log(6+4A/a^2))`。半开区间保证拼接相邻区间时端点频率只出现一次。{ref "divisor-voronoi-formula"}[除数问题的截断公式]就是这一变换的应用。

{docstring reciprocal_vanDerCorput_interval}

# 高阶导数检验
%%%
tag := "higher-derivative-tests"
file := "higher-derivatives"
%%%

设 $`k\ge2` 为整数，区间长度不超过 $`M`，且相位的连续 $`k` 阶导数处处满足 $`0<\lambda\le |f^{(k)}(t)|\le c\lambda`。取 $`\alpha=1/(2^k-2)`。van der Corput 的导数检验给出

$$`\left|\sum_{a<n\le b}e(f(n))\right|
 \ll_{k,c} M\lambda^\alpha + M^{1-2^{2-k}}\lambda^{-\alpha}.`

当 $`k=2` 时，右边是 $`M\sqrt{\lambda}+1/\sqrt{\lambda}`。提高一阶时，对相位作 Weyl 差分，由中值定理可用原相位的高阶导数控制差分相位的导数，然后选取差分长度。

{docstring vanDerCorput_higher_derivative}
