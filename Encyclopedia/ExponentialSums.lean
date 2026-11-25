import AnalyticNumberTheory.ExponentialSums.HigherDerivativeTests
import AnalyticNumberTheory.ExponentialSums.ReciprocalRealBlocks
import AnalyticNumberTheory.ExponentialSums.SharpPoissonSummation
import AnalyticNumberTheory.ExponentialSums.ReciprocalTransform
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue
import AnalyticNumberTheory.ExponentialSums.PrimeLinearSums
import AnalyticNumberTheory.ExponentialSums.PrimeDensityWeights
import AnalyticNumberTheory.ExponentialSums.SmoothedPrimeSums
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
