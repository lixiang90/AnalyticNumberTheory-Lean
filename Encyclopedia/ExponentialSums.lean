import AnalyticNumberTheory.ExponentialSums.HigherDerivativeTests
import AnalyticNumberTheory.ExponentialSums.ReciprocalRealBlocks
import AnalyticNumberTheory.ExponentialSums.SharpPoissonSummation
import AnalyticNumberTheory.ExponentialSums.ReciprocalTransform
import AnalyticNumberTheory.ExponentialSums.LinearAndWeyl
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue
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
