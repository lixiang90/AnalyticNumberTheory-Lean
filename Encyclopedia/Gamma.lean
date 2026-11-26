import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
import AnalyticNumberTheory.AnalyticTools.Gamma.StirlingSectorBounds
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools.Gamma

#doc (Manual) "Gamma 函数与竖直带中的 Stirling 公式" =>
%%%
tag := "gamma-stirling"
file := "gamma-stirling"
%%%

{index}[Gamma 函数]从 $`\Re s>0` 上的积分 $`\Gamma(s)=\int_0^\infty e^{-u}u^{s-1}\,du` 出发，分部积分得出递推式 $`\Gamma(s+1)=s\Gamma(s)`。倒数的 Weierstrass 乘积把这个递推关系与极点的位置联系起来：零点位于 $`0,-1,-2,\ldots`，每个零点都是单零点。

{docstring inv_gamma_eq_weierstrass_tprod}

解析数论经常需要固定实部、让虚部增大的估计。若 $`s=\sigma+it` 且 $`t\to+\infty`，Stirling 公式给出

$$`|\Gamma(\sigma+it)|\sim\sqrt{2\pi}\,t^{\sigma-1/2}e^{-\pi t/2}.`

指数衰减来自复对数的辐角。在有界竖直带内，对数导数还有 $`\Gamma'(s)/\Gamma(s)=\log s+O(1/|t|)`。这些估计分别控制{ref "riemann-xi"}[完备化 ζ 函数]的 Gamma 因子和零点计数中的辐角变化。

{docstring norm_complex_gamma_vertical_isEquivalent}

{docstring norm_digamma_sub_log_strip_le}

# 各阶 Stirling 展开与扇形余项
%%%
tag := "all-orders-stirling"
file := "all-orders-stirling"
%%%

在割平面 $`s\in\mathbb C\setminus(-\infty,0]` 上取 $`-\pi<\arg s<\pi`，并取正实轴上为实数的 $`\log\Gamma(s)` 分支。写成

$$`\log\Gamma(s)=\left(s-\tfrac12\right)\log s-s+\tfrac12\log(2\pi)+\Omega(s).`

记 $`B_j(x)` 为 Bernoulli 多项式，$`B_j=B_j(0)`。对任意整数 $`m\ge0`，取 $`c=\cos(\arg s/2)>0`，前 $`m` 项给出

$$`\Omega(s)=\sum_{j=1}^{m}\frac{B_{2j}}{2j(2j-1)s^{2j-1}}+R_m(s),\qquad
 |R_m(s)|\le\frac{|B_{2m+2}|(1+c^{-2m-2})}{(2m+2)(2m+1)|s|^{2m+1}}.`

例如保留 $`1/(12s)` 时，下一项是 $`-1/(360s^3)`。在任一固定扇形 $`|\arg s|\le\pi-\delta` 中，$`c` 有正下界，所以这里的三次误差对角度一致。

{docstring stirlingCoefficient_eq_bernoulli}

{docstring complex_gamma_stirling_expansion}

{docstring norm_stirlingRemainder_sub_expansion_le}

对数导数 $`\psi(s)=\Gamma'(s)/\Gamma(s)` 的前两项是 $`\log s-1/(2s)`。接下来的 $`m` 项为 $`-\sum_{j=1}^m B_{2j}/(2j s^{2j})`，其余项满足

$$`|R_m^\prime(s)|\le \frac{|B_{2m+2}|(1+c^{-2m-3})}{(2m+2)|s|^{2m+2}}.`

{docstring digamma_stirling_expansion}

{docstring norm_digamma_sub_expansion_le}

两种展开都来自同一族绝对收敛的积分。令 $`b_j(u)=B_j(\{u\})/j!`，则逐次分部积分给出

$$`I_{j,q}(s)=\int_0^\infty\frac{b_j(u)}{(s+u)^q}\,du
=-\frac{b_{j+1}(0)}{s^q}+qI_{j+1,q+1}(s)\qquad(j\ge1,\ q\ge2).`

偶阶周期 Bernoulli 核的绝对值在整数处取到最大值。将这个最优上界与 $`|s+u|\ge c(|s|+u)` 结合，就能在每一步保留余项对角度和阶数的显式依赖。

{docstring AnalyticNumberTheory.AnalyticTools.Summation.abs_bernoulliKernel_even_le}

{docstring stirlingBernoulliIntegral_step}

{docstring norm_stirlingBernoulliIntegral_le}
