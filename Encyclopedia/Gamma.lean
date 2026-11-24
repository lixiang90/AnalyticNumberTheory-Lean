import AnalyticNumberTheory.AnalyticTools.Gamma.Stirling
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
