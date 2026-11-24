import AnalyticNumberTheory.AdditiveNumberTheory.WaringFourierInversion
import AnalyticNumberTheory.AdditiveNumberTheory.WaringMajorArcs
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "Waring 主弧与实密度" =>
%%%
tag := "waring-real-density"
file := "waring-real-density"
%%%

在{ref "waring"}[幂和表示问题]中，靠近 $`a/q` 时写 $`\alpha=a/q+\beta`。指数和中 $`e(ax^k/q)` 的部分以 $`q` 为周期。在每个剩余类上用积分近似缓慢振荡的 $`e(\beta x^k)`，主项分解为模 $`q` 的完整指数和与连续积分之积。这里保留从零起求和的端点误差。

{docstring norm_waringSum_majorArc_sub_integral_le}

取分母 $`q\le B`、半宽为 $`1/Q` 的主弧。当 $`2B^2<Q` 时，这些弧两两不交。将主项升到 $`s` 次方并积分，再对既约分子求和，算术部分恰是截断到 $`B` 的奇异级数。等宽的选取使剩余的实积分与分母无关。

{docstring norm_waringMajorArcIntegralFixed_sub_main_le}

{index}[Waring 奇异积分]为了计算实积分，给单位立方体赋予均匀测度，并将它按 $`(u_1,\ldots,u_s)\mapsto \sum_i u_i^k` 推到实轴上。由于各坐标独立，所得测度的 Fourier 变换是 $`v_k(\beta)^s`，其中 $`v_k(\beta)=\int_0^1 e(\beta u^k)\,du`。

{docstring integral_e_waringDistribution}

当 $`0<k<s` 时，Fourier 反演给出连续密度。在 $`0<a<b\le1` 上对此密度积分，正好得到幂和介于两个水平之间的体积。因此，在 $`0<t<1` 上，密度等于正象限中幂球体积的导数。

{docstring integral_waringSingularIntegral_eq_volume_sub}

{docstring waringSingularIntegral_eq_density}

令 $`t` 从左侧趋向一。连续性把密度公式延至端点，给出主项中的因子 $`\Gamma(1+1/k)^s/\Gamma(s/k)`。例如，当 $`k=2,s=3` 时，正象限内半径 $`\sqrt t` 的球体积为 $`\pi t^{3/2}/6`，在一处求导便得到 $`\pi/4`。

{docstring waringSingularIntegral_one}
