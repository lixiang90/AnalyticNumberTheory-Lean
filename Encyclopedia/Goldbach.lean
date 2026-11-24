import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcIntegral
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "Goldbach 表示的局部因子与主次弧" =>
%%%
tag := "goldbach"
file := "goldbach"
%%%

{index}[Goldbach 奇异级数]令 $`S(x,\alpha)=\sum_{n\le x}\Lambda(n)e(n\alpha)`。在既约有理数 $`a/q` 处，指数因子在同一个剩余类上恒定。若每个简化剩余类中的加权素数计数与 $`x/\varphi(q)` 的偏差至多为 $`E`，把各类求和就给出主项 $`\mu(q)x/\varphi(q)`。误差中另有一项来自整除模数的素数幂。

{docstring norm_primeExpSum_rat_sub_le}

从有理数中心移到 $`\alpha=a/q+\beta` 时，额外的振荡因子为 $`e(n\beta)`。若每个整数截点上的剩余类误差都有同一上界，Abel 分部求和可将该误差传递到主弧上，并给出因子 $`1+2\pi N|\beta|`。

{docstring norm_primeExpSum_majorArc_sub_le}

若主弧两两不交，逐弧积分后可以先固定分母，再对分子求和。分子和产生 Ramanujan 和，而积分的截断宽度仍依赖于分母。下面的估计在这个步骤中保留了每个模数的误差。

{docstring norm_goldbachTernary_majorArcIntegral_sub_le_of_progressions}

{ref "waring"}[圆法的系数提取]也适用于这些加权和。三元问题的积分在次弧上可用一次逐点界和一次平方均值来估计。

{docstring norm_goldbachTernary_minorArcIntegral_le}

奇异级数记录各个素数处的局部限制。三元奇异级数在所有奇数上有统一的正下界。要据此推出充分大的奇数确实有三个素数的表示，还需要主弧积分的渐近公式以及从加权计数到素数计数的误差控制。

{docstring goldbachTernarySingularSeries_pos_of_odd}
