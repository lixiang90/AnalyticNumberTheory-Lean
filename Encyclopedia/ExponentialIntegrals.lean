import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralReal
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools

#doc (Manual) "指数积分" =>
%%%
tag := "exponential-integrals"
file := "exponential-integrals"
%%%

{index}[指数积分]指数积分在筛法与素数显式公式中有两个常见的取值范围。对正实数 $`x`，衰减的指数积分为 $`E_1(x)=\int_x^\infty e^{-t}\,dt/t`。在复数域中，$`\operatorname{Ei}` 的解析主支由 $`\gamma+\log z` 和一个整函数组成。{ref "riemann-exponential-integral"}[Riemann 的零点项]用到它在开右半平面的值。

{docstring realEOne}

# 负实轴边界值与 Euler 常数
%%%
tag := "eone-euler-normalization"
file := "euler-normalization"
%%%

当 $`x\downarrow0` 时，$`E_1(x)+\log x\longrightarrow-\gamma`。从 $`\Gamma'(1)=\int_0^\infty e^{-t}\log t\,dt=-\gamma` 出发，在 $`(x,\infty)` 上分部积分，就能确定这个常数。这也是 Buchstab 函数的 Laplace 变换中出现 $`e^{-\gamma}` 的归一化。

{docstring tendsto_log_add_eOne}

令 $`P(z)=\sum_{n\ge1}z^n/(n\,n!)`。在正实轴上比较导数，再用上述极限确定积分常数，得到
$$`E_1(x)=-\gamma-\log x-P(-x).`
第一项展开为 $`E_1(x)=-\gamma-\log x+x+O(x^2)`。当 $`x\to\infty`，衰减积分趋于零。

{docstring realEOne_eq_log_remainder}

{docstring tendsto_realEOne_atTop}

Lean 的复对数在 $`-x` 处选取辐角 $`\pi`。因此，对 $`x>0`，把这个边界取值代入幂级数定义，得到 $`\operatorname{Ei}(-x)=-E_1(x)+i\pi`。由此可见，当 $`x` 趋于正无穷时，复边界值趋于 $`i\pi`。经典实值指数积分在负实轴上取这个边界值的实部 $`-E_1(x)`。

{docstring principalExponentialIntegral_neg_real}

{docstring tendsto_principalExponentialIntegral_neg_real}
