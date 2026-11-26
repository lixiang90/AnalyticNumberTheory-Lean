import AnalyticNumberTheory.AnalyticTools.ExponentialIntegralAsymptotic
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

# 非实方向的相位与余项
%%%
tag := "exponential-integral-phase"
file := "phase-and-remainder"
%%%

{index}[指数积分的复渐近式]在上半平面取 $`P(y)=i\pi`，在下半平面取 $`P(y)=-i\pi`，其中 $`y=\Im z`。当 $`y\ne0` 时，有带显式常数的估计

$$`\left|\operatorname{Ei}(z)-P(y)-\frac{e^z}{z}\right|
 \le \frac{e^{\Re z}}{y^2}.`

例如在虚轴上，$`\operatorname{Ei}(iy)` 与 $`P(y)+e^{iy}/(iy)` 相差至多 $`1/y^2`。共轭的一对自变量具有相反的常数相位。

{docstring exponentialIntegralPhase}

{docstring exponentialIntegralPhase_neg}

{docstring norm_principalExponentialIntegral_sub_phase_sub_le}

为了得到积分常数，在穿过负实轴的分支上使用 $`\log(-z)`。这个分支在固定水平直线的左端趋于零。沿直线对它与 $`e^z/z` 的差积分，导数为 $`e^z/z^2`。分母的模至少为 $`y^2`，而 $`\int_{-\infty}^{\Re z} e^t\,dt=e^{\Re z}`，由此得到上界。

{docstring leftExponentialIntegral}

{docstring principalExponentialIntegral_eq_left_add_phase}

{docstring tendsto_leftExponentialIntegral_neg_add_im}
