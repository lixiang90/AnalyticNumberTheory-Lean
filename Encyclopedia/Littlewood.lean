import AnalyticNumberTheory.PrimeDistribution.ImprovedPrimeNumberTheorem
import AnalyticNumberTheory.RiemannZeta.Littlewood
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.ExponentialSums

#doc (Manual) "Littlewood 对 ζ 函数无零区的改进" =>
%%%
tag := "littlewood-zero-free"
file := "littlewood-zero-free"
%%%

{index}[Littlewood 无零区]给定任意常数 $`B>0`，存在依赖于 $`B` 的高度，从这个高度起有

$$`\zeta(\sigma+it)\ne0\qquad\left(\sigma\ge1-\frac{B}{\log|t|}\right).`

经典对数无零区给出一个固定的宽度系数。在这里，这个系数可以预先取得任意大，代价是起始高度随之改变。将此结论与{ref "zero-density"}[无对数损失的零密度估计]结合，可以推出{ref "hoheisel-prime-intervals"}[固定幂长区间内的素数渐近式]。

{docstring littlewood_zero_free}

# 任意阶的对数相位差分
%%%
tag := "higher-logarithmic-sums"
file := "logarithmic-sums"
%%%

记 $`e(u)=\exp(2\pi i u)`。给定正整数 $`J`，只要 $`M\le|\tau|^2` 且 $`|\tau|\le M^J`，就在整个二倍区间以及每个初段上有

$$`\left|\sum_{M<n\le b} e(\tau\log n)\right|\le C_J M^{1-\kappa_J},\qquad M\le b\le2M,`

其中 $`\kappa_J>0`。高度与长度的比例决定需要做多少次差分。给定正步长，反复使用中值定理，可把混合差分写成步长的乘积乘以中间一点的高阶导数。对二阶导数施行这个公式，就能在差分树最末端应用 van der Corput 二阶导数估计。

{docstring iterForwardDiff_mean_value}

{docstring logarithmic_block_power_saving}

# 从指数和到无零区
%%%
tag := "littlewood-strip-growth"
file := "strip-growth"
%%%

把 ζ 的有限 Dirichlet 和按二的幂分段。短段用绝对值估计，其余段用上述相消界，再由分部求和乘回实部权重。对任意 $`\varepsilon>0`，可以选取 $`0<\eta\le1/4`，使充分大的 $`T`、$`1-\eta\le\sigma\le2`、$`T\le|t|\le3T` 满足

$$`|\zeta(\sigma+it)|\le T^{\varepsilon\eta}.`

在宽度为 $`\eta` 的圆盘上估计对数导数，再用 $`3+4\cos u+\cos(2u)\ge0`，便可排除紧靠直线 $`\sigma=1` 的零点。

{docstring littlewood_strip_growth}

# 素数定理中的误差
%%%
tag := "pnt-arbitrary-exponential"
file := "prime-number-theorem"
%%%

Littlewood 无零区改变了{ref "prime-counting"}[素数定理]误差界中的常数。对每一个预先给定的 $`d>0`，都有

$$`\psi(x)=x+O_d\!\left(xe^{-d\sqrt{\log x}}\right).`

对 $`\vartheta(x)-x` 和 $`\pi(x)-\operatorname{li}(x)` 也成立同阶估计。证明先为指定的 $`d` 选择显式公式的截断高度，并用无对数损失的密度界估计零点贡献。随后扣除高次素数幂，用分部求和转回素数个数。

{docstring AnalyticNumberTheory.PrimeDistribution.prime_number_theorem_arbitrary_exp}
