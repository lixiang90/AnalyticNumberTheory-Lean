import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularSeries
import AnalyticNumberTheory.AdditiveNumberTheory.WaringPrimeModuli
import AnalyticNumberTheory.AdditiveNumberTheory.WaringVolume
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularIntegral
import AnalyticNumberTheory.AdditiveNumberTheory.WaringMinorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.WaringBasis
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "圆法与 Waring 表示数" =>
%%%
tag := "waring"
file := "waring"
%%%

{index}[Waring 问题]用 $`R_{k,s}(n)` 表示方程 $`x_1^k+\cdots+x_s^k=n` 的非负整数有序解数。设 $`k>0`，选择满足 $`n<(P+1)^k` 的截点。只要有一个坐标大于 $`P`，它的幂就已经超过目标，所以这个截断保留全部解。

取 $`S(\alpha)=\sum_{x=0}^{P} e(\alpha x^k)`。展开 $`S(\alpha)^s` 后，每个元组给出一个整数频率。乘以 $`e(-n\alpha)` 并积过一个周期，频率为零的项各贡献一，其余项的积分为零。

{docstring integral_waringSum_pow}

例如 $`n=5,k=2,s=2` 时，取 $`P=2` 即可，两个解分别是 $`(1,2)` 与 $`(2,1)`。对于四个平方，Lagrange 定理保证每个非负整数的表示数都为正。

{docstring waringCount_four_squares_pos}

在解析估计中，可把同一个积分分成靠近小分母有理数的主弧和其余的次弧。分割本身给出精确等式，估计这两部分才涉及误差项。

{docstring waringCount_eq_arcIntegrals}

{index}[局部表示数]在模 $`q` 的剩余类环上，频率也只需取模 $`q`。将幂和的完整指数和升至 $`s` 次方，再对全部频率求和，得到 $`q` 倍的同余方程解数。

{docstring waringLocalCount_fourier}

互素模数的解可以逐坐标用中国剩余定理拼接，所以局部解数具有乘法性。

{docstring waringLocalCount_mul}

整数解模任意正整数都给出同余解。例如模八的平方只有 $`0,1,4`，三个平方相加无法得到 $`7\pmod 8`。因此四平方定理中的项数不能普遍降到三。

{docstring waringCount_three_squares_eq_zero}

在素数模 $`p` 下，每个非零剩余类至多有 $`k` 个 $`k` 次根。对幂剩余集合反复应用 Cauchy–Davenport 不等式，可以证明每个剩余类都能表示成 $`k` 个 $`k` 次幂之和。

{docstring waringLocalCount_pos_prime}

当 $`p\nmid k` 且允许再加一个变量时，可以把这个额外变量在模 $`p` 下固定为一。其余变量任选提升后，差额是一个模 $`p` 等于一的单位。这些单位组成的群具有素数幂阶，取 $`k` 次幂在该群上是双射，因而每个目标都能提升到任意 $`p^r`。

{docstring waringLocalCount_pos_prime_pow}

{index}[Waring 奇异级数]在模 $`q` 的频率中只取既约分数，将每个完整指数和除以 $`q`，便得到奇异级数的第 $`q` 项。完整和的界说明该项的模至多为 $`C_k^s q^{1-s/k}`。当 $`s>2k` 时，指数小于负一，因此级数绝对收敛。这个控制与目标整数 $`n` 无关，同一个截断点对所有 $`n` 都适用。

{docstring tendstoUniformly_waringSingularSeries}

在素数模 $`p` 下，每个非零频率都是既约频率。将零频率的贡献一加回第 $`p` 项，便恢复了归一化的局部解数。

{docstring one_add_waringSingularTerm_prime}

实数解的几何因子来自正象限中 $`\sum_i x_i^k\le t` 的体积。将所有坐标同时放大 $`t^{1/k}`，体积随 $`t^{s/k}` 变化。求导得到 $`t=1` 处的实密度 $`\Gamma(1+1/k)^s/\Gamma(s/k)`。

{docstring hasDerivAt_waringVolume}

连续相位积分 $`v_k(\beta)=\int_0^1 e(\beta u^k)\,du` 随频率衰减。在 $`|\beta|\ge1` 时，其模为 $`O(|\beta|^{-1/k})`。因此只要 $`s>k`，$`v_k(\beta)^s e(-t\beta)` 在整条实线上绝对可积，任意实数目标 $`t` 都有良定义的 Fourier 奇异积分。

{docstring integrable_waringSingularIntegrand}

对于 $`k\ge 2` 和 $`s>2^k`，可以在次弧上用 Weyl 不等式控制多出的变量，用 Hua 引理控制其余 $`2^k` 个变量的均值。由此得到与目标整数无关的界 $`O(P^{s-k-\delta})`，其中 $`\delta>0`。这里主弧分母的截点取 $`P^\eta`，且 $`0<\eta\le1/2`。

{docstring waringMinorArc_power_saving}

一般模数的归一化解数如何给出奇异级数的 Euler 乘积，见{ref "waring-local-densities"}[局部密度]。主弧的逐弧近似、Fourier 反演与 Gamma 因子的计算见{ref "waring-real-density"}[Waring 主弧与实密度]。

选择 $`P=\lfloor n^{1/k}\rfloor+1`，则 $`n/P^k` 趋于一。主弧的截断奇异级数与实积分都对目标一致地趋于其完整值，加上次弧的幂次节省，可以在 $`k\ge2` 且 $`s>2^k` 时得到

$$`R_{k,s}(n)=\mathfrak S_{k,s}(n)\frac{\Gamma(1+1/k)^s}{\Gamma(s/k)}n^{s/k-1}+o(n^{s/k-1}).`

余项以 $`n^{s/k-1}` 为尺度。要从这个公式对所有充分大的目标推出正的解数，还需要奇异级数有一致正下界。

{docstring waringCount_asymptotic}

{index}[Hilbert–Waring 定理]当 $`k^3\le s` 且 $`2^k<s` 时，局部密度的一致下界使主项压过误差，所以每个充分大的整数都有表示。剩下的有限多个整数都可以用若干个一的 $`k` 次幂表示。把变量数增大到同一个上界，再以零补足，就得到对所有目标都有效的固定变量数。一次幂的情形直接取一个变量。

{docstring eventually_waringCount_pos}

{docstring hilbert_waring}
