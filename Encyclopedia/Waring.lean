import AnalyticNumberTheory.AdditiveNumberTheory.WaringSingularSeries
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

{index}[Waring 奇异级数]在模 $`q` 的频率中只取既约分数，将每个完整指数和除以 $`q`，便得到奇异级数的第 $`q` 项。完整和的界说明该项的模至多为 $`C_k^s q^{1-s/k}`。当 $`s>2k` 时，指数小于负一，因此级数绝对收敛。这个控制与目标整数 $`n` 无关，同一个截断点对所有 $`n` 都适用。

{docstring tendstoUniformly_waringSingularSeries}

在素数模 $`p` 下，每个非零频率都是既约频率。将零频率的贡献一加回第 $`p` 项，便恢复了归一化的局部解数。

{docstring one_add_waringSingularTerm_prime}
