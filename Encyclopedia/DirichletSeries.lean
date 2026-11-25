import AnalyticNumberTheory.DirichletSeries.RamachandraPolarDecay
import AnalyticNumberTheory.DirichletSeries.Ramachandra
import AnalyticNumberTheory.DirichletSeries.EulerProduct
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletSeries

#doc (Manual) "Dirichlet 级数与 Euler 乘积" =>
%%%
tag := "euler-products"
file := "euler-products"
%%%

{index}[Euler 乘积]在 $`\operatorname{Re}(s)>1` 内，$`\sum_{n\ge 1}n^{-s}` 绝对收敛。每个素数 $`p` 提供一个几何级数，展开有限多个这样的因子时，唯一分解保证每个由这些素数构成的正整数恰好出现一次。让素数集合增大，便得到

$$`\zeta(s)=\prod_p(1-p^{-s})^{-1}.`

{docstring AnalyticNumberTheory.DirichletSeries.riemannZeta_eulerProduct_hasProd}

对 Euler 乘积作对数求导，素数 $`p` 的局部因子给出 $`(\log p)p^{-s}/(1-p^{-s})`。再展开分母，可以读出每个素数幂的权重 $`\log p`。这正是{ref "prime-counting"}[素数计数]中使用的 von Mangoldt 权重。

{docstring riemannZeta_neg_logDeriv_eq_tsum_primes}

# 指数平滑与 Ramachandra 公式
%%%
tag := "ramachandra-smoothing"
file := "ramachandra-smoothing"
%%%

对 $`F(s)=\sum a_n n^{-s}`，用 Gamma 函数的 Mellin 反演在每一项引入权 $`e^{-n/X}`。设 $`X>0`，在右侧绝对收敛线上，以 $`F(s+w)\Gamma(w)X^w` 的积分表示这个平滑和。

{docstring hasSum_exponentiallySmoothed}

设在左侧直线 $`\Re w=l` 上有函数方程 $`F(s+w)=\psi(s+w)G(1-s-w)`，其中 $`-1<l<0` 且对偶级数在该线上绝对收敛。把对偶级数截为前 $`N` 项和尾和。若 $`F` 和 $`\psi` 在各自移动的带域内全纯且沿竖直方向至多按多项式增长，分别移动积分线便得到平滑和、有限对偶和与两个余项积分之间的恒等式。两条右侧积分线可独立选取。移动时越过 $`\Gamma(w)` 在零点的极点，这解释了公式中 $`F(s)` 和有限对偶和的来源。

{docstring ramachandra_smoothed_functional_equation}

# 有限阶极点对平滑公式的贡献
%%%
tag := "ramachandra-polar-residue"
file := "polar-remainder"
%%%

若围道越过 $`F` 在 $`q` 处的极点，设其阶数至多为 $`k+1`。在平移坐标 $`w` 中，极点位于 $`p=q-s`。将被积函数乘以 $`(w-p)^{k+1}` 后，取其在 $`p` 处的 $`k` 阶导数，再除以 $`k!`，即为{ref "ramachandra-smoothing"}[两条围道公式]中要扣除的留数。

{docstring ramachandra_smoothed_functional_equation_with_pole}

设 $`H=1+|\Im(q-s)|`。在定理给定的紧实部区间内，当 $`1\le X\le H^A` 时，留数对每个自然数 $`m` 均为 $`O(H^{-m})`。同一常数适用于所有对偶截断长度 $`N`。

{docstring gammaSmoothingResidue_rapid_decay}

{docstring ramachandra_smoothed_functional_equation_error}
