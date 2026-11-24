import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import AnalyticNumberTheory.DivisorProblems.DyadicDivisorEstimates
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DivisorProblems

#doc (Manual) "双曲线下的格点与除数和" =>
%%%
tag := "divisor-sums"
file := "divisor-sums"
%%%

{index}[Dirichlet 双曲线法]把 $`ab\le N` 的正整数格点按乘积分类，每个 $`n\le N` 对应 $`d(n)` 个格点。令 $`u=\lfloor\sqrt N\rfloor`。每个格点至少有一个坐标不超过 $`u`，按两个坐标分别计数时，中央的 $`u\times u` 方块会被算两次。因此

$$`\sum_{n\le N}d(n)+u^2=2\sum_{a=1}^u\lfloor N/a\rfloor.`

{docstring sum_card_divisors_add_sqrt_sq}

以 $`N=10` 为例，$`u=3`，右端为 $`2(10+5+3)=36`，故除数个数的总和为 $`27`。将取整误差与调和和式结合，可得主项 $`x\log x+(2\gamma-1)x` 及以下余项界。

{docstring abs_divisorError_le_of_one_le}

若要研究余项中的抵消，可以保留每个取整误差的符号。令 $`\psi(t)=\{t\}-1/2`，则除数余项与 $`-2\sum_{d\le\sqrt x}\psi(x/d)` 的差至多为八。这个约化把改进余项的任务化为估计一个振荡和。

{docstring abs_divisorError_add_two_sum_sawtooth_le}

在二进区间 $`D<n\le 2D` 上，相位 $`A/n` 的二阶导数 $`2A/n^3` 在端点之间只相差常数倍。van der Corput 二阶导数估计因此可以一致地用于该区间的任一子区间。

{docstring norm_sum_reciprocal_phase_le}
