import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
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
