import AnalyticNumberTheory.ModularAndPartitions.RademacherSeries
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ModularAndPartitions

#doc (Manual) "Rademacher 的精确分拆公式" =>
%%%
tag := "rademacher-series"
file := "rademacher-series"
%%%

{index}[Rademacher 公式]对每个正整数 $`n`，分拆数都可写成绝对收敛的级数

$$`p(n)=\sum_{k=1}^\infty \sqrt{k}\,A_k(n)\,\psi_k(n).`

其中 $`A_k(n)` 对模 $`k` 的既约剩余类求和，相位由 {ref "dedekind-eta"}[Dedekind 和]与 Fourier 因子给出。令 $`u=n-1/24`，解析因子是 $`(\pi\sqrt2)^{-1}` 乘以函数 $`x\mapsto \sinh(\pi\sqrt{2x/3}/k)/\sqrt{x}` 在 $`u` 处的导数。

{docstring rademacherSeriesFormula}

在高度 $`N^{-2}` 的积分圆上作{ref "farey-dissection"}[Farey 分割]。对分母为 $`k` 的一条弧作模变换，再取倒数变量，就能把主积分化为右半平面中的竖线积分。半整数阶的积分可以用双曲函数算出，正好给出 $`\sqrt{k}\,\psi_k(n)`。

{docstring integral_rademacherVerticalKernel_half}

每条弧的延展误差至多为 $`B(n)/(k\sqrt k\,N)`。同一分母至多出现 $`k` 次，而 $`\sum_{k\le N}1/\sqrt k\le 2\sqrt N`。于是保留分母不超过 $`N` 的项时，总误差至多为 $`C(n)/\sqrt N`。

{docstring partitionCount_sub_rademacherPartialSum_le}

固定 $`n` 令 $`N\to\infty` 得到这里的精确公式。固定首项再令 $`n\to\infty`，则可借助其余项的统一估计得到{ref "partition-asymptotic"}[Hardy–Ramanujan 渐近式]。
