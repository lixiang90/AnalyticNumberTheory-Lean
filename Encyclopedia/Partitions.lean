import AnalyticNumberTheory.ModularAndPartitions.Partitions
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ModularAndPartitions

#doc (Manual) "整数分拆与五边形数递推" =>
%%%
tag := "integer-partitions"
file := "integer-partitions"
%%%

{index}[分拆函数]设 $`p(n)` 为整数 $`n` 的无序分拆数，并取 $`p(0)=1`。部件 $`j` 的出现次数可为任意非负整数，生成函数中相应的因子是 $`(1-z^j)^{-1}`。对 $`|z|<1`，这些局部选择给出收敛的乘积。

{docstring tsum_partitionCount_mul_pow}

将乘积的倒数按 Euler 五边形数定理展开，再比较系数，就得到只涉及较小参数的递推。例如计算 $`p(4)` 时，只有偏移 $`1,2` 有贡献，因此 $`p(4)=p(3)+p(2)=5`。

{docstring euler_partition_recurrence}

# Rademacher 级数的收敛性
%%%
file := "absolute-convergence"
tag := "absolute-convergence"
%%%

对固定的 $`n\ge1`，Rademacher 级数中分母为 $`k\ge2` 的项，其绝对值至多为 $`C(n)k^{-3/2}`。证明只需指数和的平凡上界 $`|A_k(n)|\le k` 与双曲函数的三阶余项。这个论证对任意实相位函数都成立。算出级数的和还需要{ref "farey-dissection"}[有理点附近各弧的积分]。

{docstring summable_norm_rademacherTerm}
