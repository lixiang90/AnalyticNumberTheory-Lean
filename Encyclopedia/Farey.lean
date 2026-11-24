import AnalyticNumberTheory.AnalyticTools.FareyDissection
import AnalyticNumberTheory.ModularAndPartitions.PartitionFareyCoefficients
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools

#doc (Manual) "Farey 分数与圆周分割" =>
%%%
tag := "farey-dissection"
file := "farey-dissection"
%%%

{index}[Farey 数列]将分母不超过 $`N` 的既约分数按大小排列。若 $`a/q<b/r` 相邻，则 $`bq-ar=1` 且 $`q+r>N`。第一式给出精确间距 $`1/(qr)`，第二式说明其中数 $`(a+b)/(q+r)` 的分母已经超过上限。

{docstring fareyAdjacent_of_consecutive}

取中数作切点，切点到左右分数的距离分别为 $`1/[q(q+r)]` 和 $`1/[r(q+r)]`。例如五阶数列中 $`1/3` 与 $`2/5` 相邻，切点 $`3/8` 将这段间距分为 $`1/24` 和 $`1/40`。

{docstring fareyCut_sub_point}

{docstring fareyPoint_sub_cut}

对周期为一的连续函数，平移靠近一的区间可以把两端拼成以零为中心的一段。整个周期的积分于是按分母和简化剩余类分解。每条弧的左右宽度分别介于 $`1/(2qN)` 与 $`1/[q(N+1)]` 之间，这使得{ref "partition-asymptotic"}[分拆函数]在不同有理点附近的局部估计可以按分母求和。

{docstring integral_eq_sum_fareyArcs}

{docstring fareyFull_width_bounds}

取高度 $`N^{-2}` 的圆提取第 $`n` 个分拆系数。将每条弧上的生成函数换成模变换后的主项，逐点误差至多为 $`C(n)/\sqrt N`。积分会给每一项乘上相应弧长，而所有弧长之和恰好为一，因此总误差也满足同一个界。

{docstring AnalyticNumberTheory.ModularAndPartitions.partitionCount_sub_sum_rademacherArcs_le}
