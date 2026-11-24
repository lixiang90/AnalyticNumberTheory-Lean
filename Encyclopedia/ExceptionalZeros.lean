import AnalyticNumberTheory.DirichletLFunctions.RealZeroRepulsion
import AnalyticNumberTheory.DirichletLFunctions.FamilyZeroRepulsion
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "例外实零点与 Deuring–Heilbronn 排斥" =>
%%%
tag := "real-zero-repulsion"
file := "real-zero-repulsion"
%%%

{index}[Deuring–Heilbronn 现象]若一个实原特征的 L 函数有非常接近一的实零点，另一个实原特征的实零点便受到限制。设两个不同的非主实原特征的导子分别为 $`q_1,q_2`，其 L 函数分别有实零点 $`\alpha,\beta`，且 $`\beta\ge3/4`。令 $`L=\log(q_1q_2+2)`。库中证明存在绝对正常数 $`C,K`，使

$$`1-\beta\ \ge\ \frac{1}{KL}\log\frac{1}{C(1-\alpha)L^5}.`

当 $`C(1-\alpha)L^5<1` 时，右端为正。固定两个导子，$`\alpha` 越接近一，另一零点与一的距离下界越大。

{docstring real_zero_repulsion_logarithmic}

证明对含有四个 L 因子的 Dirichlet 级数利用系数的非负性，并把 $`L(1,\chi)` 的大小与 $`1-\alpha` 联系起来。

{docstring norm_LFunction_one_le_real_zero_gap}

# 对其他原特征的复零点
%%%
tag := "complex-zero-repulsion"
file := "complex-zeros"
%%%

设 $`\chi` 是导子为 $`q_1` 的实原非主特征，$`L(\alpha,\chi)=0` 且 $`\alpha` 为实数。对任意不同的原非主特征 $`\psi`，其导子为 $`q_2`，取它的任意复零点 $`\rho=\beta+it` 并令 $`L=\log(q_1q_2(|t|+2))`。存在一个绝对常数 $`C>0` 使

$$`1-\beta\ \ge\ \min\!\left\{\frac1{32},\frac{\log(1/(C(1-\alpha)L))}{CL}\right\}.`

这里 $`\psi` 可以是复特征。证明对四个对数导数取高阶导数，用局部零点展开得到幂和，再以 Fejér 加权的幂和估计检测零点。所得下界同时记录了两个导子和目标零点的高度。

{docstring deuring_heilbronn_distinct_primitive}

对同一个实特征，异常实零点还排斥它的其他零点以及黎曼 ζ 函数的零点。对于非原始特征，可以先传到诱导它的原特征。统一定理按目标特征的导子给出临界带中的排斥界，并且允许给整个特征族选用同一个参数 $`L`。

{docstring deuring_heilbronn_family}
