import AnalyticNumberTheory.ModularAndPartitions.DedekindEta
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ModularAndPartitions

#doc (Manual) "Dedekind η 函数及互反律" =>
%%%
tag := "dedekind-eta"
file := "dedekind-eta"
%%%

{index}[Dedekind η 函数]在上半平面令 $`q=e^{2\pi i\tau}`，则 $`\eta(\tau)=e^{\pi i\tau/12}\prod_{m\ge1}(1-q^m)`。平移 $`\tau\mapsto\tau+1` 保持每个乘积因子，前面的指数因子贡献 $`e^{\pi i/12}`。反演 $`\tau\mapsto-1/\tau` 则引入平方根。

{docstring eta_add_one}

{docstring eta_inv}

{index}[Dedekind 和]一般模变换中的相位与 Dedekind 和有关。对互素的正整数 $`h,k`，互反律同时涉及 $`s(h,k)` 和 $`s(k,h)`，因此可以沿 Euclid 算法把大参数化为小参数。

{docstring dedekind_reciprocity_div}
