import AnalyticNumberTheory.ModularAndPartitions.DedekindCongruences
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

# Dedekind 和的零值判据
%%%
tag := "dedekind-zero-criterion"
file := "zero-criterion"
%%%

设 $`k>0` 且 $`h` 与 $`k` 互素。由互反律与 $`12k\,s(h,k)` 的整数性得到同余式 $`12hk\,s(h,k)\equiv h^2+1\pmod{k}`。反过来，若 $`h^2\equiv-1\pmod{k}`，则 $`h^{-1}\equiv-h\pmod{k}`。Dedekind 和在取逆时不变、在取负时变号，因此

$$`s(h,k)=0\quad\Longleftrightarrow\quad h^2\equiv-1\pmod{k}.`

例如 $`2^2\equiv-1\pmod5`，所以 $`s(2,5)=0`。

{docstring dedekindSum_numerator_modEq}

{docstring dedekindSum_eq_zero_iff}
