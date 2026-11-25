import AnalyticNumberTheory.ModularAndPartitions.EtaNaturalBoundary
import AnalyticNumberTheory.ModularAndPartitions.DedekindModThree
import AnalyticNumberTheory.ModularAndPartitions.DedekindLogTransformation
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

# 规范对数的模变换
%%%
tag := "dedekind-eta-logarithm"
file := "canonical-logarithm"
%%%

用无穷远处的 Fourier 展开固定全纯分支 $`F(z)=\log\eta(z)`，使 $`F(z)-\pi iz/12` 在虚部趋于正无穷时趋于零。设行列式为一的整数矩阵的两行为 $`(a,b)`、$`(c,d)`。当 $`c>0` 时，

$$`F(\gamma z)-F(z)=\tfrac12\log[-i(cz+d)]+\pi i\left(\frac{a+d}{12c}-s(d,c)\right).`

这里方括号内的复数落在右半平面，可以取主值对数。对于 $`c<0` 或 $`c=0`，下面两条定理分别给出相应的分支和整数平移项。

{docstring dedekindLogEta_SL2Z_of_pos}

{docstring dedekindLogEta_SL2Z_of_neg}

{docstring dedekindLogEta_SL2Z_of_zero}

# Dedekind 和的精细同余与 η 的边界
%%%
tag := "eta-congruences-boundary"
file := "congruences-and-boundary"
%%%

取互素的 $`h,k`，其中 $`k>0`。整数 $`m=12k\,s(h,k)` 满足

$$`hm\equiv h^2+1\pmod{k\gcd(3,k)}.`

若 $`6k\,s(h,k)` 本身为整数，则它被三整除当且仅当 $`3\nmid k`。

{docstring dedekindSum_numerator_modEq_gcd_three_int}

{docstring three_dvd_dedekindSum_numerator_iff_int}

从上半平面沿竖线趋向任一有理点时，η 的极限为零。有理点在实轴上稠密，若 η 能在某个实点附近解析延拓，恒等定理就会迫使这个延拓在邻域内恒为零。因此整条实轴都是 η 的自然边界。

{docstring eta_no_analytic_extension}
