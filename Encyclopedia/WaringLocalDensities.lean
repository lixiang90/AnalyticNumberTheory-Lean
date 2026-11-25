import AnalyticNumberTheory.AdditiveNumberTheory.WaringUniformDensities
import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocalDensities
import AnalyticNumberTheory.AdditiveNumberTheory.WaringSeriesPositivity
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "Waring 奇异级数的 Euler 乘积" =>
%%%
tag := "waring-local-densities"
file := "waring-local-densities"
%%%

{index}[局部密度]给定幂次 $`k`、变量数 $`s` 和目标 $`n`，记模 $`q` 的解数为 $`M(q)`。全体 $`q^s` 个元组分布在 $`q` 个可能的目标类中，平均每类有 $`q^{s-1}` 个解，因而取 $`qM(q)/q^s` 为归一化的解数。

在{ref "waring"}[有限 Fourier 反演公式]中，频率 $`a/q` 约分后有某个分母 $`d\mid q`。按这个分母归类，恰好得到各个奇异级数系数 $`A(d)` 之和。这个有限恒等式对所有正模数成立。

{docstring sum_divisors_waringSingularTerm}

中国剩余定理使归一化解数在互素模数上相乘。对除数和作 Möbius 反演，可以把同一性质传给 $`A(q)`。

{docstring isMultiplicative_waringCoefficient}

固定素数 $`p`，模 $`p^r` 的归一化解数等于部分和 $`1+A(p)+\cdots+A(p^r)`。只要 $`s>2k` 且 $`k>0`，绝对收敛保证这个序列有极限。此极限就是 $`p` 处的局部密度。

{docstring tendsto_waringLocalCount_localFactor}

把所有素数处的局部因子相乘，展开乘积，用正整数的唯一素因子分解重排，就得到完整奇异级数。这个算术因子与{ref "waring-real-density"}[实密度]分别描述同余约束与连续体积。

{docstring hasProd_waringLocalFactor}

对于整除 $`k` 的素数，在模 $`p` 下可解还不足以直接套用单根提升。这里取 $`2v_p(k)+1` 层作为起点，用 Hensel 引理提升，再对其余变量的自由取值计数。合并有限个小素数的显式界与大素数乘积的尾部估计，就得到一个对所有 $`n` 都有效的正下界。下面给出便于应用的一组充分条件。

{docstring exists_pos_le_waringSingularSeries_re_of_cube}

# 四倍次数下的一致正下界
%%%
tag := "waring-four-degree-local"
file := "unit-coordinates"
%%%

设 $`k\ge1`。对每个素数幂 $`p^h`，只要 $`s\ge4k`，每个剩余类都有一个含单位坐标的 $`s` 项表示。证明按单位的 $`k` 次幂陪集分类。每增加两个变量，至少能达到一个原先遗漏的单位类，直到覆盖全部单位；非单位只需再加一个一。

{docstring waring_prime_power_unit_representation}

在精度 $`p^{2v_p(k)+1}` 处选出一个单位坐标，任意提升其余坐标。剩下一个单位的 $`k` 次幂方程，由 Hensel 引理求解。因此每个局部因子都得到与目标 $`n` 无关的下界。将各素数处的结果合并，对所有 $`n` 有 $`\mathfrak S_{k,s}(n)\ge c_{k,s}>0`。

{docstring waringLocalFactor_re_ge_of_four_mul}

{docstring exists_pos_le_waringSingularSeries_re_of_four_mul}

结合{ref "waring"}[圆法渐近公式]，当 $`k\ge2`、$`s>2^k` 且 $`s\ge4k` 时，每个充分大的整数都能写成 $`s` 个非负整数的 $`k` 次幂之和。

{docstring eventually_waringCount_pos_of_four_mul}
