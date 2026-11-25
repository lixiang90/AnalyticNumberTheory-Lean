import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachPrimeTripleAsymptotic
import AnalyticNumberTheory.AdditiveNumberTheory.VinogradovThreePrimes
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "Goldbach 表示的局部因子与主次弧" =>
%%%
tag := "goldbach"
file := "goldbach"
%%%

{index}[Goldbach 奇异级数]令 $`S(x,\alpha)=\sum_{n\le x}\Lambda(n)e(n\alpha)`。在既约有理数 $`a/q` 处，指数因子在同一个剩余类上恒定。若每个简化剩余类中的加权素数计数与 $`x/\varphi(q)` 的偏差至多为 $`E`，把各类求和就给出主项 $`\mu(q)x/\varphi(q)`。误差中另有一项来自整除模数的素数幂。

{docstring norm_primeExpSum_rat_sub_le}

从有理数中心移到 $`\alpha=a/q+\beta` 时，额外的振荡因子为 $`e(n\beta)`。若每个整数截点上的剩余类误差都有同一上界，Abel 分部求和可将该误差传递到主弧上，并给出因子 $`1+2\pi N|\beta|`。

{docstring norm_primeExpSum_majorArc_sub_le}

若主弧两两不交，逐弧积分后可以先固定分母，再对分子求和。分子和产生 Ramanujan 和，而积分的截断宽度仍依赖于分母。下面的估计在这个步骤中保留了每个模数的误差。

{docstring norm_goldbachTernary_majorArcIntegral_sub_le_of_progressions}

{ref "waring"}[圆法的系数提取]也适用于这些加权和。三元问题的积分在次弧上可用一次逐点界和一次平方均值来估计。

{docstring norm_goldbachTernary_minorArcIntegral_le}

奇异级数记录各个素数处的局部限制。三元奇异级数在所有奇数上有统一的正下界。这个下界使主项具有统一的正大小。

{docstring goldbachTernarySingularSeries_pos_of_odd}

对无权主项，积过一个完整周期给出三元正整数分拆数 $`\binom{N-1}{2}`。将积分区间截断到 $`[-H,H]` 时，几何级数估计给出尾部至多 $`1/(8H^2)`。据此可将分母相关的局部积分还原为完整奇异级数乘以同一个组合主项。

{docstring norm_ternarySingularIntegral_sub_choose_le}

{docstring abs_goldbachTernaryWeighted_sub_series_le}

{ref "primes-in-progressions"}[Siegel–Walfisz 定理]在对数幂大小的模数范围内给出素数分布的一致误差。取主弧分母截点为对数的适当幂，合并主弧和次弧估计，得到三元加权表示数的下述渐近公式。对任意自然数 $`A`，误差为 $`O_A(N^2/(\log N)^A)`。

{docstring goldbachTernaryWeighted_asymptotic}

对奇数 $`N`，奇异级数的正下界使主项压过误差。扣掉来自真正素数幂 $`p^j`（$`j\ge 2`）以及素数二的贡献后，剩下的表示由三个奇素数组成。这样得到 Vinogradov 三素数定理，量词是“所有充分大的奇数”，三个素数可以重复。

{docstring vinogradov_three_primes}

# 三个素数的无权表示数
%%%
tag := "goldbach-unweighted-ternary"
file := "ordered-prime-triples"
%%%

令 $`T(N)` 为满足 $`p_1+p_2+p_3=N` 的有序奇素数三元组数，允许素数重复。将对数权去掉后得到

$$`T(N)=\frac{\mathfrak S_3(N)N^2}{2(\log N)^3}
        +O\!\left(\frac{N^2}{(\log N)^4}\right).`

把素数二也计入时，上式的主项和误差阶同样成立。这里去权需要控制小素数。在每个三元组中，以 $`\log N` 代替 $`\log p_i` 会产生差额 $`\log(N/p_i)`。固定 $`p_i` 后，其余两项满足二元 Goldbach 条件。用 Selberg 上界筛控制二元表示数，利用{ref "brun-titchmarsh-full"}[Brun–Titchmarsh 不等式]对随 $`N-p_i` 变化的局部因子取平均，再作 Abel 分部求和，便能把去权误差压到上式的量级。

{docstring goldbachPrimeSieveFactor_average}

{docstring goldbachTernaryOddCount_asymptotic}

{docstring goldbachTernaryCount_asymptotic}
