import AnalyticNumberTheory.PrimeDistribution.Linnik
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "Linnik 定理与等差数列中的最小素数" =>
%%%
tag := "least-prime-linnik"
file := "least-prime-linnik"
%%%

{index}[Linnik 定理]固定模数 $`q\ge2` 和简化剩余类 $`a\bmod q`。设 $`p(a,q)` 是这个类中最小的素数。存在绝对常数 $`L>0`，使

$$`p(a,q)\le q^L.`

这里的指数同时适用于所有模数和所有简化剩余类。若直接需要一个满足同余条件的素数，下面的声明同时给出它的素性、同余式和大小界。

{docstring exists_prime_modEq_le_pow}

{docstring linnik_least_prime_power}

证明把剩余类的指示函数展开为 Dirichlet 特征，用 $`L'/L` 的高阶导数形成一个集中在有限素数区间上的加权和。导数阶数取为 $`\log q` 的常数倍，这使区间右端成为 $`q` 的固定次幂。{ref "dirichlet-family-density"}[无对数损失的零密度估计]控制整个特征族的零点总数。若存在很靠近一的实零点，它会削弱主项，同时{ref "complex-zero-repulsion"}[Deuring–Heilbronn 排斥]也会减小其他零点的贡献。保留下来的正余量迫使给定剩余类中至少有一个素数。

此证明使用 Siegel 的实零点下界，定理给出指数的存在性。保留前置常数的版本适用于全部正模数，包括 $`q=1`。

{docstring linnik_least_prime}
