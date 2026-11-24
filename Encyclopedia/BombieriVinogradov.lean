import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovPrimeCounting
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "Bombieri–Vinogradov 平均值定理" =>
%%%
tag := "bombieri-vinogradov"
file := "bombieri-vinogradov"
%%%

{index}[Bombieri–Vinogradov 定理]设 $`E(x;q)` 为 $`|\psi(x;q,a)-x/\varphi(q)|` 在模 $`q` 的简化剩余类上的最大值。对任意固定实数 $`A`，存在 $`B,C`，使得在 $`x\ge2` 且 $`1\le Q\le\sqrt x/(\log x)^B` 时有

$$`\sum_{q\le Q}E(x;q)\le C\frac{x}{(\log x)^A}.`

这里对剩余类取最大值，对模数求和。这个量词次序使模数的范围能从{ref "primes-in-progressions"}[逐模数的对数幂范围]延伸到接近平方根。

{docstring bombieriVinogradov}

特征正交关系将问题化为原始特征和的平均估计。对小导子，Siegel–Walfisz 估计的指数衰减吸收了导子个数带来的对数因子。

{docstring sum_smallConductor_psiChar_le}

对大导子，Vaughan 恒等式把素数和分成两类。第一类的短变量可以直接求和，另一个变量上的特征在完整周期中相消。第二类的双线性和带有 $`mn\le x` 的双曲截断。将列区间二分，在每层应用{ref "sieve-methods"}[乘法大筛]，可以处理随行变量改变的求和终点。

{docstring primitiveCharacterMean_cutoff_pow_two}

扣除高次素数幂的贡献后，$`\theta(x;q,a)` 同样满足这一平均值估计。

{docstring bombieriVinogradov_theta}

# 对截点也取上确界
%%%
file := "maximal-endpoints"
tag := "maximal-endpoints"
%%%

对每个模数，可以分别在 $`0\le y\le x` 和简化剩余类上取上确界，再将所得误差相加。于是每个模数甚至可以选取不同的截点。证明将区间划成对数幂个小段，用固定截点定理控制网格点，用单调性控制相邻网格点之间的变化。

{docstring bombieriVinogradov_maximal}

{docstring bombieriVinogradov_maximal_theta}

对素数计数函数作分部求和，主项变成 $`\mathrm{Li}(y)/\varphi(q)`，其中 $`\mathrm{Li}(y)=\int_2^y dt/\log t`。此时截点的范围是 $`2\le y\le x`。

{docstring bombieriVinogradov_piAP}
