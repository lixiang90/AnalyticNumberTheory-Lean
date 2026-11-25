import AnalyticNumberTheory.SieveMethods.CombinatorialSieve
import AnalyticNumberTheory.SieveMethods.LargeSieve
import AnalyticNumberTheory.SieveMethods.LegendrePrimeCounting
import AnalyticNumberTheory.SieveMethods.SelbergSieve
import AnalyticNumberTheory.SieveMethods.PrimeHybridSieve
import AnalyticNumberTheory.SieveMethods.LinearSieveFunctions
import AnalyticNumberTheory.SieveMethods.RosserSiftedCount
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.SieveMethods

#doc (Manual) "筛法的容斥与大筛不等式" =>
%%%
tag := "sieve-methods"
file := "sieve-methods"
%%%

{index}[Legendre 筛]从有限整数集合 $`A` 中筛去与 $`P` 有共同素因子的元素。对每个正因子 $`d\mid P`，记 $`A_d` 为 $`A` 中 $`d` 的倍数。用 Möbius 函数作容斥，得到精确公式

$$`\#\{a\in A:\gcd(a,P)=1\}=\sum_{d\mid P}\mu(d)\,\#A_d.`

例如 $`A=\{1,\ldots,10\}`、$`P=6` 时，依次扣掉二与三的倍数，再补回六的倍数，得到 $`10-5-3+1=3`。留下的是 $`1,5,7`。

{docstring legendre_inclusion_exclusion_int}

取 $`A=\{1,\ldots,N\}`，让 $`P` 等于所有不超过 $`\sqrt N` 的素数之积。每个合数都有一个不超过其平方根的素因子，故筛余的恰是 $`1` 和大于 $`\sqrt N` 的素数。于是用 $`\lfloor N/d\rfloor` 代替各个倍数的个数，便得到素数计数的精确公式。

{docstring legendre_primeCounting}

{index}[大筛不等式]大筛的分析形式控制一组三角多项式采样值的平方和。若采样点模一的两两距离至少为 $`\delta`，则长度为 $`N\ge1` 的多项式的平方和至多是其系数平方和的 $`N-1+\delta^{-1}` 倍。采样点越接近，系数中的 $`\delta^{-1}` 越大。

{docstring analytic_large_sieve}

{index}[Selberg 上界筛]同时筛去使 $`n` 或 $`n+2` 有小素因子的剩余类，便可控制孪生素数对的个数。对于 $`x\ge3`，Selberg 筛给出 $`O(x/(\log x)^2)` 的上界。

{docstring selberg_twin_primes_bound}

# 孪生素数与二元 Goldbach 表示
%%%
tag := "brun-and-selberg"
file := "brun-selberg"
%%%

{index}[Brun 定理]对所有 $`p,p+2` 都是素数的 $`p`，级数 $`\sum 1/p` 收敛。证明把 $`p` 按 $`2^k\le p<2^{k+1}` 分组，再用 Brun 筛所得的计数上界估计每一组。

{docstring brun_twin_primes_summable}

对于偶数 $`2N`，Selberg 筛还给出素数表示 $`2N=p+p'` 的个数上界。奇素数 $`\ell` 通常筛去两个剩余类，当 $`\ell\mid N` 时这两个类重合。由此在统一上界 $`O(N/(\log N)^2)` 上出现修正因子 $`\prod_{\ell\mid N,\,\ell>2}(1+1/(\ell-2))`。{ref "goldbach-exceptional-set"}[Goldbach 例外集]一文则说明有表示的偶数占多大比例。

{docstring selberg_goldbach_upper_bound}

# 素数支撑的混合大筛
%%%
tag := "prime-hybrid-sieve"
file := "prime-hybrid-sieve"
%%%

设 $`Q,T\ge1`，$`Y\ge[Q^2(T+2)]^8`。在任意有限素数集 $`S\subset(Y,\infty)` 上给定复系数 $`a_p`，同时对模数不超过 $`Q` 的原特征和高度 $`|t|\le T` 取均方，有

$$`\sum_{q\le Q}\ \sum_{\chi\bmod q}^{*}\int_{-T}^{T}
\left|\sum_{p\in S}a_p\chi(p)p^{-it}\right|^2dt
\le\frac{6\pi^3}{\log Y}\sum_{p\in S}p\,|a_p|^2.`

利用系数只支撑在素数上，可把同一个特征提升到多个辅助模数。对这些模数应用大筛，会在分母得到 $`\log Y`。界与 $`S` 中最大素数无关，也包括模一的特征。

{docstring prime_hybrid_large_sieve}

# 线性筛函数
%%%
tag := "linear-sieve-functions"
file := "linear-sieve"
%%%

{index}[线性筛函数]一维筛的上、下主项分别涉及函数 $`F(u)` 和 $`f(u)`。筛限与筛除素数上界之比以对数尺度参数 $`u` 表示。归一化取 $`1\le u\le2` 时 $`uF(u)=2e^\gamma`，$`uf(u)=0`，其中 $`\gamma` 是 Euler 常数。对 $`u>2`，二者满足

$$`(uF(u))'=f(u-1),\qquad (uf(u))'=F(u-1).`

右端只用到一个单位之前的值。因此从初始区间出发，每次积分就能把两函数再延拓一个单位。形式化给出在 $`[1,\infty)` 上的连续解，并证明初始值与积分递推唯一决定这个解。

{docstring hasDerivAt_mul_linearSieveFunction}

{docstring linearSieveFunction_unique}

在 $`1\le u\le3` 上，上筛函数保持 $`F(u)=2e^\gamma/u`。下筛函数从 $`u=2` 处的零开始，在 $`2\le u\le4` 上等于 $`2e^\gamma\log(u-1)/u`。这个对数来自积分 $`\int_2^u (v-1)^{-1}\,dv`。

{docstring linearSieveUpper_eq_of_le_three}

{docstring linearSieveLower_eq_of_le_four}

从算术筛权也能读出截断误差的符号。把筛权与乘性密度的乘积按平方自由因子求和，完整的 Möbius 展开给出 Euler 乘积。按素因子递减次序在第一个违反截断条件的前缀处分组，便得到剩余贡献的精确有限和。上筛的密度和等于 Euler 乘积加上这项非负余量，下筛的密度和等于 Euler 乘积减去相应余量。

{docstring rosser_main_term_eq}

{docstring betaSieve_main_terms}

随着参数 $`u` 增大，可以统一压低两种余量。设 $`V(z)=\prod_{p\le z}(1-g(p))`，乘积取在指定的筛素数上，并假设任意窗口 $`[w,z']` 上的局部积满足筛维数条件，常数为 $`A,\kappa`。取 $`y=z^u` 和 $`\beta=1+u/3`。对所有充分大的 $`u`，上、下筛的首次截断余量均至多为

$$`2A\,V(z)\exp\!\left(-\tfrac12 u\log u\right).`

下述定理对任意给定的有限递减素数表成立。门槛 $`u_0` 只依赖筛维数条件中的 $`A,\kappa`。

{docstring rosser_fundamental_lemma}

对实际筛余计数 $`S`，设 $`X` 为原序列的总量模型，$`r_d` 为被 $`d` 整除的项数与其模型值之差。将两侧筛权的界代入，可得

$$`|S-XV(z)|\le 2A X V(z)e^{-u\log u/2}
+\sum_{\substack{d\mid P(z)\\ d<z^u}} |r_d|.`

第一项只取决于筛密度，第二项保留了原序列在截断范围内的算术误差。

{docstring siftedCount_fundamental_lemma}
