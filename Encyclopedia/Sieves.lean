import AnalyticNumberTheory.SieveMethods.CombinatorialSieve
import AnalyticNumberTheory.SieveMethods.LargeSieve
import AnalyticNumberTheory.SieveMethods.LegendrePrimeCounting
import AnalyticNumberTheory.SieveMethods.SelbergSieve
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
