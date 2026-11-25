import AnalyticNumberTheory.SieveMethods.LinearSieveQuantitative
import AnalyticNumberTheory.SieveMethods.WeightedFareySieve
import AnalyticNumberTheory.SieveMethods.ShiftedAlmostPrimes
import AnalyticNumberTheory.AnalyticTools.HilbertKernelEstimates
import AnalyticNumberTheory.SieveMethods.LinearSieve
import AnalyticNumberTheory.SieveMethods.BrunTitchmarshConstant
import AnalyticNumberTheory.SieveMethods.LinearSieveEulerProducts
import AnalyticNumberTheory.SieveMethods.LinearSievePrimeContraction
import AnalyticNumberTheory.SieveMethods.LinearSieveMonotonicity
import AnalyticNumberTheory.SieveMethods.DickmanFunction
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

# Dickman 函数与上下筛之差
%%%
tag := "sieve-dickman"
file := "dickman"
%%%

{index}[Dickman 函数]在 $`0\le v\le 1` 上取一，随后满足 $`v\rho'(v)=-\rho(v-1)`。这个延迟方程把线性筛的两个主函数联系起来。对 $`u\ge1` 有

$$`F(u)-f(u)=\frac{2e^\gamma}{u}\rho(u-1).`

{docstring linearSieve_gap_eq_dickman}

滑动区间上的积分恒等式给出 $`\rho(v)>0`，并可逐个单位区间迭代。对整数 $`n\ge0` 和 $`v\ge n`，有 $`\rho(v)\le1/n!`。因此在 $`u\ge n+1` 时，上下筛主函数之差严格为正，且至多为 $`2e^\gamma/(u\,n!)`。

{docstring dickman_le_inv_factorial}

{docstring linearSieve_gap_le_factorial}

# Buchstab 函数与线性筛的归一化
%%%
tag := "sieve-buchstab-limit"
file := "buchstab-limit"
%%%

{index}[Buchstab 函数]在 $`1\le u\le2` 上有 $`\omega(u)=1/u`，此后满足 $`(u\omega(u))'=\omega(u-1)`。这个递推给出大参数时的振幅界，从而证明极限存在。对延迟方程取 Laplace 变换，再求指数积分在零点的常数项，得到

$$`\lim_{u\to\infty}\omega(u)=e^{-\gamma}.`

{docstring log_one_add_buchstabLaplace}

{docstring tendsto_buchstab}

线性筛主函数满足 $`F(u)+f(u)=2e^\gamma\omega(u)`，而它们的差由 Dickman 函数给出。因此 $`F,f` 都趋于一。$`F` 在 $`[1,\infty)` 上严格递减，$`f` 在 $`[2,\infty)` 上严格递增。对每个整数 $`n\ge0`，当 $`u\ge n+1` 时，两者偏离一的绝对值都至多为 $`2e^\gamma/(u\,n!)`。

{docstring tendsto_linearSieve}

{docstring linearSieve_bracket_one}

{docstring linearSieve_factorial_error}

# 一维筛的乘积比较与两步递推
%%%
tag := "linear-sieve-products"
file := "euler-products"
%%%

记 $`V(t)=\prod_{p<t}(1-g(p))`。假设筛选区间内任意 $`[u,v)` 都满足
$`-L\le\sum_{u\le p<v}g(p)\log p-\log(v/u)\le A`，且 $`0\le g(p)\le1-1/B`。分部求和给出 $`\log(V(w)/V(z))` 与 $`\log(\log z/\log w)` 的双向比较。令 $`K=(A+1)+B(A+1)(1+2(A+1))`，对于 $`2\le w\le t\le z` 有

$$`\left|V(t)-V(z)\frac{\log z}{\log t}\right|
  \le e^{2K}(L+K)\frac{V(z)\log z}{(\log w)^2}.`

{docstring sieveEulerBelow_uniform_comparison}

对 Rosser 下筛，连续取两层素数时，第二层满足 $`q<p` 和 $`pq^3<y`。写 $`u=\log y/\log z`。若 $`u\ge2` 并且每个子区间的乘积比较误差满足声明中的 $`\eta\le10^{-4}` 条件，则以 $`V(q)\exp[-\log(y/pq)/\log q]` 加权的两层总贡献至多为 $`(19/20)V(z)e^{-u}`。进一步估计连续积分后，同一组假设下收缩因子可降至 $`74/100`。这样可在迭代中逐对控制余项。

{docstring linearSieve_prime_pair_contraction}

{docstring linearSieve_prime_pair_contraction_sharp}

# 等差数列的 Selberg 上界
%%%
tag := "selberg-progression-weights"
file := "progression-weights"
%%%

{index}[Brun–Titchmarsh 不等式]在 $`(x,x+y]` 中计数模 $`q` 的既约剩余类 $`a` 的素数。给定 $`z\ge1`，令 $`S` 为不超过 $`z` 且与 $`q` 互素的无平方因子正整数，定义

$$`G=\sum_{d\in S}\frac{1}{\varphi(d)},\qquad
 H=\sum_{d\in S}\frac{\sigma_1(d)}{\varphi(d)},\qquad \sigma_1(d)=\sum_{b\mid d}b.`

用 Selberg 权估计筛余数目，分别按逐项上界与权的绝对值总和估计计数误差，得到

$$`\pi(x+y;q,a)-\pi(x;q,a)\le z+\frac{y}{qG}+
    \min\left\{z^2,\left(\frac HG\right)^2\right\}.`

这里 $`z` 包含筛选时需要单独计入的小素数。保留 $`G,H` 的有限和，可以直接代入指定的筛限计算。

{docstring selberg_sieve_ap_upper_bound_refined}

# Rosser 线性筛的上下界
%%%
tag := "rosser-linear-sieve-bounds"
file := "rosser-linear-sieve"
%%%

令 $`P(z)` 为待筛素数中小于 $`z` 者的乘积，$`V(z)=\prod_{p\mid P(z)}(1-g(p))`。在总规模为 $`X` 的序列中，记 $`S(z)` 为与 $`P(z)` 互素的项数，$`r_d` 为 $`d` 的倍数的实际计数与预期计数之差。假设局部密度与一保持固定距离，且所有子区间满足{ref "linear-sieve-products"}[一维对数和条件]，其中的常数固定。

对任意 $`\varepsilon>0`，存在只依赖于这些常数和 $`\varepsilon` 的筛限。当 $`z` 超过此筛限时，对全部 $`u\ge1` 有

$$`XV(z)(f(u)-\varepsilon)-R\ \le\ S(z)\ \le\
 XV(z)(F(u)+\varepsilon)+R,\qquad R=\sum_{\substack{d\mid P(z)\\d<z^u}}|r_d|.`

同一个 $`z` 下界对所有合乎条件的序列都适用。特别地，取固定 $`2<u\le4`，主项中的下筛函数为 $`2e^\gamma\log(u-1)/u>0`，因此在算术余项足够小时能得到正的筛余数目。

{docstring linearSieve_sifted_bounds}

# 线性筛余项的衰减率
%%%
tag := "quantitative-linear-sieve"
file := "quantitative-linear-sieve"
%%%

写 $`y` 为筛权的水平，取 $`2\le z\le y` 并令 $`u=\log y/\log z`。固定 $`A,D\ge0` 和 $`B>0`，假设每个待筛素数满足 $`g(p)\le1-1/B`。对于每个 $`2\le w\le v\le z`，要求 $`\sum_{w\le p<v}g(p)\log p-\log(v/w)` 落在 $`[-L,A]`，其中 $`0\le L\le D\log y/(\log\log y)^5`。求和只取待筛素数。

存在只依赖于 $`A,B,D` 的 $`c>0`，使得对充分大的 $`y` 和上述全部 $`z`，有

$$`XV(z)(f(u)-E)-R\le S(z)\le XV(z)(F(u)+E)+R,
\qquad E=c(\log\log y)^{-3/10},\quad R=\sum_{\substack{d\mid P(z)\\d<y}}|r_d|.`

两侧使用同一个算术余项 $`R`，其中每个除数的系数都是一。主项中的误差随 $`y` 衰减，即使 $`z` 靠近区间的任一端点也适用。

{docstring linearSieve_quantitative_bounds}

# 长区间上的 Brun–Titchmarsh 系数二
%%%
tag := "brun-titchmarsh-two"
file := "brun-titchmarsh"
%%%

给定 $`q\ge1`、$`x\ge0`，令 $`u=y/q`。存在一个与 $`x,q,a` 都无关的绝对常数 $`U>1`，使得当 $`u\ge U` 时，

$$`\pi(x+y;q,a)-\pi(x;q,a)\le\frac{2y}{\varphi(q)\log(y/q)}.`

这里的 $`U` 是存在性结论。这个版本把系数取到二，同时保留区间起点与模数上的一致性。

{docstring brun_titchmarsh_two_eventually}

为消去筛权对模数的依赖，把数列写成 $`qk+a`，先分出不超过筛限的小素数。对模 $`q` 的平移取平均，至少有一个平移保留 $`\varphi(q)/q` 比例的候选下标。用中国剩余定理可令保留的下标同时避开其余所有小素因子。

{docstring selberg_progression_to_rough}

对于{ref "selberg-progression-weights"}[Selberg 权的两个有限和]，在 $`q=1` 时有 $`H(z)/z\to15/\pi^2`，以及
$`G(z)-\log z\to B=\gamma+\sum_p\log p/[p(p-1)]`。这里 $`B>1.28`。取 $`z=\sqrt{u}/2`，不等式 $`(15/\pi^2)^2<4(B-\log2)` 给出严格余量，足以吸收计数误差。这个均值论证采用 Selberg 的平移方法。[Granville 与 Soundararajan，《Multiplicative number theory》，第 1.4.3 节](https://dms.umontreal.ca/~andrew/PDF/Book.To1.4.pdf#page=44)

{docstring tendsto_selbergDenominator_sub_log}

{docstring tendsto_selbergIntervalWeightMass_div}

# 平移素数与三个素因子
%%%
tag := "shifted-almost-primes"
file := "shifted-almost-primes"
%%%

固定非零偶整数 $`h`，令 $`\Omega(n)` 表示按重数计的素因子个数，例如 $`\Omega(12)=3`。存在只依赖于 $`h` 的 $`c_h>0`，使充分大的 $`x` 满足

$$`\#\{p\le x : p\ \text{为素数},\ \Omega(|p-h|)\le3\}
     \ge c_h\frac{x}{(\log x)^2}.`

取 $`h=-2` 即知有无穷多个素数 $`p` 使 $`p+2` 至多有三个素因子。证明对平移后的素数使用 {ref "rosser-linear-sieve-bounds"}[Rosser 线性筛]，再以 Kuhn 权扣除带有中等大小素因子的项。算术级数中的平均误差由 {ref "bombieri-vinogradov"}[Bombieri–Vinogradov 定理]控制。

{docstring shiftedAlmostPrimes_lower}

{docstring infinite_primes_shift_threeFactors}

# 非等距点列的求和常数
%%%
tag := "individual-spacing-sums"
file := "individual-spacings"
%%%

对有限实点列 $`x_r`，给每个点指定 $`\delta_r>0`，满足 $`\delta_r\le|x_r-x_s|` 对所有 $`s\ne r` 成立。在固定点 $`x_s` 两侧，指数核的加权和分别受单侧等距点列控制。将这些指数估计对尺度积分，就得到二次和四次核的显式常数

$$`\sum_{r\ne s}\frac{\delta_r}{(x_r-x_s)^2}\le\frac{\pi^2}{3\delta_s},
\qquad
\sum_{r\ne s}\frac{\delta_r}{(x_r-x_s)^4}\le\frac{\pi^4}{45\delta_s^3}.`

常数分别来自 $`2\zeta(2)` 与 $`2\zeta(4)`。取越来越长的等距点列并固定其中点，两式左边都趋于相应的上界。

{docstring AnalyticNumberTheory.AnalyticTools.sum_separated_exponential_right}

{docstring AnalyticNumberTheory.AnalyticTools.hilbert_quadratic_row}

{docstring AnalyticNumberTheory.AnalyticTools.hilbert_quartic_row}

# 非均匀间距的大筛
%%%
tag := "large-sieve-local-gaps"
file := "local-gap-large-sieve"
%%%

设点 $`\alpha_r` 在圆周 $`\mathbb R/\mathbb Z` 上两两相异。取 $`0<\delta_r\le1`，使每个其他点与 $`\alpha_r` 的圆周距离至少是 $`\delta_r`。对 $`S(\alpha)=\sum_{M<n\le M+N}a_ne^{2\pi i n\alpha}`，有

$$`\sum_r\frac{|S(\alpha_r)|^2}{N+C/(\pi\delta_r)}
     \le\sum_{M<n\le M+N}|a_n|^2,\qquad
 C=\sqrt{\pi^2/3+2\bigl(4+\sqrt{16+\pi^4/45}\bigr)}<4.452.`

例如对 $`Q` 阶 Farey 分数 $`a/q`，与另一既约分数 $`b/d` 的圆周距离至少为 $`1/(qd)`。所以分母为 $`q` 的每一项可取 $`\delta_r=1/(qQ)`，相应的大筛权为 $`N+CqQ/\pi`。把同分母的项合并，就得到按分母加权的算术大筛。

{docstring weighted_analytic_large_sieve}

{docstring weighted_farey_large_sieve}

{docstring weighted_arithmetic_large_sieve}

证明先在实轴上估计带核 $`1/(x_r-x_s)` 的 Hilbert 二次型。将对应的 Hermitian 矩阵平方，在特征向量上，对易子项的二次型为零。剩余项由{ref "individual-spacing-sums"}[逐点间距的二次、四次核估计]及两个不同极点的混合估计控制。最后对各点的整数平移交替求和并取平均，把实轴核化为 $`\pi/\sin(\pi x)`。

{docstring AnalyticNumberTheory.AnalyticTools.hilbert_mixed_quadratic_row_sharp}

{docstring AnalyticNumberTheory.AnalyticTools.weighted_hilbert_inequality}

{docstring weighted_hilbert_cosecant}
