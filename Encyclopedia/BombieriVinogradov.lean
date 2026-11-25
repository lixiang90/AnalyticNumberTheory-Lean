import AnalyticNumberTheory.PrimeDistribution.BarbanDavenportHalberstam
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovByZeroDensity
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


# 由零密度估计控制显式公式中的零点和
%%%
tag := "primitive-family-zero-weights"
file := "primitive-family-zero-weights"
%%%

{index}[加权零点和]设 $`Q\ge1`、$`T,x\ge2`，并记 $`H=Q^2T`。对每个导子不超过 $`Q` 的原始特征，把开临界带中 $`|\Im\rho|\le T` 的每个零点按重数计入。有

$$`\sum_{q\le Q}\sum_{\chi\bmod q}^{*}\ \sum_{\rho=\beta+i\gamma}x^\beta
\ll \bigl(\sqrt{x}\,H+xH^{1/3}\bigr)\log x\,(\log(QT))^8.`

{docstring primitive_family_zero_power_sum}

当 $`\beta\le1/2` 时，每个权重至多是 $`\sqrt{x}`，可以直接使用族的零点总数界。对右半带，在实部方向作分部求和，得到含有尾计数 $`N(\sigma,T)` 的积分。{ref "primitive-family-ingham-density"}[Ingham 估计]的指数不超过 $`(5-4\sigma)/3`。乘上 $`x^\sigma` 后，上界的对数是 $`\sigma` 的一次函数，所以最大值出现在 $`1/2` 或 $`1`。这两个端点分别给出 $`\sqrt{x}H` 和 $`xH^{1/3}`。

{docstring AnalyticNumberTheory.AnalyticTools.weighted_rpow_sum_le_of_tail}

{docstring density_weight_affine_le}

显式公式给虚部 $`\gamma` 的零点附上 $`1/(1+|\gamma|)` 的权重。把高度分成 $`1+|\gamma|\asymp 2^j` 的区间后，零点和估计中的 $`T` 项每层贡献一个常数，$`T^{1/3}` 项则给出收敛的几何级数。这样得到对所有 $`T\ge1` 成立的加权界，包括虚部为零的零点。

{docstring primitive_family_zero_reciprocal_sum}

取 $`T=\sqrt{x}`，设 $`1\le Q\le\sqrt{x}`、$`x\ge4`。导子不超过 $`2Q` 的原始特征族满足

$$`\sum_{q\le2Q}\sum_{\chi\bmod q}^{*}\sum_{|\gamma|\le\sqrt{x}}\frac{x^\beta}{1+|\gamma|}
\ll \sqrt{x}\,Q^2(\log x)^{10}+xQ^{2/3}(\log x)^9.`

{docstring primitive_dyadic_zero_reciprocal_sum}

# 从单个特征的显式公式到导子平均
%%%
tag := "density-mean-character-sums"
file := "density-mean-character-sums"
%%%

设 $`M_\chi(x)=\sup_{0\le y\le x}|\sum_{n\le y}\Lambda(n)\chi(n)|`。零密度证法所需的单特征输入是以下截断估计。对原始特征 $`\chi\bmod q`，其中 $`2\le q\le2\sqrt{x}`，要求

$$`M_\chi(x)\ll \sqrt{x}\,(1+\log(qx))^2+
 \sum_{|\gamma|\le\sqrt{x}}\frac{x^\beta}{1+|\gamma|}.`

{docstring PrimitivePsiExplicitBound}

应用{ref "character-truncated-explicit-formula"}[非主特征的截断显式公式]，对 $`Q<q\le R\le2Q` 求和，$`1/\varphi(q)` 的权与原始特征计数相配合，得到

$$`\sum_{Q<q\le R}\frac1{\varphi(q)}\sum_{\chi\bmod q}^{*}M_\chi(x)
\ll \sqrt{x}\,Q(\log x)^{11}+xQ^{-1/3}(\log x)^{10}.`

{docstring primitive_dyadic_mean_of_explicit_bound}

对 $`d<q\le D` 的各个二倍区间求和，第一项由最大的 $`D` 控制，第二项由最小的 $`d` 控制。这一步保留了上式的两个对数次数。

{docstring primitive_large_conductor_mean_of_density}

对给定的 $`A`，取 $`k=\max(0,\lceil A\rceil)`。Siegel–Walfisz 定理控制 $`q\le(\log x)^{3(k+10)}` 的小导子。若 $`D\le\sqrt{x}/(\log x)^{k+11}`，两个大导子项都至多是 $`O(x/(\log x)^A)`。下面的归约将这个估计接到算术级数中的 Bombieri–Vinogradov 定理。

在小导子估计中，可以在每个特征上分别取截点上确界。对于 $`y\ge\sqrt{x}`，Siegel–Walfisz 定理中的导子对数幂加倍便覆盖原范围；更小的 $`y` 由初等 Chebyshev 界控制。

{docstring sum_smallConductor_maximalPsiChar_le}

{docstring primitive_density_maximal_log_saving}

{docstring bombieriVinogradov_of_density_explicit}

把每个特征的截断公式代入导子平均，就得到零密度证法的无条件结论。设 $`x\ge4`、$`Q\ge1`。对于任意自然数 $`k`，若 $`Q\le\sqrt{x}/(\log x)^{k+12}`，则把每个模数的剩余类和截点 $`y` 分别最大化后，$`\psi` 的误差总和仍为 $`O_k(x/(\log x)^k)`。同一级别适用于 $`\theta` 和 $`\pi`，素数计数的主项为 $`\mathrm{Li}(y)/\varphi(q)`。

{docstring primitive_dyadic_mean_by_zero_density}

{docstring bombieriVinogradov_maximal_by_zero_density}

{docstring bombieriVinogradov_maximal_theta_by_zero_density}

{docstring bombieriVinogradov_maximal_pi_by_zero_density}

# 素数在剩余类中的平方均值
%%%
tag := "barban-davenport-halberstam"
file := "barban-davenport-halberstam"
%%%

{index}[Barban–Davenport–Halberstam 定理]设 $`A>0` 为常数，$`x`、$`Q` 为实数，且 $`x\ge2`、$`x/(\log x)^A\le Q\le x`。在每个模数的全部简化剩余类上，把 $`\psi(x;q,a)` 与 $`x/\varphi(q)` 之差平方再求和，则

$$`\sum_{q\le Q}\ \sum_{\substack{0\le a<q\\ (a,q)=1}}
 \left(\psi(x;q,a)-\frac{x}{\varphi(q)}\right)^2 \ll_A xQ\log x.`

{docstring barban_davenport_halberstam}

这里的 $`\psi` 用 von Mangoldt 函数加权，每个素数幂均按其权重计入。以 $`Q=x` 为例，平方误差总和是 $`O_A(x^2\log x)`。证明的第一步是对每个模数应用特征正交性。任取实数 $`m` 作为中心项的分子，Parseval 恒等式给出

$$`\sum_{(a,q)=1}\left(\psi(x;q,a)-\frac{m}{\varphi(q)}\right)^2
=\frac{1}{\varphi(q)}\sum_{\chi\bmod q}
 \left|\psi(x,\chi)-\mathbf{1}_{\chi=\chi_0}m\right|^2.`

{docstring progressionVariance_eq_character_mean}

取 $`m=x`。素数定理控制主特征产生的误差。其余特征由原始特征诱导，替换时只须扣除整除模数的素数幂。最后按导子重排：小导子用 Siegel–Walfisz 定理，大导子用大筛。写 $`q=kd` 后保留 $`d\le Q/k`，使大筛估计中关于上限的线性项可对 $`k` 求和。

{docstring progressionVariance_le_conductor_energy}

{docstring barban_conductor_mean}
