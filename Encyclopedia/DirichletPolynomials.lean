import AnalyticNumberTheory.PrimeDistribution.ConductorPolynomialMeans
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import AnalyticNumberTheory.SieveMethods.HalaszMontgomery
import AnalyticNumberTheory.SieveMethods.SeparatedMeanValues
import AnalyticNumberTheory.SieveMethods.ConductorMultipleSampling
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.SieveMethods

#doc (Manual) "Dirichlet 多项式的均方与大值" =>
%%%
tag := "dirichlet-polynomials"
file := "dirichlet-polynomials"
%%%

{index}[Dirichlet 多项式]对 $`D(s)=\sum_{n=1}^N a_n n^{-s}`，在竖直线 $`s=\sigma+it` 上展开 $`|D(s)|^2`。对角项与 $`t` 无关，积分后的贡献为区间长度乘以 $`\sum_{n\le N}|a_n|^2 n^{-2\sigma}`。非对角项带有振荡因子。Hilbert 不等式给出与积分区间长度无关的总误差。

{docstring dirichletPoly_mean_sq_asymp}

{index}[Halász–Montgomery 不等式]在一组离散高度上，若每处都满足 $`|D(it_j)|\ge V`，则高度的个数也受到限制。设有 $`R` 个高度，并以 $`B` 控制不同高度之差处的无权 Dirichlet 多项式的模。对角项的核值恰为 $`N`，其余每项至多为 $`B`，于是

$$`R V^2\le\left(\sum_{n=1}^N |a_n|^2\right)\bigl(N+(R-1)B\bigr).`

{docstring halasz_montgomery_dirichletPoly_count_le}

对任意间距至少为 $`\delta>0` 的实频率 $`x_j`，把 $`\left|\sum_j c_je^{itx_j}\right|^2` 在区间 $`[a,b]` 上积分。从中减去对角项 $`(b-a)\sum_j|c_j|^2`，差的绝对值至多为 $`2\pi\delta^{-1}\sum_j|c_j|^2`。证明在两个端点各使用一次 Hilbert 不等式。

{docstring AnalyticNumberTheory.SieveMethods.separated_frequency_mean_square}

# 特征族中 Dirichlet 多项式的大值
%%%
tag := "huxley-character-large-values"
file := "huxley-character-large-values"
%%%

{index}[Huxley 大值估计]设 $`P_\chi(s)=\sum_{n=1}^N a_n\chi(n)n^{-s}`。在半平面 $`\Re s\ge\sigma_0` 中，从长度 $`T\ge1` 的闭高度区间取样。对每个特征 $`\chi`，要求其不同样本的纵坐标相距至少 $`\delta>0`。记 $`R` 为各特征样本数之和，$`G=\sum_{n=1}^N |a_n|^2n^{-2\sigma_0}`。

对模 $`q` 的全体特征取 $`D=q`，对导子不超过 $`Q` 的全体本原特征取 $`D=Q^2`。若每个样本都满足 $`|P_\chi(s)|\ge V>0`，且 $`V^2\ge c\sqrt{3D}(1+\log(3D))^2G`，则

$$`R\;\ll\;(1+\delta^{-1})\left(\frac{NG}{V^2}+
\frac{NDT\,G^3}{V^6}\bigl(1+\log(D(T+3))\bigr)^4\right).`

阈值常数 $`c` 和上界的隐常数对两个特征族均为绝对常数。估计覆盖从 $`1` 到 $`N` 的所有系数。高度区间的起点和能量线 $`\sigma_0` 可以任意平移。

{docstring HalfPlaneCharacterLargeValues}

{docstring huxley_character_large_values}

证明先在 $`M\le n\le2M` 上对特征相关核移线。设高度窗口长为 $`W`，$`H=D(W+2)`。移线产生 $`M^{-1/(4+\log H)}`，对 $`M=1,2,4,\ldots` 求和至多损失一个 $`1+\log H` 因子。用带权 Cauchy–Schwarz 合并各块，可把系数能量精确加回 $`G`。最后把高度区间切成较短的窗口，使各窗口中与样本数成正比的项至多为该窗口样本数乘以 $`V^2/2`。这一步给出上界中的 $`V^{-6}` 项。

{docstring full_character_sampling}

若只取导子为 $`b` 的倍数的本原特征，且 $`1\le b\le Q`，则可在阈值和计数上界中同时取 $`D=\lfloor Q^2/b\rfloor`。理由是两特征的相关积可以提升到 $`\operatorname{lcm}(q,r)`。因 $`b\mid\gcd(q,r)`，这个模数至多为 $`Q^2/b`。同一改进也适用于任意有限高度窗口内的均方。

{docstring common_conductor_window_mean}

{docstring common_conductor_large_values}

# 固定高度的导子平均
%%%
tag := "conductor-polynomial-means"
file := "conductor-polynomial-means"
%%%

令 $`P_\chi(s)=\sum_{n\le N}a_n\chi(n)n^{-s}`。固定 $`s=1/2+it`，在 $`Q<q\le R` 的本原特征上应用大筛，得到

$$`\sum_{Q<q\le R}\frac1{\varphi(q)}\sum_{\chi\bmod q}^{*}|P_\chi(s)|^2
\le (2R+N/Q)\sum_{n\le N}\frac{|a_n|^2}{n},\qquad Q\ge1.`

{docstring AnalyticNumberTheory.PrimeDistribution.conductor_polynomial_second_moment}

模长至多为一的系数给出 $`1+\log N` 的对角和，因而可用于 Möbius 多项式。若 $`a_n=\Lambda(n)`，则用 $`\Lambda(n)\le\log N` 和 Mertens 和式得到 $`O((1+\log N)^2)`。

{docstring AnalyticNumberTheory.PrimeDistribution.mangoldt_conductor_polynomial_second}

对有界系数的四阶矩，将 $`P_\chi(s)^2` 写为长度 $`N^2` 的特征多项式。乘积系数的模由约数个数 $`d(n)` 控制。于是右端为 $`(2R+N^2/Q)(1+\log(N^2))^4`，对所有实数 $`t` 一致成立。

{docstring AnalyticNumberTheory.PrimeDistribution.bounded_conductor_polynomial_fourth}
