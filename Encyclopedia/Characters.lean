import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletLFunctions.PolyaDerivativeTruncation
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "Dirichlet 特征与区间和" =>
%%%
tag := "character-sums"
file := "character-sums"
%%%

{index}[Pólya–Vinogradov 不等式]设 $`\chi` 是模 $`q\ge 2` 的非主特征。一个完整周期的特征和为零。若只求区间 $`a<n\le b` 上的和，取绝对值后逐项相加给出长度界，而 Fourier 展开给出与区间长度无关的估计

$$`\left|\sum_{a<n\le b}\chi(n)\right|\le 4\sqrt q\log q.`

{docstring polya_vinogradov_Ioc}

这里允许 $`\chi` 由较小模数的特征诱导。排除主特征是必要的：对主特征，每个完整周期的贡献等于 $`\varphi(q)`。

# 从特征和到 L 函数的截断误差
%%%
tag := "polya-character-truncation"
file := "polya-truncation"
%%%

设 $`P_M(s,\chi)=\sum_{n\le M}\chi(n)n^{-s}`。当 $`\chi` 非主、$`\sigma=\Re s>0` 时，这些多项式收敛到 $`L(s,\chi)`。对从 $`M+1` 开始的特征和作 Abel 求和，得到

$$`|L(s,\chi)-P_M(s,\chi)|
 \le 4\sqrt q\log q\,\frac{|s|}{\sigma}(M+1)^{-\sigma}.`

{docstring tendsto_dirichletPoly_LFunction}

{docstring norm_LFunction_sub_polynomial_polya}

这个余项也适用于 $`M=0`。在临界线上，只要 $`M+1\ge q|s|`，它就至多为 $`8\sqrt{|s|}\log q`。

{docstring norm_LFunction_sub_polynomial_critical}

对有限和求导会给每个系数添上 $`-\log n`。为估计导数余项，在以 $`s` 为中心、半径 $`(4+\log(M+1))^{-1}` 的圆上使用上面的截断界。圆上 $`(M+1)^{-\Re z}` 至多为中心值的 $`e` 倍，因此 Cauchy 估计只多付出一个对数因子。{ref "critical-pointwise-character-means"}[固定高度的特征均方]将这个误差与有限多项式的均方合并。

{docstring norm_deriv_LFunction_sub_polynomial_critical}
