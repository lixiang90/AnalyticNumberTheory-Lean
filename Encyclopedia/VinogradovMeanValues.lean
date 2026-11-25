import AnalyticNumberTheory.ExponentialSums.VinogradovLowerBounds
import AnalyticNumberTheory.ExponentialSums.VinogradovNonsingular
import AnalyticNumberTheory.ExponentialSums.VinogradovSingular
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ExponentialSums

#doc (Manual) "Vinogradov 均值与幂和方程组" =>
%%%
tag := "vinogradov-mean-values"
file := "vinogradov-mean-values"
%%%

{index}[Vinogradov 均值]令 $`e(t)=\exp(2\pi i t)`。把一个多项式指数和的绝对值提升到偶数次幂，再对各系数分别积分，得到

$$`J_{s,k}(N)=\int_{[0,1]^k}\left|\sum_{n=1}^{N}e(\alpha_1 n+\cdots+\alpha_k n^k)\right|^{2s}\,d\boldsymbol\alpha.`

这个实数恰好是下列方程组的有序整数解数，其中每个变量都在 $`[1,N]` 内。

$$`\sum_{i=1}^s x_i^j=\sum_{i=1}^s y_i^j\qquad(1\le j\le k).`

展开积分后，只要某个幂和之差是非零整数，对相应的 $`\alpha_j` 从零到一积分就得到零。满足全部方程的每一对元组则贡献一。

{docstring vinogradovJ_eq_card_solutions}

# 对角范围与主项系数
%%%
tag := "vinogradov-diagonal-range"
file := "diagonal"
%%%

当 $`s\le k` 时，前 $`s` 个幂和由 Newton 恒等式确定全部初等对称多项式，进而确定首一多项式 $`\prod_i(X-x_i)`。因此 $`y` 是 $`x` 的一个排列，重复坐标也按重数保留。例如 $`s=2` 时，和与平方和确定乘积 $`x_1x_2=((x_1+x_2)^2-(x_1^2+x_2^2))/2`，两个坐标便是同一个二次多项式的根。

{docstring exists_perm_of_equal_power_sums}

每个 $`x` 至少有一个配对，最多有 $`s!` 个配对。坐标互异时恰有 $`s!` 个。因此在对角范围内，

$$`N^s\le J_{s,k}(N)\le s!N^s,\qquad
\lim_{N\to\infty}\frac{J_{s,k}(N)}{N^s}=s!.`

{docstring vinogradovJ_diagonal_bounds}

{docstring vinogradovJ_diagonal_tendsto}

# 任意次数的计数下界
%%%
tag := "vinogradov-volume-bound"
file := "lower-bound"
%%%

记 $`r(\boldsymbol u)` 为幂和向量等于 $`\boldsymbol u` 的元组数，则 $`\sum r=N^s` 而 $`\sum r^2=J_{s,k}(N)`。第 $`j` 个幂和落在 $`[0,sN^j]` 中。对这些向量应用 Cauchy–Schwarz 不等式，得到在所有 $`s,k,N` 下都成立的有限下界

$$`N^{2s}\le J_{s,k}(N)\prod_{j=1}^k(sN^j+1).`

{docstring vinogradovJ_box_lower}

# 平移、同余与非奇异解
%%%
tag := "vinogradov-congruences"
file := "congruences"
%%%

对同一组有序变量，同时施加整数仿射变换 $`t\mapsto at+b`，其中 $`a\ne0`，保持齐次幂和方程的解数。二项展开说明每个新方程只涉及原来较低次和同次的方程。把所有变量限制在模 $`p` 的一个剩余类，因而可以将长度 $`N` 缩短为至多 $`\lfloor N/p\rfloor+1`。另一个归约适用于指定幂和之差的非齐次方程。将变量按幂和向量分组，对相应的纤维大小应用均值不等式，便知指定任何差值的解数都至多为差值零的解数。

{docstring vinogradovCountOn_affine}

{docstring vinogradovCountOn_residue_le}

{docstring vinogradovShiftedPairs_card_le}

设 $`p>k\ge1` 是素数与次数，$`h_1,\ldots,h_k` 为指定的整数。在每条边长 $`mp^k` 的整数盒中，考虑 $`k` 个坐标两两模 $`p` 不同且满足

$$`\sum_{i=1}^k x_i^j\equiv h_j\pmod {p^j}\qquad (1\le j\le k)`

的有序元组。其个数至多为 $`k!m^k p^{k(k-1)/2}`。这里 $`p^{k(k-1)/2}` 来自把每个第 $`j` 次幂和从模 $`p^j` 提升到模 $`p^k` 的选择数。给定全部提升值后，Newton 恒等式确定以各坐标为根的首一多项式。模 $`p` 两两不同的条件确保各坐标的配对唯一到排列。

{docstring vinogradov_congruence_box_le}

在均值递推中，若两边都选出了 $`k` 个两两不同模 $`p` 的坐标，可以把其余坐标按剩余类分组。对指数和使用 Hölder 不等式后，所有剩余坐标限制在同一个剩余类。上面的同余盒控制选出的坐标；其余坐标平移后可除以 $`p`，从而得到长度 $`\lfloor N/p\rfloor+1` 的均值。

{docstring vinogradov_marked_card_le}

若至少一边出现的剩余类不足 $`k` 个，则先枚举剩余类，再估计每种排列对应的混合均值。下面的界保留了挑选至多 $`k-1` 个剩余类时的二项式因子。

{docstring vinogradov_singular_interval_le}
