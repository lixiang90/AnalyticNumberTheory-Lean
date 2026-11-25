import AnalyticNumberTheory.ExponentialSums.VinogradovLowerBounds
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
