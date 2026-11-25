import AnalyticNumberTheory.DivisorProblems.GaussCircleCubeRoot
import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import AnalyticNumberTheory.DivisorProblems.DivisorCubeRoot
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DivisorProblems

#doc (Manual) "双曲线下的格点与除数和" =>
%%%
tag := "divisor-sums"
file := "divisor-sums"
%%%

{index}[Dirichlet 双曲线法]把 $`ab\le N` 的正整数格点按乘积分类，每个 $`n\le N` 对应 $`d(n)` 个格点。令 $`u=\lfloor\sqrt N\rfloor`。每个格点至少有一个坐标不超过 $`u`，按两个坐标分别计数时，中央的 $`u\times u` 方块会被算两次。因此

$$`\sum_{n\le N}d(n)+u^2=2\sum_{a=1}^u\lfloor N/a\rfloor.`

{docstring sum_card_divisors_add_sqrt_sq}

以 $`N=10` 为例，$`u=3`，右端为 $`2(10+5+3)=36`，故除数个数的总和为 $`27`。将取整误差与调和和式结合，可得主项 $`x\log x+(2\gamma-1)x` 及以下余项界。

{docstring abs_divisorError_le_of_one_le}

若要研究余项中的抵消，可以保留每个取整误差的符号。令 $`\psi(t)=\{t\}-1/2`，则除数余项与 $`-2\sum_{d\le\sqrt x}\psi(x/d)` 的差至多为八。这个约化把改进余项的任务化为估计一个振荡和。

{docstring abs_divisorError_add_two_sum_sawtooth_le}

在二进区间 $`D<n\le 2D` 上，相位 $`A/n` 的二阶导数 $`2A/n^3` 在端点之间只相差常数倍。van der Corput 二阶导数估计因此可以一致地用于该区间的任一子区间。

{docstring norm_sum_reciprocal_phase_le}

将锯齿函数夹在两个有限 Fourier 和之间，再逐频率使用二阶导数估计，可以把每个二进区间的贡献控制在 $`O(x^{1/3})` 内。从一到 $`\sqrt x` 共有 $`O(\log x)` 个区间，包括末尾可能不完整的一段。合起来便将双曲线法的平方根误差改进到

$$`\Delta(x)=O\bigl(x^{1/3}\log x\bigr).`

{docstring abs_divisorError_le_cubeRoot_mul_log}

# Gauss 圆问题
%%%
tag := "gauss-circle-error"
file := "gauss-circle"
%%%

{index}[Gauss 圆问题]把平方半径记为 $`x`。闭圆盘内整点数 $`R(x)` 包含原点和边界点。面积给出的主项是 $`\pi x`，余项满足

$$`|R(x)-\pi x|\ll x^{1/3}\qquad(x\ge2).`

{docstring AnalyticNumberTheory.DivisorProblems.abs_gaussCircleError_le_cubeRoot}

按坐标轴和对角线分成八个扇区后，只需沿 $`0\le u\le\sqrt{x/2}` 计算圆弧 $`v=\sqrt{x-u^2}` 下的整点。对称公式分别计入坐标轴和对角线上的格点。比较圆弧下的面积后，余项化为锯齿函数沿圆弧的和，另有一个绝对值至多为八的边界误差。

{docstring AnalyticNumberTheory.DivisorProblems.gaussCircleCount_eq_octant_slices}

{docstring AnalyticNumberTheory.DivisorProblems.abs_gaussCircleError_add_octant_sawtooth_le}

将锯齿函数作 Fourier 逼近，再用二阶导数估计各个频率的和，得到三分之一次方界。把格点按 $`m^2+n^2` 分组，同一余项也适用于两平方表示数的求和函数。

{docstring AnalyticNumberTheory.DivisorProblems.sum_repTwoSquares_sub_pi_isBigO_cubeRoot}
