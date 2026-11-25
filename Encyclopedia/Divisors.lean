import AnalyticNumberTheory.DivisorProblems.DivisorExponent
import AnalyticNumberTheory.DivisorProblems.TruncatedVoronoi
import AnalyticNumberTheory.DivisorProblems.GaussCircleCubeRoot
import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import AnalyticNumberTheory.DivisorProblems.DivisorPowerMeans
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

# 除数函数的任意整数阶矩
%%%
tag := "divisor-power-means"
file := "divisor-power-means"
%%%

{index}[广义除数函数]令 $`d_r(n)` 为把 $`n` 写成 $`r` 个正整数的有序乘积的方式数，允许因子等于一。逐次对除数求和便得到递推 $`d_{r+1}(n)=\sum_{u\mid n}d_r(u)`。普通除数函数是 $`d(n)=d_2(n)`。

{docstring orderedDivisorCount}

对每个 $`n=uv` 都有 $`d(n)\le d(u)d(v)`，因为 $`n` 的每个除数都可以拆成 $`u` 和 $`v` 的两个除数的乘积。若已知 $`d(m)^k\le d_{2^k}(m)`，就在所有 $`uv=n` 上对两个因子的界作卷积。这样的有序对恰有 $`d(n)` 个，归纳给出 $`d(n)^{k+1}\le d_{2^{k+1}}(n)`。

{docstring card_divisors_pow_le_ordered}

在 $`n\le N` 的双曲线区域上，每增加一个有序因子，带 $`1/n` 权的和至多多出一个调和和。对普通和，最后一个因子直接贡献 $`\lfloor N/u\rfloor\le N/u`。于是对每个整数 $`k\ge0` 和 $`N\ge1` 有

$$`\sum_{n\le N}\frac{d(n)^k}{n}\le(1+\log N)^{2^k},
\qquad \sum_{n\le N}d(n)^k\le N(1+\log N)^{2^k-1}.`

{docstring sum_card_divisors_pow_div_le}

{docstring sum_card_divisors_pow_le}

例如取 $`k=2`，带权和至多为四次对数。这正是{ref "short-prime-polynomial-moments"}[短 Möbius 多项式四阶矩]中平方系数所需的界。

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

# 除数误差的 Voronoï 截断公式
%%%
tag := "divisor-voronoi-formula"
file := "voronoi-formula"
%%%

{index}[Voronoï 截断公式]设 $`\Delta(x)=\sum_{n\le x}d(n)-x\log x-(2\gamma-1)x`。双曲线求和把误差写成锯齿函数之和。对锯齿函数作随位置变化的 Fourier 截断，再用{ref "poisson-reciprocal-phase"}[倒数相位变换]，相同乘积的因子对合成系数 $`d(n)`，驻相因子则产生相移 $`-\pi/4`。对任意实数 $`1\le y\le x` 有

$$`\Delta(x)=\frac{x^{1/4}}{\pi\sqrt{2}}\sum_{n\le y}\frac{d(n)}{n^{3/4}}
 \cos\!\left(4\pi\sqrt{nx}-\frac{\pi}{4}\right)+R(x,y).`

对每个 $`\varepsilon>0`，一致余项为 $`R(x,y)=O_\varepsilon(x^\varepsilon(x^{1/4}+\sqrt{x/y}))`。例如取 $`y=\sqrt{x}`，两项同为 $`x^{1/4}`。另一种常用形式将余项写为 $`O_\varepsilon(x^{1/6+\varepsilon}y^{1/6}+x^{1/2+\varepsilon}y^{-1/2})`。

{docstring truncated_voronoi_divisor_formula_real}

{docstring truncated_voronoi_classical_error}

# 突破三分之一次幂的除数误差
%%%
tag := "divisor-exponent"
file := "divisor-exponent"
%%%

对于 $`x\ge2`，令 $`\Delta(x)=\sum_{n\le x}d(n)-x\log x-(2\gamma-1)x`。在狄利克雷双曲线法的分块求和中，对原变量使用三阶导数估计，对{ref "poisson-reciprocal-phase"}[倒数相位变换]后的平方根相位使用五阶导数估计。平衡两种估计，得到一个绝对常数 $`C`，使得

$$`|\Delta(x)|\le Cx^{27/82}(\log x)^2.`

因为 $`1/3-27/82=1/246>0`，两个对数因子也能由这一幂次差吸收，从而 $`\Delta(x)/x^{1/3}\to0`。{ref "higher-derivative-tests"}[高阶导数检验]给出上述两种分块估计共同使用的工具。

{docstring abs_divisorError_le_vanDerCorput_exponent}

{docstring divisorError_isLittleO_cubeRoot}
