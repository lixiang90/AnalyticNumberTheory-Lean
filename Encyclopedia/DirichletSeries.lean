import AnalyticNumberTheory.DirichletSeries.RamachandraPolarDecay
import AnalyticNumberTheory.DirichletSeries.Ramachandra
import AnalyticNumberTheory.DirichletSeries.EulerProduct
import AnalyticNumberTheory.DirichletSeries.FrequencyUniqueness
import AnalyticNumberTheory.DirichletSeries.FrequencyDensity
import AnalyticNumberTheory.DirichletSeries.FrequencyMeanValues
import AnalyticNumberTheory.DirichletSeries.EventualLandau
import AnalyticNumberTheory.DirichletSeries.OrdinaryAbel
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletSeries

#doc (Manual) "Dirichlet 级数与 Euler 乘积" =>
%%%
tag := "euler-products"
file := "euler-products"
%%%

{index}[Euler 乘积]在 $`\operatorname{Re}(s)>1` 内，$`\sum_{n\ge 1}n^{-s}` 绝对收敛。每个素数 $`p` 提供一个几何级数，展开有限多个这样的因子时，唯一分解保证每个由这些素数构成的正整数恰好出现一次。让素数集合增大，便得到

$$`\zeta(s)=\prod_p(1-p^{-s})^{-1}.`

{docstring AnalyticNumberTheory.DirichletSeries.riemannZeta_eulerProduct_hasProd}

对 Euler 乘积作对数求导，素数 $`p` 的局部因子给出 $`(\log p)p^{-s}/(1-p^{-s})`。再展开分母，可以读出每个素数幂的权重 $`\log p`。这正是{ref "prime-counting"}[素数计数]中使用的 von Mangoldt 权重。

{docstring riemannZeta_neg_logDeriv_eq_tsum_primes}

# 广义 Dirichlet 级数的收敛半平面
%%%
tag := "general-dirichlet-convergence"
file := "general-dirichlet-convergence"
%%%

设 $`0\le\lambda_0<\lambda_1<\cdots` 且 $`\lambda_n\to\infty`。{index}[广义 Dirichlet 级数]的第 $`n` 项是 $`a_n e^{-\lambda_n s}`。取 $`\lambda_n=\log(n+1)`、系数取 $`a(n+1)`，前 $`N` 项的和就等于普通 Dirichlet 级数从 $`1` 到 $`N` 的部分和。

{docstring DirichletFrequency}

{docstring DirichletFrequency.logarithmic_partialSum}

在一点 $`s_0` 固定系数的权重，并令 $`A(u)=\sum_{\lambda_n\le u}a_n e^{-\lambda_n s_0}`。这个阶梯函数在每个指数处纳入对应的项。对有限和使用 Abel 求和，就能直接得到边界项 $`A(\lambda_N)e^{-z\lambda_N}` 和一段有限积分。

{docstring DirichletFrequency.partialSum_eq_boundary_add_integral}

若 $`|A(u)|\le C e^{\alpha u}` 且 $`d=\Re z-\alpha>0`，则边界项趋于零，得到

$$`F(s_0+z)=z\int_{\lambda_0}^{\infty} A(u)e^{-zu}\,du.`

截在 $`\lambda_N` 并保留该项时，误差至多为 $`C(1+|z|/d)e^{-d\lambda_N}`。这个估计也给出向右逐渐变宽的区域上的一致收敛。只要 $`d\ge\delta>0` 且 $`|z|\le Kd e^{Hd}`，就可以为整个区域选取同一个截断位置。

{docstring DirichletFrequency.tendsto_partialSum_integral}

{docstring DirichletFrequency.norm_partialSum_sub_sum_le}

{docstring DirichletFrequency.tendstoUniformlyOn_of_summatory_bound}

一点处的有序收敛使 $`A(u)` 有界。取 $`\alpha=0` 并让 $`s_0` 趋近收敛横坐标，便知在整个开收敛半平面内，部分和局部一致收敛，和函数全纯。

{docstring DirichletFrequency.analyticOnNhd_sum}

# 实截点的 Abel 求和公式
%%%
tag := "abel-real-cutoffs"
file := "real-cutoffs"
%%%

固定 $`s_0`，写 $`A_s(u)=\sum_{\lambda_n\le u}a_n e^{-s\lambda_n}`。两个实截点 $`x<y` 可以落在相邻指数之间，也可以恰好等于指数。和 $`A_{s_0+z}(y)-A_{s_0+z}(x)` 包含右端点处的项，左端点处的项已经被减去。有限 Abel 公式给出

$$`A_{s_0+z}(y)-A_{s_0+z}(x)
   =A_{s_0}(y)e^{-zy}-A_{s_0}(x)e^{-zx}+z\int_x^y A_{s_0}(u)e^{-zu}\,du.`

{docstring DirichletFrequency.summatory_sub_eq_boundary_add_integral}

在相邻指数之间，阶梯函数 $`A_{s_0}` 恒定。移动右端点时，积分新添的一段恰好补偿右边界项的变化。交换两个端点，定向积分和有限和同时变号。让实截点趋于正无穷，也得到与有序部分和相同的极限。

{docstring DirichletFrequency.tendsto_summatory_iff}

若 $`|A_{s_0}(u)|\le Ce^{\alpha u}` 且 $`d=\Re z-\alpha>0`，在任意 $`y\ge\lambda_0` 截断后，误差至多为 $`C(1+|z|/d)e^{-dy}`。指数中的 $`y` 可以直接取实际截点。

{docstring DirichletFrequency.norm_summatory_sub_sum_le}

对普通 Dirichlet 级数，截点 $`\log x` 纳入的正整数恰有 $`\lfloor x\rfloor` 个。令 $`B(t)=\sum_{1\le n\le t}a_n`，在积分中作代换 $`u=\log t`，便对所有 $`0<x<y` 得到

$$`\sum_{x<n\le y}a_n n^{-s}
   =B(y)y^{-s}-B(x)x^{-s}+s\int_x^y B(t)t^{-s-1}\,dt.`

{docstring DirichletFrequency.logarithmic_count_log}

{docstring dirichletPartialSum_sub_eq_coeffPartialSum_integral}

取 $`x=1`、$`y=2`，即使 $`a_1\ne0`，左边也只留下 $`a_2 2^{-s}`。右边积分区间内部的 $`B(t)=a_1`，其贡献与边界项中含 $`a_1` 的部分恰好抵消。

# 指数的密度与绝对收敛
%%%
tag := "dirichlet-frequency-density"
file := "frequency-density"
%%%

设 $`\sigma_c` 和 $`\sigma_a` 分别是有序收敛与绝对收敛的横坐标。到达第 $`n` 个指数时，已有 $`n+1` 项。指数的疏密可以用上极限衡量。

$$`D=\limsup_{n\to\infty}\frac{\log(n+1)}{\lambda_n}.`

{docstring DirichletFrequency.exponentDensity}

若 $`d>D`，取 $`D<\beta<d` 且 $`\beta>0`。充分大的 $`n` 满足 $`\log(n+1)\le\beta\lambda_n`，故 $`e^{-d\lambda_n}\le(n+1)^{-d/\beta}`。右侧是收敛的 $`p` 级数。

{docstring DirichletFrequency.summable_exp_of_exponentDensity_lt}

在 $`s_0` 处有序收敛时，单项 $`a_ne^{-s_0\lambda_n}` 有界。以上比较给出 $`\Re s>\Re s_0+D` 时的绝对收敛。因此有限的 $`D` 给出 $`\sigma_c\le\sigma_a\le\sigma_c+D`。Lean 的横坐标取扩展实数值，故也覆盖处处收敛或处处发散的情形。

{docstring DirichletFrequency.absoluteAbscissa_le_abscissa_add}

普通 Dirichlet 级数的 $`\lambda_n=\log(n+1)` 给出 $`D=1`。若取 $`\lambda_n=n+1`，令 $`w=e^{-s}` 就得到幂级数 $`\sum a_n w^{n+1}`。此时 $`D=0`，两种横坐标相同。

{docstring DirichletFrequency.logarithmic_exponentDensity}

{docstring DirichletFrequency.positiveIntegers_absoluteAbscissa_eq}

# 从实轴上的函数值恢复系数
%%%
tag := "general-dirichlet-uniqueness"
file := "general-dirichlet-uniqueness"
%%%

在{ref "general-dirichlet-convergence"}[广义 Dirichlet 级数]中，各指数严格递增。在实轴上取 $`t\to+\infty`，减去前 $`n` 项后，首个尚未减去的指数为 $`\lambda_n`。乘以 $`e^{t\lambda_n}`，所得极限就是对应系数。

$$`a_n=\lim_{t\to+\infty}e^{t\lambda_n}
  \left(F(t)-\sum_{k<n}a_k e^{-t\lambda_k}\right).`

{docstring DirichletFrequency.tendsto_coefficient}

例如 $`F(t)=2+3e^{-\sqrt{2}\,t}`，先令 $`t\to+\infty` 得到常数项 $`2`，再把 $`F(t)-2` 乘以 $`e^{\sqrt{2}\,t}` 即得 $`3`。一般情形由下一指数 $`\lambda_{n+1}` 控制剩余项。由此可以在任意趋于正无穷的实数列上逐项比较两个具有相同指数的级数。

{docstring DirichletFrequency.ConvergesAt.real_remainder}

{docstring DirichletFrequency.eq_of_sum_eq_on_seq}

# 竖直线上的系数反演与二次均值
%%%
tag := "general-dirichlet-vertical-means"
file := "vertical-means"
%%%

固定一条绝对收敛线 $`\Re s=\sigma`，令 $`s=\sigma+it`。第 $`n` 项的高度因子是 $`e^{-i\lambda_n t}`。若要读出频率 $`u` 的系数，可先乘以 $`e^{us}`，再取从 $`-T` 到 $`T` 的积分平均。此时各项的频率变为 $`u-\lambda_n`。

{docstring DirichletFrequency.AbsConvergesAt.vertical_expansion}

一个频率 $`r` 的平均值为 $`\sin(rT)/(rT)`，在 $`r=0` 处取值为 $`1`。这个核的绝对值至多为 $`1`。当 $`T\to\infty` 时，每个非零频率的平均趋于零，绝对可和性允许逐项取极限。

{docstring AnalyticNumberTheory.AnalyticTools.symmetricMean_exp}

{docstring AnalyticNumberTheory.AnalyticTools.tendsto_symmetricMean_expansion}

因此当 $`u=\lambda_k` 时，

$$`a_k=\lim_{T\to\infty}\frac{1}{2T}\int_{-T}^{T}
 F(\sigma+it)e^{\lambda_k(\sigma+it)}\,dt.`

当 $`u` 不在指数列中时，极限为零。这里固定的是一条{ref "dirichlet-frequency-density"}[绝对收敛线]，即使恰好在绝对收敛半平面的边界，只要该线上的级数绝对收敛，公式仍然成立。

{docstring DirichletFrequency.tendsto_vertical_frequency_mean}

{docstring DirichletFrequency.tendsto_vertical_coefficient}

对具有相同频率的两个级数，把 $`F_a(\sigma+it)` 乘以 $`\overline{F_b(\tau+it)}`。展开后配对 $`(n,m)` 的振荡频率是 $`\lambda_m-\lambda_n`，所以均值只保留 $`n=m` 的项。两条绝对收敛线可以独立选择。

{docstring DirichletFrequency.tendsto_vertical_mixed_mean}

取同一级数和同一条线，便得到

$$`\lim_{T\to\infty}\frac{1}{2T}\int_{-T}^{T}|F(\sigma+it)|^2\,dt
 =\sum_{n\ge0}|a_n|^2e^{-2\sigma\lambda_n}.`

例如 $`F(s)=2+3e^{-\sqrt{2}s}` 的二次均值是 $`4+9e^{-2\sqrt{2}\sigma}`。交叉项在对称平均中趋于零。

{docstring DirichletFrequency.tendsto_vertical_mean_square}

# 广义 Dirichlet 级数的逐项微分
%%%
tag := "general-dirichlet-derivatives"
file := "termwise-derivatives"
%%%

频率 $`\lambda_n` 的指数项每求一次导数，就多出一个因子 $`-\lambda_n`。在{ref "general-dirichlet-convergence"}[有序收敛的开半平面]内，这给出任意阶导数的展开

$$`F^{(k)}(s)=\sum_{n\ge0}(-\lambda_n)^k a_n e^{-\lambda_n s}.`

{docstring DirichletFrequency.iteratedDeriv_sum}

先对有限部分和求导，再用全纯函数序列的局部一致收敛把导数传到极限。每一阶加权部分和都在原来的开半平面内局部一致收敛。

{docstring DirichletFrequency.tendstoLocallyUniformlyOn_weighted_partialSum}

# 正系数级数的 Landau 奇点定理
%%%
tag := "landau-general-dirichlet"
file := "landau-singularity"
%%%

设 $`a_n\ge0`。在实轴上，各项同号，因此有序收敛与绝对收敛具有相同的横坐标。在有限的收敛横坐标 $`\sigma_c` 处，和函数必有奇点。这里的结论也排除了与右半平面上的和函数相符的任何圆盘全纯延拓。

{docstring DirichletFrequency.absoluteAbscissa_eq_of_nonneg}

设级数在 $`\Re s>\sigma` 内收敛，并且能延拓到以 $`\sigma` 为中心、半径为 $`r` 的开圆盘。取实数 $`x<c`，其中 $`c>\sigma`，在 $`c` 处向左展开 Taylor 级数。由{ref "general-dirichlet-derivatives"}[逐项微分]，Taylor 展开中每个频率对第 $`k` 项的贡献为

$$`a_n e^{-c\lambda_n}\frac{((c-x)\lambda_n)^k}{k!}.`

{docstring DirichletFrequency.hasSum_taylorMoment_frequency}

这些数非负。对 $`k` 求和得到 $`a_n e^{-x\lambda_n}`，于是 Taylor 级数的收敛给出原级数在 $`x` 处的绝对收敛。令 $`c` 从右方趋于 $`\sigma`，可使 $`x` 遍历圆盘内的左半段。因此 $`\sigma_a\le\sigma-r`，而且和函数在整个开圆盘上与给定的延拓相等。取 $`\sigma=\sigma_c` 就得到矛盾。

{docstring DirichletFrequency.landau_absoluteAbscissa_le}

{docstring DirichletFrequency.landau_eqOn_ball}

有限个任意复系数只贡献一个整的指数多项式。去掉这些项后，以上奇点结论适用于最终为非负实数的系数。例如 $`\sum_{n\ge0}2^{-ns}=1/(1-2^{-s})` 的收敛横坐标为零。改变有限个系数，在 $`s=0` 的极点仍然存在。

{docstring DirichletFrequency.sum_tail_eq_sub}

{docstring DirichletFrequency.no_continuation_of_eventually_nonneg}

# 指数平滑与 Ramachandra 公式
%%%
tag := "ramachandra-smoothing"
file := "ramachandra-smoothing"
%%%

对 $`F(s)=\sum a_n n^{-s}`，用 Gamma 函数的 Mellin 反演在每一项引入权 $`e^{-n/X}`。设 $`X>0`，在右侧绝对收敛线上，以 $`F(s+w)\Gamma(w)X^w` 的积分表示这个平滑和。

{docstring hasSum_exponentiallySmoothed}

设在左侧直线 $`\Re w=l` 上有函数方程 $`F(s+w)=\psi(s+w)G(1-s-w)`，其中 $`-1<l<0` 且对偶级数在该线上绝对收敛。把对偶级数截为前 $`N` 项和尾和。若 $`F` 和 $`\psi` 在各自移动的带域内全纯且沿竖直方向至多按多项式增长，分别移动积分线便得到平滑和、有限对偶和与两个余项积分之间的恒等式。两条右侧积分线可独立选取。移动时越过 $`\Gamma(w)` 在零点的极点，这解释了公式中 $`F(s)` 和有限对偶和的来源。

{docstring ramachandra_smoothed_functional_equation}

# 有限阶极点对平滑公式的贡献
%%%
tag := "ramachandra-polar-residue"
file := "polar-remainder"
%%%

若围道越过 $`F` 在 $`q` 处的极点，设其阶数至多为 $`k+1`。在平移坐标 $`w` 中，极点位于 $`p=q-s`。将被积函数乘以 $`(w-p)^{k+1}` 后，取其在 $`p` 处的 $`k` 阶导数，再除以 $`k!`，即为{ref "ramachandra-smoothing"}[两条围道公式]中要扣除的留数。

{docstring ramachandra_smoothed_functional_equation_with_pole}

设 $`H=1+|\Im(q-s)|`。在定理给定的紧实部区间内，当 $`1\le X\le H^A` 时，留数对每个自然数 $`m` 均为 $`O(H^{-m})`。同一常数适用于所有对偶截断长度 $`N`。

{docstring gammaSmoothingResidue_rapid_decay}

{docstring ramachandra_smoothed_functional_equation_error}
