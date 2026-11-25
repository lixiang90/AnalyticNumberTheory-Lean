import AnalyticNumberTheory.AnalyticTools.LaplaceJordanInversion
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools

#doc (Manual) "Fourier、Mellin 与 Laplace 变换" =>
%%%
tag := "fourier-mellin"
file := "fourier-mellin"
%%%

{index}[Fourier 变换]在核 $`e^{-2\pi i x\xi}` 的归一化下，函数 $`g(x)=e^{-\pi x^2}` 的 Fourier 变换仍是 $`g`。常数 $`\pi` 的位置很重要，它使得频率变量与原变量采用同一尺度。

{docstring fourier_gaussian_selfReciprocal}

{index}[Mellin 变换]Mellin 变换的核为 $`t^{s-1}`，它适合处理伸缩。对 $`t>0` 展开 $`1/(e^t-1)=\sum_{n\ge1}e^{-nt}`，在积分中作代换 $`u=nt`，每一项贡献 $`n^{-s}\Gamma(s)`。当 $`\operatorname{Re}(s)>1` 时，可以交换求和与积分，于是得到 $`\Gamma(s)\zeta(s)`。

{docstring mellin_inv_exp_sub_one_eq_gamma_mul_zeta}

# 从 Fourier 反演到竖线积分
%%%
tag := "transform-inversion"
file := "transform-inversion"
%%%

{index}[反演公式]设 $`f` 和它的 Fourier 变换都在实轴上绝对可积。在 $`f` 的任一连续点 $`x`，用相反符号的核积分就能恢复函数值：
$$`f(x)=\int_{\mathbb R}e^{2\pi i x\xi}\widehat f(\xi)\,d\xi.`

{docstring fourier_inversion}

对 Mellin 变换取 $`t=e^{-u}`，幂函数核随即化为指数核。固定 $`\sigma\in\mathbb R`，若 $`\int_0^\infty |f(t)|t^{\sigma-1}\,dt` 和变换在直线 $`\operatorname{Re}s=\sigma` 上的积分都绝对收敛，则在 $`x>0` 的连续点有
$$`f(x)=\frac{1}{2\pi}\int_{\mathbb R} x^{-\sigma-it}
                  \mathcal M f(\sigma+it)\,dt.`

{docstring mellin_eq_fourier_bridge}

{docstring mellin_inversion_bridge}

{index}[Bromwich 反演]对单边 Laplace 变换 $`F(s)=\int_0^\infty e^{-su}f(u)\,du`，将 $`e^{-\sigma u}f(u)` 在负半轴及原点取为零，所得函数记为 $`g`。它的 Fourier 变换满足 $`\widehat g(\xi)=F(\sigma+2\pi i\xi)`。因此，如果 $`g` 和 $`t\mapsto F(\sigma+it)` 都绝对可积，则在 $`x>0` 的连续点有
$$`f(x)=\frac{1}{2\pi}\int_{\mathbb R}e^{(\sigma+it)x}F(\sigma+it)\,dt.`
当 $`x<0` 时，同一积分为零。

{docstring fourier_laplaceDamped}

{docstring laplace_inversion}

{docstring laplace_inversion_neg}

# 在跳跃点反演
%%%
tag := "laplace-stieltjes-inversion"
file := "laplace-stieltjes-inversion"
%%%

{index}[Laplace–Stieltjes 反演]设一个单位质量集中在 $`a\ge0`，其累积函数为 $`f(u)=\mathbf{1}_{u>a}`，Laplace 变换为 $`e^{-as}/s`。对称截断竖线积分，先取 $`-T\le\operatorname{Im}s\le T`，再令 $`T\to\infty`。在任意 $`\sigma>0` 上，极限在 $`x<a` 时为零，在 $`x>a` 时为一，在 $`x=a` 时为二分之一。这也给出了原点处单位阶跃的反演值。

{docstring laplaceTransform_unitStep}

{docstring laplace_unitStep_inversion}

对一般正测度 $`\mu` 写 $`L_\mu(s)=\int_{\mathbb R} e^{-su}\,d\mu(u)`。设 $`\mu` 是 σ 有限测度且 $`\int_{\mathbb R}e^{-\sigma u}\,d\mu(u)<\infty`，其中 $`\sigma>0`。在有限高度，交换积分次序把 $`L_\mu(s)/s` 的反演写为 Perron 核 $`K_T(e^{x-u},\sigma)` 关于 $`\mu` 的积分。界 $`|K_T(y,\sigma)|\le 2y^\sigma` 与高度无关，因而可以用控制收敛定理逐点取极限，得到
$$`\lim_{T\to\infty}\frac{1}{2\pi}\int_{-T}^{T}
     e^{(\sigma+it)x}\frac{L_\mu(\sigma+it)}{\sigma+it}\,dt
     =\mu((-\infty,x))+\tfrac12\mu(\{x\}).`

{docstring truncatedBromwich_laplaceStieltjes}

{docstring laplaceStieltjes_inversion}

当 $`\mu` 是支撑在 $`[0,\infty)` 的有限测度时，$`L_\mu(s)/s` 正是累积函数 $`u\mapsto\mu((-\infty,u))` 的单边 Laplace 变换。上述公式在这个函数的每个连续点恢复函数值，在每个跳跃点给出左右极限的平均值。

{docstring laplaceTransform_cumulative}

{docstring laplace_cumulative_inversion}

# 局部有界变差函数的反演
%%%
tag := "laplace-jordan-inversion"
file := "laplace-jordan-inversion"
%%%

{index}[有界变差函数的反演]设 $`F(s)=\int_0^\infty e^{-su}f(u)\,du`，其中 $`f` 为实值函数。选定实数 $`\sigma`，使 $`\int_0^\infty e^{-\sigma u}|f(u)|\,du<\infty`。在 $`x>0` 处，若存在 $`0\le a<x<b` 使 $`f` 在 $`[a,b]` 上有界变差，则
$$`\lim_{T\to\infty}\frac1{2\pi}\int_{-T}^{T}e^{(\sigma+it)x}F(\sigma+it)\,dt
=\frac{f(x-)+f(x+)}2.`

{docstring laplace_jordan_inversion}

当 $`x=0` 时，只需 $`f` 在某个 $`[0,b]` 上有界变差，反演值是 $`f(0+)/2`。这是单边变换的端点效应：从负半轴取过来的极限是零。对任何 $`x<0`，只要加权积分收敛，截断积分的极限都是零。例如 $`f=\mathbf1_{(0,1)}` 在两个端点的反演值同为 $`1/2`，在区间内部的反演值为一。

{docstring laplace_jordan_inversion_zero}

{docstring laplace_jordan_inversion_neg}

为什么只须考察 $`x` 附近的变差？在有限高度 $`T`，将 $`g(u)=e^{-\sigma u}f(u)` 从正半轴用零延拓，Bromwich 积分便等于 $`e^{\sigma x}` 乘以 $`g` 的逆 Fourier 积分，频率范围为 $`|\xi|\le T/(2\pi)`。

{docstring truncatedBromwich_eq_fourier}

{index}[Riemann 局部化原理]两个可积函数若在 $`x` 的邻域相等，其截断逆 Fourier 积分之差趋向于零。把差函数移到原点附近，再除以位移变量，所得函数仍可积。它的 Fourier 变换在正负无穷处都趋向零，这给出了局部化所需的消去。

{docstring truncatedFourierInverse_localization}

在含有 $`x` 的小区间上，用 Jordan 分解把 $`f` 写成两个单调函数的差。可把这两个函数都向左延拓为零、向右延拓为常数。单调函数对应的 Stieltjes 测度在跳跃点给出半个原子质量；取差就恢复了 $`f` 的左右极限平均值。

{docstring exists_monotone_extensions_of_boundedVariation}

{docstring laplace_monotone_inversion}
