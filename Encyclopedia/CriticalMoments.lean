import AnalyticNumberTheory.RiemannZeta.CriticalSecondMomentExpansion
import AnalyticNumberTheory.RiemannZeta.ReflectedSecondMoment
import AnalyticNumberTheory.RiemannZeta.CriticalMeanSquare
import AnalyticNumberTheory.DirichletLFunctions.CriticalCorrelations
import AnalyticNumberTheory.RiemannZeta.HurwitzMeanSquare
import AnalyticNumberTheory.RiemannZeta.FourthMomentAsymptotic
import AnalyticNumberTheory.RiemannZeta.HurwitzStripMeanSquare
import AnalyticNumberTheory.DirichletLFunctions.StripMeanSquare
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "ζ 的临界线矩与 Dirichlet L 函数的均方" =>
%%%
tag := "critical-second-moment"
file := "critical-second-moment"
%%%

{index}[ζ 函数的二阶矩]在临界线 $`s=1/2+it` 上，ζ 函数的均方随高度按对数增长，并且主项系数恰好为一。

$$`\int_1^T |\zeta(1/2+it)|^2\,dt\sim T\log T.`

{docstring mean_sq_riemannZeta_half_asymptotic}

取长为 $`\lfloor T\rfloor+1` 的 Dirichlet 多项式近似 ζ。两者之差的平方在 $`[1,T]` 上积分，再除以 $`T`，所得误差有一个绝对常数上界。

{docstring mean_sq_zeta_sub_long_dirichletPoly_half}

为了从{ref "dirichlet-polynomials"}[Dirichlet 多项式均值定理]读出主项，把多项式在 $`M=\lfloor T/\sqrt{\log T}\rfloor+1` 处截短。对角项给出调和和 $`\sum_{m\le M}1/m\sim\log T`。在均值定理中，非对角项相对于对角项的误差受 $`2\pi M/T` 控制。删掉的长多项式尾段，其系数平方和至多为 $`O(\sqrt{\log T})`。最后对两次近似分别使用平方可积函数的三角不等式，便可把短多项式的主项传回 ζ 函数。

# 周期系数与 Dirichlet 特征
%%%
tag := "periodic-second-moment"
file := "periodic-coefficients"
%%%

若 Dirichlet 级数的系数 $`a(n)` 以 $`q` 为周期且模不超过一，临界线均方除以 $`T\log T` 后的极限为一个周期内的系数平方平均值。证明先把多项式按剩余类拆为 Hurwitz ζ 函数的有限近似，再用同一个均方准则提取对角项。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_periodicLFunction_half}

对固定模数 $`q` 的 Dirichlet 特征，平方权在可逆剩余类上等于一，在其余类上等于零。因此极限是 $`\varphi(q)/q`。这个系数也适用于非原始特征，此处使用的是系数序列给定的模数。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_LFunction_half}

只在一个剩余类上取系数一，还能提取有理移位的 Hurwitz ζ 函数。计入周期分解中的尺度因子后，它的均方主项系数为一。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_hurwitzZeta_rational_half}

对任意固定的实移位 $`0<a\le1`，同样有主项 $`T\log T`。证明直接对频率 $`\log(n+a)` 应用间隔频率均值定理，并利用 $`\sum_{1\le n\le N}1/(n+a)` 与调和和的差至多为一。因此，无理移位也包括在内。

{docstring mean_sq_hurwitzZeta_half}

用复极化恒等式可以同时比较两个任意复周期序列 $`a,b`。把临界线上的乘积 $`L_a(s)\overline{L_b(s)}` 积分并除以 $`T\log T`，极限为 $`q^{-1}\sum_{r\bmod q}a(r)\overline{b(r)}`。因此，同一模数的两个不同特征在这个均值下正交。

{docstring AnalyticNumberTheory.DirichletLFunctions.mixed_mean_periodicLFunctions}

{docstring AnalyticNumberTheory.DirichletLFunctions.mixed_mean_LFunctions_of_ne}

# 临界线右侧的 Hurwitz 均方
%%%
tag := "hurwitz-strip-mean"
file := "hurwitz-strip"
%%%

{index}[Hurwitz ζ 函数的均方]对固定的实数 $`0<a\le1` 和 $`1/2<\sigma\le1`，移位 $`a` 可以是无理数。按区间长度归一化后的均方趋于一个有限常数，

$$`\lim_{T\to\infty}\frac1T\int_1^T|\zeta(\sigma+it,a)|^2\,dt
=\sum_{n=0}^{\infty}(n+a)^{-2\sigma}=\zeta(2\sigma,a).`

当 $`a=1` 时，右侧为 Riemann ζ 函数的值 $`\zeta(2\sigma)`。积分从高度一开始，因此公式也包含 $`\sigma=1`。证明将长多项式在 $`\sqrt T` 附近分成两段。短段的均值给出对角和，长段的均方误差由收敛级数 $`\sum(n+a)^{-2\sigma}` 的尾项控制。临界线 $`\sigma=1/2` 时这个级数发散，前节中的因子 $`\log T` 正来自其部分和。

{docstring mean_sq_hurwitzZeta_of_half_lt}

{docstring hurwitzZeta_re_eq_square_diagonal}

对任意固定周期 $`q` 和复系数 $`a(n)`，同一条直线上的均方也有极限。它等于 $`\sum_{n\ge1}|a(n)|^2 n^{-2\sigma}`。对于模 $`q` 的任意 Dirichlet 特征，系数的绝对值在与 $`q` 互素的整数处为一，在其余整数处为零，所以极限只由模数决定，具体为

$$`\zeta(2\sigma)\prod_{p\mid q}(1-p^{-2\sigma}).`

例如对模四的任一特征，主项系数就是 $`(1-2^{-2\sigma})\zeta(2\sigma)`，因为所有偶数项都被删去。

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_periodicLFunction_of_half_lt}

{docstring AnalyticNumberTheory.DirichletLFunctions.mean_sq_LFunction_strip_euler_factors}

# ζ 函数在临界线两侧的二次矩
%%%
tag := "zeta-strip-second-moment-error"
file := "strip-mean-square"
%%%

取 $`I_\sigma(T)=\int_1^T|\zeta(\sigma+it)|^2\,dt`。当 $`1/2<\sigma<1` 固定时，Dirichlet 多项式的对角项决定主项。保留各频率间距的均方估计给出

$$`I_\sigma(T)=(T-1)\zeta(2\sigma)+O_\sigma(T^{2-2\sigma}).`

对固定 $`0<\sigma<1/2`，应用函数方程，把积分转到 $`1-\sigma` 处。Gamma 因子引入幂权；分部积分后得到

$$`I_\sigma(T)=\frac{(2\pi)^{2\sigma-1}\zeta(2-2\sigma)}{2-2\sigma}
 T^{2-2\sigma}+O_\sigma(T).`

两式均对 $`T\ge1` 成立。右半带中误差随 $`T` 次线性增长，左半带中主项比线性项增长得快。

{docstring riemannZeta_right_strip_second_moment}

{docstring riemannZeta_left_strip_second_moment}

# ζ 函数的四阶矩
%%%
tag := "critical-fourth-moment"
file := "fourth-moment"
%%%

{index}[Ingham 四阶矩定理]Ingham 的渐近公式给出四阶矩主项的精确系数。随着 $`T\to\infty`，

$$`\int_1^T |\zeta(1/2+it)|^4\,dt\sim\frac{T(\log T)^4}{2\pi^2}.`

{docstring fourthMoment_riemannZeta_equivalent}

平方展开中有两个对角项，各自的系数来自同一个算术和，其中 $`d(n)` 是 $`n` 的正因子个数。

$$`\sum_{n\le X}\frac{d(n)^2}{n}=\frac{(\log X)^4}{4\pi^2}+O\big((1+\log X)^3\big).`

{docstring AnalyticNumberTheory.DivisorProblems.divisor_square_harmonic_error}

在 $`[T,2T]` 上先把两个多项式截到 $`\lfloor\delta T\rfloor`。当 $`0<\delta\le1/(4\pi)` 时，混合项的相位导数远离零，可以逐项估计其振荡积分。均方比较给出两个对角项的主贡献。令 $`\delta` 趋于零，再对二倍区间求和，就得到从一到 $`T` 的渐近式。

{docstring fourthMoment_riemannZeta_dyadic_tendsto}

{index}[ζ 函数的四阶矩]对每个 $`\varepsilon>0`，存在常数 $`C_\varepsilon`，使对所有 $`T\ge1` 有

$$`\int_1^T |\zeta(1/2+it)|^4\,dt\le C_\varepsilon T^{1+\varepsilon}.`

在 $`t\in[T,2T]` 上，从{ref "riemann-xi"}[光滑函数方程]出发，将 $`\zeta(1/2+it)^2` 展开为带正因子数系数 $`d(n)` 的两个加权多项式。对任意固定 $`\eta>0`，在 $`\lceil T^{1+\eta}\rceil` 处截断的点态误差为 $`O_\eta(1)`。

{docstring norm_zeta_sq_sub_fourthMomentPieces_le}

每个多项式的积分权由高斯函数支配。使用除数多项式的均方估计，并把高度按二的幂分段求和，就得到上述四阶矩界。

{docstring fourthMoment_riemannZeta_le}

用留数移线提取长度 $`\lceil T\rceil` 的两个主多项式，可以把上界进一步改进到 $`O(T(\log T)^4)`。在 $`[T,2T]` 上，$`\zeta(1/2+it)^2` 与两个主多项式之和的差，其平方积分为 $`O(T(1+\log T)^3)`。主多项式的对角和涉及 $`\sum_{n\le T}d(n)^2/n`，这说明第四次对数幂从哪里出现。

{docstring zeta_sq_sub_fourthMomentMainTerms_mean_sq}

{docstring fourthMoment_riemannZeta_log_isBigO}

# 临界线二次矩的第二主项
%%%
tag := "zeta-critical-second-term"
file := "critical-second-term"
%%%

令 $`I(T)=\int_1^T|\zeta(1/2+it)|^2\,dt`。Riemann–Siegel 实余弦和的对角项给出调和数；其中的欧拉常数决定线性项的系数。对所有 $`T\ge 8\pi`，有

$$`I(T)=T\log\frac{T}{2\pi}+(2\gamma-1)T+O\!\left(T^{3/4}\sqrt{\log(T+2)}\right).`

此处误差为 $`o(T)`，因此能把第二主项从误差中分离出来。不同频率之间的余弦积分由振荡估计控制。

{docstring riemannZeta_critical_second_moment_expansion}

{docstring riemannZeta_critical_second_moment_remainder}
