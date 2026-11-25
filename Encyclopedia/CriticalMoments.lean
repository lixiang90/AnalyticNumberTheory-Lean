import AnalyticNumberTheory.DirichletLFunctions.PerronWeightedMoments
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyUniformMoment
import AnalyticNumberTheory.DirichletLFunctions.PeriodicCriticalSecondMoment
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilyFourthMoment
import AnalyticNumberTheory.DirichletLFunctions.FullFamilyFourthSampling
import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentConstants
import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilySecondMoment
import AnalyticNumberTheory.DirichletLFunctions.CriticalPointwiseIntegrals
import AnalyticNumberTheory.RiemannZeta.HurwitzCriticalSecondMoment
import AnalyticNumberTheory.RiemannZeta.CriticalSecondMomentError
import AnalyticNumberTheory.RiemannZeta.CriticalSecondMomentExpansion
import AnalyticNumberTheory.RiemannZeta.ReflectedSecondMoment
import AnalyticNumberTheory.RiemannZeta.CriticalMeanSquare
import AnalyticNumberTheory.DirichletLFunctions.CriticalCorrelations
import AnalyticNumberTheory.RiemannZeta.HurwitzMeanSquare
import AnalyticNumberTheory.RiemannZeta.FourthMomentAsymptotic
import AnalyticNumberTheory.RiemannZeta.FourthMomentIngham
import AnalyticNumberTheory.RiemannZeta.FourthMomentDiscrete
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

# 固定高度的特征均方与 Perron 积分
%%%
tag := "critical-pointwise-character-means"
file := "pointwise-character-means"
%%%

{index}[固定模数的逐点均方]固定 $`s=1/2+it`。先在模 $`q` 的全部特征上求有限多项式的平方和。把系数按可逆剩余类分组，利用特征正交关系，再对每一类应用 Cauchy–Schwarz 不等式。长为 $`N` 的整数区间里，每类包含的项数至多为 $`1+N/q`，与区间起点无关。

{docstring AnalyticNumberTheory.DirichletLFunctions.fixed_modulus_polynomial_energy}

在临界线上 $`|n^{-s}|^2=1/n`，因此系数 $`a_n` 的贡献由 $`\sum_{n\le N}|a_n|^2/n` 控制。

{docstring AnalyticNumberTheory.DirichletLFunctions.critical_polynomial_energy}

取 $`U=1+|s|`，$`H=1+\log(qU)`，在 $`N=\lceil qU\rceil` 处应用{ref "polya-character-truncation"}[非主特征的截断估计]。对每个实高度和每个 $`q\ge2`，存在与它们无关的常数，使得

$$`\sum_{\chi\bmod q,\,\chi\ne\chi_0}|L^{(j)}(s,\chi)|^2
 \ll \varphi(q)\,U H^{2j+2}\qquad(j=0,1).`

{docstring AnalyticNumberTheory.DirichletLFunctions.nonprincipal_critical_pointwise_means}

{ref "logarithmic-prime-character-sums"}[素数和的对数平滑]引入了核 $`s^{-2}`。上式开方后，对整条临界线积分可得

$$`\int_{\mathbb R}
 \left(\sum_{\chi\bmod q,\,\chi\ne\chi_0}|L^{(j)}(1/2+it,\chi)|^2\right)^{1/2}
 \frac{dt}{|1/2+it|^2}
 \ll \sqrt{\varphi(q)}\,(1+\log q)^{j+1}\qquad(j=0,1).`

证明同时给出绝对可积性。把模数对数因子提出后，积分尾部由 $`(1+|t|)^{-5/4}` 控制。

{docstring AnalyticNumberTheory.AnalyticTools.critical_line_perron_integral_bound}

{docstring AnalyticNumberTheory.DirichletLFunctions.nonprincipal_critical_perron_means}

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

主项的误差还能省下一个对数因子。对所有 $`T\ge 2`，有一个与 $`T` 无关的常数，使得

$$`\int_0^T |\zeta(1/2+it)|^4\,dt
=\frac{T(\log T)^4}{2\pi^2}+O\big(T(\log T)^3\big).`

{docstring fourthMoment_riemannZeta_sharp_remainder}

在 $`[T,2T]` 上，把 $`\zeta(s)^2` 分解成长度 $`N=\lfloor T/(4\pi)\rfloor` 的除数多项式 $`P_N(s)`、它在函数方程下的反射项，以及余项 $`R(s)`。函数方程把含 $`R` 的两个混合项合并成 $`4\operatorname{Re}(R(s)P_N(1-s))`。将这个乘积的积分移至 $`\operatorname{Re}s=2`，连同矩形水平边一并估计，得到 $`O(T(1+\log T)^3)`。对二倍区间求和保留了同一阶的余项。

{docstring fourthMomentCrossTerm_integral_bound}

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

保留首修正项对平方积分的振荡贡献，可以进一步把余项压到 $`O(\sqrt T\log T)`。证明在截点 $`\lfloor\sqrt{t/(2\pi)}\rfloor` 不变的各段上积分，并用首修正系数的一致导数界控制振幅。

{docstring riemannZeta_critical_second_moment_sharp}

{docstring riemannZeta_critical_second_moment_sharp_remainder}

# Hurwitz ζ 的移位与第二主项
%%%
tag := "hurwitz-critical-second-term"
file := "hurwitz-critical-second-term"
%%%

固定实数 $`0<a\le1`。Hurwitz ζ 函数在临界线上的平方积分满足

$$`\int_1^T|\zeta(1/2+it,a)|^2\,dt
=T\log(T/(2\pi))+(\gamma-\psi(a)-1)T
+O_a\!\left(T^{3/4}\sqrt{\log(T+2)}\right).`

这里 $`\psi(a)=\Gamma'(a)/\Gamma(a)`。随高度移动的截断点产生两个对角和，其中移位调和和的常数项为 $`-\psi(a)`。异频项的振荡估计与近似函数方程的余项合在一起，给出上式的误差。取 $`a=1` 时，$`\psi(1)=-\gamma`，线性项与 Riemann ζ 的公式一致。

{docstring hurwitz_critical_diagonal_expansion}

{docstring hurwitz_critical_second_moment_expansion}

对固定模数，把临界线上所有 Dirichlet 特征的平方模相加。特征正交性将其化为既约剩余类对应的 Hurwitz 平方模之和。

{docstring AnalyticNumberTheory.DirichletLFunctions.character_family_critical_energy}

对高度积分后，这一全特征族的二阶矩中，$`T\log(T/(2\pi))` 的系数为 $`\varphi(q)^2/q`，线性项系数由既约剩余类上的移位常数给出。误差常数允许依赖固定模数。

{docstring AnalyticNumberTheory.DirichletLFunctions.character_family_critical_second_moment}

# 单个原始 Dirichlet 特征的二阶矩
%%%
tag := "primitive-critical-second-term"
file := "primitive-character-second-term"
%%%

设 $`\chi` 为模 $`q` 的原始特征，允许取非实值。在高度 $`t` 处，对称截断长度为 $`\lfloor\sqrt{qt/(2\pi)}\rfloor`。把有限和乘上导子与高度决定的相位后，可以用它和它的共轭控制临界线上 $`L` 函数的模，误差为 $`O_q(t^{-1/4})`。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_critical_polynomial_error}

二阶矩的首项为 $`(\varphi(q)/q)T\log(T/(2\pi))`。线性项系数由与 $`q` 互素的整数的调和和决定。对固定 $`q`，余项为 $`O_q(T^{3/4}\sqrt{\log(T+2)})`，因此该公式可以辨别每个原始特征的第二主项。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_critical_second_moment_expansion}

令 $`P(q)=\sum_{p\mid q}(\log p)/(p-1)`。提取密度因子以后，单个原始特征的线性项系数为 $`2\gamma-1+\log q+2P(q)`。全特征族求和再提取 $`\varphi(q)^2/q` 后，相应系数为 $`2\gamma-1+\log q+P(q)`。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_character_second_moment}

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_second_moment}

# 临界线附近的四阶矩与分离样本
%%%
tag := "near-critical-fourth-moments"
file := "near-critical-fourth-moments"
%%%

设 $`T\ge 2`。当 $`|\sigma-1/2|\le 1/(200\log T)` 时，黎曼 ζ 函数满足

$$`\int_0^T|\zeta(\sigma+it)|^4\,dt\ll T(\log T)^4.`

这个估计对窄带内的实部一致。证明将 $`\int_0^T\zeta(z+it)^2\zeta(z-it)^2\,dt` 视为 $`z` 的全纯函数。取实数 $`z=\sigma` 就得到四阶矩；在临界线上输入已有均值，在稍远的两条竖线上输入多项式增长界，再用矩形上的最大模原理插值。

{docstring fourthMoment_riemannZeta_narrow_strip}

在带宽减半后，可绕 $`\sigma+it` 作半径 $`1/(400\log T)` 的圆。Cauchy 导数积分给出的四次方损失为半径的负四次幂，从而有

$$`\int_0^T|\zeta'(\sigma+it)|^4\,dt\ll T(\log T)^8\qquad\left(|\sigma-1/2|\le\frac{1}{400\log T}\right).`

{docstring fourthMoment_deriv_riemannZeta_narrow_strip}

{index}[分离高度样本]设 $`\delta>0`，$`S\subset[-T,T]` 为有限集，每两个不同元素至少相距 $`\delta`。在各样本点附近取互不相交的区间，结合函数及其导数的四阶均值，可得

$$`\sum_{t\in S}|\zeta(1/2+it)|^4\ll (\delta^{-1}+\log T)T(\log T)^4.`

允许负高度、零和端点 $`\pm T`。常数对 $`\delta` 和 $`S` 一致；在同一条直线 $`|\sigma-1/2|\le 1/(800\log T)` 上也有相同的求和界。

{docstring fourthMoment_riemannZeta_separated}

{docstring fourthMoment_riemannZeta_separated_narrow_strip}

# 周期 L 函数和单个非原始特征的二阶矩
%%%
tag := "periodic-critical-second-term"
file := "periodic-critical-second-term"
%%%

设 $`q\ge 1`，$`\Phi` 为任意复值 $`q` 周期函数。令 $`A=q^{-1}\sum_{r=1}^q|\Phi(r)|^2`，$`\widehat\Phi` 为按 $`q^{-1/2}` 归一化的离散 Fourier 变换，并记

$$`H(\Phi)=-\frac1q\sum_{r=1}^q|\Phi(r)|^2\psi(r/q).`

临界线上的两个对角和分别带有 $`\Phi` 和 $`\widehat\Phi`。Parseval 恒等式使两者的均方系数同为 $`A`，它们的常数项则分别是 $`H(\Phi)` 和 $`H(\widehat\Phi)`。因此

$$`\int_1^T |L(1/2+it,\Phi)|^2\,dt
= A T\log\frac{T}{2\pi}
+\bigl[H(\Phi)+H(\widehat\Phi)-A(1+\log q)\bigr]T
+ O_{q,\Phi}\!\left(T^{3/4}\sqrt{\log(T+2)}\right).`

{docstring AnalyticNumberTheory.DirichletLFunctions.periodic_critical_second_moment}

对任意模 $`q` 的单个特征 $`\chi`，有 $`A=\varphi(q)/q`。对偶权 $`\widehat\chi(k)` 由频率 $`-k` 处的 Gauss 和除以 $`\sqrt q` 给出。将它代入 $`H` 就得到单个非原始特征的显式线性项。

{docstring AnalyticNumberTheory.DirichletLFunctions.individual_character_second_moment}

# 固定模数特征族的临界线第四矩
%%%
tag := "character-family-critical-fourth"
file := "character-family-critical-fourth"
%%%

{index}[Dirichlet 特征族的第四矩]设 $`q\ge1`、$`T\ge1`，记 $`J_T(F)=\int_{-T}^T |F(1/2+it)|^4\,dt`。对固定模数的原始特征求和，得到对模数和高度都一致的界

$$`\sum_{\chi\bmod q}^{*} J_T(L(\,\cdot\,,\chi))
 \ll \varphi(q)\,T\bigl(1+\log(qT)\bigr)^4.`

在每段高度上，平滑函数方程把问题归结为长度约 $`\sqrt{q(1+|t|)}` 的特征多项式及衰减的尾和。多项式平方的系数按乘积 $`mn` 合并，受除数函数控制。模 $`q` 的特征正交性把均方拆成同余类内的和，类内频率的间距使右端保留因子 $`\varphi(q)`。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_family_critical_fourth_moment}

设 $`\chi^*` 是诱导 $`\chi` 的原始特征，导子为 $`d`。对模 $`q` 的全部特征，$`\sum_\chi J_T(L(\,\cdot\,,\chi^*))` 和 $`\sum_\chi J_T(L(\,\cdot\,,\chi))` 都至多为 $`CqT(1+\log(qT))^4`。后一个估计要计入有限个 Euler 因子，因为

$$`L(s,\chi)=L(s,\chi^*)\prod_{p\mid q,\ p\nmid d}(1-\chi^*(p)p^{-s}).`

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_critical_fourth_moments}

当 $`\Re s\ge1/4` 时，各因子模的四次方至多为 $`(1+p^{-1/4})^4`。按导子分组后，即使把素数范围扩大到 $`p\mid q/d`，带权除数和仍有绝对上界

$$`\sum_{d\mid q}\varphi(d)\prod_{p\mid q/d}(1+p^{-1/4})^4\ll q.`

{docstring AnalyticNumberTheory.DirichletLFunctions.conductor_euler_fourth_weight_le}

对 $`1\le d\le Q` 的所有原始特征再求和，得到 $`Q^2T(1+\log(QT))^4` 阶的上界。积分区间仍为 $`[-T,T]`，可直接用于同时含有正、负虚部的均值估计。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_conductors_critical_fourth_moment}

# 固定模数特征族的近临界四阶矩
%%%
tag := "character-family-near-critical-fourth"
file := "character-family-near-critical-fourth"
%%%

{index}[Dirichlet 特征族的分离样本]设 $`q\ge1`、$`T\ge2`，记 $`L=\log(qT)`。在 $`|\sigma-1/2|\le 1/(200L)` 内，模 $`q` 的本原特征满足

$$`\sum_{\chi\bmod q}^{*}\int_{-T}^{T}|L(\sigma+it,\chi)|^4\,dt\ll\varphi(q)\,T L^4.`

这里的常数对模数、高度和带内的实部一致。解析插值作用在整个特征族的积分和上。对具有复系数的函数 $`f`，使用全纯对偶函数 $`z\mapsto\overline{f(\bar z)}`，即可在实参数 $`\sigma` 处恢复第四绝对矩。矩形上的二次指数权同时控制水平边，从而在 $`T` 小而 $`q` 大时仍能使用同一个带宽。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_family_fourth_narrow_symmetric}

将带宽缩为 $`1/(400L)`，在每个点使用 Cauchy 积分公式，得到

$$`\sum_{\chi\bmod q}^{*}\int_{-T}^{T}|L'(\sigma+it,\chi)|^4\,dt\ll\varphi(q)\,T L^8.`

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_family_deriv_fourth_narrow_symmetric}

对每个 $`\chi` 各取有限集 $`E_\chi\subset[-T,T]`，同一集合中两个不同元素相距至少 $`\delta>0`。不同特征的集合可以重叠。沿临界线的样本满足

$$`\sum_{\chi\bmod q}^{*}\ \sum_{t\in E_\chi}|L(1/2+it,\chi)|^4
 \ll(\delta^{-1}+L)\,\varphi(q)\,T L^4.`

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_family_fourth_separated}

对模 $`q` 的全部特征取和，上述三条界对实际的 $`L(s,\chi)` 及诱导它的本原函数 $`L(s,\chi^*)` 均成立，右端的 $`\varphi(q)` 换为 $`q`。另外，若把所有导子 $`d\le Q` 的本原特征合并，窄带 $`|\sigma-1/2|\le1/(200\log(QT))` 内的积分和至多为 $`C Q^2T\log^4(QT)`。

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_fourth_narrow_symmetric}

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_deriv_fourth_narrow_symmetric}

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_fourth_separated}

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_conductors_fourth_narrow_strip}

# 对移位、模数和高度一致的二阶矩
%%%
tag := "uniform-hurwitz-character-family-moment"
file := "uniform-hurwitz-character-family-moment"
%%%

固定 $`B\ge3`，记 $`T^*=\max(T,B)`、$`W(T)=\sqrt T\min(1,\sqrt T)`。对所有 $`0<a\le1` 和所有 $`T\ge0`，有

$$`\int_0^T|\zeta(1/2+it,a)|^2\,dt
=T\log\frac{T^*}{2\pi}+(\gamma-\psi(a)-1)T
+O_B\!\left(W(T)\bigl(a^{-1/2}+\log T^*\bigr)\right).`

这里 $`\psi(a)=\Gamma'(a)/\Gamma(a)`。当 $`a` 趋近零时，Dirichlet 级数的首项 $`a^{-1/2-it}` 的平方模为 $`1/a`。在任意固定高度区间 $`0\le T\le U` 上，先从积分中减去 $`T/a`，剩余量为 $`O_U(T(a^{-1/2}+1))`。由于 $`\psi(a)+1/a` 在 $`0<a\le1` 上有界，首项的贡献恰好与线性项中的奇性相抵消。这给出 $`T\le1` 时的误差因子 $`W(T)=T`。高处的估计使用临界线上平方模与对角调和和之差的积分。

{docstring hurwitz_critical_initial_moment}

{docstring hurwitz_critical_diagonal_uniform}

{docstring hurwitz_second_moment_uniform}

对模 $`q\ge1` 的全部 Dirichlet 特征取平均，包括由较小导子诱导的特征。令 $`P(q)=\sum_{p\mid q}(\log p)/(p-1)`，可得

$$`\frac1{\varphi(q)}\sum_{\chi\bmod q}\int_0^T|L(1/2+it,\chi)|^2\,dt
=\frac{\varphi(q)}q\left[T\log\frac{qT^*}{2\pi}+(2\gamma-1+P(q))T\right]
+O_B\!\left(\frac{\varphi(q)}q W(T)\log T^*\right).`

由{ref "hurwitz-critical-second-term"}[特征正交性]，左边等于 $`q^{-1}` 乘以既约剩余类 $`h` 上的 Hurwitz 二阶矩之和。取 $`a=h/q` 后，移位误差的求和由 $`\sum_{1\le h\le q,\,(h,q)=1}\sqrt{q/h}\le20\varphi(q)` 控制。因此同一个误差常数适用于所有模数。

{docstring AnalyticNumberTheory.AnalyticTools.reduced_sqrt_ratio_sum_le}

{docstring AnalyticNumberTheory.DirichletLFunctions.full_character_second_moment_uniform}

# Perron 积分中的加权四阶矩
%%%
tag := "perron-weighted-fourth-moments"
file := "perron-weighted-fourth-moments"
%%%

{index}[Perron 权下的四阶矩]在平均分布定理的复积分证法中，Perron 核给高度积分附上 $`1/|s|` 的权。沿 $`s=1/2+it` 积分，并对 $`q\le Q` 的本原特征求和，有

$$`\sum_{q\le Q}\frac1{\varphi(q)}\sum_{\chi\bmod q}^{*}
\int_{-T}^T \frac{|L(1/2+it,\chi)|^4}{|1/2+it|}\,dt
\ll Q\,\log^5(QT),\qquad Q\ge1,\quad T\ge2.`

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_perron_fourth_moment}

固定 $`q` 时，普通四阶矩在 $`[-u,u]` 上的上界含因子 $`\varphi(q)u`。在 $`u\le |t|\le 2u` 上，分母至少为 $`u`。每个这样的高度区间便贡献同阶的上界，相加损失一个对数因子。对 $`|t|\le1` 则用 $`|1/2+it|\ge1/2`。把 $`L` 换成 $`L'` 后，同样的计算给出 $`Q\log^9(QT)`。

{docstring AnalyticNumberTheory.DirichletLFunctions.primitive_perron_deriv_fourth_moment}
