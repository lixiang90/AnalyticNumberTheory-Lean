import AnalyticNumberTheory.PrimeDistribution.PrimeCountingError
import AnalyticNumberTheory.PrimeDistribution.RiemannPrimePowerFormula
import AnalyticNumberTheory.PrimeDistribution.ShiftedZeroFormula
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingNormalization
import AnalyticNumberTheory.PrimeDistribution.RiemannPolarNormalization
import AnalyticNumberTheory.PrimeDistribution.RiemannEiZeroSum
import AnalyticNumberTheory.PrimeDistribution.RiemannExponentialIntegral
import AnalyticNumberTheory.PrimeDistribution.PrimeCountingExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingSharp
import AnalyticNumberTheory.PrimeDistribution.SharpExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.FullPerronContour
import AnalyticNumberTheory.PrimeDistribution.TrivialZeroTerm
import AnalyticNumberTheory.PrimeDistribution.SymmetricExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.IntegratedExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingZeroSum
import AnalyticNumberTheory.PrimeDistribution.RiemannCountingMellin
import AnalyticNumberTheory.PrimeDistribution.RiemannPrimeCounting
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.PrimeDistribution.LeastPrime
import AnalyticNumberTheory.PrimeDistribution.LeastPrimeSubexponential
import AnalyticNumberTheory.PrimeDistribution.ReciprocalTotient
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "Chebyshev 函数与素数定理" =>
%%%
tag := "prime-counting"
file := "prime-counting"
%%%

{index}[素数定理]von Mangoldt 函数在 $`n=p^m`（$`m\ge1`）处取 $`\log p`，其余处为零。它的部分和 $`\psi(x)` 把每个素数幂按其底数计权。de la Vallée Poussin 型估计给出正数 $`C,c`，使得在 $`x\ge2` 时

$$`|\psi(x)-x|\le Cx\exp(-c\sqrt{\log x}).`

{docstring abs_psi_sub_id_le_exp}

除去高次素数幂并作分部求和，可以恢复普通素数计数 $`\pi(x)`。本库采用从 $`2` 起算的对数积分 $`\int_2^x dt/\log t`。下面的存在量词允许误差常数改变。

{docstring abs_primePi_sub_logIntegral_le_exp}

{index}[等差数列中的最小素数]在模 $`q` 的互素剩余类 $`a` 内，$`\theta(x;q,a)` 是一个有限和，每项都是正的素数对数。因此它首次取正值的阈值，恰好是这一类的最小素数。若从 $`\psi(x;q,a)` 出发，还须扣除高次素数幂可能贡献的部分。

{docstring leastPrimeAP_le_iff_thetaAP_pos}

{docstring leastPrimeAP_le_of_psiAP}

对任意固定的 $`ε>0`，把{ref "primes-in-progressions"}[Siegel–Walfisz 定理]中的截点取作 $`x=\exp(Cq^ε)`，可以使主项压过误差。取充分大的常数 $`C`，此结论对每个正模数和每个简化剩余类都成立。

{docstring leastPrimeAP_le_exp_rpow}

# 欧拉函数的倒数与 Mertens 乘积
%%%
tag := "reciprocal-totient"
file := "reciprocal-totient"
%%%

{index}[欧拉函数]对每个正整数 $`n`，欧拉乘积表明 $`n/\varphi(n)` 的大小只由 $`n` 的不同素因子决定。每个素因子至少是 $`2`，所以它们的个数 $`\omega(n)` 满足 $`\omega(n)\log 2\le\log n`。

{docstring div_totient_eq_reciprocal_product}

{docstring primeFactors_card_mul_log_two_le}

任取 $`y\ge2`。在 $`p\le y` 的部分，补入所有遗漏的素数只会增大乘积。Mertens 第三定理的对数误差式给出 $`\prod_{p\le y}(1-1/p)^{-1}\ll\log y`，常数从 $`y=2` 起一致。

{docstring reciprocal_mertens_product_le}

在 $`p>y` 的部分，每个因子等于 $`1+1/(p-1)\le\exp(2/y)`。由此得到

$$`\frac{n}{\varphi(n)}\le
\prod_{p\le y}(1-1/p)^{-1}
\exp\!\left(\frac{2\log n}{y\log 2}\right).`

{docstring reciprocal_totient_large_primes_le}

{docstring div_totient_le_mertens_mul_exp}

取 $`y=\log(10n)`，大素因子的总贡献便被绝对常数控制。于是对包括 $`n=1` 在内的所有正整数都有 $`n/\varphi(n)\ll\log\log(10n)`。这一估计直接用于{ref "smoothed-rational-prime-bound"}[有理频率的 Gauss 系数]。

{docstring div_totient_le_loglog}

# Riemann 素数幂计数与 Möbius 反演
%%%
tag := "riemann-prime-counting"
file := "riemann-prime-counting"
%%%

{index}[Riemann 素数幂计数函数]令 $`J(x)=\sum_{1<n\le x}\Lambda(n)/\log n`。素数 $`p` 的贡献为 $`1`，平方 $`p^2` 的贡献为 $`1/2`，一般的 $`p^k` 贡献 $`1/k`。按指数重新求和，得到

$$`J(x)=\sum_{1\le k\le L}\frac{\pi(x^{1/k})}{k},\qquad L=\lfloor\log x/\log 2\rfloor.`

{docstring riemannPrimeCounting}

{docstring riemannPrimeCounting_eq_sum_primePi}

对于 $`x\ge2`，Möbius 反演恢复通常的素数计数：

$$`\pi(x)=\sum_{1\le d\le L}\frac{\mu(d)}d\,J(x^{1/d}).`

展开右边后，指数乘积 $`m=dj` 的系数为 $`m^{-1}\sum_{d\mid m}\mu(d)`。除了 $`m=1`，所有系数都为零。有限倍数和形式的同一个反演对任意环值函数成立。

{docstring primePi_eq_sum_moebius_riemannPrimeCounting}

{docstring AnalyticNumberTheory.AnalyticTools.Summation.sum_moebius_mul_sum_multiples}

在跳跃点取左右极限的平均值，就得到 $`J_0` 和 $`\pi_0`。例如在 $`x=8`，普通计数给出 $`J(8)=4+1/2+1/3=29/6`，而半权计数给出 $`J_0(8)=4+1/2+1/6=14/3`。用 $`J_0` 反演时，三次根恰好是素数 $`2`，所以 $`J_0(2)=1/2`。由此 $`\pi_0(8)=14/3-1/2-1/6=4`。

{docstring riemannPrimeCounting_half_succ}

{docstring primePiWithEndpoint_half_succ}

在 Lean 中，参数 $`c` 指定截点处的权重。取 $`c=0,1/2,1` 分别得到严格计数、半权计数与包含端点的计数。两道反演公式只需要把原数与各次根的截点权重取成同一个 $`c`。

{docstring riemannPrimeCounting_eq_sum_primePiWithEndpoint}

{docstring primePiWithEndpoint_eq_sum_moebius_riemannPrimeCounting}

# 素数幂计数与 zeta 对数的 Mellin 变换
%%%
tag := "riemann-counting-mellin"
file := "riemann-counting-mellin"
%%%

{index}[素数幂计数的 Mellin 变换]在 $`\Re s>1` 内，取由 Euler 乘积确定的解析对数 $`\log\zeta(s)`。它的 Dirichlet 系数是 $`\Lambda(n)/\log n`。对系数求部分和便是{ref "riemann-prime-counting"}[Riemann 的素数幂计数] $`J`，从而

$$`\log\zeta(s)=s\int_1^\infty J(t)\,t^{-s-1}\,dt.`

{docstring logZeta_eq_mellin_riemannPrimeCounting}

反过来，任取 $`c>1`，将 $`\log\zeta(s)x^s/s` 沿 $`\Re s=c` 对称截断。{ref "sharp-perron-partial-sums"}[Perron 反演]给出

$$`J_0(x)=\lim_{T\to\infty}\frac{1}{2\pi}\int_{-T}^{T}
       \log\zeta(c+it)\frac{x^{c+it}}{c+it}\,dt \qquad (x>0).`

在 $`x=p^k` 处，最后一项贡献 $`1/(2k)`。例如 $`x=8` 时，不论把积分线放在 $`c=2` 还是 $`c=3`，都恢复 $`14/3`。对固定的 $`x,c`，截断高度为 $`T` 的误差至多是 $`C(x,c)/T`。

{docstring tendsto_logZetaPerronIntegral_riemannPrimeCounting}

{docstring norm_logZetaPerronIntegral_sub_riemannPrimeCounting_le}

# 用有限零点和计算区间内的素数幂质量
%%%
tag := "riemann-counting-zero-sum"
file := "riemann-counting-zero-sum"
%%%

{index}[素数幂计数的截断显式公式]区间 $`(a,b]` 内的素数幂质量为 $`J(b)-J(a)`。固定高度 $`T`，对每个指数 $`\rho` 记

$$`L_\rho(a,b)=\int_a^b \frac{t^{\rho-1}}{\log t}\,dt.`

当 $`a>1` 时，积分沿实轴正向进行。$`L_1(a,b)` 是普通的对数积分差。对于非平凡零点，$`L_\rho` 直接给出该零点在两个端点间的贡献。

{docstring zeroLogIntegral}

{docstring zeroLogIntegral_one}

对所有 $`2\le T\le a\le b`，存在同一个绝对常数使

$$`J(b)-J(a)=L_1(a,b)-\sum_{|\Im\rho|\le T}m_\rho L_\rho(a,b)
+O\,\left(\frac{b\log^2 b/T+\log b}{\log a}\right).`

和遍及临界带内不同的非平凡零点，$`m_\rho` 是解析重数。如果 $`b\le 2a`，分母消去一个对数因子，误差成为 $`O(b\log b/T+1)`。例如在 $`(a,2a]` 内取 $`T=a`，误差为 $`O(\log a)`。

{docstring riemannPrimeCounting_interval_zero_formula}

{docstring riemannPrimeCounting_dyadic_zero_formula}

证明对 Chebyshev 函数的截断显式公式作分部求和，权重取 $`w(t)=1/\log t`。若离散部分和与光滑函数 $`F` 的差在 $`[a,b]` 上至多为 $`M`，单调权把区间加权和同 $`\int_a^b w(t)F'(t)\,dt` 的差控制在 $`2Mw(a)` 以内。这个估计也覆盖恰好落在端点的素数幂。

{docstring AnalyticNumberTheory.AnalyticTools.Summation.norm_weighted_sum_sub_integral_of_partial_sums}

# Chebyshev 函数的一次积分与全部零点
%%%
tag := "integrated-explicit-formula"
file := "integrated-explicit-formula"
%%%

{index}[Chebyshev 函数的积分显式公式]把 $`\Psi_1(x)=\int_1^x\psi(t)\,dt/t` 写成有限和，每个 $`n\le x` 的权重为 $`\log(x/n)`。例如 $`x=4` 时，$`n=4` 的权重恰为零，
$`\Psi_1(4)=(\log 2)^2+\log 3\log(4/3)`。

{docstring logWeightedSum_vonMangoldt_eq_integral_psi}

对每个 $`x\ge1` 有精确等式

$$`\Psi_1(x)=x-1-\log(2\pi)\log x
-\sum_\rho\frac{x^\rho-1}{\rho^2}
-\sum_{m=1}^\infty\frac{x^{-2m}-1}{4m^2}.`

第一组和遍及临界带内所有非平凡零点，按解析重数计数。对固定的 $`x`，分子 $`|x^\rho-1|\le x+1`，而 $`\sum_\rho|\rho|^{-2}<\infty`。第二组和遍及负偶整数，也绝对收敛。取 $`x=1` 时，两个级数的每一项和等式的两边都是零。

{docstring exists_integrated_explicit_formula_psi}

为得到这个公式，先将{ref "centered-zeta-partial-fractions"}[以原点为基点的部分分式]除以 $`s^2`。在对数坐标 $`u=\log x\ge0` 下，极点 $`\omega` 对应的逆变换是 $`(e^{\omega u}-1)/\omega^2`。这个核对整个零点族给出可逐项积分的共同上界。

{docstring AnalyticNumberTheory.AnalyticTools.integratedPole}

{docstring AnalyticNumberTheory.AnalyticTools.summable_integratedPole}

{docstring AnalyticNumberTheory.AnalyticTools.laplaceTransform_tsum_integratedPole}

极点 $`1` 给出 $`x-1`，常数 $`-\log(2\pi)` 给出线性项 $`-\log(2\pi)\log x`。在 $`\Re s>1` 上求和后作 Bromwich 反演，得到同一个有限 von Mangoldt 加权和。

{docstring exists_laplaceTransform_integratedZetaZeroSum}

{docstring exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum}

# 半权 Chebyshev 函数的对称差分公式
%%%
tag := "symmetric-explicit-formula"
file := "symmetric-explicit-formula"
%%%

{index}[Chebyshev 函数的对称差分]写 $`u=\log x`，在跳跃点把 $`\psi` 的左右极限平均，记为 $`\psi_0`。例如 $`\psi_0(8)=\psi(7)+(\log 2)/2`。在对数坐标中，每个算术系数 $`a_n` 对一次对数平均的贡献为 $`a_n\max(u-\log n,0)`。对称取 $`u-h,u+h` 两点作差再除以 $`2h`，恰好经过折点的那一项给出 $`a_n/2`。

{docstring midpointPsi}

{docstring midpointPsi_nat_succ}

{docstring AnalyticNumberTheory.DirichletSeries.eventually_symmetric_logWeightedSum}

对 $`x>1`，固定 $`x` 后取充分小的 $`h>0`，使 $`(xe^{-h},xe^h)` 内只能含有等于 $`x` 的整数。将{ref "integrated-explicit-formula"}[一次积分显式公式]在两端相减，立刻得到精确等式

$$`\psi_0(x)=K_h(1,x)-\log(2\pi)-\sum_\rho K_h(\rho,x)
-\sum_{m\ge1}K_h(-2m,x),\qquad
K_h(\omega,x)=\frac{x^\omega\sinh(\omega h)}{h\omega^2}.`

{docstring AnalyticNumberTheory.AnalyticTools.symmetricPole}

{docstring exists_symmetric_explicit_formula_midpointPsi}

每个这样的宽度都给出同一个半权值。固定 $`h` 时，两组级数分别绝对收敛，因而可以把取差运算移入级数。$`h` 趋于零时，单个核趋向 $`x^\omega/\omega`；此时非平凡零点的求和还需要指定取极限的方式。

{docstring summable_symmetric_nontrivial}

{docstring summable_symmetric_trivial}

# 平凡零点求和与对称极限
%%%
tag := "trivial-zero-term"
file := "trivial-zero-term"
%%%

{index}[平凡零点的对数项]在 $`x>1` 时，负偶整数对显式公式的贡献可以直接求和。令 $`u=\log x`，在单位圆内的对数幂级数给出

$$`\sum_{m\ge1}\frac{x^{-2m}}{-2m}
=\tfrac12\log(1-x^{-2}).`

右边为负数。由于每个零点在 $`-\zeta'/\zeta` 中的符号为负，平凡零点对 $`\psi_0(x)` 的总贡献为 $`-\tfrac12\log(1-x^{-2})`。

{docstring hasSum_exp_trivialZetaZero_div}

对{ref "integrated-explicit-formula"}[一次积分公式]中负偶整数的级数，可以在任一 $`u>0` 处逐项求导。在 $`v>u/2` 上，各导数的模都被可求和的等比级数 $`e^{-mu}` 控制。于是{ref "symmetric-explicit-formula"}[对称差分]中平凡零点的级数也有同一个极限。

{docstring hasDerivAt_tsum_integrated_trivialZetaZero}

{docstring tendsto_tsum_symmetric_trivialZetaZero}

对非平凡零点，先固定 $`h>0` 求和，再令 $`h\downarrow0`，所得极限为

$$`\lim_{h\downarrow0}\sum_\rho
 \frac{x^\rho\sinh(\rho h)}{h\rho^2}
=x-\log(2\pi)-\tfrac12\log(1-x^{-2})-\psi_0(x).`

例如 $`x=2` 时，右边的最后一项为 $`-(\log 2)/2`。这个极限指定了宽度 $`h` 与无穷求和的次序。

{docstring AnalyticNumberTheory.AnalyticTools.tendsto_symmetricPole}

{docstring exists_tendsto_symmetric_nontrivial_midpointPsi}

# 完整 Perron 矩形中的极点和零点
%%%
tag := "full-zeta-perron-contour"
file := "full-zeta-perron-contour"
%%%

{index}[ζ 函数的完整 Perron 矩形]取 $`x>0`，沿左右边界为 $`-2N-1` 和 $`2`、上下边界为 $`\pm T` 的矩形正向积分。假定 $`T>0` 与非平凡零点的纵坐标绝对值都不相等。矩形内有极点 $`1`、原点、前 $`N` 个负偶整数，以及 $`|\Im\rho|\le T` 的所有非平凡零点。

{docstring zetaRectangleZeros}

{docstring mem_zetaRectangleZeros_iff}

对 $`F_x(s)=-(\zeta'/\zeta)(s)x^s/s` 应用{ref "rectangular-simple-residues"}[矩形留数定理]，得

$$`\frac1{2\pi i}\int_{\partial R}F_x(s)\,ds=x-\log(2\pi)
-\sum_{|\Im\rho|\le T}m_\rho\frac{x^\rho}{\rho}
-\sum_{m=1}^N\frac{x^{-2m}}{-2m}.`

{docstring rectangleBoundary_zetaPerron}

第一项来自 $`s=1`，第二项来自 Perron 核在 $`s=0` 的极点。非平凡零点按解析重数计数，负偶整数都是单零点。例如把左边界从 $`-3` 移到 $`-5` 时，新收入的零点是 $`-4`，归一化围道积分因它增加 $`x^{-4}/4`。这个有限等式允许独立选择 $`x,T,N`。

{docstring zetaPerron_principalPart_one}

{docstring zetaPerron_principalPart_zero}

{docstring zetaPerron_principalPart_at_zero}

{docstring zeroMultiplicity_trivialZetaZero}

# 按零点高度截断的 Chebyshev 显式公式
%%%
tag := "sharp-chebyshev-explicit-formula"
file := "sharp-chebyshev-explicit-formula"
%%%

{index}[von Mangoldt 显式公式]给定 $`x>1`，记 $`\psi_0(x)` 为在素数幂处取左右极限平均的 Chebyshev 函数。将非平凡零点按 $`|\Im\rho|\le T` 截断，每个不同的零点乘以它的解析重数 $`m_\rho`。对任意趋于无穷的实高度，von Mangoldt 显式公式给出

$$`\psi_0(x)=x-\lim_{T\to\infty}\sum_{|\Im\rho|\le T}
 m_\rho\frac{x^\rho}{\rho}-\log(2\pi)-\tfrac12\log(1-x^{-2}).`

{docstring sharpZetaZeroSum}

{docstring tendsto_explicit_formula_midpointPsi}

若 $`x` 不是素数幂，就可以把左端写成通常的 $`\psi(x)`。例如从 $`7` 到 $`8` 时，$`\psi` 增加 $`\log 2`，故在 $`x=8` 处级数给出 $`\psi(7)+(\log 2)/2`。

{docstring midpointPsi_eq_psi_of_not_primePower}

从{ref "full-zeta-perron-contour"}[有限矩形的留数等式]出发，令左边界取负奇整数 $`-2\lceil R\rceil-1`，再于 $`(R^2,R^2+1)` 中选一个避开零点的高度 $`U`。当 $`R\to\infty` 时，上、下两条水平边和左边的积分均趋于零。右边的积分由 Perron 反演给出半权值，负偶整数的贡献由{ref "trivial-zero-term"}[对数幂级数]求和。

{docstring exists_expandingPerron_heights}

{docstring exists_tendsto_zetaPerron_edges}

最后令 $`R=\sqrt T`。把截断从 $`T` 移到 $`U`，最多增加一个单位高度带内的零点；对 $`T\ge 2`，它们的总贡献至多为 $`Cx\log T/T`。这一步也处理了 $`T` 恰好等于某个零点纵坐标绝对值的情形。

{docstring sharpZetaZeroSum_unit_variation}

{docstring hasSum_cpow_trivialZetaZero_div}

{docstring tendsto_sharpZetaZeroSum_midpointPsi}

# 素数幂计数的区间显式公式
%%%
tag := "sharp-prime-power-interval"
file := "sharp-prime-power-interval"
%%%

{index}[Riemann 素数幂计数的区间公式]给定 $`1<a\le b`，$`J_0(b)-J_0(a)` 把开区间中的 $`p^k` 计为 $`1/k`，把两个不同端点上的素数幂各计为 $`1/(2k)`。例如 $`(4,8)` 内只有素数幂 $`5,7`，两端还有 $`2^2,2^3`，所以 $`J_0(8)-J_0(4)=2+\tfrac14+\tfrac16=\tfrac{29}{12}`。

记 $`L_\rho(a,b)=\int_a^b t^{\rho-1}\,dt/\log t`。将非平凡零点按纵坐标绝对值截断，并保留解析重数，有

$$`J_0(b)-J_0(a)=\int_a^b\frac{dt}{\log t}
-\lim_{T\to\infty}\sum_{|\Im\rho|\le T}m_\rho L_\rho(a,b)
-\int_a^b\frac{dt}{t(t^2-1)\log t}.`

{docstring sharpZeroLogIntegral}

{docstring trivialZeroLogIntegral}

{docstring tendsto_riemannPrimeCounting_interval_explicit_formula}

在 $`[a,b]` 上对{ref "sharp-chebyshev-explicit-formula"}[Chebyshev 显式公式]作带权分部积分，权函数取 $`w(t)=1/\log t`。边界项用 $`\psi_0(a),\psi_0(b)`。积分中的 $`\psi_0` 与通常的 $`\psi` 几乎处处相等，所以两者给出同一个积分。

{docstring riemannPrimeCounting_midpoint_abel}

极限移入积分需要对 $`t` 和高度的联合控制。对 $`a\le t\le b`，Perron 核的一致界先控制右边的围道积分，再由另外三条边的估计控制整个零点部分和。这样即使区间含有跳跃点，仍可以使用支配收敛定理。

{docstring eventually_norm_sharpZetaZeroSum_le_on_Icc}

{docstring AnalyticNumberTheory.DirichletSeries.norm_dirichletContourIntegral_le}

{docstring AnalyticNumberTheory.AnalyticTools.Summation.tendsto_weighted_derivatives_of_bounded_primitives}

最后一项来自平凡零点。对 $`\tfrac12\log(1-t^{-2})` 求导，得到正密度 $`1/[t(t^2-1)]`；它在计数公式中带负号。

{docstring hasDerivAt_trivialZeroLog}

# 用零点计算单点素数幂计数与素数计数
%%%
tag := "prime-counting-explicit-formula"
file := "prime-counting-explicit-formula"
%%%

{index}[素数计数函数的显式公式]在 $`1<a<2` 中任选一个基点，例如 $`a=3/2`。因为第一个素数幂是 $`2`，所以 $`J_0(a)=0`。将{ref "sharp-prime-power-interval"}[区间显式公式]右边截到高度 $`T`，记为 $`E_T(a,x)`。改变积分方向时三个贡献同时变号，因此无论 $`x` 在基点的哪一侧，只要 $`x>1`，都有 $`J_0(x)=\lim_{T\to\infty}E_T(a,x)`。

{docstring riemannExplicitIncrement}

{docstring riemannExplicitIncrement_swap}

{docstring tendsto_riemannExplicitIncrement_midpoint}

再用有限 Möbius 反演。取正整数 $`N\ge\lfloor\log x/\log 2\rfloor`，在所有根 $`x^{1/d}` 处使用同一个高度，则

$$`\pi_0(x)=\lim_{T\to\infty}\sum_{d=1}^{N}\frac{\mu(d)}{d}\,E_T(a,x^{1/d}).`

{docstring tendsto_primePi_midpoint_explicit_formula}

例如 $`x=8` 时，$`J_0(8)=14/3`、$`J_0(\sqrt 8)=1`、$`J_0(2)=1/2`，反演给出 $`\pi_0(8)=14/3-1/2-1/6=4`。普通的素数计数 $`\pi(x)` 在素数端点比 $`\pi_0(x)` 多半项。高次素数幂处，$`J_0` 的端点修正已经在反演中抵消。

{docstring primePi_eq_midpoint_add_endpoint}

{docstring tendsto_primePi_explicit_formula}

# 指数积分与 Riemann 的零点项
%%%
tag := "riemann-exponential-integral"
file := "riemann-exponential-integral"
%%%

{index}[指数积分与非平凡零点]在正实轴上，指数积分的归一化为
$$`\operatorname{Ei}(z)=\gamma+\log z+\sum_{n=1}^{\infty}\frac{z^n}{n\,n!}.`
使用复对数的主支就将它延拓到沿非正实轴割开的复平面。幂级数部分处处绝对收敛，逐项微分给出 $`\operatorname{Ei}'(z)=e^z/z`。[NIST DLMF 的正实轴公式](https://dlmf.nist.gov/6.6.E1)

{docstring AnalyticNumberTheory.AnalyticTools.principalExponentialIntegral}

{docstring AnalyticNumberTheory.AnalyticTools.summable_exponentialIntegralRemainder}

{docstring AnalyticNumberTheory.AnalyticTools.hasDerivAt_principalExponentialIntegral}

对 $`\Re\rho>0` 与 $`t>1`，点 $`\rho\log t` 始终在开右半平面内。链式法则给出 $`\frac{d}{dt}\operatorname{Ei}(\rho\log t)=t^{\rho-1}/\log t`，于是
$$`L_\rho(a,b)=\operatorname{Ei}(\rho\log b)-\operatorname{Ei}(\rho\log a).`
当 $`\rho=1` 时，它给出通常的对数积分差；对于 ζ 的每个非平凡零点，同一条等式给出相应的零点项。

{docstring hasDerivAt_exponentialIntegral_log}

{docstring zeroLogIntegral_eq_exponentialIntegral_sub}

记 $`S_T(x)=\sum_{|\Im\rho|\le T}m_\rho\operatorname{Ei}(\rho\log x)`。取 $`1<a<2` 为基点，在同一个高度 $`T` 计算 $`S_T(x)-S_T(a)` 后再取极限。这给出{ref "prime-counting-explicit-formula"}[单点计数公式]的指数积分写法。
$$`J_0(x)=\operatorname{Ei}(\log x)-\operatorname{Ei}(\log a)
-\lim_{T\to\infty}(S_T(x)-S_T(a))
-\int_a^x\frac{dt}{t(t^2-1)\log t}.`

{docstring sharpZetaEiSum}

{docstring sharpZeroLogIntegral_eq_EiSum_sub}

{docstring tendsto_exponentialIntegral_zero_formula}

# 单个端点的 Ei 零点和
%%%
tag := "individual-ei-zero-sum"
file := "individual-ei-zero-sum"
%%%

{index}[按高度收敛的 Ei 零点和]固定 $`x>1`，再让高度趋于正无穷，单个端点的和
$$`S(x)=\lim_{T\to\infty}\sum_{|\Im\rho|\le T}m_\rho\operatorname{Ei}(\rho\log x)`
存在。于是{ref "riemann-exponential-integral"}[基点归一化的 Riemann 公式]中可以分别求出 $`S(x)` 和 $`S(a)`，再作差。

{docstring riemannEiZeroSum}

{docstring tendsto_sharpZetaEiSum}

{docstring riemannPrimeCounting_eq_Ei_sub_zeroSum}

在每个有限高度，零点 $`\rho,\overline{\rho}` 的解析重数相同。它们在{ref "exponential-integral-phase"}[指数积分的渐近式]中的相位恰好抵消。剩下的首项之和，是{ref "sharp-chebyshev-explicit-formula"}[Chebyshev 零点和]除以 $`\log x`。

{docstring sum_zeroMultiplicity_eq_zero_of_conj_odd}

{docstring sharpZetaEiSum_eq_leading_add_remainder}

单个余项的模至多为 $`x/((\log x)^2(\Im\rho)^2)`。单位高度带的零点计数估计保证这些余项按解析重数绝对可和，这就把单端点的收敛问题归结为已知的 Chebyshev 公式。

{docstring norm_riemannEiZeroRemainder_le}

{docstring summable_riemannEiZeroRemainder}

{docstring tendsto_sum_nontrivialZerosUpTo_of_summable}

# 平凡零点的尾积分与归一化常数
%%%
tag := "riemann-counting-normalization"
file := "riemann-counting-normalization"
%%%

{index}[Riemann 公式的归一化]记 $`S(x)` 为{ref "individual-ei-zero-sum"}[按高度收敛的零点和]。把平凡零点的贡献从 $`x` 积到无穷远，得到
$$`B(x)=\int_x^\infty\frac{dt}{t(t^2-1)\log t},\qquad
0\le B(x)\le\frac{1}{x(x-1)\log x}.`
由于 $`B(a)-B(x)` 恰好等于区间 $`[a,x]` 上的积分，原先依赖两个端点的计数公式可以写成
$$`J_0(x)=\operatorname{Ei}(\log x)-S(x)+B(x)+C \qquad (x>1).`
取 $`a=3/2`，此时还没有素数幂，故 $`C=S(a)-\operatorname{Ei}(\log a)-B(a)`。这个常数对所有 $`x` 相同，素数幂端点仍然取半权。

{docstring riemannTrivialZeroTail}

{docstring integrableOn_riemannTrivialZeroTail}

{docstring riemannTrivialZeroTail_bounds}

{docstring tendsto_riemannTrivialZeroTail_atTop}

{docstring trivialZeroLogIntegral_eq_tail_sub}

{docstring riemannCountingConstant}

{docstring riemannPrimeCounting_eq_Ei_zeroSum_tail_constant}

令 $`u>0`。沿实变量 $`y` 平移时，极点项和 ζ 的对数导数各自在 $`y=1` 发散，两者的差却有可去奇点。设 $`P(z)=\sum_{n\ge1}z^n/(n\,n!)`，将 $`\zeta_1(y)=(y-1)\zeta(y)` 连续延拓至 $`1`，则 $`-P((1-y)u)-\log\zeta_1(y)` 是这个差的原函数。由 $`\zeta_1(0)=1/2`、$`\zeta(y)\to1` 和{ref "eone-euler-normalization"}[实指数积分的衰减]，得到
$$`\lim_{R\to\infty}\int_0^R
\left(\frac{e^{(1-y)u}}{1-y}-\frac{\zeta'(y)}{\zeta(y)}\right)dy
=\operatorname{Ei}(u)-\log 2.`

{docstring riemannZeta₁_zero_eq_half}

{docstring riemannZeta₁_re_pos_of_nonneg}

{docstring tendsto_riemannZeta_ofReal_atTop}

{docstring tendsto_integral_riemannPolar_sub_logDeriv}

# 第一个素数之前的平移公式
%%%
tag := "real-shift-before-first-prime"
file := "real-shift-before-first-prime"
%%%

{index}[显式公式的实平移]在区间 $`1<x<2` 内，各个素数幂的 von Mangoldt 权重和为零。这使我们可以在这一段上比较不同实平移的留数。记 $`u=\log x`，设 $`y>0` 且 $`y\ne1`。单个极点 $`\omega` 的平移留数可拆为
$$`A_y(\omega)=\frac{e^{(\omega-y)u}}{\omega-y}
=e^{-yu}\frac{e^{\omega u}}{\omega}
 + K_y(\omega),\qquad
K_y(\omega)=\frac{y e^{(\omega-y)u}}{\omega(\omega-y)}.`
这里对同一族零点只需处理一次按高度求和的首项。修正项 $`K_y` 多出一个分母，因而可以按绝对收敛级数处理。

{docstring AnalyticNumberTheory.AnalyticTools.shiftedPoleResidue_eq_damped_add}

{docstring AnalyticNumberTheory.AnalyticTools.hasSum_shiftedPoleCorrection}

具体地，设 $`L(x)=\lim_{T\to\infty}\sum_{|\Im\rho|\le T}m_\rho x^\rho/\rho`。把平移后的留数按非平凡零点 $`\rho` 和平凡零点 $`-2m` 求和，得到
$$`A_y(1)-\frac{\zeta'(y)}{\zeta(y)}
=e^{-yu}L(x)+\sum_\rho m_\rho K_y(\rho)+\sum_{m=1}^{\infty}A_y(-2m).`
这把{ref "riemann-counting-normalization"}[极点与对数导数的积分]同两族零点联系起来。

{docstring sharpZetaZeroSumLimit}

{docstring sharpZetaZeroSumLimit_eq}

{docstring shifted_explicit_formula_of_lt_two}

推导时先对{ref "integrated-explicit-formula"}[一次积分的显式公式]作分部积分。对满足 $`F(0)=0` 的原函数，所得表达式为 $`y e^{-yu}F(u)+y^2\int_0^u e^{-yt}F(t)\,dt`。在首个素数之前，算术端的 $`F` 恒为零。零点端可以逐项平移，且把同一个零点的不同出现合并后，权重就是该点的解析重数。

{docstring AnalyticNumberTheory.AnalyticTools.hasSum_exponentialShiftOfPrimitive_integratedPole}

{docstring AnalyticNumberTheory.RiemannZeta.ZetaZeroEnumeration.hasSum_distinct}

{docstring integratedZetaZeroSum_eq_logWeightedSum}

{docstring AnalyticNumberTheory.RiemannZeta.neg_logDeriv_riemannZeta_eq_distinct_centered}

# Riemann 的素数幂显式公式
%%%
tag := "riemann-prime-power-formula"
file := "riemann-prime-power-formula"
%%%

{index}[Riemann 的素数幂显式公式]对每个实数 $`x>1`，令 $`J_0(x)` 在 $`p^k<x` 时计入 $`1/k`，在 $`p^k=x` 时计入 $`1/(2k)`。则有
$$`J_0(x)=\operatorname{Ei}(\log x)
-\lim_{T\to\infty}\sum_{|\Im\rho|\le T}m_\rho\operatorname{Ei}(\rho\log x)
-\log 2+\int_x^\infty\frac{dt}{t(t^2-1)\log t}.`
这里 $`\rho` 遍历 ζ 函数在开临界带内的不同零点，$`m_\rho` 是解析重数。指数积分取{ref "exponential-integrals"}[主支]，正负虚部共用同一个截断高度。等式对每个端点无条件成立。

{docstring riemannPrimeCounting_explicit_formula}

{docstring tendsto_riemannPrimeCounting_principalEi_formula}

常数来自第一个素数之前的零计数。固定 $`1<a<2`，对{ref "real-shift-before-first-prime"}[平移公式]的两边沿 $`0<y<\infty` 积分。非平凡零点的首项有共同的因子 $`e^{-y\log a}`，其余项可以{ref "ei-shifted-residues"}[在积分内求和]。负偶数零点给出平凡零点尾积分的相反数。极点与 ζ 的对数导数组合后，由 $`\zeta(0)=-1/2` 得到 $`\operatorname{Ei}(\log a)-\log2`。这就确定了{ref "riemann-counting-normalization"}[对所有端点相同的常数]。

{docstring integral_shiftedNontrivialZeroContribution}

{docstring shiftedTrivialZeroContribution_eq_integral}

{docstring integral_shiftedTrivialZeroContribution}

{docstring riemannEiZeroSum_sub_tail_of_lt_two}

{docstring riemannCountingConstant_eq_neg_log_two}

对 $`x^{1/d}` 作{ref "prime-counting-explicit-formula"}[有限 Möbius 反演]可恢复通常的 $`\pi(x)`。例如 $`J_0(4)=1+1+1/4=9/4`，而 $`J_0(2)=1/2`，所以 $`\pi(4)=9/4-(1/2)(1/2)=2`。当 $`x` 本身是素数时，在反演所得的中点值上再加 $`1/2`。

{docstring primePi_eq_moebius_principalEi_formula}

# 素数定理的误差与零点实部
%%%
tag := "von-koch-error"
file := "von-koch-error"
%%%

{index}[von Koch 判别法]令 $`\Theta` 为 ζ 函数所有非平凡零点实部的上确界。对每个实数 $`x\ge2`，都有
$$`|\psi(x)-x|\le C x^{\Theta}(\log x)^2.`
这里 $`\psi(x)=\sum_{n\le x}\Lambda(n)` 在素数幂处计入整个跳跃。估计对 $`x` 的位置没有额外限制。

{docstring abs_psi_sub_id_le_zetaSupRe_log_sq}

在截断高度 $`T=x` 的显式公式中，每个零点满足 $`|x^\rho|=x^{\Re\rho}\le x^\Theta`。再把零点按高度分组，利用计重数的零点计数 $`N(T)\ll T\log T`，得到
$$`\sum_{|\Im\rho|\le T}\frac{m_\rho}{|\rho|}\ll(\log T)^2.`

{docstring sum_zeroMultiplicity_div_norm_le}

反过来，若一个固定幂次 $`a` 满足 $`\psi(x)-x=O(x^a)`，则 $`\Theta\le a`。这是因为更靠右的零点会迫使误差沿一列趋于无穷的 $`x` 超过这个幂界。于是，对任意 $`a`，$`\Theta\le a` 当且仅当每个 $`\varepsilon>0` 都给出误差 $`O(x^{a+\varepsilon})`。换言之，$`\Theta` 是所有可用幂次的下确界。

{docstring zetaSupRe_le_iff_psi_error_isBigO}

{docstring zetaSupRe_eq_sInf_psi_error_exponents}

由函数方程的对称性，$`\Theta=1/2` 与{ref "riemann-hypothesis"}[黎曼猜想]等价。代入上面的上界，再用逆推论，便得到 von Koch 判别法
$$`\mathrm{RH}\quad\Longleftrightarrow\quad\psi(x)=x+O\!\left(\sqrt{x}(\log x)^2\right).`

{docstring riemannHypothesisProp_iff_psi_error_isBigO_sqrt_log_sq}

# 普通素数计数的平方根误差
%%%
tag := "prime-counting-rh-error"
file := "rh-prime-counting-error"
%%%

{index}[素数计数的平方根误差]记 $`\pi(x)=\#\{p\le x\}`、$`\operatorname{Li}_2(x)=\int_2^x dt/\log t`。黎曼猜想等价于
$$`\pi(x)=\operatorname{Li}_2(x)+O(\sqrt{x}\log x).`
同一判别法以 $`\theta(x)=\sum_{p\le x}\log p` 表示时，误差为 $`O(\sqrt{x}(\log x)^2)`。

{docstring riemannHypothesisProp_iff_primePi_error_isBigO_sqrt_log}

{docstring riemannHypothesisProp_iff_theta_error_isBigO_sqrt_log_sq}

这一个对数因子的差别来自分部求和。设 $`\Theta` 是非平凡零点实部的上确界。从{ref "von-koch-error"}[对 $`\psi` 的无条件误差界]中去掉高次素数幂，得到 $`|\theta(x)-x|\ll x^\Theta(\log x)^2`。把 $`\theta(x)-x` 除以 $`\log x` 后，分部求和的余项由 $`\int_2^x t^{\Theta-1}dt` 控制。因此对所有 $`x\ge2` 有 $`|\pi(x)-\operatorname{Li}_2(x)|\ll x^\Theta\log x`。

{docstring abs_theta_sub_id_le_zetaSupRe_log_sq}

{docstring abs_primePi_sub_logIntegral_le_zetaSupRe_log}

逆向论证有一个端点常数。令 $`E(x)=\pi(x)-\operatorname{Li}_2(x)`，则
$$`\theta(x)-x=E(x)\log x-\int_2^x\frac{E(t)}{t}\,dt-2.`
这里的 $`-2` 来自对数积分的下端点。若 $`E(x)=O(\sqrt{x}\log x)`，右边给出 $`\theta(x)-x=O(\sqrt{x}(\log x)^2)`，从而由 von Koch 判别法推出黎曼猜想。

{docstring theta_sub_id_eq_primePi_error_abel}
