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
