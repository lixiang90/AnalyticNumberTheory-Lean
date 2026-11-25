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
