import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.PrimeDistribution.LeastPrime
import AnalyticNumberTheory.PrimeDistribution.LeastPrimeSubexponential
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
