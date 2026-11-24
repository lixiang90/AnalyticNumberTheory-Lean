import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachExceptionalSet
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AdditiveNumberTheory

#doc (Manual) "二素数表示的例外集" =>
%%%
tag := "goldbach-exceptional-set"
file := "goldbach-exceptional-set"
%%%

{index}[Goldbach 例外集]令 $`E(N)` 为不超过 $`N` 且不能写成两个素数之和的正偶数的个数。两个素数可以相同。对于每个固定的自然数 $`A`，有

$$`E(N)\ll_A\frac{N}{(\log N)^A}.`

因此，在不超过 $`N` 的正偶数中，可以表示成两个素数之和的比例趋于一。这个密度结论允许有例外。是否每个大于二的偶数都可表示，仍是开放问题。

{docstring goldbachExceptionalSet_card_isBigO}

{docstring even_sum_two_primes_proportion_tendsto_one}

证明先研究带 von Mangoldt 权的表示数 $`R_2(n)`。在一个完整周期上，Bessel 不等式把不同目标整数的 Fourier 系数一起控制。结合{ref "goldbach"}[主弧的奇异级数]和次弧上的素数指数和估计，可以对加权表示数与主项之差的绝对值求和。

{docstring goldbachBinaryWeighted_mean_isBigO}

对偶数，二元奇异级数有统一的正下界。把较小整数单独计数，再从其余表示中扣掉高次素数幂，仍无两素数表示的整数就必须贡献可观的误差。用上式除以单个例外至少贡献的误差，便得到例外集的上界。
