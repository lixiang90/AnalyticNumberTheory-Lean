import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.PrimeDistribution

#doc (Manual) "等差数列中的素数与 Siegel–Walfisz 定理" =>
%%%
tag := "primes-in-progressions"
file := "primes-in-progressions"
%%%

{index}[Siegel–Walfisz 定理]用 $`\psi(x;q,a)` 记简化剩余类 $`a\bmod q` 中的 von Mangoldt 加权和。对每个固定的实数 $`A\ge0`，存在正常数 $`C,c`，使得对所有 $`x\ge2`、$`1\le q\le(\log x)^A` 和 $`(a,q)=1`，都有

$$`\left|\psi(x;q,a)-\frac{x}{\varphi(q)}\right|\le Cx\exp(-c\sqrt{\log x}).`

{docstring siegelWalfisz}

用 Dirichlet 特征的正交关系展开剩余类指示函数后，主特征给出{ref "prime-counting"}[素数定理]的主项，非主特征则需要消去估计。令 $`T=\exp(\sqrt{\log x})`。普通无零区域控制虚部非零的零点，Siegel 对可能实零点的界控制靠近实轴的情形。两者合并后，矩形的左边可以取在 $`1-d/\sqrt{\log x}`，并在其中一致地控制 $`L'/L`。常数允许依赖于 $`A`。

{docstring siegelWalfisz_logDeriv_rectangle}

在{ref "perron-inversion"}[截断 Perron 公式]中，采用半整数截点 $`x=N+1/2`。邻近整数的贡献可按距离分组求和，得到对所有特征一致的误差。把积分移到无零矩形左边，因子 $`x^s` 的模就获得 $`\exp(-c\sqrt{\log x})` 的节省。由于特征和只依赖于 $`\lfloor x\rfloor`，最后可把估计传回实数截点。

{docstring perron_twist_halfInteger_error_le}

这一模数范围足以处理{ref "goldbach"}[三元 Goldbach 问题]的主弧：主弧分母的截点可以选为对数的固定次幂。
