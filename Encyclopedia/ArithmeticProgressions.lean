import AnalyticNumberTheory.PrimeDistribution.PageProgressions
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

# Page 定理与例外导子
%%%
tag := "page-prime-progressions"
file := "page-exceptional-conductor"
%%%

固定模数上限 $`Q\ge2`。Page 定理允许在所有导子不超过 $`Q` 的原特征中标出至多一个例外实特征。对其余非主特征，包括由这些原特征诱导的特征，同一个常数给出随 $`Q` 和虚部高度变化的无零区域。

{docstring page_zeroFree_region_primitiveCharacter}

若例外特征的导子为 $`d`，所有满足 $`q\le Q` 且 $`d\nmid q` 的模数都可使用同一组部分和估计。若无例外，定理取 $`d=0`，从而覆盖所有正模数。对简化剩余类用特征正交关系求和，便得到相应的 $`\psi(k;q,r)` 估计。式中的 $`Y` 控制无零区域适用的尺度，允许 $`1\le k\le N` 共用一次选择。

{docstring page_psiChar_partial}

{docstring page_psiAP}
