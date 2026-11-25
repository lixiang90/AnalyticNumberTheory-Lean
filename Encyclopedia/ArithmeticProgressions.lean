import AnalyticNumberTheory.PrimeDistribution.PageProgressions
import AnalyticNumberTheory.PrimeDistribution.SignedCharacterExplicitFormula
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

# 特征和的截断显式不等式
%%%
tag := "character-truncated-explicit-formula"
file := "character-truncated-explicit-formula"
%%%

{index}[特征和的截断显式公式]设 $`\chi` 是模 $`q` 的非主特征。对所有 $`x\ge4` 和 $`0\le y\le x`，特征和 $`\psi(y,\chi)=\sum_{n\le y}\chi(n)\Lambda(n)` 满足

$$`|\psi(y,\chi)|\ll \sqrt{x}\,(1+\log(qx))^2+\sum_{\substack{L(\rho,\chi)=0,\ 0<\beta<1\\ |\gamma|\le\sqrt{x}}} m(\rho)\,\frac{x^\beta}{1+|\gamma|},\qquad \rho=\beta+i\gamma.`

这里 $`m(\rho)` 是解析重数，隐常数是绝对常数。零点和同时包含正、负虚部和实零点。同一右端控制区间 $`[0,x]` 中的每个截点，也适用于模数超过 $`\sqrt{x}` 的情形。

{docstring nonprincipal_psi_truncated_explicit_bound}

对本原特征，证明在半整数 $`h=\lfloor y\rfloor+1/2` 处使用 Perron 公式。把整函数权 $`g_h(s)=(h^s-1)/s`（其中 $`g_h(0)=\log h`）乘以完成的 $`L` 函数的对数导数，再把积分移到 $`\Re s=-1/2`。每个零点贡献 $`m(\rho)g_h(\rho)`。对于靠近原点的零点，泛函方程将它与同一高度的 $`1-\overline\rho` 配对，二者重数相同，由此得到上式中的零点权。

{docstring AnalyticNumberTheory.DirichletLFunctions.sum_norm_perronDifferenceWeight_le}

由本原特征诱导到模 $`q` 时，临界带内的零点及重数保持不变。von Mangoldt 和中新出现的误差只来自整除 $`q` 的素数幂，可并入平方根误差项。

对于 $`1\le y\le x`，还可以保留留数的复数值，得到固定高度的显式公式

$$`\psi(y,\chi)=-\sum_{|\gamma|\le\sqrt{x}}m(\rho)\frac{y^\rho-1}{\rho}
+O\!\left(\sqrt{x}\,(1+\log(qx))^2\right).`

零点取自 $`0<\Re\rho<1`。在 $`y=1` 处，零点权都为零。一般截点由半整数移来，核对 $`y` 的导数是 $`y^{\rho-1}`，模至多为一。再用单位高度区间中的零点数估计，把避开零点所选的高度移至 $`\sqrt{x}`。

{docstring nonprincipal_psi_signed_explicit_formula}

# 可选截断高度的显式公式
%%%
tag := "explicit-formula-height"
file := "explicit-formula-height"
%%%

{index}[截断高度]取一个非主 Dirichlet 特征 $`\chi\bmod q`，并选定 $`0<T\le\sqrt{x}`。对每个实数端点 $`1\le y\le x`，都有

$$`\psi(y,\chi)
=-\sum_{\substack{L(\rho,\chi)=0,\ 0<\Re\rho<1\\ |\Im\rho|\le T}}
m(\rho)\frac{y^\rho-1}{\rho}
+O\!\left(\frac{x}{T}(1+\log(qx))^2\right).`

隐常数与模数、特征、端点和高度都无关。边界 $`|\Im\rho|=T` 上的零点计入和中。取 $`T=\sqrt{x}` 即得{ref "character-truncated-explicit-formula"}[平方根高度的公式]。取较小的 $`T` 会增大截断误差，同时缩短需要考察的零点区间。

{docstring nonprincipal_psi_signed_explicit_at_height}

当 $`T\ge8` 时，在半整数处使用 Perron 公式，并在 $`[T-3/4,T-1/4]` 中选取避开零点的积分高度。最后移回 $`T` 时，只有宽度至多为一的水平带内的零点会改变留数和。

{docstring perron_halfInteger_height_parameters}

{docstring primitive_signed_explicit_at_height_of_perron}

当 $`0<T\le8` 时，实部在 $`(0,1)`、虚部在 $`[-8,8]` 内的零点个数可由 Jensen 估计控制。正则化权在 $`y=1` 时为零，因此同一公式包括左端点。对非本原特征，诱导保持临界带内的零点及其重数，特征和的差来自整除模数的素数幂。

{docstring nonprincipal_psi_signed_explicit_small_height}

{docstring primitive_signed_explicit_height_of_perron}
