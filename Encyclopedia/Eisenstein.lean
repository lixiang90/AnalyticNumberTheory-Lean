import AnalyticNumberTheory.ModularAndPartitions.EisensteinConeContinuation
import AnalyticNumberTheory.ModularAndPartitions.EisensteinIntegralWeights
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.ModularAndPartitions

#doc (Manual) "复权 Eisenstein 级数" =>
%%%
tag := "eisenstein-series"
file := "eisenstein-series"
%%%

取上半平面中的 $`z`。当 $`\Re s>2` 时，{index}[Eisenstein 级数]由绝对收敛的格点和给出

$$`G(z,s)=\sum_{(m,n)\in\mathbb Z^2\setminus\{(0,0)\}}(mz+n)^{-s}.`

为了明确复幂的含义，这里取 $`-\pi\le\arg w<\pi`。特别地，当 $`n>0` 时，$`(-n)^{-s}=e^{\pi i s}n^{-s}`。这个选择影响复权时的常数项。

{docstring eisensteinG_eq_latticeSum}

# 从格点和得到解析延拓
%%%
tag := "eisenstein-complex-weight"
file := "continuation"
%%%

令 $`q=e^{2\pi iz}`，则 $`|q|<1`。对每一行格点用 Lipschitz 求和，可将 $`G(z,s)` 写成常数项和一个 Lambert 级数之和。写 $`A(s)=1+e^{\pi i s}`，在 $`s\ne1` 时，所得公式为

$$`G(z,s)=A(s)\zeta(s)+\frac{A(s)(-2\pi i)^s}{\Gamma(s)}
               \sum_{m,n\ge1} n^{s-1}q^{mn}.`

Lambert 级数在固定的 $`z` 上关于 $`s` 局部一致绝对收敛。在 $`s=1` 处，$`A(s)` 的零点消去 $`\zeta(s)` 的极点，得 $`G(z,1)=-\pi i`。整个表达式对权 $`s` 为整函数，对每个固定的权在上半平面关于 $`z` 全纯。

{docstring AnalyticNumberTheory.AnalyticTools.lipschitz_summation}

{docstring differentiable_eisensteinG_weight}

{docstring differentiableOn_eisensteinG_upperHalfPlane}

{docstring eisensteinG_one}

# 整数权的模变换
%%%
tag := "eisenstein-integral-weights"
file := "integral-weights"
%%%

对 $`\gamma=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\mathrm{SL}_2(\mathbb Z)` 写 $`j=cz+d`。当整数 $`k\ge3` 时，由格点换元得到 $`G(\gamma z,k)=j^kG(z,k)`。权二的解析延拓满足

$$`G(\gamma z,2)=j^2G(z,2)-2\pi i c j.`

例如取反演 $`z\mapsto-1/z`，修正项为 $`-2\pi i z`。对于平移 $`z\mapsto z+1`，$`c=0`，而 Fourier 展开说明周期性可推广到任意复权。

{docstring eisensteinG_nat_modular}

{docstring eisensteinG_two_modular}

{docstring eisensteinG_add_one}

# 复权模变换的锥和
%%%
tag := "eisenstein-period-cone"
file := "period-cone"
%%%

若 $`c>0`，变换因子 $`j=cz+d` 在上半平面。格点换元时，辐角越过分支切线的项可按指标 $`k\ge0`、$`dk<c\ell` 描述。在 $`\Re s>2` 时，周期差有绝对收敛的表达式

$$`j^{-s}G(\gamma z,s)-G(z,s)
  =(e^{-\pi i s}-e^{\pi i s})
    \sum_{\substack{k,\ell\in\mathbb Z\\k\ge0,\;dk<c\ell}}(kz+\ell)^{-s}.`

左边作为 $`s` 的函数延拓至整个复平面。取 $`k=0` 时正整数 $`\ell` 全部参与求和，这一边界由负实轴上的辐角约定决定。

{docstring eisensteinPeriod_eq_cone}

{docstring differentiable_eisensteinPeriod}

用周期差除以上式的指数因子，得到锥和的亚纯延拓。在权二处留数为 $`c/j`，在权一处留数为 $`(1-j^{-1})/2`。权二处的留数与指数因子的导数相乘，恰好恢复整数权变换中的修正项。

{docstring eisensteinConeContinuation_residue_two}

{docstring eisensteinConeContinuation_residue_one}
