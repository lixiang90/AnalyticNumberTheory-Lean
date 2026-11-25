import AnalyticNumberTheory.RiemannZeta.RiemannSharpApproximation
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.SmoothedDirichletSums
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.RiemannZeta

#doc (Manual) "黎曼 ξ 函数与临界线" =>
%%%
tag := "riemann-xi"
file := "riemann-xi"
%%%

{index}[黎曼 ξ 函数]将 $`\zeta(s)` 与 Gamma 因子配成整函数 $`\xi(s)` 后，函数方程成为关于 $`s\mapsto 1-s` 的对称关系。按本库的归一化，$`\xi(0)=\xi(1)=1/2`。

{docstring xi_one_sub}

取 $`s=1/2+it`，此时 $`1-s=\overline{s}`。再用 $`\xi(\overline{s})=\overline{\xi(s)}`，可知临界线上每一点的函数值都为实数。

{docstring xi_half_add_mul_I_im}

{index}[光滑函数方程]用高斯权 $`e^{w^2}` 作竖线积分，可以把 $`\xi(s)^k` 写成关于 $`s` 和 $`1-s` 的两项之和。具体地，令 $`I_c(s,k)` 为沿 $`w=c+it` 对 $`\xi(s+w)^k e^{w^2}/w` 关于 $`t` 的积分，其中 $`c>0`。向左移动积分线时，$`w=0` 的留数给出 $`\xi(s)^k`。因此 $`I_c(s,k)+I_c(1-s,k)=2\pi\,\xi(s)^k`。

{docstring xi_pow_gaussian_functional_equation}

在 $`0<\Re s<1` 内，把两条积分线上的 Dirichlet 级数逐项积分，得到 $`\zeta(s)` 的两个绝对收敛的加权和。对 $`\zeta(s)^2`，展开系数是正因子个数 $`d(n)`。每个权由独立的竖线积分给定，因而可继续估计截断误差。

{docstring riemannZeta_smoothed_functional_equation}

{docstring riemannZeta_sq_smoothed_functional_equation}

# 两个截断和与 Hurwitz ζ 函数
%%%
tag := "sharp-hurwitz-equation"
file := "sharp-cutoffs"
%%%

{index}[近似函数方程]设 $`s=\sigma+it`，其中 $`0<\sigma<1`。取两个实截断点 $`x,y\ge 2`，使 $`2\pi xy=|t|`。对于 $`0<a\le1`，直接求和的一侧包含所有 $`m\ge0` 且 $`m+a\le x` 的项 $`(m+a)^{-s}`。另一侧按非零整数频率求和。写 $`e(u)=\exp(2\pi i u)`，便有

$$`\zeta(s,a)=\sum_{0\le m\le x-a}(m+a)^{-s}+
 \Gamma(1-s)\sum_{0<|n|\le y} e(-na)(-2\pi i n)^{s-1}+R.`

复幂取主值。余项对平移参数 $`a` 一致，对正、负高度均满足

$$`|R|\le256\left(1+\frac1{1-\sigma}\right)
  \left[x^{-\sigma}\bigl(1+\log(y+2)\bigr)+\frac{x^{1-\sigma}}{\sqrt{|t|}}\right].`

{docstring hurwitzZeta_sharp_afe}

取 $`a=1`，所有平移因子都等于一，正、负频率合成同一个 Gamma 因子，乘以 $`\sum_{n\le y}n^{s-1}`。例如，临界线上取 $`x=y=\sqrt{|t|/(2\pi)}`，两个有限和等长，误差为 $`O(|t|^{-1/4}\log |t|)`。对有理平移按同余类求和，就得到{ref "sharp-periodic-equation"}[周期系数的对应公式]。

{docstring riemannZeta_sharp_afe}
