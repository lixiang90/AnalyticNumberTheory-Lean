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
