import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import AnalyticNumberTheory.SieveMethods.HalaszMontgomery
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.SieveMethods

#doc (Manual) "Dirichlet 多项式的均方与大值" =>
%%%
tag := "dirichlet-polynomials"
file := "dirichlet-polynomials"
%%%

{index}[Dirichlet 多项式]对 $`D(s)=\sum_{n=1}^N a_n n^{-s}`，在竖直线 $`s=\sigma+it` 上展开 $`|D(s)|^2`。对角项与 $`t` 无关，积分后的贡献为区间长度乘以 $`\sum_{n\le N}|a_n|^2 n^{-2\sigma}`。非对角项带有振荡因子。Hilbert 不等式给出与积分区间长度无关的总误差。

{docstring dirichletPoly_mean_sq_asymp}

{index}[Halász–Montgomery 不等式]在一组离散高度上，若每处都满足 $`|D(it_j)|\ge V`，则高度的个数也受到限制。设有 $`R` 个高度，并以 $`B` 控制不同高度之差处的无权 Dirichlet 多项式的模。对角项的核值恰为 $`N`，其余每项至多为 $`B`，于是

$$`R V^2\le\left(\sum_{n=1}^N |a_n|^2\right)\bigl(N+(R-1)B\bigr).`

{docstring halasz_montgomery_dirichletPoly_count_le}
