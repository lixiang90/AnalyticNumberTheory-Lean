import AnalyticNumberTheory.DirichletSeries.EulerProduct
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletSeries

#doc (Manual) "Dirichlet 级数与 Euler 乘积" =>
%%%
tag := "euler-products"
file := "euler-products"
%%%

{index}[Euler 乘积]在 $`\operatorname{Re}(s)>1` 内，$`\sum_{n\ge 1}n^{-s}` 绝对收敛。每个素数 $`p` 提供一个几何级数，展开有限多个这样的因子时，唯一分解保证每个由这些素数构成的正整数恰好出现一次。让素数集合增大，便得到

$$`\zeta(s)=\prod_p(1-p^{-s})^{-1}.`

{docstring AnalyticNumberTheory.DirichletSeries.riemannZeta_eulerProduct_hasProd}

对 Euler 乘积作对数求导，素数 $`p` 的局部因子给出 $`(\log p)p^{-s}/(1-p^{-s})`。再展开分母，可以读出每个素数幂的权重 $`\log p`。这正是{ref "prime-counting"}[素数计数]中使用的 von Mangoldt 权重。

{docstring riemannZeta_neg_logDeriv_eq_tsum_primes}
