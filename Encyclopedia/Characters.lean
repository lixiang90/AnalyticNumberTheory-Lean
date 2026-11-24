import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DirichletLFunctions

#doc (Manual) "Dirichlet 特征与区间和" =>
%%%
tag := "character-sums"
file := "character-sums"
%%%

{index}[Pólya–Vinogradov 不等式]设 $`\chi` 是模 $`q\ge 2` 的非主特征。一个完整周期的特征和为零。若只求区间 $`a<n\le b` 上的和，取绝对值后逐项相加给出长度界，而 Fourier 展开给出与区间长度无关的估计

$$`\left|\sum_{a<n\le b}\chi(n)\right|\le 4\sqrt q\log q.`

{docstring polya_vinogradov_Ioc}

这里允许 $`\chi` 由较小模数的特征诱导。排除主特征是必要的：对主特征，每个完整周期的贡献等于 $`\varphi(q)`。
