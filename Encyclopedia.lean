import Encyclopedia.Summation
import Encyclopedia.DirichletSeries
import Encyclopedia.Zeta
import Encyclopedia.Characters
import Encyclopedia.Primes
import Encyclopedia.ArithmeticProgressions
import Encyclopedia.BombieriVinogradov
import Encyclopedia.PartitionAsymptotic
import Encyclopedia.ExponentialSums
import Encyclopedia.Waring
import Encyclopedia.WaringArchimedean
import Encyclopedia.WaringLocalDensities
import Encyclopedia.Divisors
import Encyclopedia.Partitions
import Encyclopedia.Farey
import Encyclopedia.Sieves
import Encyclopedia.Goldbach
import Encyclopedia.LatticePoints
import Encyclopedia.DirichletPolynomials
import Encyclopedia.Transforms
import Encyclopedia.Gamma
import Encyclopedia.ComplexBounds
import Encyclopedia.EntireFunctions
import Encyclopedia.Perron
import Encyclopedia.ZetaZeros
import Encyclopedia.LFunctions
import Encyclopedia.Eta
import Encyclopedia.References

open Verso.Genre Manual

#doc (Manual) "解析数论百科全书" =>
%%%
authors := ["AnalyticNumberTheory-Lean Contributors"]
shortTitle := "解析数论百科"
tag := "encyclopedia-home"
%%%

本百科按数学问题组织。每个条目给出公式的适用条件、推导中的关键一步，以及可从 Lean 库直接引用的定理。选题参考潘承洞、潘承彪《解析数论基础》{citep panPan1999}[]。

从{ref "euler-products"}[Euler 乘积]出发，可以追踪素数幂如何进入{ref "prime-counting"}[素数定理]。从{ref "exponential-sums"}[指数和]出发，可以看到一个周期上的积分如何提取{ref "waring"}[幂和方程的解数]。

{include 0 Encyclopedia.Transforms}

{include 0 Encyclopedia.Summation}

{include 0 Encyclopedia.Gamma}

{include 0 Encyclopedia.ComplexBounds}

{include 0 Encyclopedia.EntireFunctions}

{include 0 Encyclopedia.DirichletSeries}

{include 0 Encyclopedia.Perron}

{include 0 Encyclopedia.Zeta}

{include 0 Encyclopedia.ZetaZeros}

{include 0 Encyclopedia.Characters}

{include 0 Encyclopedia.LFunctions}

{include 0 Encyclopedia.Primes}

{include 0 Encyclopedia.ArithmeticProgressions}

{include 0 Encyclopedia.BombieriVinogradov}

{include 0 Encyclopedia.ExponentialSums}

{include 0 Encyclopedia.Waring}

{include 0 Encyclopedia.WaringArchimedean}

{include 0 Encyclopedia.WaringLocalDensities}

{include 0 Encyclopedia.Goldbach}

{include 0 Encyclopedia.Divisors}

{include 0 Encyclopedia.LatticePoints}

{include 0 Encyclopedia.Eta}

{include 0 Encyclopedia.Farey}

{include 0 Encyclopedia.Partitions}

{include 0 Encyclopedia.PartitionAsymptotic}

{include 0 Encyclopedia.Sieves}

{include 0 Encyclopedia.DirichletPolynomials}

# 索引
%%%
number := false
tag := "index"
file := "index-terms"
%%%

{theIndex}
