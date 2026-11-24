import AnalyticNumberTheory.AnalyticTools.EntireFunctions.HadamardFactorization
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

#doc (Manual) "整函数的典型乘积与零点展开" =>
%%%
tag := "entire-functions"
file := "entire-functions"
%%%

{index}[Hadamard 因式分解]设 $`f` 是不恒为零的整函数，增长阶严格小于二。先把原点处的零点写成 $`z^m`。对其余每个零点 $`\rho`，取带指数修正的因子 $`(1-z/\rho)e^{z/\rho}`。同一零点按重数反复计入。Hadamard 定理说明余下的无零因子形如 $`e^{A+Bz}`。库中的陈述同时处理有限个和无限个非零零点。

{docstring hadamard_factorization_genus_one}

在避开零点处取对数导数，可将乘积换成和。修正因子的作用在这里清晰可见，每项为 $`1/(z-\rho)+1/\rho`，两个常数阶贡献相消，使远处零点的贡献更小。

{docstring hadamard_logDeriv_genus_one}

{ref "complex-bounds"}[Jensen 公式]给出圆盘内零点数的控制，而{ref "zeta-zeros"}[ζ 函数零点计数]将这些工具用于具有函数方程的特定整函数。
