import AnalyticNumberTheory.DivisorProblems.TwoSquares
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AnalyticNumberTheory.DivisorProblems

#doc (Manual) "整数圆盘与二平方和" =>
%%%
tag := "circle-lattice-points"
file := "circle-lattice-points"
%%%

{index}[Jacobi 二平方和公式]记 $`r_2(n)` 为 $`a^2+b^2=n` 的有序整数解数，符号也计入。模四的实特征 $`\chi_4` 在偶数上为零，在奇数 $`1,3\pmod 4` 上分别取 $`1,-1`。对于 $`n\ge1`，Jacobi 的公式把一个圆周上的格点数写成因子和。

{docstring repTwoSquares_eq_four_mul_sum_chi4}

以 $`n=5` 为例，因子 $`1` 和 $`5` 的特征值都是一，因此 $`r_2(5)=8`。这八个格点由 $`(1,2)` 交换坐标、改变符号得到。

{index}[Gauss 圆问题]把各圆周的格点数相加并补上原点，得到 $`a^2+b^2\le x` 的格点数。这里的 $`x` 是半径的平方，所以圆盘面积为 $`\pi x`。本库的初等估计在 $`x\ge 1` 时将格点数与面积的偏差控制在 $`5\sqrt{x}` 以内。

{docstring abs_gaussCircleError_le}
