import VersoManual
import AnalyticNumberTheory
import Encyclopedia.References

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "解析数论百科全书 — Analytic Number Theory Encyclopedia" =>
%%%
authors := ["AnalyticNumberTheory-Lean Contributors"]
shortTitle := "解析数论百科"
tag := "encyclopedia-home"
%%%

本百科全书基于 Lean 4 与 Mathlib (`v4.36.0`) 构建，围绕潘承洞、潘承彪《解析数论基础》{citep panPan1999}[] 的核心理论体系展开形式化与阐述。

# 预备测试
%%%
tag := "smoke-test"
file := "smoke-test"
%%%

黎曼 $`\zeta` 函数定义为 $`\zeta(s) = \sum_{n=1}^{\infty} n^{-s}`，当 $`\operatorname{Re}(s) > 1` 时绝对收敛：

$$`\zeta(s) = \prod_{p} \left(1 - p^{-s}\right)^{-1}`

在 Lean 中对应 {name}`AnalyticNumberTheory.zetaFn`：

{docstring AnalyticNumberTheory.zetaFn}

# 索引
%%%
number := false
tag := "index"
file := "index-terms"
%%%

{theIndex}
