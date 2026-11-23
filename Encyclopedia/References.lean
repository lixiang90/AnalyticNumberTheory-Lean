import VersoManual

open Verso.Genre.Manual

/-- 《解析数论基础》（潘承洞、潘承彪著，科学出版社）。 -/
def panPan1999 : InProceedings where
  title := inlines!"解析数论基础（Foundations of Analytic Number Theory）"
  authors := #[inlines!"潘承洞", inlines!"潘承彪"]
  year := 1991
  booktitle := inlines!"科学出版社（现代数学基础丛书）"
