import VersoManual
import Encyclopedia

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  sourceLink := some "https://github.com/lixiang90/AnalyticNumberTheory-Lean"
  issueLink := some "https://github.com/lixiang90/AnalyticNumberTheory-Lean/issues"

def main := manualMain (%doc Encyclopedia) (config := config)
