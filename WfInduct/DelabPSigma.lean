import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Delaborator.SubExpr

open Lean

open Meta

open Lean.PrettyPrinter
open Lean.PrettyPrinter.Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr

@[delab app.PSigma.mk]
def delabSigma : Delab := whenPPOption getPPNotation do
  let Expr.app (.app _ x) y ← getExpr | failure
  `(⟨ $(← delab x), $(← delab y)⟩)
