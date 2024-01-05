import Lean

set_option autoImplicit false

open Lean Elab Command Meta

-- #check WellFounded.fixF

def lambda1NoContext {α} (e : Expr) (k : FVarId → Expr →  MetaM α) : MetaM α := do
  lambdaTelescope e fun args body => do
    let #[param] := args | unreachable!
    mapMetaM (withReader (fun ctx => { ctx with lctx := ctx.lctx.erase param.fvarId! })) do
      k param.fvarId! body

def mapWriter {σ α m} [Monad m] (f : σ → m σ) (k : StateT (Array σ) m α) : StateT (Array σ) m α := do
  fun s₁ => do
    let (a, s₂) ← k #[]
    let s₂' ← s₂.mapM f
    pure (a, s₁ ++ s₂')

-- Non-tail-positions: Replace calls to oldIH with fn, and float out induction hypotheses
-- built from newIH
partial def process (fn : Expr) (oldIH newIH : FVarId) (e : Expr) :
    StateT (Array Expr) MetaM Expr := do
  if e.isApp  && e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
    let #[arg, proof] := e.getAppArgs  | unreachable!

    let arg' ← process fn oldIH newIH arg
    let proof' ← process fn oldIH newIH proof

    let IH := mkAppN (.fvar newIH) #[arg', proof']
    modify (·.push IH)
    return .app fn arg
  else if e.isApp && e.getAppArgs.any (·.isFVarOf oldIH) then
    -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
    -- So beta-reduce that definition.

    -- Need to look through theorems here!
    let e' ← withTransparency .all do whnf e
    -- TODO: Check that e' actually changed
    process fn oldIH newIH e'
  else if let .app e1 e2 := e then
    return .app (← process fn oldIH newIH e1) (← process fn oldIH newIH e2)
  else if let .letE n t v b _ := e then
    let v' ← process fn oldIH newIH v
    withLetDecl n t v' fun x => do
      mapWriter (mkLetFVars (usedLetOnly := true) #[x] ·) do
      let b' ← process fn oldIH newIH (b.instantiate1 x)
      mkLetFVars (usedLetOnly := false) #[x] b'
  else if e.isLambda then
    lambdaTelescope e fun xs body => do
      mapWriter (mkLambdaFVars (usedOnly := true) xs ·) do
        let body' ← process fn oldIH newIH body
        mkLambdaFVars (usedOnly := false) xs body'
  else
    return e

def withLetDecls {α} (vals : Array Expr) (k : Array FVarId → MetaM α) (i : Nat := 0) : MetaM α := do
  if h : i < vals.size then
    let e := vals[i]
    withLetDecl s!"IH{i+1}" e (← inferType e) fun a =>
      withLetDecls vals (fun args => k (args.push a.fvarId!)) (i + 1)
  else
    k #[]
termination_by _ vals k i => vals.size - i

def assertIHs (vals : Array Expr) (mvarid : MVarId) : MetaM MVarId := do
  let mut mvarid := mvarid
  for v in vals, i in [0:vals.size] do
    mvarid ← mvarid.assert s!"IH{i+1}" (← inferType v) v
  return mvarid

-- Base case: Introduce a new hyp
def createHyp (motiveFVar : FVarId) (fn : Expr) (oldIH newIH : FVarId) (toClear : Array FVarId)
    (goal : Expr) (e : Expr) : MetaM Expr := do
  -- logInfo m!"Tail position {e}"
  let (_e', IHs) ← process fn oldIH newIH e |>.run #[]

  let mvar ← mkFreshExprSyntheticOpaqueMVar goal (tag := `hyp)
  let mut mvarId := mvar.mvarId!
  -- logInfo m!"New hyp 1 {mvarId}"
  mvarId ← assertIHs IHs mvarId
  -- logInfo m!"New hyp 2 {mvarId}"
  for fv in toClear do
    mvarId ← mvarId.clear fv
  -- logInfo m!"New hyp 3 {mvarId}"
  mvarId ← mvarId.cleanup
  let (_, _mvarId) ← mvarId.revertAfter motiveFVar
  let mvar ← instantiateMVars mvar
  -- logInfo <| m!"New hyp {_mvarId}" ++ Format.line ++ m!"used as {mvar}"
  pure mvar

partial def buildInductionBody (motiveFVar : FVarId) (fn : Expr) (toClear : Array FVarId)
    (goal : Expr) (oldIH newIH : FVarId) (e : Expr) : MetaM Expr := do
  if let some caseOnApp ← toCasesOnApp? e then
    throwError m!"TODO: buildInductionBody hits caseOnApp {caseOnApp.declName}"

  if e.isDIte then
    let #[_α, c, h, t, f] := e.getAppArgs | unreachable!
    -- TODO look for recursive calls in α, c, h
    let t' ← lambdaTelescope t fun args t => do
      -- TODO: Telescope only 1
      let t' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH t
      mkLambdaFVars args t'
    let f' ← lambdaTelescope f fun args f => do
      -- TODO: Telescope only 1
      let f' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH f
      mkLambdaFVars args f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c h t' f'

  if let some matcherApp ← matchMatcherApp? e then
    -- logInfo m!"{matcherApp.matcherName} {goal} {←inferType (Expr.fvar newIH)} => {matcherApp.discrs} {matcherApp.remaining}"
    if matcherApp.remaining.size > 0 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let motive' ← lambdaTelescope matcherApp.motive fun motiveArgs _motiveBody => do
        unless motiveArgs.size == matcherApp.discrs.size do
          throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
        -- Remove the old IH that was added in mkFix

        let eType ← newIH.getType
        let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
          let motiveArg := motiveArgs[i]!
          let discr     := matcherApp.discrs[i]!
          let eTypeAbst ← kabstract eTypeAbst discr
          return eTypeAbst.instantiate1 motiveArg

        let goalAbst ← matcherApp.discrs.size.foldRevM (init := goal) fun i goalAbst => do
          let motiveArg := motiveArgs[i]!
          let discr     := matcherApp.discrs[i]!
          let goalAbst ← kabstract goalAbst discr
          return goalAbst.instantiate1 motiveArg

        let motiveBody ← mkArrow eTypeAbst goalAbst
        mkLambdaFVars motiveArgs motiveBody

      let matcherLevels ← match matcherApp.uElimPos? with
        | none     => pure matcherApp.matcherLevels
        | some pos =>
          let uElim ← getLevel goal -- TODO: Double check
          pure <| matcherApp.matcherLevels.set! pos uElim

      let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
      let aux := mkApp aux motive'
      let aux := mkAppN aux matcherApp.discrs
      unless (← isTypeCorrect aux) do
        throwError "failed to add argument to matcher application, type error when constructing the new motive"
      let mut auxType ← inferType aux

      let mut alts' := #[]
      for alt in matcherApp.alts, numParams in matcherApp.altNumParams do
        let Expr.forallE _ d b _ ← whnfD auxType | unreachable!
        let alt' ← forallBoundedTelescope d (some numParams) fun xs d => do
          let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
          let alt' ← lambda1NoContext alt fun oldIH' alt => do
            let alt' ← forallBoundedTelescope d (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              -- logInfo m!"goal': {goal'}"
              let alt' ← buildInductionBody motiveFVar fn (toClear.push newIH'.fvarId!) goal' oldIH' newIH'.fvarId! alt
              mkLambdaFVars #[newIH'] alt' -- x is the new argument we are adding to the alternative
            mkLambdaFVars xs alt'
          pure alt'
        auxType := b.instantiate1 alt'
        alts' := alts'.push alt'
      let matcherApp' := { matcherApp with
        matcherLevels := matcherLevels,
        motive        := motive',
        alts          := alts',
        remaining     := matcherApp.remaining.set! 0 (.fvar newIH)
      }
      -- check matcherApp'.toExpr
      -- logInfo m!"matcherApp' {matcherApp'.toExpr}"
      return matcherApp'.toExpr
    else
      createHyp motiveFVar fn oldIH newIH toClear goal e
  else if let .letE n t v b _ := e then
    -- TODO: process t and b
    withLetDecl n t v fun x => do
      -- Should we keep let declaraions in the inductive theorem?
      -- If not, we can add them to `toClear`.
      let b' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH (b.instantiate1 x)
      mkLetFVars #[x] b'
  else if let some (n, t, v, b) := e.letFun? then
    -- TODO: process t and b
    withLocalDecl n .default t fun x => do
      let b' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH (b.instantiate1 x)
      -- logInfo m!"x: {x}, v: {v}, b: {b}, b': {b'}"
      mkLetFun x v b'
  else
    -- logInfo m!"End of buildInductionBody: {e}"
    createHyp motiveFVar fn oldIH newIH toClear goal e

elab "#derive_induction " ident:ident : command => runTermElabM fun _xs => do
  let orig_e ← Term.withSynthesize <| Term.elabTerm ident none
  -- TODO: There must be a nicer way to fully qualify the ident
  let .const name _ := orig_e | throwErrorAt ident "not a single identifier"
  let e ← whnf (← instantiateMVars orig_e)
  lambdaTelescope e fun params body => do
    unless params.size > 0 do
      throwError f!"Term is not a lambda application"
    body.withApp fun f fixArgs => do
      -- logInfo f!"{fixArgs}"
      unless f.isConstOf ``WellFounded.fixF do
        throwError f!"Term isn’t application of {``WellFounded.fixF}"
      let #[argType, rel, _motive, body, arg, acc] := fixArgs |
        throwError f!"Application of WellFounded.fixF has wrong arity {fixArgs.size}"
      unless ← isDefEq arg params.back do
        throwError f!"fixF application argument {arg} is not function argument "
      let [argLevel, _motiveLevel] := f.constLevels! | unreachable!
      -- logInfo body
      -- mkFresh

      let motiveType ← mkArrow argType (.sort levelZero)
      withLocalDecl `motive .default motiveType fun motive => do

      let e' := mkAppN (.const ``WellFounded.fixF [argLevel, levelZero]) #[argType, rel, motive]
      let fn := mkAppN orig_e params.pop
      let body' ← forallTelescope (← inferType e').bindingDomain! fun xs _ => do
        let #[param, genIH] := xs | unreachable!
        -- open body with the same arg
        let body ← instantiateLambda body #[param]
        lambda1NoContext body fun oldIH body => do
            let body' ← buildInductionBody motive.fvarId! fn #[genIH.fvarId!] (.app motive param) oldIH genIH.fvarId! body
            mkLambdaFVars #[param, genIH] body'

      let e' := mkAppN e' #[body', arg, acc]


      let e' ← mkLambdaFVars #[params.back] e'
      let mvars ← getMVarsNoDelayed e'
      for mvar in mvars, i in [:mvars.size] do
        mvar.setUserName s!"case{i+1}"
      let e' ← mkLambdaFVars (binderInfoForMVars := .default) (mvars.map .mvar) e'
      let e' ← mkLambdaFVars (binderInfoForMVars := .default) (params.pop ++ #[motive]) e'
      let e' ← mkLambdaFVars params.pop e'
      let e' ← instantiateMVars e'
      let eTyp ← inferType e'
      -- logInfo m!"eTyp: {eTyp}"
      -- logInfo m!"e has MVar: {e'.hasMVar}"
      check e'

      addDecl <| Declaration.defnDecl {
          name := .append name `induct, levelParams := [], type := eTyp, value := e'
          hints := ReducibilityHints.regular 0
          safety := DefinitionSafety.safe
      }
  pure ()

namespace Test

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by ackermann p => p

-- set_option pp.explicit true
-- #derive_induction ackermann
-- #check ackermann.induct

universe u
opaque _root_.List.attach : {α : Type u} → (l : List α) → List { x // x ∈ l }

inductive Tree | node : List Tree → Tree
def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)

#derive_induction Tree.rev

set_option linter.unusedVariables false in
def with_have : Nat → Nat
  | 0 => 0
  | n+1 =>
    if n % 2 = 0 then
      let h1 : n < n+2 := Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      with_have n
    else
      have h2 : n < n+1 := Nat.lt_succ_self n
      with_have n
termination_by with_have n => n

set_option pp.match false in
#derive_induction with_have
#check with_have.induct

end Test

#exit


open Lean Lean.Meta in
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

namespace OverlappingTest


def f : Nat → Bool -- := fun x => match h : x with
  | 0 => True
  | 1 => False
  | n+1 => f (n - 1)
termination_by f n => n
decreasing_by
  · simp_wf
    apply Nat.lt_succ_of_le
    apply Nat.sub_le

#derive_induction f
#check f.induct

example (n : Nat) : f n ↔ n % 2 = 0 := by
  induction n using f.induct with
  | case1 => simp [f]
  | case2 => simp [f]
  | case3 n IH =>
    have h : n ≠ 0 := sorry
    simp [f, IH]
    cases n with
    | zero => contradiction
    | succ n =>
      rw [Nat.succ_sub_succ, Nat.sub_zero]
      rw [Nat.mod_eq_sub_mod (a := Nat.succ _) (h := Nat.le_add_left 2 n)]
      rw [Nat.add_sub_cancel (m := 2)]
      apply Iff.rfl

#eval tst ``f

#check f.match_1
#check f.match_1.splitter
#check f.match_1.eq_3

#check f._eq_3
#check f._unfold


end OverlappingTest


def foo : Nat → Nat
  | 0 => 0
  | n =>
    have h : n ≠ 0 := sorry
    foo (n - 1)
termination_by foo n => n
decreasing_by
  · simp_wf
    apply Nat.sub_lt
    apply Nat.zero_lt_of_ne_zero h
    apply Nat.zero_lt_one


#derive_induction foo
#check foo.induct

axiom foo.induct_better (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n ≠ 0 → motive (n - 1) → motive n) (x : Nat) : motive x

theorem foo_eq_0 (n : Nat) : foo n = 0 := by
  induction n using foo.induct_better with
  | case1 => simp [foo]
  | case2 n h0 IH => simp [foo]; exact IH



#eval tst ``foo

#check foo._eq_2

set_option pp.match false
set_option pp.proofs.withType false
#check foo.match_1.splitter
