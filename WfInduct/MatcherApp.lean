import Lean

set_option autoImplicit false

open Lean Meta


def matchMatcherOrCasesOnApp? (e : Expr) : MetaM (Option MatcherApp) := do
  if let some matcherApp ← matchMatcherApp? e then
    return some matcherApp
  if let some casesOnApp ← toCasesOnApp? e then
    return some {
      matcherName := casesOnApp.declName
      matcherLevels := casesOnApp.us.toArray
      uElimPos? := if casesOnApp.propOnly then none else some 0
      params := casesOnApp.params
      motive := casesOnApp.motive
      discrs := casesOnApp.indices.push casesOnApp.major
      alts := casesOnApp.alts
      remaining := casesOnApp.remaining
      altNumParams := casesOnApp.altNumParams
    }
  return none


/--
Removes `fvarId` from the local context, and replaces occurrences of it with `e`.
It is the responsibility of the caller to ensure that `e` is well-typed in the context
of any occurrence of `fvarId`.
-/
def Lean.Meta.withReplaceFVarId {α} (fvarId : FVarId) (e : Expr) : MetaM α → MetaM α :=
  withReader fun ctx => { ctx with
    lctx := ctx.lctx.replaceFVarId fvarId e
    localInstances := ctx.localInstances.erase fvarId }

-- Just a wrapper that implements local context hygiene, to be upstreamed
open Match in
partial def forallAltTelescope {α} (altType : Expr) (altNumParams numDiscrEqs : Nat)
    (k : (ys : Array Expr) → (eqs : Array Expr) → (args : Array Expr) → (mask : Array Bool) → (type : Expr) → MetaM α)
    : MetaM α := do
  go #[] #[] #[] #[] 0 altType
where
  go (ys : Array Expr) (eqs : Array Expr) (args : Array Expr) (mask : Array Bool) (i : Nat) (type : Expr) : MetaM α := do
    let type ← whnfForall type
    if i < altNumParams then
      let Expr.forallE n d b .. := type
        | throwError "expecting {altNumParams} parameters, including {numDiscrEqs} equalities, but found type{indentExpr altType}"
      if i < altNumParams - numDiscrEqs then
        let d ← unfoldNamedPattern d
        withLocalDeclD n d fun y => do
          let typeNew := b.instantiate1 y
          if let some (_, lhs, rhs) ← matchEq? d then
            if lhs.isFVar && ys.contains lhs && args.contains lhs && Lean.Meta.Match.forallAltTelescope.isNamedPatternProof typeNew y then
               let some j  := ys.getIdx? lhs | unreachable!
               let ys      := ys.eraseIdx j
               let some k  := args.getIdx? lhs | unreachable!
               let mask    := mask.set! k false
               let args    := args.map fun arg => if arg == lhs then rhs else arg
               let arg     ← mkEqRefl rhs
               let typeNew := typeNew.replaceFVar lhs rhs
               return ← withReplaceFVarId lhs.fvarId! rhs do
                withReplaceFVarId y.fvarId! arg do
                  go ys eqs (args.push arg) (mask.push false) (i+1) typeNew
          go (ys.push y) eqs (args.push y) (mask.push true) (i+1) typeNew
      else
        let arg ← if let some (_, _, rhs) ← matchEq? d then
          mkEqRefl rhs
        else if let some (_, _, _, rhs) ← matchHEq? d then
          mkHEqRefl rhs
        else
          throwError "unexpected match alternative type{indentExpr altType}"
        withLocalDeclD n d fun eq => do
          let typeNew := b.instantiate1 eq
          go ys (eqs.push eq) (args.push arg) (mask.push false) (i+1) typeNew
    else
      let type ← unfoldNamedPattern type
      /- Recall that alternatives that do not have variables have a `Unit` parameter to ensure
         they are not eagerly evaluated. -/
      if ys.size == 1 then
        if (← inferType ys[0]!).isConstOf ``Unit && !(← dependsOn type ys[0]!.fvarId!) then
          let rhs := mkConst ``Unit.unit
          return ← withReplaceFVarId ys[0]!.fvarId! rhs do
          return (← k #[] #[] #[rhs] #[false] type)
      k ys eqs args mask type

/--
Given `n` and a type `α₁ → α₂ → ... → αₙ → Sort u`, returns the types `α₁, α₂, ..., αₙ`.

This can be used to infer the expected type of the alternatives when constructing a `MatcherApp`.
-/
def arrowDomainsN (n : Nat) (type : Expr) : MetaM (Array Expr) := do
  let mut type := type
  let mut ts := #[]
  for i in [:n] do
    type ← whnfForall type
    let Expr.forallE _ α β _ ← pure type | throwError "expected {n} arguments, got {i}"
    if β.hasLooseBVars then throwError "unexpected dependent type"
    ts := ts.push α
    type := β
  return ts

/-- Iterated `mkArrow`. Also see `arrowDomainsN`. -/
def mkArrowN (ds : Array Expr) (e : Expr) : CoreM Expr := ds.foldrM mkArrow e


/--
Performs a possibly type-changing transformation to a `MatcherApp`.

* `onParams` is run on each parameter and discrimitant
* `onMotive` runs on the body of the motive, and is passed the motive parameters
  (same number as discrs)
* `onAlt` runs on each alternative, and is passed the expected type of the alternative,
   as inferred from the motive
* `onRemaining` runs on the remaining arguments (and may change their number)

If `useSplitter` is true, the matcher is replaced with the splitter.
NB: Not all code can handle a `MatcherApp` where `matcherName` is a splitter.

This function works even if the the type of alternatives do *not* fit the inferred type. This
allows you to post-process the `MatcherApp` with `MatcherApp.inferMatchType`, which will
infer a type, given all the alternatives.
-/
def Lean.Meta.MatcherApp.transform (matcherApp : MatcherApp)
    (useSplitter := false)
    (onParams : Expr → MetaM Expr := pure)
    (onMotive : Array Expr → Expr → MetaM Expr := fun _ e => pure e)
    (onAlt : Expr → Expr → MetaM Expr := fun _ e => pure e)
    (onRemaining : Array Expr → MetaM (Array Expr) := pure) :
    MetaM MatcherApp := do

  -- We also handle CasesOn applications here, and need to treat them specially in a
  -- few places.
  -- TODO: Expand MatcherApp with the necessary fields to make this more uniform
  -- (in particular, include discrEq and whether there is a splitter)
  let isCasesOn := isCasesOnRecursor (← getEnv) matcherApp.matcherName

  let numDiscrEqs ←
    if isCasesOn then pure 0 else
    match ← getMatcherInfo? matcherApp.matcherName with
    | some info => pure info.getNumDiscrEqs
    | none      => throwError "matcher {matcherApp.matcherName} has no MatchInfo found"

  let params' ← matcherApp.params.mapM onParams
  let discrs' ← matcherApp.discrs.mapM onParams

  let (motive', uElim) ← lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
    let motiveBody' ← onMotive motiveArgs motiveBody
    return (← mkLambdaFVars motiveArgs motiveBody', ← getLevel motiveBody')

  let matcherLevels ← match matcherApp.uElimPos? with
    | none     => pure matcherApp.matcherLevels
    | some pos => pure <| matcherApp.matcherLevels.set! pos uElim

  if useSplitter && !isCasesOn then
    -- We replace the matcher with the splitter
    let matchEqns ← Match.getEquationsFor matcherApp.matcherName
    let splitter := matchEqns.splitterName

    let aux := mkAppN (mkConst splitter matcherLevels.toList) params'
    let aux := mkApp aux motive'
    let aux := mkAppN aux discrs'
    unless (← isTypeCorrect aux) do
      logError m!"failed to transform matcher, type error when constructing new motive:{indentExpr aux}"
      check aux
    let altTypes ← arrowDomainsN matcherApp.alts.size (← inferType aux)

    let mut alts' := #[]
    for alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        splitterNumParams in matchEqns.splitterAltNumParams,
        altType in altTypes do
      let alt' ← forallAltTelescope (← inferType alt) (numParams - numDiscrEqs) 0 fun ys _eqs args _mask _bodyType => do
        let altType ← instantiateForall altType ys
        -- The splitter inserts its extra paramters after the first ys.size parameters, before
        -- the parameters for the numDiscrEqs
        forallBoundedTelescope altType (splitterNumParams - ys.size) fun ys2 altType => do
          forallBoundedTelescope altType numDiscrEqs fun ys3 altType => do
          let alt ← try instantiateLambda alt (args ++ ys3)
                    catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
          let alt' ← onAlt altType alt
          mkLambdaFVars (ys ++ ys2 ++ ys3) alt'
      alts' := alts'.push alt'

    let remaining' ← onRemaining matcherApp.remaining

    return { matcherApp with
      matcherName   := splitter
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      altNumParams  := matchEqns.splitterAltNumParams
      alts          := alts'
      remaining     := remaining'
    }
  else
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) params'
    let aux := mkApp aux motive'
    let aux := mkAppN aux discrs'
    unless (← isTypeCorrect aux) do
      -- check aux
      logError m!"failed to transform matcher, type error when constructing new motive:{indentExpr aux}"
      check aux
    let altTypes ← arrowDomainsN matcherApp.alts.size (← inferType aux)

    let mut alts' := #[]
    for alt in matcherApp.alts,
        numParams in matcherApp.altNumParams,
        altType in altTypes do
      let alt' ← forallBoundedTelescope altType numParams fun xs altType => do
        let alt ← instantiateLambda alt xs
          let alt' ← onAlt altType alt
          mkLambdaFVars xs alt'
      alts' := alts'.push alt'

    let remaining' ← onRemaining matcherApp.remaining

    return { matcherApp with
      matcherLevels := matcherLevels
      params        := params'
      motive        := motive'
      discrs        := discrs'
      alts          := alts'
      remaining     := remaining'
    }


/--
Given a `MatcherApp`, replaces the motive with one that is inferred from the actual types of the
alternatives.

For example, given
```
(match (motive := Nat → Unit → ?) n with
 0 => 1
 _ => true) ()
```
(for any `?`; this will be ignored) will give this type
```
(match n with
 | 0 => Nat
 | _ => Bool)
```

The given `MatcherApp` must not use a splitter in `matcherName`.
The resulting expression *will* use the splitter corresponding to `matcherName` (this is necessary
for the construction).

Interally, this needs to reduce the matcher in a given branch; this is done using
`Split.simpMatchTarget`.
-/
def Lean.Meta.MatcherApp.inferMatchType (matcherApp : MatcherApp) : MetaM MatcherApp := do
  -- In matcherApp.motive, replace the (dummy) matcher body with a type
  -- derived from the inferred types of the alterantives
  let nExtra := matcherApp.remaining.size
  matcherApp.transform (useSplitter := true)
    (onMotive := fun motiveArgs body => do
      let extraParams ← arrowDomainsN nExtra body
      let propMotive ← mkLambdaFVars motiveArgs (.sort levelZero)
      let propAlts ← matcherApp.alts.mapM fun termAlt =>
        lambdaTelescope termAlt fun xs termAltBody => do
          -- We have alt parameters and parameters corresponding to the extra args
          let xs1 := xs[0 : xs.size - nExtra]
          let xs2 := xs[xs.size - nExtra : xs.size]
          -- logInfo m!"altIH: {xs} => {altIH}"
          let altType ← inferType termAltBody
          for x in xs2 do
            if altType.hasAnyFVar (· == x.fvarId!) then
              throwError "Type {altType} of alternative {termAlt} still depends on {x}"
          -- logInfo m!"altIH type: {altType}"
          mkLambdaFVars xs1 altType
      let matcherLevels ← match matcherApp.uElimPos? with
        | none     => pure matcherApp.matcherLevels
        | some pos => pure <| matcherApp.matcherLevels.set! pos levelOne
      let typeMatcherApp := { matcherApp with
        motive := propMotive
        matcherLevels := matcherLevels
        discrs := motiveArgs
        alts := propAlts
        remaining := #[]
      }
      mkArrowN extraParams typeMatcherApp.toExpr
    )
    (onAlt := fun expAltType alt => do
      let altType ← inferType alt
      let eq ← mkEq expAltType altType
      let proof ← mkFreshExprSyntheticOpaqueMVar eq
      let goal := proof.mvarId!
      -- logInfo m!"Goal: {goal}"
      let goal ← Split.simpMatchTarget goal
      -- logInfo m!"Goal after splitting: {goal}"
      try
        goal.refl
      catch _ =>
        logInfo m!"Cannot close goal after splitting: {goal}"
        goal.admit
      mkEqMPR proof alt
    )
