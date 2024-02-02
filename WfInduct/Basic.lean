import Lean

set_option autoImplicit false

open Lean Elab Command Meta

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


def Lean.Meta.MatcherApp.transform (matcherApp : MatcherApp)
    (onParams : Expr → MetaM Expr)
    (onMotive : Array Expr → Expr → MetaM Expr)
    (onAlt : Expr → Expr → MetaM Expr)
    (onRemaining : Array Expr → MetaM (Array Expr)) :
    MetaM MatcherApp := do

  -- TODO: Include discrEq info in MatcherApp, like numAltParams
  let .some matcherInfo ← getMatcherInfo? matcherApp.matcherName
    | throwError "matcher {matcherApp.matcherName} has no MatchInfo found"
  let numDiscrEqs := matcherInfo.getNumDiscrEqs

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

  -- We replace the matcher with the splitter
  -- (TODO: What if there is a splitter in the first place)
  let matchEqns ← Match.getEquationsFor matcherApp.matcherName
  let splitter := matchEqns.splitterName

  let aux := mkAppN (mkConst splitter matcherLevels.toList) params'
  let aux := mkApp aux motive'
  let aux := mkAppN aux discrs'
  unless (← isTypeCorrect aux) do
    check aux
    throwError "failed to transform matcher, type error when constructing new motive:{indentExpr aux}"
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
    alts          := alts'
    remaining     := remaining'
  }

-- From PackDomain
private partial def mkPSigmaCasesOn (y : Expr) (codomain : Expr) (xs : Array Expr) (value : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (y : FVarId) (ys : Array Expr) : MetaM Unit := do
    if ys.size < xs.size - 1 then
      let xDecl  ← xs[ys.size]!.fvarId!.getDecl
      let xDecl' ← xs[ys.size + 1]!.fvarId!.getDecl
      let #[s] ← mvarId.cases y #[{ varNames := [xDecl.userName, xDecl'.userName] }] | unreachable!
      go s.mvarId s.fields[1]!.fvarId! (ys.push s.fields[0]!)
    else
      let ys := ys.push (mkFVar y)
      mvarId.assign (value.replaceFVars xs ys)
  go mvar.mvarId! y.fvarId! #[]
  instantiateMVars mvar


/-- Opens the body of a lambda, _without_ putting the free variable into the local context.
This is used when replacing that paramters with a different expression.
This way it will not be picked up by metavariables.
-/
def removeLamda {α} (e : Expr) (k : FVarId → Expr →  MetaM α) : MetaM α := do
  let .lam _n _d b _bi := ← whnfD e | throwError "removeLamda: expected lambda, got {e}"
  let x ← mkFreshFVarId
  let b := b.instantiate1 (.fvar x)
  k x b


-- Replace calls to oldIH back to calls to the original function. At the end,
-- oldIH better be unused
partial def foldCalls (fn : Expr) (oldIH : FVarId) (e : Expr) : MetaM Expr := do
  let r ← id do
    -- logInfo m!"foldCalls {mkFVar oldIH} {indentExpr e}"
    if ! e.hasAnyFVar (· == oldIH) then
      return e

    if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
      let #[arg, _proof] := e.getAppArgs | unreachable!
      let arg' ← foldCalls fn oldIH arg
      return .app fn arg'

    if let .letE n t v b _ := e then
      let t' ← foldCalls fn oldIH t
      let v' ← foldCalls fn oldIH v
      return ← withLetDecl n t' v' fun x => do
        let b' ← foldCalls fn oldIH (b.instantiate1 x)
        mkLetFVars  #[x] b'

    if let some (n, t, v, b) := e.letFun? then
      let t' ← foldCalls fn oldIH t
      let v' ← foldCalls fn oldIH v
      return ← withLocalDecl n .default t' fun x => do
        let b' ← foldCalls fn oldIH (b.instantiate1 x)
        mkLetFun x v' b'

    if let some matcherApp ← matchMatcherApp? e then
      -- logInfo m!"{matcherApp.matcherName} {goal} {←inferType (Expr.fvar newIH)} => {matcherApp.discrs} {matcherApp.remaining}"
      if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
        let motive' ← lambdaTelescope matcherApp.motive fun motiveArgs motiveBody => do
          unless motiveArgs.size == matcherApp.discrs.size do
            throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"
          -- TODO: Also fold in body of the motive?
          let some (_extra, body) := motiveBody.arrow? | throwError "motive not an arrow"
          mkLambdaFVars motiveArgs body

        let mut alts' : Array Expr := #[]
        for alt in matcherApp.alts, numParams in matcherApp.altNumParams do
          let alt' ← lambdaTelescope alt fun xs alt => do
            unless xs.size = numParams + 1 do
              throwError "unexpected matcher application, alternative must be lambda expression with #{numParams + 1} arguments"
            let alt ← foldCalls fn (xs.back.fvarId!) alt
            mkLambdaFVars xs.pop alt
          alts' := alts'.push alt'

        let matcherApp' := { matcherApp with
          motive        := motive'
          alts          := alts'
          remaining     := #[]
        }
        -- check matcherApp'.toExpr
        -- logInfo m!"matcherApp' {matcherApp'.toExpr}"
        return matcherApp'.toExpr

    if e.getAppArgs.any (·.isFVarOf oldIH) then
      -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
      -- So beta-reduce that definition.

      -- Need to look through theorems here!
      let e' ← withTransparency .all do whnf e
      if e == e' then
        throwError "foldCalls: cannot reduce application of {e.getAppFn} in {indentExpr e} "
      return ← foldCalls fn oldIH e'

    if let .app e1 e2 := e then
      return .app (← foldCalls fn oldIH e1) (← foldCalls fn oldIH e2)

    if let .lam n t body bi := e then
      let t' ← foldCalls fn oldIH t
      return ← withLocalDecl n bi t' fun x => do
        let body' ← foldCalls fn oldIH (body.instantiate1 x)
        mkLambdaFVars #[x] body'

    if let .forallE n t body bi := e then
      let t' ← foldCalls fn oldIH t
      return ← withLocalDecl n bi t' fun x => do
        let body' ← foldCalls fn oldIH (body.instantiate1 x)
        mkForallFVars #[x] body'

    -- Looks like there are more expression forms to handle here
    throwError "foldCalls: cannot eliminate {mkFVar oldIH} from {indentExpr e}"

  -- sanity check for debugging
  if r.hasAnyFVar (· == oldIH) then
    throwError "foldCalls: failed to eliminate {mkFVar oldIH} from {indentExpr r}"
  return r


/--
Given proofs of `P₁`, …, `Pₙ`, returns a proof of `P₁ ∧ … ∧ Pₙ`.
If `n = 0` returns a proof of `True`.
If `n = 1` returns the proof of `P₁`.
-/
def mkAndIntroN : Array Expr → MetaM Expr
| #[] => return mkConst ``True.intro []
| #[e] => return e
| es => es.foldrM (start := es.size - 1) (fun a b => mkAppM ``And.intro #[a,b]) es.back


-- Non-tail-positions: Collect induction hypotheses
-- (TODO: Worth folding with `foldCalls`, like before?)
-- (TODO: Accumulated with a left fold)
-- (TODO: Revert context in the leaf, based on local context?)
partial def collectIHs (fn : Expr) (oldIH newIH : FVarId) (e : Expr) : MetaM (Array Expr) := do
  if ! e.hasAnyFVar (· == oldIH) then
    return #[]

  if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
    let #[arg, proof] := e.getAppArgs  | unreachable!

    let arg' ← foldCalls fn oldIH arg
    let proof' ← foldCalls fn oldIH proof
    let ihs ← collectIHs fn oldIH newIH arg

    return ihs.push (mkAppN (.fvar newIH) #[arg', proof'])

  if let .letE n t v b _ := e then
    let ihs1 ← collectIHs fn oldIH newIH v
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2

  if let some (n, t, v, b) := e.letFun? then
    let ihs1 ← collectIHs fn oldIH newIH v
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2

  if let some matcherApp ← matchMatcherApp? e then
    -- logInfo m!"{matcherApp.matcherName} {Expr.fvar oldIH}/{Expr.fvar newIH} => {matcherApp.discrs} {matcherApp.remaining}"
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
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

        -- Will later be overriden with a type that’s itself a match
        -- statement and the infered alt types
        let dummyGoal := mkConst ``True []

        let motiveBody ← mkArrow eTypeAbst dummyGoal
        mkLambdaFVars motiveArgs motiveBody

      let matcherLevels ← match matcherApp.uElimPos? with
        | none     => pure matcherApp.matcherLevels
        | some pos =>
          let uElim := .zero -- TODO: Double check
          pure <| matcherApp.matcherLevels.set! pos uElim

      -- NB: Do *not* use the splitter here, we want fewer assumptions
      let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
      let aux := mkApp aux motive'
      let aux := mkAppN aux matcherApp.discrs
      unless (← isTypeCorrect aux) do
        throwError "failed to add argument to matcher application, type error when constructing the new motive"
      let altTypes ← arrowDomainsN matcherApp.alts.size (← inferType aux)

      let mut altIHs : Array Expr := #[]
      for alt in matcherApp.alts,
          numParams in matcherApp.altNumParams,
          altType in altTypes do
        let altIH ← forallBoundedTelescope altType (some numParams) fun xs altType => do
          let alt ← try instantiateLambda alt xs[:numParams] catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
          let altIH ← removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope altType (some 1) fun newIH' _goal' => do
              let #[newIH'] := newIH' | unreachable!
              let altIHs ← collectIHs fn oldIH' newIH'.fvarId! alt
              let altIH ← mkAndIntroN altIHs
              mkLambdaFVars #[newIH'] altIH
          mkLambdaFVars xs altIH
        altIHs := altIHs.push altIH

      -- Now figure out the actual motive, with an explicit match
      let motive'' ← lambdaTelescope motive' fun motiveArgs motiveBody => do
        let some (extra, _dummy) := motiveBody.arrow? |
          throwError "motive not an arrow"
        let propMotive ← mkLambdaFVars motiveArgs (.sort levelZero)
        let propAlts ← altIHs.mapM fun altIH =>
          lambdaTelescope altIH fun xs altIH => do
            -- logInfo m!"altIH: {xs} => {altIH}"
            let altType ← inferType altIH
            -- logInfo m!"altIH type: {altType}"
            if altType.hasAnyFVar (· == xs.back.fvarId!) then
              throwError "Type {altType} of alternative {altIH} still depends on the IH"
            mkLambdaFVars xs.pop altType
        let typeMatcherApp := { matcherApp with
          motive := propMotive
          discrs := motiveArgs
          alts := propAlts
          remaining := #[] -- matcherApp.remaining.set! 0 (.fvar newIH)
        }
        mkLambdaFVars motiveArgs (← mkArrow extra typeMatcherApp.toExpr)

      -- Finally, cast the types of the alts as necessary
      -- We need to use the splitter now, else we cannot reduce
      -- the match in the type
      let matchEqns ← Match.getEquationsFor matcherApp.matcherName
      let splitter := matchEqns.splitterName

      let aux := mkAppN (mkConst splitter matcherLevels.toList) matcherApp.params
      let aux := mkApp aux motive''
      let aux := mkAppN aux matcherApp.discrs
      unless (← isTypeCorrect aux) do
        throwError "matcher with final motive is not type correct"
      let altTypes ← arrowDomainsN matcherApp.alts.size (← inferType aux)

      let mut finalAlts := #[]
      for alt in altIHs,
        splitterNumParams in matchEqns.splitterAltNumParams,
        numParams in matcherApp.altNumParams,
        expAltType in altTypes do
        let finalAlt ← forallAltTelescope (← inferType alt) numParams 0 fun ys _eqs args _mask _bodyType => do
          let expAltType ← instantiateForall expAltType ys
          forallBoundedTelescope expAltType (splitterNumParams - ys.size) fun ys2 expAltType => do
            forallBoundedTelescope expAltType (some 1) fun newIH' expAltType => do
              let #[newIH'] := newIH' | unreachable!

              -- logInfo m!"ys: {ys} args: {args} eqs: {_eqs} ys2: {ys2} splitterNumParams: {splitterNumParams}"
              let alt ← try instantiateLambda alt (args.push newIH') catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"

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
              mkLambdaFVars (ys ++ ys2 ++ #[newIH']) (← mkEqMPR proof alt)
        -- logInfo m!"Wrapped IH: {finalAlt}"
        finalAlts := finalAlts.push finalAlt

      -- logInfo m!"Inferred motive for match-in-types: {indentExpr motive''}"
      check motive''

      let matcherApp' := { matcherApp with
        matcherName   := splitter,
        matcherLevels := matcherLevels,
        motive        := motive'',
        alts          := finalAlts,
        remaining     := matcherApp.remaining.set! 0 (.fvar newIH)
      }
      -- logInfo m!"matcherApp' {indentExpr matcherApp'.toExpr}"
      check matcherApp'.toExpr
      return #[ matcherApp'.toExpr ]

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
    -- So beta-reduce that definition.

    -- Need to look through theorems here!
    let e' ← withTransparency .all do whnf e
    if e == e' then
      throwError "collectIHs: cannot reduce application of {e.getAppFn} in {indentExpr e} "
    return ← collectIHs fn oldIH newIH e'

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    throwError "collectIHs: could not collect recursive calls from call {indentExpr e}"

  if let .app e1 e2 := e then
    return (← collectIHs fn oldIH newIH e1) ++ (← collectIHs fn oldIH newIH e2)

  if let .proj _ _ e := e then
    return ← collectIHs fn oldIH newIH e

  if let .forallE n t body bi := e then
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  if let .lam n t body bi := e then
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  if let .mdata _m b := e then
    return ← collectIHs fn oldIH newIH b

  throwError "collectIHs: could not collect recursive calls from {indentExpr e}"

def withLetDecls {α} (vals : Array Expr) (k : Array FVarId → MetaM α) (i : Nat := 0) : MetaM α := do
  if h : i < vals.size then
    let e := vals[i]
    withLetDecl s!"IH{i+1}" e (← inferType e) fun a =>
      withLetDecls vals (fun args => k (args.push a.fvarId!)) (i + 1)
  else
    k #[]
termination_by vals.size - i

-- Because of term duplications we might encounter the same IH multiple times.
-- We deduplicate them (by type, not proof term) here.
-- This could be improved and catch cases where the same IH is used in different contexts.
-- (Cf. `assignSubsumed` in `WF.Fix`)
def deduplicateIHs (vals : Array Expr) : MetaM (Array Expr) := do
  let mut vals' := #[]
  let mut types := #[]
  for v in vals do
    let t ← inferType v
    unless types.contains t do
      vals' := vals'.push v
      types := types.push t
  return vals'

def assertIHs (vals : Array Expr) (mvarid : MVarId) : MetaM MVarId := do
  let mut mvarid := mvarid
  for v in vals.reverse, i in [0:vals.size] do
    mvarid ← mvarid.assert s!"IH{i+1}" (← inferType v) v
  return mvarid

-- Base case: Introduce a new hyp
def createHyp (motiveFVar : FVarId) (fn : Expr) (oldIH newIH : FVarId) (toClear : Array FVarId)
    (goal : Expr) (IHs : Array Expr) (e : Expr) : MetaM Expr := do
  -- logInfo m!"Tail position {e}"
  let IHs := IHs ++ (← collectIHs fn oldIH newIH e)
  let IHs ← deduplicateIHs IHs

  let mvar ← mkFreshExprSyntheticOpaqueMVar goal (tag := `hyp)
  let mut mvarId := mvar.mvarId!
  -- logInfo m!"New hyp 1 {mvarId}"
  mvarId ← assertIHs IHs mvarId
  -- logInfo m!"New hyp 2 {mvarId}"
  for fv in toClear do
    mvarId ← mvarId.tryClear fv
  -- logInfo m!"New hyp 3 {mvarId}"
  mvarId ← mvarId.cleanup
  let (_, _mvarId) ← mvarId.revertAfter motiveFVar
  let mvar ← instantiateMVars mvar
  -- logInfo <| m!"New hyp {_mvarId}" ++ Format.line ++ m!"used as {mvar}"
  pure mvar

partial def buildInductionBody (motiveFVar : FVarId) (fn : Expr) (toClear : Array FVarId)
    (goal : Expr) (oldIH newIH : FVarId) (IHs : Array Expr) (e : Expr) : MetaM Expr := do
  -- logInfo m!"buildInductionBody:{indentExpr e}"

  if e.isDIte then
    let #[_α, c, h, t, f] := e.getAppArgs | unreachable!
    let IHs := IHs ++ (← collectIHs fn oldIH newIH c)
    let c' ← foldCalls fn oldIH c
    let h' ← foldCalls fn oldIH h
    let t' ← withLocalDecl `h .default c' fun h => do
      let t ← instantiateLambda t #[h]
      let t' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH IHs t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => do
      let f ← instantiateLambda f #[h]
      let f' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH IHs f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'

  if let some casesOnApp ← toCasesOnApp? e then
    if casesOnApp.remaining.size == 1 && casesOnApp.remaining[0]!.isFVarOf oldIH then
      let discrs := casesOnApp.indices ++ #[casesOnApp.major]

      let motive' ← lambdaTelescope casesOnApp.motive fun motiveArgs _motiveBody => do
        unless motiveArgs.size == 1 do
          throwError "unexpected matcher application, motive must be lambda expression with 1 argument"

        let mut argTypeAbst ← newIH.getType
        for motiveArg in motiveArgs.reverse, discr in discrs.reverse do
          argTypeAbst := (← kabstract argTypeAbst discr).instantiate1 motiveArg

        let mut goalAbst := goal
        for motiveArg in motiveArgs.reverse, discr in discrs.reverse do
          goalAbst := (← kabstract goalAbst discr).instantiate1 motiveArg

        let motiveBody ← mkArrow argTypeAbst goalAbst
        mkLambdaFVars motiveArgs motiveBody

      let us ← if casesOnApp.propOnly then
        pure casesOnApp.us
      else
        pure ((← getLevel goal) :: casesOnApp.us.tail!)
      -- TODO: Levels
      let aux := mkAppN (mkConst casesOnApp.declName us) casesOnApp.params
      let aux := mkApp aux motive'
      let aux := mkAppN aux discrs
      unless (← isTypeCorrect aux) do
        throwError "failed to add argument to casesOn application, type error when constructing the new motive"
      let mut auxType ← inferType aux

      let mut alts' := #[]
      for alt in casesOnApp.alts,
          numParams in casesOnApp.altNumParams do
        let Expr.forallE _ d b _ ← whnfD auxType | unreachable!
        let alt' ← forallBoundedTelescope d (some numParams) fun xs d => do
          let alt ← try instantiateLambda alt xs catch _ => throwError "unexpected matcher application, insufficient number of parameters in alternative"
          let alt' ← removeLamda alt fun oldIH' alt => do
            let alt' ← forallBoundedTelescope d (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              -- logInfo m!"goal': {goal'}"
              let alt' ← buildInductionBody motiveFVar fn (toClear.push newIH'.fvarId!) goal' oldIH' newIH'.fvarId! IHs alt
              mkLambdaFVars #[newIH'] alt' -- x is the new argument we are adding to the alternative
            mkLambdaFVars xs alt'
          pure alt'
        auxType := b.instantiate1 alt'
        alts' := alts'.push alt'
      let casesOnApp' := { casesOnApp with
        us        := us,
        motive    := motive',
        alts      := alts',
        remaining := casesOnApp.remaining.set! 0 (.fvar newIH)
      }
      -- check matcherApp'.toExpr
      -- logInfo m!"matcherApp' {matcherApp'.toExpr}"
      return casesOnApp'.toExpr

  if let some matcherApp ← matchMatcherApp? e then
    -- logInfo m!"{matcherApp.matcherName} {goal} {←inferType (Expr.fvar newIH)} => {matcherApp.discrs} {matcherApp.remaining}"
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then

      -- Fold recursive calls in params and discrs, and collect IHs
      let mut IHs := IHs
      for param in matcherApp.params do
        IHs := IHs ++ (← collectIHs fn oldIH newIH param)
      for discr in matcherApp.discrs do
        IHs := IHs ++ (← collectIHs fn oldIH newIH discr)

      let matcherApp' ← matcherApp.transform
        (onParams := foldCalls fn oldIH)
        (onMotive := fun xs _body => do
          -- Remove the old IH that was added in mkFix
          -- TODO: mkArrow first, then only one loop over the discrs
          let eType ← newIH.getType
          let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
            let motiveArg := xs[i]!
            let discr     := matcherApp.discrs[i]!
            let eTypeAbst ← kabstract eTypeAbst discr
            return eTypeAbst.instantiate1 motiveArg

          let goalAbst ← matcherApp.discrs.size.foldRevM (init := goal) fun i goalAbst => do
            let motiveArg := xs[i]!
            let discr     := matcherApp.discrs[i]!
            let goalAbst ← kabstract goalAbst discr
            return goalAbst.instantiate1 motiveArg

          mkArrow eTypeAbst goalAbst)
        (onAlt := fun expAltType alt => do
          removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope expAltType (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              let alt' ← buildInductionBody motiveFVar fn (toClear.push newIH'.fvarId!) goal' oldIH' newIH'.fvarId! IHs alt
              mkLambdaFVars #[newIH'] alt')
        (onRemaining := fun _ => pure #[.fvar newIH])

      -- check matcherApp'.toExpr
      -- logInfo m!"matcherApp' {matcherApp'.toExpr}"
      return matcherApp'.toExpr

  if let .letE n t v b _ := e then
    let IHs := IHs ++ (← collectIHs fn oldIH newIH v)
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t' v' fun x => do
      -- Should we keep let declaraions in the inductive theorem?
      -- If not, we can add them to `toClear`.
      let toClear := toClear.push x.fvarId!
      let b' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH IHs (b.instantiate1 x)
      mkLetFVars #[x] b'

  if let some (n, t, v, b) := e.letFun? then
    let IHs := IHs ++ (← collectIHs fn oldIH newIH v)
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLocalDecl n .default t' fun x => do
      -- Should we keep have declaraions in the inductive theorem?
      -- If not, we can add them to `toClear`.
      let toClear := toClear.push x.fvarId!
      let b' ← buildInductionBody motiveFVar fn toClear goal oldIH newIH IHs (b.instantiate1 x)
      -- logInfo m!"x: {x}, v: {v}, b: {b}, b': {b'}"
      mkLetFun x v' b'

  -- logInfo m!"Tail position at end of buildInductionBody: {e}"
  createHyp motiveFVar fn oldIH newIH toClear goal IHs e

partial def findFixF {α} (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  lambdaTelescope e fun params body => do
    if body.isAppOf ``WellFounded.fixF then
      k params body
    else
      let body' ← whnf body
      if body == body' then
        throwError "Term {body} is not a fixF application"
      else
        findFixF body' (fun args e' => k (params ++ args) e')

def deriveUnaryInduction (name : Name) : MetaM Name := do
  let info ← getConstInfo name
  let e := Expr.const name (info.levelParams.map mkLevelParam)
  findFixF e fun params body => do
    unless params.size > 0 do
      throwError "Term {e} is not a lambda application"
    body.withApp fun f fixArgs => do
      -- logInfo f!"{fixArgs}"
      unless f.isConstOf ``WellFounded.fixF do
        throwError "Term isn’t application of {``WellFounded.fixF}, but of {f}"
      let #[argType, rel, _motive, body, arg, acc] := fixArgs |
        throwError "Application of WellFounded.fixF has wrong arity {fixArgs.size}"
      unless ← isDefEq arg params.back do
        throwError "fixF application argument {arg} is not function argument "
      let [argLevel, _motiveLevel] := f.constLevels! | unreachable!
      -- logInfo body
      -- mkFresh

      let motiveType ← mkArrow argType (.sort levelZero)
      withLocalDecl `motive .default motiveType fun motive => do

      let e' := mkAppN (.const ``WellFounded.fixF [argLevel, levelZero]) #[argType, rel, motive]
      let fn := mkAppN e params.pop
      let body' ← forallTelescope (← inferType e').bindingDomain! fun xs _ => do
        let #[param, genIH] := xs | unreachable!
        -- open body with the same arg
        let body ← instantiateLambda body #[param]
        removeLamda body fun oldIH body => do
          let body' ← buildInductionBody motive.fvarId! fn #[genIH.fvarId!] (.app motive param) oldIH genIH.fvarId! #[] body
          if body'.hasAnyFVar (· == oldIH) then
            throwError m!"Did not fully eliminate {mkFVar oldIH} from induction principle body:{indentExpr body}"
          mkLambdaFVars #[param, genIH] body'

      let e' := mkAppN e' #[body', arg, acc]

      let e' ← mkLambdaFVars #[params.back] e'
      let mvars ← getMVarsNoDelayed e'
      for mvar in mvars, i in [:mvars.size] do
        mvar.setUserName s!"case{i+1}"
      let e' ← mkLambdaFVars (binderInfoForMVars := .default) (mvars.map .mvar) e'

      -- We could pass (usedOnly := true) below, and get nicer induction principles that
      -- do do not mention odd unused parameters.
      -- But the downside is that automatic instantiation of the principle (e.g. when
      -- deriving the binary one) is much harder, as one would have to infer which parameters
      -- to pass. So for now lets just keep them around.
      let e' ← mkLambdaFVars (binderInfoForMVars := .default) (params.pop ++ #[motive]) e'
      let e' ← instantiateMVars e'


      let eTyp ← inferType e'
      -- logInfo m!"eTyp: {eTyp}"
      -- logInfo m!"e has MVar: {e'.hasMVar}"
      check e'

      let inductName := .append name `induct
      addDecl <| Declaration.defnDecl {
          name := inductName, levelParams := info.levelParams, type := eTyp, value := e'
          hints := ReducibilityHints.regular 0
          safety := DefinitionSafety.safe
      }
      return inductName

/--
In the type of `value`, reduce
* `PSigma.casesOn (PSigma.mk a b) (fun x y => k x y)  -->  k a b`
* `foo._unary (PSigma.mk a b) (fun x y => k x y)      -->  foo a b`
and then wrap `e` in an appropriate type hint.
-/
def cleanPackedArgs (eqnInfo : WF.EqnInfo) (value : Expr) : MetaM Expr := do
  -- TODO: This implementation is a bit haphazard.
  -- Simply use Meta.transform instead.
  let name := eqnInfo.declNames[0]!
  let foldLemma ← do
    let ci ← getConstInfoDefn name
    let us := ci.levelParams
    let naryConst := mkConst name (us.map mkLevelParam)
    lambdaTelescope ci.value fun xs body => do
      let type ← mkEq body (mkAppN naryConst xs)
      mkLambdaFVars xs (← mkExpectedTypeHint (← mkEqRefl body) type)
  let (result, _) ← simp (← inferType value) {
      config := {
        -- Empirically determinied minially required simp options
        beta := true
        iota := true
        zeta := false
        eta := false
        etaStruct := .none
        proj := false
      }
      simpTheorems := (← SimpTheoremsArray.addTheorem {} (.decl name) foldLemma)
  }
  mkExpectedTypeHint value result.expr

def deriveBinaryInduction (eqnInfo : WF.EqnInfo) (unaryInductName : Name): MetaM Unit := do
  if eqnInfo.declNames.size > 1 then
    throwError "Mutual recursion not supported"
  let name := eqnInfo.declNames[0]!

  let ci ← getConstInfoDefn name
  let unaryInductCI ← getConstInfo unaryInductName
  let us := unaryInductCI.levelParams
  -- We determine the arity based on the value, not the type, like the WF translation does
  -- But we get the parameters from the type, because they have better names there
  let arity ← lambdaTelescope ci.value fun xs _body => pure xs.size
  unless arity > eqnInfo.fixedPrefixSize + 1 do
    throwError "Unexpected lambda arity in body of {name}"
  let value ← forallBoundedTelescope ci.type arity fun xs _ => do
    unless arity = xs.size do
      throwError "Not enough foralls in type of {name}"
    let body ← instantiateLambda ci.value xs
    let fixedParams : Array Expr := xs[:eqnInfo.fixedPrefixSize]
    let targetParams : Array Expr := xs[eqnInfo.fixedPrefixSize:]

    let packedArg ← body.withApp fun f args => do
      unless f.isConstOf eqnInfo.declNameNonRec do
        throwError "{name} is not defined via {eqnInfo.declNameNonRec}, but {f}"
      unless args.size = eqnInfo.fixedPrefixSize + 1 do
        throwError "unexpected number of parameters to {eqnInfo.declNameNonRec} "
      -- unless args.pop = fixedParams do
      --  throwErrorAt ident "unexpected number of parameters to {eqnInfo.declNameNonRec} "
      return args.back

    let elimInfo ← getElimExprInfo (mkConst unaryInductName (us.map mkLevelParam))
    -- We assume the eliminator created by deriveUnaryInduction
    -- has fixed prefix and motive in the beginning and target at the end
    unless elimInfo.motivePos = eqnInfo.fixedPrefixSize do
        throwError "unary induction principle does not start with fixed prefix"
    let #[targetPos] := elimInfo.targetsPos
      | throwError "unary induction has more than one target pos?"
    -- unless targetPos = elimInfo.motivePos + 1 + elimInfo.altsInfo.size do
    --  throwError "unary induction has target not at the end?"

    let unaryElimType ← instantiateForall elimInfo.elimType xs[:eqnInfo.fixedPrefixSize]

    let motiveType ← mkForallFVars targetParams (.sort levelZero)
    withLocalDecl `motive .default motiveType fun motive => do

    let packedDomain ← id do -- TODO: Expose in PackDomain
        let mut d ← inferType targetParams.back
        for x in targetParams.pop.reverse do
          d ← mkAppOptM ``PSigma #[some (← inferType x), some (← mkLambdaFVars #[x] d)]
        return d

    let unaryMotive ← do
      withLocalDecl `x .default packedDomain fun packed => do
        let codomain := .sort levelZero
          let value := mkAppN motive targetParams
        mkLambdaFVars #[packed] (← mkPSigmaCasesOn packed codomain targetParams value)
    let unaryElimType ← instantiateForall unaryElimType #[unaryMotive]

    let remaining_alts : Nat := targetPos - eqnInfo.fixedPrefixSize - 1
    forallBoundedTelescope unaryElimType remaining_alts fun alts _unaryElimType => do
        let value := elimInfo.elimExpr
        let value := mkAppN value fixedParams
        let value := mkApp value unaryMotive
        let value := mkAppN value alts
        let value := mkApp value packedArg
        let value ← mkLambdaFVars targetParams value
        let value ← mkLambdaFVars alts value
        let value ← mkLambdaFVars #[motive] value
        let value ← mkLambdaFVars fixedParams value
        let value ← cleanPackedArgs eqnInfo value
        return value

  let inductName := .append name `induct
  -- logInfo m!"Final {value}"
  check value
  addDecl <| Declaration.defnDecl {
    name := inductName,
    levelParams := us,
    type := (← inferType value),
    value := value,
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
}

def deriveInduction (name : Name) : MetaM Unit := do
  if let some eqnInfo := WF.eqnInfoExt.find? (← getEnv) name then
    let unaryInductName ← deriveUnaryInduction eqnInfo.declNameNonRec
    unless eqnInfo.declNameNonRec = name do
      deriveBinaryInduction eqnInfo unaryInductName
  else
    _ ← deriveUnaryInduction name

elab "#derive_induction " ident:ident : command => runTermElabM fun _xs => do
  let [name] ← resolveGlobalConst ident
    | throwErrorAt ident m!"ambiguous identifier"
  deriveInduction name
