/-
Syntactic pre-pass: replace every `ValUse` of a `ValDef` whose right-hand
side is a `FuncValue` with that `FuncValue` itself, and drop those
`ValDef`s from their `BlockValue`. This is what lets `eval` (`Eval.lean`)
stay a plain structurally-recursive function over `Expr`: without this
pass, `Apply(ValUse f, args)` would need to look up `f`'s value in the
environment at eval time, and since that value is itself an `Expr`
(`FuncValue`) whose evaluation isn't otherwise bound, faithfully modelling
"apply what's bound to a `ValUse`" would require a real closure `Value`
that captures an `Env` — which breaks structural recursion (see `Eval.lean`
's "no closures" module docstring).

## Why this is sound

The task this pass exists for is a contract's local `def` used more than
once (a real downstream example: a helper computing a given token amount,
used twice), which the ErgoScript compiler represents as a `ValDef`
binding id `f` to a `FuncValue`, called at each use site via
`Apply(ValUse f, args)` — *not* inlined at each call site (that's what the
compiler does for a local `def` used only once). Evaluating a `FuncValue`
ValDef's right-hand side can never itself fail (`eval`'s `.funcValue` case,
if it were reached standalone, has no side effects to speak of — it would
just be "build a closure"), so dropping that `ValDef` from the environment
and substituting its literal body at every use is exactly the same
computation `eval` would otherwise perform lazily, just done once,
syntactically, ahead of time, instead of once per `Apply`. Differential
testing against sigma-rust's real evaluator (`difftest/`) covers this pass
empirically, on top of this argument.

## The id-shadowing subtlety this pass has to get right

The compiler's id-assignment scheme *reuses* the outer `ValDef`'s numeric
id as the sole argument id of the `FuncValue` it's bound to — confirmed by
inspecting a real exported downstream tree, where `ValDef` id 11 is bound
to `.funcValue [(11, SType.sBox)] body`, i.e. the function's own
*parameter* is also numbered 11. Inside `body`, `ValUse 11` means "the
parameter" (the nearer, lexically-enclosing binder), not "recurse into the
function being defined" — ordinary shadowing. A naive *global* find-and
-replace of every `ValUse 11` with the `FuncValue` itself would therefore
wrongly rewrite the function's own parameter references too.

`rewriteExpr` avoids this by threading its substitution map `m` downward
through `funcValue`, removing any entries whose id collides with one of
that `funcValue`'s own parameter ids before recursing into its body — so a
`ValUse` of a locally-shadowed id is left alone, while a `ValUse` of a
genuinely enclosing to-be-inlined `FuncValue` id is substituted. `m` itself
is built *incrementally*, growing as `rewriteDefs` walks each
`BlockValue`'s `ValDef` list left to right (mirroring the real scoping: a
`ValDef`'s right-hand side can only reference *earlier* `ValDef`s in the
same/enclosing block, never later ones), so a to-be-inlined `FuncValue`'s
own body is *itself* already fully rewritten (any further to-be-inlined
`ValUse`s inside it resolved) by the time it's substituted at a later call
site — no re-rewriting of a substituted-in subtree is ever needed.

## Why there's no global-distinctness precondition

This pass does not reject a tree (return `none`) just because a `ValDef`
id repeats, even though the compiler's ids come from one incrementing
counter: a real exported downstream tree can still have the same id bound
more than once. `collectValDefIds` on one such tree finds ids
`4,5,6` bound twice and id `13` bound *three* times — the compiler resets
its id counter (or reuses a small pool) independently inside each branch
of a multi-way mutually-exclusive `if` (e.g. a contract with several
alternative spending actions), since those branches are mutually
exclusive at runtime and their `ValDef`s are never
simultaneously live. A global-distinctness precondition would reject this
real, correct, compiler-produced tree, so none is enforced.

`inlineFuns` is unconditionally safe against this kind of reuse regardless,
by construction, with no precondition needed: `m` is an ordinary immutable
list threaded *linearly* through one call chain, so
- **sibling branches never share map state.** `rewriteExpr`'s `.ifExpr c t
  f` (and every other multi-child case) calls `rewriteExpr m t` and
  `rewriteExpr m f` with the *same* input `m`; whatever `t`'s own
  processing extends `m` with is local to that call and is simply
  discarded once `rewriteExpr m t` returns — `f` never sees it. Two
  branches reusing id `4` for unrelated `ValDef`s therefore can't collide.
- **nested reuse (proper shadowing) is also fine.** `rewriteDefs`
  *prepends* each new `ValDef` onto the front of `m`, and lookups
  (`List.find?`) return the first — i.e. innermost/most recent — match. A
  `ValDef` id `4` inside a block nested under another `ValDef` id `4`
  correctly shadows the outer one, exactly like ordinary lexical scoping.
- The one case that genuinely needed care — a `FuncValue`'s own parameter
  id coinciding with its enclosing `ValDef`'s id (the "id-shadowing
  subtlety" above) — is handled separately, by `funcValue`'s explicit
  `m.filter` before recursing into the body.

`inlineFuns` therefore always returns `some`; see its doc comment for why
the `Option Expr` return type is kept anyway.
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean

mutual
/-- Collect every `ValDef` id bound anywhere in `e` — used only to check
    the "all `ValDef` ids distinct" precondition (see module docstring).
    Walks into every sub-expression, including inside `FuncValue` bodies
    and `BlockValue`-nested `ValDef` right-hand sides. -/
def collectValDefIds : Expr → List Nat
  | .const _ => []
  | .constPlaceholder _ _ => []
  | .blockValue defs result => collectValDefIdsFromDefs defs ++ collectValDefIds result
  | .valUse _ _ => []
  | .outputs => []
  | .height => []
  | .selfBox => []
  | .inputs => []
  | .context => []
  | .calcBlake2b256 e => collectValDefIds e
  | .deserializeContext _ _ => []
  | .atLeast b i => collectValDefIds b ++ collectValDefIds i
  | .mapOf i m _ => collectValDefIds i ++ collectValDefIds m
  | .byIndex c i d =>
      collectValDefIds c ++ collectValDefIds i ++
        (match d with | some e => collectValDefIds e | none => [])
  | .sigmaOr items => collectValDefIdsList items
  | .sigmaAnd items => collectValDefIdsList items
  | .createProveDlog e => collectValDefIds e
  | .boolToSigmaProp e => collectValDefIds e
  | .binOp _ l r => collectValDefIds l ++ collectValDefIds r
  | .andOf e => collectValDefIds e
  | .orOf e => collectValDefIds e
  | .logicalNot e => collectValDefIds e
  | .ifExpr c t f => collectValDefIds c ++ collectValDefIds t ++ collectValDefIds f
  | .extractScriptBytes e => collectValDefIds e
  | .extractAmount e => collectValDefIds e
  | .extractId e => collectValDefIds e
  | .extractRegisterAs e _ _ => collectValDefIds e
  | .optionGet e => collectValDefIds e
  | .optionIsDefined e => collectValDefIds e
  | .optionGetOrElse e d => collectValDefIds e ++ collectValDefIds d
  | .getVar _ _ => []
  | .collection _ items => collectValDefIdsList items
  | .tuple items => collectValDefIdsList items
  | .selectField e _ => collectValDefIds e
  | .sizeOf e => collectValDefIds e
  | .sliceOf i f u => collectValDefIds i ++ collectValDefIds f ++ collectValDefIds u
  | .filterOf i c _ => collectValDefIds i ++ collectValDefIds c
  | .existsOf i c _ => collectValDefIds i ++ collectValDefIds c
  | .forAllOf i c _ => collectValDefIds i ++ collectValDefIds c
  | .foldOf i z f => collectValDefIds i ++ collectValDefIds z ++ collectValDefIds f
  | .appendOf i c => collectValDefIds i ++ collectValDefIds c
  | .funcValue _ body => collectValDefIds body
  | .apply f args => collectValDefIds f ++ collectValDefIdsList args
  | .methodCall o _ _ args => collectValDefIds o ++ collectValDefIdsList args
  | .propertyCall o _ _ => collectValDefIds o
  | .upcast e _ => collectValDefIds e
  | .downcast e _ => collectValDefIds e
  | .negation e => collectValDefIds e
  | .byteArrayToBigInt e => collectValDefIds e
  | .byteArrayToLong e => collectValDefIds e

def collectValDefIdsList : List Expr → List Nat
  | [] => []
  | e :: rest => collectValDefIds e ++ collectValDefIdsList rest

def collectValDefIdsFromDefs : List (Nat × Expr) → List Nat
  | [] => []
  | (id, rhs) :: rest => id :: (collectValDefIds rhs ++ collectValDefIdsFromDefs rest)
end

/-- `true` iff `ids` contains a repeated element. -/
def hasDup : List Nat → Bool
  | [] => false
  | n :: rest => rest.contains n || hasDup rest

def isFuncValue : Expr → Bool
  | .funcValue _ _ => true
  | _ => false

/-- The substitution map: `(ValDef id, its already-rewritten FuncValue
    right-hand side)`, threaded and grown by `rewriteDefs` as it walks a
    `BlockValue`'s `ValDef` list left to right. -/
abbrev FuncMap := List (Nat × Expr)

mutual
/-- Rewrite `e` under substitution map `m` (see module docstring). -/
def rewriteExpr (m : FuncMap) : Expr → Expr
  | .const v => .const v
  | .constPlaceholder id tpe => .constPlaceholder id tpe
  | .blockValue defs result =>
      let (m', defs') := rewriteDefs m defs
      .blockValue defs' (rewriteExpr m' result)
  | .valUse id tpe =>
      match m.find? (fun p => p.1 == id) with
      | some (_, funcE) => funcE
      | none => .valUse id tpe
  | .outputs => .outputs
  | .height => .height
  | .selfBox => .selfBox
  | .inputs => .inputs
  | .context => .context
  | .calcBlake2b256 e => .calcBlake2b256 (rewriteExpr m e)
  | .deserializeContext v t => .deserializeContext v t
  | .atLeast b i => .atLeast (rewriteExpr m b) (rewriteExpr m i)
  | .mapOf i f t => .mapOf (rewriteExpr m i) (rewriteExpr m f) t
  | .byIndex c i d =>
      .byIndex (rewriteExpr m c) (rewriteExpr m i)
        (match d with
          | some x => some (rewriteExpr m x)
          | none => none)
  | .sigmaOr items => .sigmaOr (rewriteExprList m items)
  | .sigmaAnd items => .sigmaAnd (rewriteExprList m items)
  | .createProveDlog e => .createProveDlog (rewriteExpr m e)
  | .boolToSigmaProp e => .boolToSigmaProp (rewriteExpr m e)
  | .binOp k l r => .binOp k (rewriteExpr m l) (rewriteExpr m r)
  | .andOf e => .andOf (rewriteExpr m e)
  | .orOf e => .orOf (rewriteExpr m e)
  | .logicalNot e => .logicalNot (rewriteExpr m e)
  | .ifExpr c t f => .ifExpr (rewriteExpr m c) (rewriteExpr m t) (rewriteExpr m f)
  | .extractScriptBytes e => .extractScriptBytes (rewriteExpr m e)
  | .extractAmount e => .extractAmount (rewriteExpr m e)
  | .extractId e => .extractId (rewriteExpr m e)
  | .extractRegisterAs e r t => .extractRegisterAs (rewriteExpr m e) r t
  | .optionGet e => .optionGet (rewriteExpr m e)
  | .optionIsDefined e => .optionIsDefined (rewriteExpr m e)
  | .optionGetOrElse e d => .optionGetOrElse (rewriteExpr m e) (rewriteExpr m d)
  | .getVar v t => .getVar v t
  | .collection t items => .collection t (rewriteExprList m items)
  | .tuple items => .tuple (rewriteExprList m items)
  | .selectField e i => .selectField (rewriteExpr m e) i
  | .sizeOf e => .sizeOf (rewriteExpr m e)
  | .sliceOf i f u => .sliceOf (rewriteExpr m i) (rewriteExpr m f) (rewriteExpr m u)
  | .filterOf i c t => .filterOf (rewriteExpr m i) (rewriteExpr m c) t
  | .existsOf i c t => .existsOf (rewriteExpr m i) (rewriteExpr m c) t
  | .forAllOf i c t => .forAllOf (rewriteExpr m i) (rewriteExpr m c) t
  | .foldOf i z f => .foldOf (rewriteExpr m i) (rewriteExpr m z) (rewriteExpr m f)
  | .appendOf i c => .appendOf (rewriteExpr m i) (rewriteExpr m c)
  | .funcValue args body =>
      -- Shadow: drop any `m` entry whose id collides with one of this
      -- lambda's own parameter ids before recursing into `body` — see
      -- module docstring's "id-shadowing subtlety".
      let argIds := args.map Prod.fst
      let m' := m.filter (fun p => !argIds.contains p.1)
      .funcValue args (rewriteExpr m' body)
  | .apply f args => .apply (rewriteExpr m f) (rewriteExprList m args)
  | .methodCall o ti mi args => .methodCall (rewriteExpr m o) ti mi (rewriteExprList m args)
  | .propertyCall o ti mi => .propertyCall (rewriteExpr m o) ti mi
  | .upcast e t => .upcast (rewriteExpr m e) t
  | .downcast e t => .downcast (rewriteExpr m e) t
  | .negation e => .negation (rewriteExpr m e)
  | .byteArrayToBigInt e => .byteArrayToBigInt (rewriteExpr m e)
  | .byteArrayToLong e => .byteArrayToLong (rewriteExpr m e)
termination_by e => sizeOf e

def rewriteExprList (m : FuncMap) : List Expr → List Expr
  | [] => []
  | e :: rest => rewriteExpr m e :: rewriteExprList m rest
termination_by es => sizeOf es

/-- Rewrite a `BlockValue`'s `ValDef` list left to right, growing `m` with
    every `FuncValue`-bound `ValDef` encountered (and dropping it from the
    emitted list) so that later `ValDef`s/the enclosing `result` can use
    it — mirrors real ErgoTree scoping (a `ValDef` can only reference
    *earlier* bindings). Returns the map as grown by the *whole* list
    (for the caller to use on `result`) together with the surviving,
    rewritten defs. -/
def rewriteDefs (m : FuncMap) : List (Nat × Expr) → (FuncMap × List (Nat × Expr))
  | [] => (m, [])
  | (id, rhs) :: rest =>
      let rhs' := rewriteExpr m rhs
      if isFuncValue rhs' then
        rewriteDefs ((id, rhs') :: m) rest
      else
        -- A plain ValDef shadows any outer FuncValue binding with the same id.
        let (mOut, restOut) := rewriteDefs (m.filter (fun p => p.1 != id)) rest
        (mOut, (id, rhs') :: restOut)
termination_by defs => sizeOf defs
end

/-- The public entry point: inline every `FuncValue`-bound `ValDef` at its
    `ValUse` sites and drop the `ValDef`. Always `some` — see module
    docstring's "revised precondition" section for why no tree can make
    this fail; the `Option` return type is kept (rather than simplifying
    to a plain `Expr`) so `spendable` (`Sigma.lean`) and callers don't
    need to change if a real future precondition is ever found. -/
def inlineFuns (e : Expr) : Option Expr :=
  some (rewriteExpr [] e)

-- Regression: an inner plain `ValDef` reusing a FuncValue's id must shadow it.
#guard
  match inlineFuns
      (.blockValue [(1, .funcValue [(2, .sInt)] (.valUse 2 .sInt))]
        (.blockValue [(1, .const (.vInt 5))] (.valUse 1 .sInt))) with
  | some (.blockValue [] (.blockValue [(1, _)] (.valUse 1 _))) => true
  | _ => false

end ErgoTreeLean
