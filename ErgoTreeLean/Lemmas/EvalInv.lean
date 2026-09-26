/-
Inversion lemmas for `eval`: one `@[eval_inv]` rewrite per node kind, turning a
success equation `eval consts ctx env e = .ok w` into a statement about `e`'s
children in which every runtime pattern match of `Eval.lean` is already
resolved (the intermediate values appear as existentials with their
constructor shape pinned).

Running `simp only [eval_inv, …] at h` on `h : eval … tree = .ok w` for a
concrete `tree` therefore performs symbolic execution: simp rewrites the tree
bottom-up, and its existential-elimination lemmas (`exists_eq_left` and
friends) substitute each intermediate value as soon as a child's equation
fixes it. Environment lookups (`valUse`) against a literal environment reduce
by deciding numeral equalities, so no environment ever needs pinning by hand.

Two refinements keep the result small:
* `binOp (.logical .and)` and the relations have a second, higher-priority
  form for the result `.vBool true`, so an `&&` chain known to be true splits
  into a flat conjunction instead of a case split.
* `blockValue` is inverted one `ValDef` at a time, so a block never produces an
  existential environment.
-/
import ErgoTreeLean.Eval
import ErgoTreeLean.Sigma
import ErgoTreeLean.Tactics.Attr
import Aesop
import Mathlib.Data.List.Forall2

set_option linter.unnecessarySeqFocus false

namespace ErgoTreeLean

/-! ## Postponed facts

`Later p` is `p`, marked as a fact `eval_sym` decodes only once everything
before it is decoded: the rest of a block after a `ValDef`, and the branches of
an `if`. Its engine stops `simp` at a `Later` (the `laterStop` simproc,
`Tactics/EvalSym.lean`), so a block is executed one definition at a time, each
continuation seeing the value of the definition before it, and a branch whose
condition is already decided is dropped unexamined. `eval_simp` unfolds `Later`
right away (`later_iff`). -/

/-- `p`, postponed; see above. -/
def Later (p : Prop) : Prop := p

theorem later_iff (p : Prop) : Later p ↔ p := Iff.rfl

/-! ## `Except` normalization -/

@[eval_inv] theorem Except.bind_eq_ok_iff {ε α β} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[eval_inv] theorem Except.pure_eq_ok_iff' {ε α} (a b : α) : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[eval_inv] theorem Except.error_eq_ok_iff {ε α} (e : ε) (b : α) : (Except.error e : Except ε α) = .ok b ↔ False := by
  simp

@[eval_inv] theorem Except.ok_eq_ok_iff {ε α} (a b : α) : (Except.ok a : Except ε α) = .ok b ↔ a = b := by
  simp

variable (c : List Value) (x : Context) (env : Env)

/-! ## Leaves -/

@[eval_inv] theorem eval_const_ok (v w : Value) : eval c x env (.const v) = .ok w ↔ v = w := by
  simp [eval, pure, Except.pure]

@[eval_inv] theorem eval_constPlaceholder_ok (i : Nat) (t : SType) (w : Value) :
    eval c x env (.constPlaceholder i t) = .ok w ↔ c[i]? = some w := by
  simp only [eval]; split <;> simp_all [pure, Except.pure]

@[eval_inv] theorem eval_valUse_nil_ok (i : Nat) (t : SType) (w : Value) :
    eval c x [] (.valUse i t) = .ok w ↔ False := by
  simp [eval]

@[eval_inv] theorem eval_valUse_cons_ok (k : Nat) (v : Value) (i : Nat) (t : SType) (w : Value) :
    eval c x ((k, v) :: env) (.valUse i t) = .ok w ↔ if k = i then v = w else eval c x env (.valUse i t) = .ok w := by
  by_cases h : k = i
  · subst h; simp [eval, List.find?, pure, Except.pure]
  · have : (k == i) = false := by simpa using h
    simp [eval, List.find?, this, h]

@[eval_inv] theorem eval_outputs_ok (w : Value) :
    eval c x env .outputs = .ok w ↔ .vColl .sBox (x.outputs.map .vBox) = w := by
  simp [eval, pure, Except.pure]

@[eval_inv] theorem eval_inputs_ok (w : Value) :
    eval c x env .inputs = .ok w ↔ .vColl .sBox (x.inputs.map .vBox) = w := by
  simp [eval, pure, Except.pure]

@[eval_inv] theorem eval_selfBox_ok (w : Value) :
    eval c x env .selfBox = .ok w ↔ .vBox x.selfBox = w := by
  simp [eval, pure, Except.pure]

@[eval_inv] theorem eval_height_ok (w : Value) :
    eval c x env .height = .ok w ↔ .vInt (x.height : Int) = w := by
  simp [eval, pure, Except.pure]

@[eval_inv] theorem eval_dataInputs_ok (w : Value) :
    eval c x env (.propertyCall .context 101 1) = .ok w ↔ .vColl .sBox (x.dataInputs.map .vBox) = w := by
  simp [eval, pure, Except.pure]

/-! ## Unary nodes with a single shape-checked operand

Each proof: unfold one `eval` step, case on the operand's result and shape. -/

/-- Shared proof script for the single-operand nodes below. -/
local macro "inv_unary" e:term : tactic => `(tactic| (
  simp only [eval]
  cases h : eval c x env $e with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind, pure, Except.pure] <;> aesop))

@[eval_inv] theorem eval_sizeOf_ok (e : Expr) (w : Value) :
    eval c x env (.sizeOf e) = .ok w ↔ ∃ t vs, eval c x env e = .ok (.vColl t vs) ∧ w = .vInt vs.length := by
  inv_unary e

@[eval_inv] theorem eval_extractScriptBytes_ok (e : Expr) (w : Value) :
    eval c x env (.extractScriptBytes e) = .ok w ↔
      ∃ b, eval c x env e = .ok (.vBox b) ∧ w = bytesToVColl b.propositionBytes := by
  inv_unary e

@[eval_inv] theorem eval_extractAmount_ok (e : Expr) (w : Value) :
    eval c x env (.extractAmount e) = .ok w ↔ ∃ b, eval c x env e = .ok (.vBox b) ∧ w = .vLong b.value := by
  inv_unary e

@[eval_inv] theorem eval_extractId_ok (e : Expr) (w : Value) :
    eval c x env (.extractId e) = .ok w ↔ ∃ b, eval c x env e = .ok (.vBox b) ∧ w = bytesToVColl b.id := by
  inv_unary e

@[eval_inv] theorem eval_extractRegisterAs_ok (e : Expr) (r : Int) (t : SType) (w : Value) :
    eval c x env (.extractRegisterAs e r t) = .ok w ↔
      ∃ b, eval c x env e = .ok (.vBox b) ∧ w = .vOption t (b.register r) := by
  inv_unary e

@[eval_inv] theorem eval_tokens_ok (e : Expr) (w : Value) :
    eval c x env (.propertyCall e 99 8) = .ok w ↔
      ∃ b, eval c x env e = .ok (.vBox b) ∧
        w = .vColl (.sTuple [.sColl .sByte, .sLong])
          (b.tokens.map (fun (tid, amt) => .vTuple [bytesToVColl tid, .vLong amt])) := by
  inv_unary e

@[eval_inv] theorem eval_indices_ok (e : Expr) (w : Value) :
    eval c x env (.propertyCall e 12 14) = .ok w ↔
      ∃ t vs, eval c x env e = .ok (.vColl t vs) ∧
        w = .vColl .sInt ((List.range vs.length).map (fun (i : Nat) => Value.vInt (i : Int))) := by
  inv_unary e

@[eval_inv] theorem eval_optionGet_ok (e : Expr) (w : Value) :
    eval c x env (.optionGet e) = .ok w ↔ ∃ t, eval c x env e = .ok (.vOption t (some w)) := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    rename_i o; cases o <;> simp

@[eval_inv] theorem eval_optionIsDefined_ok (e : Expr) (w : Value) :
    eval c x env (.optionIsDefined e) = .ok w ↔
      ∃ t o, eval c x env e = .ok (.vOption t o) ∧ w = .vBool o.isSome := by
  inv_unary e

/-- `optionIsDefined` known true: the option is `some`. -/
@[eval_inv high] theorem eval_optionIsDefined_true (e : Expr) :
    eval c x env (.optionIsDefined e) = .ok (.vBool true) ↔
      ∃ t v, eval c x env e = .ok (.vOption t (some v)) := by
  rw [eval_optionIsDefined_ok]
  constructor
  · rintro ⟨t, o, h, hw⟩; cases o <;> simp_all
  · rintro ⟨t, v, h⟩; exact ⟨t, some v, h, rfl⟩

@[eval_inv] theorem eval_optionGetOrElse_ok (e d : Expr) (w : Value) :
    eval c x env (.optionGetOrElse e d) = .ok w ↔
      ∃ t, eval c x env e = .ok (.vOption t (some w)) ∨
        (eval c x env e = .ok (.vOption t none) ∧ eval c x env d = .ok w) := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    rename_i o; cases o <;> simp

@[eval_inv] theorem eval_selectField_ok (e : Expr) (i : Nat) (w : Value) :
    eval c x env (.selectField e i) = .ok w ↔
      ∃ vs, eval c x env e = .ok (.vTuple vs) ∧ 1 ≤ i ∧ vs[i - 1]? = some w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    split
    · split <;> simp_all
    · simp; omega

@[eval_inv] theorem eval_boolToSigmaProp_ok (e : Expr) (w : Value) :
    eval c x env (.boolToSigmaProp e) = .ok w ↔
      ∃ b, eval c x env e = .ok (.vBool b) ∧ w = .vSigmaProp (.trivial b) := by
  inv_unary e

@[eval_inv] theorem eval_createProveDlog_ok (e : Expr) (w : Value) :
    eval c x env (.createProveDlog e) = .ok w ↔
      ∃ g, eval c x env e = .ok (.vGroupElement g) ∧ w = .vSigmaProp (.proveDlog g) := by
  inv_unary e

@[eval_inv] theorem eval_logicalNot_ok (e : Expr) (w : Value) :
    eval c x env (.logicalNot e) = .ok w ↔ ∃ b, eval c x env e = .ok (.vBool b) ∧ w = .vBool (!b) := by
  inv_unary e

@[eval_inv high] theorem eval_logicalNot_true (e : Expr) :
    eval c x env (.logicalNot e) = .ok (.vBool true) ↔ eval c x env e = .ok (.vBool false) := by
  rw [eval_logicalNot_ok]; constructor
  · rintro ⟨b, h, hb⟩; cases b <;> simp_all
  · intro h; exact ⟨false, h, rfl⟩

/-! ## `byIndex`, `ifExpr` -/

@[eval_inv] theorem eval_byIndex_ok (coll idx : Expr) (w : Value) :
    eval c x env (.byIndex coll idx none) = .ok w ↔
      ∃ t vs i, eval c x env coll = .ok (.vColl t vs) ∧ eval c x env idx = .ok (.vInt i) ∧
        0 ≤ i ∧ vs[i.toNat]? = some w := by
  simp only [eval]
  cases h : eval c x env coll with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    cases h2 : eval c x env idx with
    | error => simp
    | ok v =>
      cases v <;> simp
      rename_i i
      split <;> rename_i hi
      · simp; omega
      · split <;> simp_all

theorem eval_ifExpr_ok (cnd t f : Expr) (w : Value) :
    eval c x env (.ifExpr cnd t f) = .ok w ↔
      (eval c x env cnd = .ok (.vBool true) ∧ eval c x env t = .ok w) ∨
      (eval c x env cnd = .ok (.vBool false) ∧ eval c x env f = .ok w) := by
  simp only [eval]
  cases h : eval c x env cnd with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind]
    rename_i b; cases b <;> simp

@[eval_inv] theorem eval_ifExpr_later (cnd t f : Expr) (w : Value) :
    eval c x env (.ifExpr cnd t f) = .ok w ↔
      (eval c x env cnd = .ok (.vBool true) ∧ Later (eval c x env t = .ok w)) ∨
      (eval c x env cnd = .ok (.vBool false) ∧ Later (eval c x env f = .ok w)) :=
  eval_ifExpr_ok c x env cnd t f w

/-! ## Logical `&&` / `||` (lazy) -/

@[eval_inv] theorem eval_and_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.logical .and) l r) = .ok w ↔
      (eval c x env l = .ok (.vBool false) ∧ w = .vBool false) ∨
      (eval c x env l = .ok (.vBool true) ∧ ∃ b, eval c x env r = .ok (.vBool b) ∧ w = .vBool b) := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    rename_i b; cases b <;> simp
    · exact eq_comm
    · cases h2 : eval c x env r with
      | error => simp
      | ok v => cases v <;> simp <;> rename_i b <;> cases b <;> simp [eq_comm]

@[eval_inv high] theorem eval_and_true (l r : Expr) :
    eval c x env (.binOp (.logical .and) l r) = .ok (.vBool true) ↔
      eval c x env l = .ok (.vBool true) ∧ eval c x env r = .ok (.vBool true) := by
  rw [eval_and_ok]; simp

@[eval_inv] theorem eval_or_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.logical .or) l r) = .ok w ↔
      (eval c x env l = .ok (.vBool true) ∧ w = .vBool true) ∨
      (eval c x env l = .ok (.vBool false) ∧ ∃ b, eval c x env r = .ok (.vBool b) ∧ w = .vBool b) := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    rename_i b; cases b <;> simp
    · cases h2 : eval c x env r with
      | error => simp
      | ok v => cases v <;> simp <;> rename_i b <;> cases b <;> simp [eq_comm]
    · exact eq_comm

@[eval_inv high] theorem eval_or_true (l r : Expr) :
    eval c x env (.binOp (.logical .or) l r) = .ok (.vBool true) ↔
      eval c x env l = .ok (.vBool true) ∨
      (eval c x env l = .ok (.vBool false) ∧ eval c x env r = .ok (.vBool true)) := by
  rw [eval_or_ok]; simp

/-! ## Relations -/

@[eval_inv] theorem eval_eq_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .eq) l r) = .ok w ↔
      ∃ a b, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ w = .vBool (Value.beq a b) := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : eval c x env r with
    | error => simp [bind, Except.bind]
    | ok v => simp only [bind, Except.bind, pure, Except.pure]; aesop

@[eval_inv high] theorem eval_eq_true (l r : Expr) :
    eval c x env (.binOp (.relation .eq) l r) = .ok (.vBool true) ↔
      ∃ a b, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ Value.beq a b = true := by
  rw [eval_eq_ok]; aesop

@[eval_inv] theorem eval_neq_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .neq) l r) = .ok w ↔
      ∃ a b, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ w = .vBool (!Value.beq a b) := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : eval c x env r with
    | error => simp [bind, Except.bind]
    | ok v => simp only [bind, Except.bind, pure, Except.pure]; aesop

@[eval_inv high] theorem eval_neq_true (l r : Expr) :
    eval c x env (.binOp (.relation .neq) l r) = .ok (.vBool true) ↔
      ∃ a b, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ Value.beq a b = false := by
  rw [eval_neq_ok]; aesop

/-- Shared shape of the four ordering relations (`sameKindRaw`, which
    `eval_inv` computes on constructor-headed operands, then a comparison). -/
def ordRel : RelationOp → Int → Int → Bool
  | .ge, p, q => decide (p ≥ q)
  | .gt, p, q => decide (p > q)
  | .le, p, q => decide (p ≤ q)
  | .lt, p, q => decide (p < q)
  | .eq, _, _ => false
  | .neq, _, _ => false

theorem eval_ord_ok (op : RelationOp) (hop : op ≠ .eq ∧ op ≠ .neq) (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation op) l r) = .ok w ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        w = .vBool (ordRel op p q) := by
  obtain ⟨h1, h2⟩ := hop
  cases op <;> simp only [ne_eq, not_true_eq_false] at h1 h2 <;> simp only [eval] <;>
  · cases h : eval c x env l with
    | error => simp [bind, Except.bind]
    | ok v =>
      cases h2 : eval c x env r with
      | error => simp [bind, Except.bind]
      | ok v' =>
        simp only [bind, Except.bind]
        cases hk : sameKindRaw v v' with
        | none => simp [hk]
        | some t => obtain ⟨k, p, q⟩ := t; simp [pure, Except.pure, ordRel]; aesop

theorem eval_gt_true (l r : Expr) :
    eval c x env (.binOp (.relation .gt) l r) = .ok (.vBool true) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p > q := by
  rw [eval_ord_ok c x env .gt ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_ge_true (l r : Expr) :
    eval c x env (.binOp (.relation .ge) l r) = .ok (.vBool true) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p ≥ q := by
  rw [eval_ord_ok c x env .ge ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_lt_true (l r : Expr) :
    eval c x env (.binOp (.relation .lt) l r) = .ok (.vBool true) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p < q := by
  rw [eval_ord_ok c x env .lt ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_le_true (l r : Expr) :
    eval c x env (.binOp (.relation .le) l r) = .ok (.vBool true) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p ≤ q := by
  rw [eval_ord_ok c x env .le ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_gt_false (l r : Expr) :
    eval c x env (.binOp (.relation .gt) l r) = .ok (.vBool false) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p ≤ q := by
  rw [eval_ord_ok c x env .gt ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_ge_false (l r : Expr) :
    eval c x env (.binOp (.relation .ge) l r) = .ok (.vBool false) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ p < q := by
  rw [eval_ord_ok c x env .ge ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_lt_false (l r : Expr) :
    eval c x env (.binOp (.relation .lt) l r) = .ok (.vBool false) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ q ≤ p := by
  rw [eval_ord_ok c x env .lt ⟨nofun, nofun⟩]; simp [ordRel]

theorem eval_le_false (l r : Expr) :
    eval c x env (.binOp (.relation .le) l r) = .ok (.vBool false) ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧ q < p := by
  rw [eval_ord_ok c x env .le ⟨nofun, nofun⟩]; simp [ordRel]

/-- An ordering whose result is not yet known (e.g. bound by a `ValDef`). -/
theorem eval_gt_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .gt) l r) = .ok w ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        w = .vBool (decide (p > q)) := by
  rw [eval_ord_ok c x env .gt ⟨nofun, nofun⟩]; simp [ordRel]
theorem eval_ge_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .ge) l r) = .ok w ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        w = .vBool (decide (p ≥ q)) := by
  rw [eval_ord_ok c x env .ge ⟨nofun, nofun⟩]; simp [ordRel]
theorem eval_lt_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .lt) l r) = .ok w ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        w = .vBool (decide (p < q)) := by
  rw [eval_ord_ok c x env .lt ⟨nofun, nofun⟩]; simp [ordRel]
theorem eval_le_ok (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .le) l r) = .ok w ↔
      ∃ a b k p q, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        w = .vBool (decide (p ≤ q)) := by
  rw [eval_ord_ok c x env .le ⟨nofun, nofun⟩]; simp [ordRel]

/-! ## Blocks, one `ValDef` at a time -/

@[eval_inv] theorem eval_blockValue_nil_ok (r : Expr) (w : Value) :
    eval c x env (.blockValue [] r) = .ok w ↔ eval c x env r = .ok w := by
  simp [eval, evalDefs, pure, Except.pure, bind, Except.bind]

theorem eval_blockValue_cons_ok (i : Nat) (e : Expr) (rest : List (Nat × Expr)) (r : Expr) (w : Value) :
    eval c x env (.blockValue ((i, e) :: rest) r) = .ok w ↔
      ∃ v, eval c x env e = .ok v ∧ eval c x ((i, v) :: env) (.blockValue rest r) = .ok w := by
  simp only [eval, evalDefs]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v => simp [bind, Except.bind]

@[eval_inv] theorem eval_blockValue_cons_later (i : Nat) (e : Expr) (rest : List (Nat × Expr)) (r : Expr) (w : Value) :
    eval c x env (.blockValue ((i, e) :: rest) r) = .ok w ↔
      ∃ v, eval c x env e = .ok v ∧ Later (eval c x ((i, v) :: env) (.blockValue rest r) = .ok w) :=
  eval_blockValue_cons_ok c x env i e rest r w

/-! ## Evaluated lists (`sigmaAnd`/`sigmaOr`/`collection`/`tuple`) -/

@[eval_inv] theorem evalList_nil_ok (w : List Value) : evalList c x env [] = .ok w ↔ w = [] := by
  simp [evalList, pure, Except.pure, eq_comm]

@[eval_inv] theorem evalList_cons_ok (e : Expr) (rest : List Expr) (w : List Value) :
    evalList c x env (e :: rest) = .ok w ↔
      ∃ v vs, eval c x env e = .ok v ∧ evalList c x env rest = .ok vs ∧ w = v :: vs := by
  simp only [evalList]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : evalList c x env rest with
    | error => simp [bind, Except.bind]
    | ok vs => simp [bind, Except.bind, pure, Except.pure, eq_comm]

@[eval_inv] theorem toSigmaProps_nil_ok (w : List SigmaBoolean) : toSigmaProps [] = .ok w ↔ w = [] := by
  simp [toSigmaProps, pure, Except.pure, eq_comm]

@[eval_inv] theorem toSigmaProps_cons_ok (v : Value) (rest : List Value) (w : List SigmaBoolean) :
    toSigmaProps (v :: rest) = .ok w ↔ ∃ sb sbs, v = .vSigmaProp sb ∧ toSigmaProps rest = .ok sbs ∧ w = sb :: sbs := by
  cases v <;> simp [toSigmaProps]
  cases h : toSigmaProps rest <;> simp [Functor.map, Except.map, eq_comm]

@[eval_inv] theorem eval_sigmaAnd_ok (items : List Expr) (w : Value) :
    eval c x env (.sigmaAnd items) = .ok w ↔
      ∃ vs sbs, evalList c x env items = .ok vs ∧ toSigmaProps vs = .ok sbs ∧ w = .vSigmaProp (normalizeCand sbs) := by
  simp only [eval]
  cases h : evalList c x env items with
  | error => simp [bind, Except.bind]
  | ok vs =>
    simp only [bind, Except.bind, Except.bind_eq_ok_iff]
    cases h2 : toSigmaProps vs <;> simp [pure, Except.pure, h2, eq_comm]

@[eval_inv] theorem eval_sigmaOr_ok (items : List Expr) (w : Value) :
    eval c x env (.sigmaOr items) = .ok w ↔
      ∃ vs sbs, evalList c x env items = .ok vs ∧ toSigmaProps vs = .ok sbs ∧ w = .vSigmaProp (normalizeCor sbs) := by
  simp only [eval]
  cases h : evalList c x env items with
  | error => simp [bind, Except.bind]
  | ok vs =>
    simp only [bind, Except.bind, Except.bind_eq_ok_iff]
    cases h2 : toSigmaProps vs <;> simp [pure, Except.pure, h2, eq_comm]

@[eval_inv] theorem eval_collection_ok (t : SType) (items : List Expr) (w : Value) :
    eval c x env (.collection t items) = .ok w ↔ ∃ vs, evalList c x env items = .ok vs ∧ w = .vColl t vs := by
  simp only [eval]
  cases h : evalList c x env items <;> simp [bind, Except.bind, pure, Except.pure] <;> aesop

@[eval_inv] theorem eval_tuple_ok (items : List Expr) (w : Value) :
    eval c x env (.tuple items) = .ok w ↔ ∃ vs, evalList c x env items = .ok vs ∧ w = .vTuple vs := by
  simp only [eval]
  cases h : evalList c x env items <;> simp [bind, Except.bind, pure, Except.pure] <;> aesop

/-! ## `atLeast` -/

@[eval_inv] theorem eval_atLeast_ok (b i : Expr) (w : Value) :
    eval c x env (.atLeast b i) = .ok w ↔
      ∃ k τ vs sbs, eval c x env b = .ok (.vInt k) ∧ eval c x env i = .ok (.vColl τ vs) ∧
        toSigmaProps vs = .ok sbs ∧ 0 ≤ k ∧ k ≤ 255 ∧ k ≤ (sbs.length : Int) ∧ sbs ≠ [] ∧
        w = .vSigmaProp (cthresholdReduce k.toNat sbs) := by
  simp only [eval]
  cases h : eval c x env b with
  | error => simp [bind, Except.bind]
  | ok bv =>
    cases h2 : eval c x env i with
    | error => simp [bind, Except.bind]
    | ok iv =>
      cases bv <;> cases iv <;> simp [bind, Except.bind]
      rename_i k τ vs
      cases h3 : toSigmaProps vs with
      | error => simp [h3]
      | ok sbs =>
        simp only [h3, Except.ok.injEq, and_assoc, exists_and_left, exists_eq_left', exists_eq_left]
        split
        · rename_i hh; simp; intros; omega
        · split
          · rename_i _ hh; simp; intros; exact absurd hh (Int.not_lt.mpr ‹_›)
          · split
            · simp_all
            · simp_all [pure, Except.pure]; constructor
              · rintro rfl; rfl
              · rintro ⟨-, -, -, rfl⟩; rfl

/-! ## Higher-order collection operations -/

@[eval_inv] theorem eval_forAll_ok (input : Expr) (a : Nat) (t : SType) (body : Expr) (et : SType) (w : Value) :
    eval c x env (.forAllOf input (.funcValue [(a, t)] body) et) = .ok w ↔
      ∃ τ vs b, eval c x env input = .ok (.vColl τ vs) ∧ forallHelper c x env a body vs = .ok b ∧ w = .vBool b := by
  simp only [eval]
  cases h : eval c x env input with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind] <;> rename_i vs <;>
      cases hf : forallHelper c x env a body vs <;> simp [hf, pure, Except.pure, and_assoc] <;> aesop

theorem forallHelper_true_iff (a : Nat) (body : Expr) (l : List Value) :
    forallHelper c x env a body l = .ok true ↔ ∀ v ∈ l, eval c x ((a, v) :: env) body = .ok (.vBool true) := by
  induction l with
  | nil => simp [forallHelper, pure, Except.pure]
  | cons v vs ih =>
    simp only [forallHelper]
    cases h : eval c x ((a, v) :: env) body with
    | error => simp [bind, Except.bind, h]
    | ok bv =>
      cases bv <;> simp [bind, Except.bind, h, pure, Except.pure]
      rename_i b; cases b <;> simp [ih]

/-- Not in `eval_inv` (it would expand the loop body under a binder on
    every pass); use `forallHelper_true_iff` explicitly. -/
theorem eval_forAll_true (input : Expr) (a : Nat) (t : SType) (body : Expr) (et : SType) :
    eval c x env (.forAllOf input (.funcValue [(a, t)] body) et) = .ok (.vBool true) ↔
      ∃ τ vs, eval c x env input = .ok (.vColl τ vs) ∧ ∀ v ∈ vs, eval c x ((a, v) :: env) body = .ok (.vBool true) := by
  rw [eval_forAll_ok]; simp [← forallHelper_true_iff]

@[eval_inv] theorem eval_exists_ok (input : Expr) (a : Nat) (t : SType) (body : Expr) (et : SType) (w : Value) :
    eval c x env (.existsOf input (.funcValue [(a, t)] body) et) = .ok w ↔
      ∃ τ vs b, eval c x env input = .ok (.vColl τ vs) ∧ existsHelper c x env a body vs = .ok b ∧ w = .vBool b := by
  simp only [eval]
  cases h : eval c x env input with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind] <;> rename_i vs <;>
      cases hf : existsHelper c x env a body vs <;> simp [hf, pure, Except.pure, and_assoc] <;> aesop

/-- Success of `exists` with `true`: some element satisfies the body (all
    earlier elements evaluated to `false`, which is dropped here). -/
theorem existsHelper_true_imp (a : Nat) (body : Expr) (l : List Value)
    (h : existsHelper c x env a body l = .ok true) : ∃ v ∈ l, eval c x ((a, v) :: env) body = .ok (.vBool true) := by
  induction l with
  | nil => simp [existsHelper, pure, Except.pure] at h
  | cons v vs ih =>
    simp only [existsHelper] at h
    cases hv : eval c x ((a, v) :: env) body with
    | error => simp [bind, Except.bind, hv] at h
    | ok bv =>
      cases bv <;> simp [bind, Except.bind, hv] at h
      rename_i b; cases b
      · obtain ⟨w, hw, hw'⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩
      · exact ⟨v, List.mem_cons_self .., hv⟩

@[eval_inv] theorem eval_map_ok (input : Expr) (a : Nat) (t : SType) (body : Expr) (et : SType) (w : Value) :
    eval c x env (.mapOf input (.funcValue [(a, t)] body) et) = .ok w ↔
      ∃ τ vs out, eval c x env input = .ok (.vColl τ vs) ∧ mapHelper c x env a body vs = .ok out ∧ w = .vColl et out := by
  simp only [eval]
  cases h : eval c x env input with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind] <;> rename_i vs <;>
      cases hf : mapHelper c x env a body vs <;> simp [hf, pure, Except.pure, and_assoc] <;> aesop

/-- `map` succeeds iff the body succeeds on every element, pointwise. -/
theorem mapHelper_ok_iff (a : Nat) (body : Expr) (l out : List Value) :
    mapHelper c x env a body l = .ok out ↔ List.Forall₂ (fun v r => eval c x ((a, v) :: env) body = .ok r) l out := by
  induction l generalizing out with
  | nil => cases out <;> simp [mapHelper, pure, Except.pure]
  | cons v vs ih =>
    simp only [mapHelper]
    cases h : eval c x ((a, v) :: env) body with
    | error => cases out <;> simp [bind, Except.bind, h]
    | ok r =>
      cases h2 : mapHelper c x env a body vs with
      | error =>
        cases out <;> simp [bind, Except.bind, h]
        intro _ hf; have := (ih _).mpr hf; simp_all
      | ok rs =>
        have := (ih rs).mp h2
        cases out <;> simp [bind, Except.bind, h, pure, Except.pure]
        rintro rfl
        constructor
        · rintro rfl; exact this
        · intro hf; have := (ih _).mpr hf; rw [h2] at this; injection this

@[eval_inv] theorem eval_filter_ok (input : Expr) (a : Nat) (t : SType) (body : Expr) (et : SType) (w : Value) :
    eval c x env (.filterOf input (.funcValue [(a, t)] body) et) = .ok w ↔
      ∃ τ vs out, eval c x env input = .ok (.vColl τ vs) ∧ filterHelper c x env a body vs = .ok out ∧ w = .vColl et out := by
  simp only [eval]
  cases h : eval c x env input with
  | error => simp [bind, Except.bind]
  | ok v => cases v <;> simp [bind, Except.bind] <;> rename_i vs <;>
      cases hf : filterHelper c x env a body vs <;> simp [hf, pure, Except.pure, and_assoc] <;> aesop

/-! ## Arithmetic, casts -/

/-- The result `Eval.lean` computes for an arithmetic `BinOp` on two raw
    operands of kind `k` (`none` = overflow / division error). -/
def arithRes : ArithOp → NumKind → Int → Int → Option Int
  | .plus, k, a, b => checkedArith k (· + ·) a b
  | .minus, k, a, b => checkedArith k (· - ·) a b
  | .multiply, k, a, b => checkedArith k (· * ·) a b
  | .divide, k, a, b => checkedDiv k a b
  | .modulo, k, a, b => if k == .bigint then checkedRemBigInt a b else checkedRemFixed k a b
  | .max, _, a, b => some (max a b)
  | .min, _, a, b => some (min a b)

theorem eval_arith_ok (op : ArithOp) (l r : Expr) (w : Value) :
    eval c x env (.binOp (.arith op) l r) = .ok w ↔
      ∃ a b k p q z, eval c x env l = .ok a ∧ eval c x env r = .ok b ∧ sameKindRaw a b = some (k, p, q) ∧
        arithRes op k p q = some z ∧ k.wrap z = w := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : eval c x env r with
    | error => simp [bind, Except.bind]
    | ok v' =>
      simp only [bind, Except.bind]
      cases hk : sameKindRaw v v' with
      | none => simp [hk]
      | some t =>
        obtain ⟨k, p, q⟩ := t
        cases op <;> simp only [arithRes] <;>
          first | (split <;> simp_all [pure, Except.pure]) | simp_all [pure, Except.pure]

theorem eval_upcast_ok (e : Expr) (t : SType) (w : Value) :
    eval c x env (.upcast e t) = .ok w ↔
      ∃ v k p tk z, eval c x env e = .ok v ∧ v.numKind = some (k, p) ∧ sTypeToNumKind? t = some tk ∧
        upcastValue k p tk = some z ∧ tk.wrap z = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    simp only [bind, Except.bind]
    rcases hv : v.numKind with _ | ⟨k, p⟩ <;> rcases ht : sTypeToNumKind? t with _ | tk <;> simp [hv, ht]
    cases hu : upcastValue k p tk <;> simp [hu, pure, Except.pure]

theorem eval_downcast_ok (e : Expr) (t : SType) (w : Value) :
    eval c x env (.downcast e t) = .ok w ↔
      ∃ v k p tk z, eval c x env e = .ok v ∧ v.numKind = some (k, p) ∧ sTypeToNumKind? t = some tk ∧
        downcastValue k p tk = some z ∧ tk.wrap z = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    simp only [bind, Except.bind]
    rcases hv : v.numKind with _ | ⟨k, p⟩ <;> rcases ht : sTypeToNumKind? t with _ | tk <;> simp [hv, ht]
    cases hu : downcastValue k p tk <;> simp [hu, pure, Except.pure]

@[eval_inv] theorem sTypeToNumKind?_sBigInt : sTypeToNumKind? .sBigInt = some .bigint := rfl
@[eval_inv] theorem sTypeToNumKind?_sLong : sTypeToNumKind? .sLong = some .long := rfl
@[eval_inv] theorem sTypeToNumKind?_sInt : sTypeToNumKind? .sInt = some .int := rfl

/-- Widening never fails: `upcast` to a wider or equal kind returns the value. -/
@[eval_inv] theorem upcastValue_eq_some_iff (k : NumKind) (p : Int) (tk : NumKind) (z : Int) :
    upcastValue k p tk = some z ↔ k.rank ≤ tk.rank ∧ p = z := by
  unfold upcastValue
  cases k <;> cases tk <;> simp [NumKind.rank]

section
variable (k : NumKind)
@[eval_inv] theorem NumKind.rank_byte : NumKind.rank .byte = 0 := rfl
@[eval_inv] theorem NumKind.rank_short : NumKind.rank .short = 1 := rfl
@[eval_inv] theorem NumKind.rank_int : NumKind.rank .int = 2 := rfl
@[eval_inv] theorem NumKind.rank_long : NumKind.rank .long = 3 := rfl
@[eval_inv] theorem NumKind.rank_bigint : NumKind.rank .bigint = 4 := rfl
/-- Every kind upcasts to `BigInt`. -/
@[eval_inv] theorem NumKind.rank_le_four : k.rank ≤ 4 := by cases k <;> decide
end

/-! ## Environment-free leaves: `getVar` -/

@[eval_inv] theorem eval_getVar_ok (i : Nat) (t : SType) (w : Value) :
    eval c x env (.getVar i t) = .ok w ↔
      (x.getVar i = none ∧ .vOption t none = w) ∨
      (∃ v, x.getVar i = some v ∧ SType.beq (typeOf v) t = true ∧ .vOption t (some v) = w) := by
  simp only [eval]
  cases h : x.getVar i with
  | none => simp [pure, Except.pure]
  | some v => by_cases hb : SType.beq (typeOf v) t = true <;> simp [hb, pure, Except.pure]

/-! ## Remaining collection nodes -/

@[eval_inv] theorem eval_byIndex_default_ok (coll idx d : Expr) (w : Value) :
    eval c x env (.byIndex coll idx (some d)) = .ok w ↔
      ∃ t vs i, eval c x env coll = .ok (.vColl t vs) ∧ eval c x env idx = .ok (.vInt i) ∧
        ((0 ≤ i ∧ vs[i.toNat]? = some w) ∨ ((i < 0 ∨ vs[i.toNat]? = none) ∧ eval c x env d = .ok w)) := by
  simp only [eval]
  cases h : eval c x env coll with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind, pure, Except.pure]
    cases h2 : eval c x env idx with
    | error => simp
    | ok v =>
      cases v <;> simp
      rename_i i
      split <;> rename_i hi
      · have : ¬ 0 ≤ i := by omega
        simp [hi, this]
      · have : 0 ≤ i := by omega
        split <;> rename_i hv <;> simp [hi, this, hv, pure, Except.pure]
        · intro hlen; rw [List.getElem?_eq_none_iff.mpr (by omega)] at hv; cases hv
        · have := List.getElem?_eq_none_iff.mp hv; intro; omega

@[eval_inv] theorem eval_appendOf_ok (l r : Expr) (w : Value) :
    eval c x env (.appendOf l r) = .ok w ↔
      ∃ t1 vs1 t2 vs2, eval c x env l = .ok (.vColl t1 vs1) ∧ eval c x env r = .ok (.vColl t2 vs2) ∧
        .vColl t1 (vs1 ++ vs2) = w := by
  simp only [eval]
  cases h : eval c x env l with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : eval c x env r with
    | error => simp [bind, Except.bind]
    | ok v' => cases v <;> cases v' <;> simp [bind, Except.bind, pure, Except.pure]

@[eval_inv] theorem eval_foldOf_ok (input zero : Expr) (a : Nat) (t : SType) (body : Expr) (w : Value) :
    eval c x env (.foldOf input zero (.funcValue [(a, t)] body)) = .ok w ↔
      ∃ τ vs z, eval c x env input = .ok (.vColl τ vs) ∧ eval c x env zero = .ok z ∧
        foldHelper c x env a body z vs = .ok w := by
  simp only [eval]
  cases h : eval c x env input with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases h2 : eval c x env zero with
    | error => simp [bind, Except.bind]
    | ok z => cases v <;> simp [bind, Except.bind]

@[eval_inv] theorem foldHelper_nil_ok (a : Nat) (body : Expr) (acc w : Value) :
    foldHelper c x env a body acc [] = .ok w ↔ acc = w := by
  simp [foldHelper, pure, Except.pure]

@[eval_inv] theorem foldHelper_cons_ok (a : Nat) (body : Expr) (acc v : Value) (vs : List Value) (w : Value) :
    foldHelper c x env a body acc (v :: vs) = .ok w ↔
      ∃ acc', eval c x ((a, .vTuple [acc, v]) :: env) body = .ok acc' ∧ foldHelper c x env a body acc' vs = .ok w := by
  simp only [foldHelper]
  cases eval c x ((a, .vTuple [acc, v]) :: env) body <;> simp [bind, Except.bind]

@[eval_inv] theorem eval_apply_ok (params : List (Nat × SType)) (body : Expr) (args : List Expr) (w : Value) :
    eval c x env (.apply (.funcValue params body) args) = .ok w ↔
      ∃ avs env', evalList c x env args = .ok avs ∧ bindArgs env params avs = some env' ∧
        eval c x env' body = .ok w := by
  simp only [eval]
  cases h : evalList c x env args with
  | error => simp [bind, Except.bind]
  | ok avs =>
    simp only [bind, Except.bind]
    cases hb : bindArgs env params avs <;> simp [hb]

@[eval_inv] theorem eval_andOf_ok (e : Expr) (w : Value) :
    eval c x env (.andOf e) = .ok w ↔
      ∃ vs bs, eval c x env e = .ok (.vColl .sBoolean vs) ∧ toBoolList vs = .ok bs ∧ .vBool (bs.all id) = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind]
    rename_i t vs; cases t <;> simp
    cases toBoolList vs <;> simp [pure, Except.pure]

@[eval_inv] theorem eval_orOf_ok (e : Expr) (w : Value) :
    eval c x env (.orOf e) = .ok w ↔
      ∃ vs bs, eval c x env e = .ok (.vColl .sBoolean vs) ∧ toBoolList vs = .ok bs ∧ .vBool (bs.any id) = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    cases v <;> simp [bind, Except.bind]
    rename_i t vs; cases t <;> simp
    cases toBoolList vs <;> simp [pure, Except.pure]

@[eval_inv] theorem toBoolList_nil_ok (w : List Bool) : toBoolList [] = .ok w ↔ [] = w := by
  simp [toBoolList, pure, Except.pure]

@[eval_inv] theorem toBoolList_cons_ok (v : Value) (vs : List Value) (w : List Bool) :
    toBoolList (v :: vs) = .ok w ↔ ∃ b bs, v = .vBool b ∧ toBoolList vs = .ok bs ∧ b :: bs = w := by
  cases v <;> simp [toBoolList]
  cases toBoolList vs <;> simp [bind, Except.bind, pure, Except.pure]

/-! ## Numeric-kind decoding (for the ordering relations) -/

@[eval_inv] theorem sameKindRaw_eq_some_iff (a b : Value) (k : NumKind) (p q : Int) :
    sameKindRaw a b = some (k, p, q) ↔ a.numKind = some (k, p) ∧ b.numKind = some (k, q) := by
  unfold sameKindRaw
  cases ha : a.numKind <;> cases hb : b.numKind <;> simp
  rename_i x y; obtain ⟨k1, a1⟩ := x; obtain ⟨k2, b2⟩ := y
  by_cases hk : k1 = k2 <;> simp [hk] <;> aesop

@[eval_inv] theorem Value.numKind_eq_some_iff (v : Value) (k : NumKind) (p : Int) :
    v.numKind = some (k, p) ↔ v = k.wrap p := by
  cases v <;> cases k <;> simp [Value.numKind, NumKind.wrap, eq_comm]

section
variable (p : Int)
@[eval_inv] theorem NumKind.wrap_byte : NumKind.wrap .byte p = .vByte p := rfl
@[eval_inv] theorem NumKind.wrap_short : NumKind.wrap .short p = .vShort p := rfl
@[eval_inv] theorem NumKind.wrap_int : NumKind.wrap .int p = .vInt p := rfl
@[eval_inv] theorem NumKind.wrap_long : NumKind.wrap .long p = .vLong p := rfl
@[eval_inv] theorem NumKind.wrap_bigint : NumKind.wrap .bigint p = .vBigInt p := rfl
@[eval_inv] theorem NumKind.wrap_eq_vInt (k : NumKind) (q : Int) : k.wrap p = .vInt q ↔ k = .int ∧ p = q := by
  cases k <;> simp [NumKind.wrap]
@[eval_inv] theorem NumKind.wrap_eq_vLong (k : NumKind) (q : Int) : k.wrap p = .vLong q ↔ k = .long ∧ p = q := by
  cases k <;> simp [NumKind.wrap]
@[eval_inv] theorem NumKind.vInt_eq_wrap (k : NumKind) (q : Int) : .vInt q = k.wrap p ↔ k = .int ∧ p = q := by
  cases k <;> simp [NumKind.wrap, eq_comm]
@[eval_inv] theorem NumKind.vLong_eq_wrap (k : NumKind) (q : Int) : .vLong q = k.wrap p ↔ k = .long ∧ p = q := by
  cases k <;> simp [NumKind.wrap, eq_comm]
@[eval_inv] theorem NumKind.vBigInt_eq_wrap (k : NumKind) (q : Int) : .vBigInt q = k.wrap p ↔ k = .bigint ∧ p = q := by
  cases k <;> simp [NumKind.wrap, eq_comm]
@[eval_inv] theorem NumKind.vShort_eq_wrap (k : NumKind) (q : Int) : .vShort q = k.wrap p ↔ k = .short ∧ p = q := by
  cases k <;> simp [NumKind.wrap, eq_comm]
@[eval_inv] theorem NumKind.vByte_eq_wrap (k : NumKind) (q : Int) : .vByte q = k.wrap p ↔ k = .byte ∧ p = q := by
  cases k <;> simp [NumKind.wrap, eq_comm]
@[eval_inv] theorem NumKind.wrap_eq_vBigInt (k : NumKind) (q : Int) : k.wrap p = .vBigInt q ↔ k = .bigint ∧ p = q := by
  cases k <;> simp [NumKind.wrap]
@[eval_inv] theorem NumKind.wrap_inj (k k' : NumKind) (q : Int) : k.wrap p = k'.wrap q ↔ k = k' ∧ p = q := by
  cases k <;> cases k' <;> simp [NumKind.wrap]
end


/-! ## Numeric operands, telescoped

The rules `eval_inv` uses for the orderings, arithmetic and casts. The
operands' kind and payload are bound right where each operand's own equation
fixes them (`∃ k p, eval l = .ok (k.wrap p) ∧ ∃ q, …`), so `simp` eliminates
each existential as soon as it is decided instead of restructuring one flat
`∃ a b k p q, …` prefix, which re-simplifies the whole body under the binders
at every step. -/

theorem sameKind_tele {A B : Value → Prop} {P : NumKind → Int → Int → Prop} :
    (∃ a b k p q, A a ∧ B b ∧ sameKindRaw a b = some (k, p, q) ∧ P k p q) ↔
      ∃ k p, A (k.wrap p) ∧ ∃ q, B (k.wrap q) ∧ P k p q := by
  simp only [sameKindRaw_eq_some_iff, Value.numKind_eq_some_iff]
  constructor
  · rintro ⟨a, b, k, p, q, ha, hb, ⟨rfl, rfl⟩, h⟩; exact ⟨k, p, ha, q, hb, h⟩
  · rintro ⟨k, p, ha, q, hb, h⟩; exact ⟨_, _, k, p, q, ha, hb, ⟨rfl, rfl⟩, h⟩

@[eval_inv high] theorem eval_gt_true' (l r : Expr) :
    eval c x env (.binOp (.relation .gt) l r) = .ok (.vBool true) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p > q := by
  rw [eval_gt_true c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_ge_true' (l r : Expr) :
    eval c x env (.binOp (.relation .ge) l r) = .ok (.vBool true) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p ≥ q := by
  rw [eval_ge_true c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_lt_true' (l r : Expr) :
    eval c x env (.binOp (.relation .lt) l r) = .ok (.vBool true) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p < q := by
  rw [eval_lt_true c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_le_true' (l r : Expr) :
    eval c x env (.binOp (.relation .le) l r) = .ok (.vBool true) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p ≤ q := by
  rw [eval_le_true c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_gt_false' (l r : Expr) :
    eval c x env (.binOp (.relation .gt) l r) = .ok (.vBool false) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p ≤ q := by
  rw [eval_gt_false c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_ge_false' (l r : Expr) :
    eval c x env (.binOp (.relation .ge) l r) = .ok (.vBool false) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ p < q := by
  rw [eval_ge_false c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_lt_false' (l r : Expr) :
    eval c x env (.binOp (.relation .lt) l r) = .ok (.vBool false) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ q ≤ p := by
  rw [eval_lt_false c x env l r]; exact sameKind_tele

@[eval_inv high] theorem eval_le_false' (l r : Expr) :
    eval c x env (.binOp (.relation .le) l r) = .ok (.vBool false) ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ q < p := by
  rw [eval_le_false c x env l r]; exact sameKind_tele

@[eval_inv] theorem eval_gt_ok' (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .gt) l r) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ w = .vBool (decide (p > q)) := by
  rw [eval_gt_ok c x env l r w]; exact sameKind_tele

@[eval_inv] theorem eval_ge_ok' (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .ge) l r) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ w = .vBool (decide (p ≥ q)) := by
  rw [eval_ge_ok c x env l r w]; exact sameKind_tele

@[eval_inv] theorem eval_lt_ok' (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .lt) l r) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ w = .vBool (decide (p < q)) := by
  rw [eval_lt_ok c x env l r w]; exact sameKind_tele

@[eval_inv] theorem eval_le_ok' (l r : Expr) (w : Value) :
    eval c x env (.binOp (.relation .le) l r) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧ w = .vBool (decide (p ≤ q)) := by
  rw [eval_le_ok c x env l r w]; exact sameKind_tele

@[eval_inv] theorem eval_arith_ok' (op : ArithOp) (l r : Expr) (w : Value) :
    eval c x env (.binOp (.arith op) l r) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env l = .ok (k.wrap p) ∧ ∃ q, eval c x env r = .ok (k.wrap q) ∧
        ∃ z, arithRes op k p q = some z ∧ k.wrap z = w := by
  rw [eval_arith_ok c x env op l r w]
  refine Iff.trans ?_ (sameKind_tele (A := fun a => eval c x env l = .ok a) (B := fun b => eval c x env r = .ok b)
    (P := fun k p q => ∃ z, arithRes op k p q = some z ∧ k.wrap z = w))
  constructor
  · rintro ⟨a, b, k, p, q, z, ha, hb, hs, hz, hw⟩; exact ⟨a, b, k, p, q, ha, hb, hs, z, hz, hw⟩
  · rintro ⟨a, b, k, p, q, ha, hb, hs, z, hz, hw⟩; exact ⟨a, b, k, p, q, z, ha, hb, hs, hz, hw⟩

@[eval_inv] theorem eval_upcast_ok' (e : Expr) (t : SType) (w : Value) :
    eval c x env (.upcast e t) = .ok w ↔
      ∃ tk, sTypeToNumKind? t = some tk ∧ ∃ (k : NumKind) (p : Int), eval c x env e = .ok (k.wrap p) ∧
        ∃ z, upcastValue k p tk = some z ∧ tk.wrap z = w := by
  rw [eval_upcast_ok c x env e t w]
  simp only [Value.numKind_eq_some_iff]
  constructor
  · rintro ⟨v, k, p, tk, z, hv, rfl, ht, hz, hw⟩; exact ⟨tk, ht, k, p, hv, z, hz, hw⟩
  · rintro ⟨tk, ht, k, p, hv, z, hz, hw⟩; exact ⟨_, k, p, tk, z, hv, rfl, ht, hz, hw⟩

@[eval_inv] theorem eval_downcast_ok' (e : Expr) (t : SType) (w : Value) :
    eval c x env (.downcast e t) = .ok w ↔
      ∃ tk, sTypeToNumKind? t = some tk ∧ ∃ (k : NumKind) (p : Int), eval c x env e = .ok (k.wrap p) ∧
        ∃ z, downcastValue k p tk = some z ∧ tk.wrap z = w := by
  rw [eval_downcast_ok c x env e t w]
  simp only [Value.numKind_eq_some_iff]
  constructor
  · rintro ⟨v, k, p, tk, z, hv, rfl, ht, hz, hw⟩; exact ⟨tk, ht, k, p, hv, z, hz, hw⟩
  · rintro ⟨tk, ht, k, p, hv, z, hz, hw⟩; exact ⟨_, k, p, tk, z, hv, rfl, ht, hz, hw⟩

theorem eval_negation_ok (e : Expr) (w : Value) :
    eval c x env (.negation e) = .ok w ↔
      ∃ v k p, eval c x env e = .ok v ∧ v.numKind = some (k, p) ∧
        ∃ z, checkedNeg k p = some z ∧ k.wrap z = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    simp only [bind, Except.bind]
    rcases hv : v.numKind with _ | ⟨k, p⟩ <;> simp [hv]
    cases hu : checkedNeg k p <;> simp [pure, Except.pure]

@[eval_inv] theorem eval_negation_ok' (e : Expr) (w : Value) :
    eval c x env (.negation e) = .ok w ↔
      ∃ (k : NumKind) (p : Int), eval c x env e = .ok (k.wrap p) ∧
        ∃ z, checkedNeg k p = some z ∧ k.wrap z = w := by
  rw [eval_negation_ok c x env e w]
  simp only [Value.numKind_eq_some_iff]
  constructor
  · rintro ⟨v, k, p, hv, rfl, z, hz, hw⟩; exact ⟨k, p, hv, z, hz, hw⟩
  · rintro ⟨k, p, hv, z, hz, hw⟩; exact ⟨_, k, p, hv, rfl, z, hz, hw⟩

/-! ## Oracle nodes -/

/-- `blake2b256`: the operand's bytes, hashed by the context's oracle. -/
@[eval_inv] theorem eval_calcBlake2b256_ok (e : Expr) (w : Value) :
    eval c x env (.calcBlake2b256 e) = .ok w ↔
      ∃ vs bs, eval c x env e = .ok (.vColl .sByte vs) ∧ vsToBytes vs = .ok bs ∧
        bytesToVColl (x.oracle.blake2b256 bs) = w := by
  simp only [eval]
  cases h : eval c x env e with
  | error => simp [bind, Except.bind]
  | ok v =>
    simp only [bind, Except.bind]
    cases v <;> simp
    rename_i t vs
    cases t <;> simp
    cases hb : vsToBytes vs <;> simp [pure, Except.pure]

/-- `DeserializeContext`: the context variable's bytes, deserialized and
    evaluated by the context's oracle, with the expected type. -/
@[eval_inv] theorem eval_deserializeContext_ok (i : Nat) (t : SType) (w : Value) :
    eval c x env (.deserializeContext i t) = .ok w ↔
      ∃ vs bs, x.getVar i = some (.vColl .sByte vs) ∧ vsToBytes vs = .ok bs ∧
        x.oracle.deserialize bs = some w ∧ SType.beq (typeOf w) t = true := by
  simp only [eval]
  cases h : x.getVar i with
  | none => simp
  | some v =>
    simp only
    cases v <;> simp
    rename_i τ vs
    cases τ <;> simp
    cases hb : vsToBytes vs <;> simp [bind, Except.bind]
    rename_i bs
    cases hd : x.oracle.deserialize bs <;> simp
    split <;> simp_all [pure, Except.pure] <;> (rintro rfl; assumption)

/-! ## Orientation fixes -/

@[eval_inv] theorem some_eq_register_iff (v : Value) (b : Box) (r : Int) :
    some v = b.register r ↔ b.register r = some v := eq_comm

@[eval_inv] theorem false_eq_beq_iff {α : Type} [BEq α] (a b : α) : (false = (a == b)) ↔ (a == b) = false := eq_comm
@[eval_inv] theorem true_eq_beq_iff {α : Type} [BEq α] (a b : α) : (true = (a == b)) ↔ (a == b) = true := eq_comm
@[eval_inv] theorem false_eq_valueBeq_iff (a b : Value) : (false = Value.beq a b) ↔ Value.beq a b = false := eq_comm
@[eval_inv] theorem false_eq_not_iff (b : Bool) : (false = !b) ↔ b = true := by cases b <;> simp
@[eval_inv] theorem true_eq_not_iff (b : Bool) : (true = !b) ↔ b = false := by cases b <;> simp
@[eval_inv] theorem true_eq_valueBeq_iff (a b : Value) : (true = Value.beq a b) ↔ Value.beq a b = true := eq_comm

end ErgoTreeLean
