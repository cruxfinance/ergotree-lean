/-
Forward rules for the collection loops `eval_sym` leaves folded
(`existsHelper`/`mapHelper`/`foldHelper`/`filterHelper` facts; `forallHelper`
has the exact `forallHelper_true_iff`, `Lemmas/EvalInv.lean`), and an
invariant rule for `fold`, the building block for transaction-level
statements (a sum over `INPUTS`/`OUTPUTS` is a `fold` whose accumulator
satisfies an invariant).
-/
import ErgoTreeLean.Lemmas.EvalInv

namespace ErgoTreeLean

variable {c : List Value} {x : Context} {env : Env} {a : Nat} {body : Expr}

/-- `exists` returned `false`: the body is `false` on every element. -/
theorem existsHelper_false_iff (l : List Value) :
    existsHelper c x env a body l = .ok false ↔ ∀ v ∈ l, eval c x ((a, v) :: env) body = .ok (.vBool false) := by
  induction l with
  | nil => simp [existsHelper, pure, Except.pure]
  | cons v vs ih =>
    simp only [existsHelper]
    cases h : eval c x ((a, v) :: env) body with
    | error => simp [bind, Except.bind, h]
    | ok bv =>
      cases bv <;> simp [bind, Except.bind, h, pure, Except.pure]
      rename_i b; cases b <;> simp [ih]

/-- `forall` returned `false`: the body is `false` on some element. -/
theorem forallHelper_false_imp (l : List Value) (h : forallHelper c x env a body l = .ok false) :
    ∃ v ∈ l, eval c x ((a, v) :: env) body = .ok (.vBool false) := by
  induction l with
  | nil => simp [forallHelper, pure, Except.pure] at h
  | cons v vs ih =>
    simp only [forallHelper] at h
    cases hv : eval c x ((a, v) :: env) body with
    | error => simp [bind, Except.bind, hv] at h
    | ok bv =>
      cases bv <;> simp [bind, Except.bind, hv] at h
      rename_i b; cases b
      · exact ⟨v, List.mem_cons_self .., hv⟩
      · obtain ⟨w, hw, hw'⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩

/-- `map`, pointwise: the output has the input's length, and its `i`-th
    element is the body's value on the input's `i`-th element. -/
theorem mapHelper_getElem? {l out : List Value} (h : mapHelper c x env a body l = .ok out) :
    out.length = l.length ∧
      ∀ (i : Nat) v, l[i]? = some v → ∃ r, out[i]? = some r ∧ eval c x ((a, v) :: env) body = .ok r := by
  have h2 := (mapHelper_ok_iff c x env a body l out).mp h
  refine ⟨h2.length_eq.symm, fun i v hv => ?_⟩
  clear h
  induction h2 generalizing i with
  | nil => simp at hv
  | cons hr _ ih =>
    cases i with
    | zero => simp at hv ⊢; subst hv; exact hr
    | succ i => simpa using ih i (by simpa using hv)

/-- `filter` keeps a sublist of its input. -/
theorem filterHelper_sublist {l out : List Value} (h : filterHelper c x env a body l = .ok out) :
    out.Sublist l := by
  induction l generalizing out with
  | nil => simp [filterHelper, pure, Except.pure] at h; subst h; exact .slnil
  | cons v vs ih =>
    simp only [filterHelper] at h
    cases hv : eval c x ((a, v) :: env) body with
    | error => simp [bind, Except.bind, hv] at h
    | ok bv =>
      cases bv <;> simp [bind, Except.bind, hv] at h
      cases hr : filterHelper c x env a body vs with
      | error => simp [hr] at h
      | ok rest =>
        simp [hr, pure, Except.pure] at h; subst h
        rename_i b; cases b
        · exact (ih hr).cons _
        · exact (ih hr).cons₂ _

/-- `fold` invariant: a property of the accumulator that the initial value
    has and every step preserves holds of the result. -/
theorem foldHelper_inv (P : Value → Prop) {l : List Value} {acc w : Value}
    (h0 : P acc)
    (hstep : ∀ acc v r, P acc → v ∈ l → eval c x ((a, .vTuple [acc, v]) :: env) body = .ok r → P r)
    (h : foldHelper c x env a body acc l = .ok w) : P w := by
  induction l generalizing acc with
  | nil => simp [foldHelper, pure, Except.pure] at h; exact h ▸ h0
  | cons v vs ih =>
    simp only [foldHelper] at h
    cases hv : eval c x ((a, .vTuple [acc, v]) :: env) body with
    | error => simp [bind, Except.bind, hv] at h
    | ok r =>
      simp [bind, Except.bind, hv] at h
      exact ih (hstep acc v r h0 (List.mem_cons_self ..) hv)
        (fun acc' v' r' hp hm he => hstep acc' v' r' hp (List.mem_cons_of_mem _ hm) he) h

/-- `fold` as a relation-preserving walk: if every step maps an accumulator
    related to `f`'s running value to one related to the next value, the
    result is related to the fold of `f` (e.g. `R acc s := acc = .vBigInt s`
    and `f s v := s + amount v` turns a script-level sum into `List.foldl`). -/
theorem foldHelper_foldl {β : Type} (R : Value → β → Prop) (f : β → Value → β) {l : List Value} {acc w : Value}
    {s : β} (h0 : R acc s)
    (hstep : ∀ acc s v r, R acc s → v ∈ l → eval c x ((a, .vTuple [acc, v]) :: env) body = .ok r → R r (f s v))
    (h : foldHelper c x env a body acc l = .ok w) : R w (l.foldl f s) := by
  induction l generalizing acc s with
  | nil => simp [foldHelper, pure, Except.pure] at h; exact h ▸ h0
  | cons v vs ih =>
    simp only [foldHelper] at h
    cases hv : eval c x ((a, .vTuple [acc, v]) :: env) body with
    | error => simp [bind, Except.bind, hv] at h
    | ok r =>
      simp [bind, Except.bind, hv] at h
      exact ih (hstep acc s v r h0 (List.mem_cons_self ..) hv)
        (fun acc' s' v' r' hp hm he => hstep acc' s' v' r' hp (List.mem_cons_of_mem _ hm) he) h

end ErgoTreeLean
