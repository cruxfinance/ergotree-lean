/-
Decoding rules for `eval_sym`: facts that turn what the `eval_inv` rules leave
behind into plain equations and `Int` facts.

* `SType.beq` is lawful (`SType.beq_iff_eq`), so a `getVar` type check or a
  `vColl` element-type comparison becomes an equation between types, and
  `typeOf v = .sInt` (etc.) pins the shape of `v`.
* `Value.beq` is lawful on values with no `vOption` inside
  (`Value.beq_iff_eq_of_optFree`, `Value.beq_eq_true_iff_of_optFree`). It is not lawful in general: `vOption`'s
  `beq` ignores the element type, as sigma-rust's runtime `Opt` has none. For
  a comparison against a value whose shape is only partly known,
  `Value.beq_vColl_right` and friends peel one constructor at a time, and
  `Value.beqList_getElem?_of_optFree` transfers a known element across a
  `beqList`.
* `arithRes` (the arithmetic result `eval_arith_ok` leaves) becomes the plain
  `Int` result plus the overflow side-condition as two `Int` bounds
  (`arithRes_plus_eq_some_iff` and friends). `NumKind.lo`/`NumKind.hi` are the
  bounds; for a concrete kind they reduce to numerals.
* `upcastValue` to `BigInt` never fails and never changes the payload.
-/
import ErgoTreeLean.Lemmas.EvalInv
import ErgoTreeLean.Lemmas.Beq

set_option linter.unnecessarySeqFocus false

namespace ErgoTreeLean

/-! ## `SType.beq` is lawful -/

theorem SType.eq_of_beq (a : SType) : ∀ b, SType.beq a b = true → a = b := by
  induction a using SType.rec (motive_2 := fun ts => ∀ bs, SType.beqList ts bs = true → ts = bs) with
  | sOption t ih => intro b h; cases b <;> simp [SType.beq] at h; exact congrArg _ (ih _ h)
  | sColl t ih => intro b h; cases b <;> simp [SType.beq] at h; exact congrArg _ (ih _ h)
  | sTuple ts ih => intro b h; cases b <;> simp [SType.beq] at h; exact congrArg _ (ih _ h)
  | sFunc ds r ih1 ih2 =>
    intro b h; cases b <;> simp [SType.beq] at h
    rw [ih1 _ h.1, ih2 _ h.2]
  | nil => rename_i bs h; cases bs <;> simp [SType.beqList] at h ⊢
  | cons t ts ih1 ih2 =>
    rename_i bs h; cases bs <;> simp [SType.beqList] at h
    rw [ih1 _ h.1, ih2 _ h.2]
  | _ => intro b h; cases b <;> simp [SType.beq] at h ⊢

@[eval_inv] theorem SType.beq_iff_eq (a b : SType) : SType.beq a b = true ↔ a = b :=
  ⟨SType.eq_of_beq a b, fun h => h ▸ SType.beq_refl a⟩

@[eval_inv] theorem SType.beq_eq_false_iff (a b : SType) : SType.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e; rw [(SType.beq_iff_eq a b).mpr e] at h; cases h
  · intro h; cases h' : SType.beq a b
    · rfl
    · exact absurd ((SType.beq_iff_eq a b).mp h') h

instance : LawfulBEq SType where
  eq_of_beq {a b} h := SType.eq_of_beq a b h
  rfl {a} := SType.beq_refl a

/-! ## `typeOf` pins a value's shape -/

section typeOf
variable (v : Value)
@[eval_inv] theorem typeOf_eq_sBoolean : typeOf v = .sBoolean ↔ ∃ b, v = .vBool b := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sByte : typeOf v = .sByte ↔ ∃ n, v = .vByte n := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sShort : typeOf v = .sShort ↔ ∃ n, v = .vShort n := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sInt : typeOf v = .sInt ↔ ∃ n, v = .vInt n := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sLong : typeOf v = .sLong ↔ ∃ n, v = .vLong n := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sBigInt : typeOf v = .sBigInt ↔ ∃ n, v = .vBigInt n := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sGroupElement : typeOf v = .sGroupElement ↔ ∃ g, v = .vGroupElement g := by
  cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sSigmaProp : typeOf v = .sSigmaProp ↔ ∃ sb, v = .vSigmaProp sb := by
  cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sBox : typeOf v = .sBox ↔ ∃ b, v = .vBox b := by cases v <;> simp [typeOf]
@[eval_inv] theorem typeOf_eq_sColl (t : SType) : typeOf v = .sColl t ↔ ∃ vs, v = .vColl t vs := by
  cases v <;> simp [typeOf, eq_comm]
@[eval_inv] theorem typeOf_eq_sOption (t : SType) : typeOf v = .sOption t ↔ ∃ o, v = .vOption t o := by
  cases v <;> simp [typeOf, eq_comm]
end typeOf

/-! ## `Value.beq`

`beq` is an equivalence (`Value.beq_refl`, `Value.beq_symm`) that equals `=`
on option-free values. The one-sided rules below decode a comparison against a
constructor-headed value whose other side is unknown. -/

mutual
/-- `v` contains no `vOption` (including inside tuples, collections and box
    registers): on such values `Value.beq` is equality. -/
def Value.optFree : Value → Bool
  | .vOption _ _ => false
  | .vBox b => Box.optFree b
  | .vColl _ vs => Value.optFreeList vs
  | .vTuple vs => Value.optFreeList vs
  | _ => true

def Value.optFreeList : List Value → Bool
  | [] => true
  | v :: vs => Value.optFree v && Value.optFreeList vs

def Box.optFree : Box → Bool
  | ⟨_, _, _, _, r⟩ => Box.optFreeRegs r

def Box.optFreeRegs : List (Nat × Value) → Bool
  | [] => true
  | (_, v) :: rs => Value.optFree v && Box.optFreeRegs rs
end

private theorem beqTokens_eq : ∀ (t1 t2 : List (List UInt8 × Int)), Box.beqTokens t1 t2 = true → t1 = t2
  | [], [], _ => rfl
  | (a, x) :: xs, (b, y) :: ys, h => by
    simp [Box.beqTokens] at h
    rw [h.1.1, h.1.2, beqTokens_eq xs ys h.2]
  | [], _ :: _, h => by simp [Box.beqTokens] at h
  | _ :: _, [], h => by simp [Box.beqTokens] at h

mutual
theorem Value.eq_of_beq_of_optFree : ∀ (a b : Value), a.optFree = true → Value.beq a b = true → a = b
  | .vUnit, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vBool _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vByte _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vShort _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vInt _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vLong _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vBigInt _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vGroupElement _, b, _, h => by cases b <;> simp_all [Value.beq]
  | .vSigmaProp s, b, _, h => by
    cases b <;> simp [Value.beq] at h
    rw [SigmaBoolean.eq_of_beq s _ h]
  | .vBox x, b, ho, h => by
    cases b <;> simp [Value.beq] at h
    rw [Box.eq_of_beq_of_optFree x _ (by simpa [Value.optFree] using ho) h]
  | .vColl t vs, b, ho, h => by
    cases b <;> simp [Value.beq] at h
    rw [(SType.beq_iff_eq _ _).mp h.1,
      Value.eq_of_beqList_of_optFree vs _ (by simpa [Value.optFree] using ho) h.2]
  | .vTuple vs, b, ho, h => by
    cases b <;> simp [Value.beq] at h
    rw [Value.eq_of_beqList_of_optFree vs _ (by simpa [Value.optFree] using ho) h]
  | .vOption _ _, _, ho, _ => by simp [Value.optFree] at ho

theorem Value.eq_of_beqList_of_optFree :
    ∀ (as bs : List Value), Value.optFreeList as = true → Value.beqList as bs = true → as = bs
  | [], [], _, _ => rfl
  | a :: as, b :: bs, ho, h => by
    simp [Value.beqList] at h; simp [Value.optFreeList] at ho
    rw [Value.eq_of_beq_of_optFree a b ho.1 h.1, Value.eq_of_beqList_of_optFree as bs ho.2 h.2]
  | [], _ :: _, _, h => by simp [Value.beqList] at h
  | _ :: _, [], _, h => by simp [Value.beqList] at h

theorem Box.eq_of_beq_of_optFree : ∀ (a b : Box), a.optFree = true → Box.beq a b = true → a = b
  | ⟨i1, v1, p1, t1, r1⟩, ⟨i2, v2, p2, t2, r2⟩, ho, h => by
    simp only [Box.beq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Box.optFree] at ho
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, beqTokens_eq t1 t2 h4, Box.eq_of_beqRegisters_of_optFree r1 r2 ho h5]

theorem Box.eq_of_beqRegisters_of_optFree :
    ∀ (a b : List (Nat × Value)), Box.optFreeRegs a = true → Box.beqRegisters a b = true → a = b
  | [], [], _, _ => rfl
  | (i, v) :: as, (j, w) :: bs, ho, h => by
    simp [Box.beqRegisters] at h; simp [Box.optFreeRegs] at ho
    rw [h.1.1, Value.eq_of_beq_of_optFree v w ho.1 h.1.2, Box.eq_of_beqRegisters_of_optFree as bs ho.2 h.2]
  | [], _ :: _, _, h => by simp [Box.beqRegisters] at h
  | _ :: _, [], _, h => by simp [Box.beqRegisters] at h

theorem SigmaBoolean.eq_of_beq : ∀ (a b : SigmaBoolean), SigmaBoolean.beq a b = true → a = b
  | .trivial _, b, h => by cases b <;> simp_all [SigmaBoolean.beq]
  | .proveDlog _, b, h => by cases b <;> simp_all [SigmaBoolean.beq]
  | .cor xs, b, h => by
    cases b <;> simp [SigmaBoolean.beq] at h
    rw [SigmaBoolean.eq_of_beqList xs _ h]
  | .cand xs, b, h => by
    cases b <;> simp [SigmaBoolean.beq] at h
    rw [SigmaBoolean.eq_of_beqList xs _ h]
  | .cthreshold k xs, b, h => by
    cases b <;> simp [SigmaBoolean.beq] at h
    rw [h.1, SigmaBoolean.eq_of_beqList xs _ h.2]

theorem SigmaBoolean.eq_of_beqList : ∀ (a b : List SigmaBoolean), SigmaBoolean.beqList a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [SigmaBoolean.beqList] at h
    rw [SigmaBoolean.eq_of_beq a b h.1, SigmaBoolean.eq_of_beqList as bs h.2]
  | [], _ :: _, h => by simp [SigmaBoolean.beqList] at h
  | _ :: _, [], h => by simp [SigmaBoolean.beqList] at h
end

/-- `Value.beq` is equality when one side is option-free. -/
theorem Value.beq_iff_eq_of_optFree {a b : Value} (h : a.optFree = true) : Value.beq a b = true ↔ a = b :=
  ⟨Value.eq_of_beq_of_optFree a b h, fun e => e ▸ Value.beq_refl a⟩

mutual
theorem Value.eq_of_beq_of_optFree_right : ∀ (b a : Value), b.optFree = true → Value.beq a b = true → a = b
  | .vUnit, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vBool _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vByte _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vShort _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vInt _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vLong _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vBigInt _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vGroupElement _, a, _, h => by cases a <;> simp_all [Value.beq]
  | .vSigmaProp s, a, _, h => by
    cases a <;> simp [Value.beq] at h
    rw [SigmaBoolean.eq_of_beq _ s h]
  | .vBox x, a, ho, h => by
    cases a <;> simp [Value.beq] at h
    rw [Box.eq_of_beq_of_optFree_right x _ (by simpa [Value.optFree] using ho) h]
  | .vColl t vs, a, ho, h => by
    cases a <;> simp [Value.beq] at h
    rw [(SType.beq_iff_eq _ _).mp h.1,
      Value.eq_of_beqList_of_optFree_right vs _ (by simpa [Value.optFree] using ho) h.2]
  | .vTuple vs, a, ho, h => by
    cases a <;> simp [Value.beq] at h
    rw [Value.eq_of_beqList_of_optFree_right vs _ (by simpa [Value.optFree] using ho) h]
  | .vOption _ _, _, ho, _ => by simp [Value.optFree] at ho

theorem Value.eq_of_beqList_of_optFree_right :
    ∀ (bs as : List Value), Value.optFreeList bs = true → Value.beqList as bs = true → as = bs
  | [], [], _, _ => rfl
  | b :: bs, a :: as, ho, h => by
    simp [Value.beqList] at h; simp [Value.optFreeList] at ho
    rw [Value.eq_of_beq_of_optFree_right b a ho.1 h.1, Value.eq_of_beqList_of_optFree_right bs as ho.2 h.2]
  | [], _ :: _, _, h => by simp [Value.beqList] at h
  | _ :: _, [], _, h => by simp [Value.beqList] at h

theorem Box.eq_of_beq_of_optFree_right : ∀ (b a : Box), b.optFree = true → Box.beq a b = true → a = b
  | ⟨i2, v2, p2, t2, r2⟩, ⟨i1, v1, p1, t1, r1⟩, ho, h => by
    simp only [Box.beq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Box.optFree] at ho
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, beqTokens_eq t1 t2 h4, Box.eq_of_beqRegisters_of_optFree_right r2 r1 ho h5]

theorem Box.eq_of_beqRegisters_of_optFree_right :
    ∀ (b a : List (Nat × Value)), Box.optFreeRegs b = true → Box.beqRegisters a b = true → a = b
  | [], [], _, _ => rfl
  | (j, w) :: bs, (i, v) :: as, ho, h => by
    simp [Box.beqRegisters] at h; simp [Box.optFreeRegs] at ho
    rw [h.1.1, Value.eq_of_beq_of_optFree_right w v ho.1 h.1.2,
      Box.eq_of_beqRegisters_of_optFree_right bs as ho.2 h.2]
  | [], _ :: _, _, h => by simp [Box.beqRegisters] at h
  | _ :: _, [], _, h => by simp [Box.beqRegisters] at h
end

/-- `Value.beq` is equality when the right side is option-free. -/
theorem Value.beq_iff_eq_of_optFree_right {a b : Value} (h : b.optFree = true) : Value.beq a b = true ↔ a = b :=
  ⟨Value.eq_of_beq_of_optFree_right b a h, fun e => e ▸ Value.beq_refl a⟩

/-- A comparison against an option-free value (e.g. a literal) is an equation;
    `simp` discharges the side condition by computing `optFree`. -/
@[eval_inv high] theorem Value.beq_eq_true_iff_of_optFree (a b : Value) (h : b.optFree = true) :
    Value.beq a b = true ↔ a = b := Value.beq_iff_eq_of_optFree_right h

section optFree
variable (t : SType) (v : Value) (vs : List Value) (n : Int)
@[eval_inv] theorem Value.optFree_vColl : (Value.vColl t vs).optFree = Value.optFreeList vs := by
  simp [Value.optFree]
@[eval_inv] theorem Value.optFree_vTuple : (Value.vTuple vs).optFree = Value.optFreeList vs := by
  simp [Value.optFree]
@[eval_inv] theorem Value.optFree_vByte : (Value.vByte n).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vShort : (Value.vShort n).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vInt : (Value.vInt n).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vLong : (Value.vLong n).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vBigInt : (Value.vBigInt n).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vBool (b : Bool) : (Value.vBool b).optFree = true := rfl
@[eval_inv] theorem Value.optFree_vGroupElement (g : List UInt8) : (Value.vGroupElement g).optFree = true := rfl
@[eval_inv] theorem Value.optFreeList_nil : Value.optFreeList [] = true := rfl
@[eval_inv] theorem Value.optFreeList_cons : Value.optFreeList (v :: vs) = (v.optFree && Value.optFreeList vs) := by
  simp [Value.optFreeList]
end optFree

@[eval_inv] theorem Value.beq_self (a : Value) : Value.beq a a = true := Value.beq_refl a

/-! One-sided decoding: the known side is constructor-headed. -/

section oneSided
variable (a : Value)

@[eval_inv] theorem Value.beq_vInt_right (n : Int) : Value.beq a (.vInt n) = true ↔ a = .vInt n := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vLong_right (n : Int) : Value.beq a (.vLong n) = true ↔ a = .vLong n := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vBigInt_right (n : Int) : Value.beq a (.vBigInt n) = true ↔ a = .vBigInt n := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vShort_right (n : Int) : Value.beq a (.vShort n) = true ↔ a = .vShort n := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vByte_right (n : Int) : Value.beq a (.vByte n) = true ↔ a = .vByte n := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vBool_right (b : Bool) : Value.beq a (.vBool b) = true ↔ a = .vBool b := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_vGroupElement_right (g : List UInt8) :
    Value.beq a (.vGroupElement g) = true ↔ a = .vGroupElement g := by
  cases a <;> simp [Value.beq]
@[eval_inv] theorem Value.beq_wrap_right (k : NumKind) (n : Int) : Value.beq a (k.wrap n) = true ↔ a = k.wrap n := by
  cases k <;> cases a <;> simp [Value.beq, NumKind.wrap]

@[eval_inv] theorem Value.beq_vInt_left (n : Int) : Value.beq (.vInt n) a = true ↔ a = .vInt n := by
  cases a <;> simp [Value.beq] <;> exact eq_comm
@[eval_inv] theorem Value.beq_vLong_left (n : Int) : Value.beq (.vLong n) a = true ↔ a = .vLong n := by
  cases a <;> simp [Value.beq] <;> exact eq_comm
@[eval_inv] theorem Value.beq_vBigInt_left (n : Int) : Value.beq (.vBigInt n) a = true ↔ a = .vBigInt n := by
  cases a <;> simp [Value.beq] <;> exact eq_comm
@[eval_inv] theorem Value.beq_wrap_left (k : NumKind) (n : Int) : Value.beq (k.wrap n) a = true ↔ a = k.wrap n := by
  cases k <;> cases a <;> simp [Value.beq, NumKind.wrap] <;> exact eq_comm

@[eval_inv] theorem Value.beq_vColl_right (t : SType) (vs : List Value) :
    Value.beq a (.vColl t vs) = true ↔ ∃ ws, a = .vColl t ws ∧ Value.beqList ws vs = true := by
  cases a <;> simp [Value.beq, SType.beq_iff_eq]
@[eval_inv] theorem Value.beq_vTuple_right (vs : List Value) :
    Value.beq a (.vTuple vs) = true ↔ ∃ ws, a = .vTuple ws ∧ Value.beqList ws vs = true := by
  cases a <;> simp [Value.beq]
end oneSided

@[eval_inv] theorem Value.beqList_nil_right (as : List Value) : Value.beqList as [] = true ↔ as = [] := by
  cases as <;> simp [Value.beqList]
@[eval_inv] theorem Value.beqList_cons_right (as : List Value) (b : Value) (bs : List Value) :
    Value.beqList as (b :: bs) = true ↔ ∃ a as', as = a :: as' ∧ Value.beq a b = true ∧ Value.beqList as' bs = true := by
  cases as <;> simp [Value.beqList]

theorem Value.beqList_iff_forall₂ (as bs : List Value) :
    Value.beqList as bs = true ↔ List.Forall₂ (fun a b => Value.beq a b = true) as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [Value.beqList]
  | cons a as ih => cases bs <;> simp [Value.beqList, ih]

theorem Value.beqList_length {as bs : List Value} (h : Value.beqList as bs = true) : as.length = bs.length :=
  ((Value.beqList_iff_forall₂ as bs).mp h).length_eq

/-- A known option-free element transfers across a `beqList`. -/
theorem Value.beqList_getElem?_of_optFree {as bs : List Value} (h : Value.beqList as bs = true) {i : Nat} {b : Value}
    (hb : bs[i]? = some b) (ho : b.optFree = true) : as[i]? = some b := by
  induction bs generalizing as i with
  | nil => simp at hb
  | cons b' bs ih =>
    cases as with
    | nil => simp [Value.beqList] at h
    | cons a as =>
      simp only [Value.beqList, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp at hb ⊢; subst hb
        exact (Value.beq_iff_eq_of_optFree_right ho).mp h.1
      | succ i => simpa using ih h.2 (by simpa using hb)

@[simp, eval_inv] theorem Value.optFree_wrap (k : NumKind) (n : Int) : (k.wrap n).optFree = true := by
  cases k <;> rfl

@[simp, eval_inv] theorem Value.optFree_bytesToVColl (bs : List UInt8) : (bytesToVColl bs).optFree = true := by
  unfold bytesToVColl; simp only [Value.optFree]
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [Value.optFreeList, Value.optFree, ih]

@[eval_inv] theorem bytesToVColl_inj (a b : List UInt8) : bytesToVColl a = bytesToVColl b ↔ a = b := by
  constructor
  · intro h; exact (bytesToVColl_beq_true a b).mp (by rw [h]; exact Value.beq_refl _)
  · rintro rfl; rfl

/-! ## Arithmetic: `arithRes` to plain `Int` facts with overflow bounds -/

/-- Lower bound of `k`'s range. -/
abbrev NumKind.lo (k : NumKind) : Int := k.bounds.1
/-- Upper bound of `k`'s range. -/
abbrev NumKind.hi (k : NumKind) : Int := k.bounds.2

@[eval_inv] theorem NumKind.lo_bigint : NumKind.lo .bigint = -(2 ^ 255) := rfl
@[eval_inv] theorem NumKind.hi_bigint : NumKind.hi .bigint = 2 ^ 255 - 1 := rfl
@[eval_inv] theorem NumKind.lo_long : NumKind.lo .long = -9223372036854775808 := rfl
@[eval_inv] theorem NumKind.hi_long : NumKind.hi .long = 9223372036854775807 := rfl
@[eval_inv] theorem NumKind.lo_int : NumKind.lo .int = -2147483648 := rfl
@[eval_inv] theorem NumKind.hi_int : NumKind.hi .int = 2147483647 := rfl
@[eval_inv] theorem NumKind.lo_short : NumKind.lo .short = -32768 := rfl
@[eval_inv] theorem NumKind.hi_short : NumKind.hi .short = 32767 := rfl
@[eval_inv] theorem NumKind.lo_byte : NumKind.lo .byte = -128 := rfl
@[eval_inv] theorem NumKind.hi_byte : NumKind.hi .byte = 127 := rfl

theorem checkedArith_eq_some_iff (k : NumKind) (op : Int → Int → Int) (a b z : Int) :
    checkedArith k op a b = some z ↔ z = op a b ∧ k.lo ≤ op a b ∧ op a b ≤ k.hi := by
  simp only [checkedArith, NumKind.inRange, NumKind.lo, NumKind.hi]
  by_cases h : k.bounds.1 ≤ op a b ∧ op a b ≤ k.bounds.2
  · simp [h, eq_comm]
  · rw [if_neg (by simpa using h)]
    simp only [reduceCtorEq, false_iff]
    exact fun ⟨_, h1⟩ => h h1

@[eval_inv] theorem arithRes_plus_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .plus k a b = some z ↔ z = a + b ∧ k.lo ≤ a + b ∧ a + b ≤ k.hi :=
  checkedArith_eq_some_iff k _ a b z
@[eval_inv] theorem arithRes_minus_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .minus k a b = some z ↔ z = a - b ∧ k.lo ≤ a - b ∧ a - b ≤ k.hi :=
  checkedArith_eq_some_iff k _ a b z
@[eval_inv] theorem arithRes_multiply_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .multiply k a b = some z ↔ z = a * b ∧ k.lo ≤ a * b ∧ a * b ≤ k.hi :=
  checkedArith_eq_some_iff k _ a b z
@[eval_inv] theorem arithRes_max_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .max k a b = some z ↔ z = max a b := by simp [arithRes, eq_comm]
@[eval_inv] theorem arithRes_min_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .min k a b = some z ↔ z = min a b := by simp [arithRes, eq_comm]

/-- `tdiv` is Lean's truncating division `Int.tdiv`. -/
theorem tdiv_eq_tdiv (a b : Int) : tdiv a b = a.tdiv b := by
  unfold tdiv
  cases a <;> cases b <;> simp [Int.tdiv, Int.natAbs, Int.negSucc_lt_zero] <;> omega

@[eval_inv] theorem arithRes_divide_eq_some_iff (k : NumKind) (a b z : Int) :
    arithRes .divide k a b = some z ↔ b ≠ 0 ∧ ¬(a = k.lo ∧ b = -1) ∧ z = tdiv a b := by
  simp only [arithRes, checkedDiv]
  by_cases h0 : b = 0 <;> simp [h0]
  by_cases h1 : a = k.lo ∧ b = -1
  · simp [h1.1, h1.2]
  · simp [eq_comm]

/-- Upcasting to `BigInt` never fails and keeps the payload. -/
@[eval_inv high] theorem upcastValue_bigint_eq_some_iff (k : NumKind) (p z : Int) :
    upcastValue k p .bigint = some z ↔ p = z := by
  cases k <;> simp [upcastValue, NumKind.rank]

end ErgoTreeLean
