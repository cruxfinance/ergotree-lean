/-
`Value.beq` facts: reflexivity (so `beq = false` really means `≠`), and the
`Coll[Byte]` encoding comparison `bytesToVColl a == bytesToVColl b ↔ a = b`.
Moved here from per-contract lemma files (where they were first proved,
downstream of this repo) so every contract proof can use them.
-/
import ErgoTreeLean.Eval
import Mathlib.Data.List.Nodup

namespace ErgoTreeLean

mutual
theorem SType.beq_refl : ∀ t : SType, SType.beq t t = true
  | .sBoolean | .sByte | .sShort | .sInt | .sLong | .sBigInt | .sGroupElement
  | .sSigmaProp | .sBox | .sAvlTree | .sContext | .sHeader | .sPreHeader
  | .sGlobal | .sUnit | .sAny => rfl
  | .sOption t => by simp [SType.beq, SType.beq_refl t]
  | .sColl t => by simp [SType.beq, SType.beq_refl t]
  | .sTuple ts => by simp [SType.beq, SType.beqList_refl ts]
  | .sFunc ds r => by simp [SType.beq, SType.beqList_refl ds, SType.beq_refl r]

theorem SType.beqList_refl : ∀ ts : List SType, SType.beqList ts ts = true
  | [] => by simp [SType.beqList]
  | t :: ts => by simp [SType.beqList, SType.beq_refl t, SType.beqList_refl ts]
end

mutual
theorem SigmaBoolean.beq_refl : ∀ sb : SigmaBoolean, SigmaBoolean.beq sb sb = true
  | .trivial b => by simp [SigmaBoolean.beq]
  | .proveDlog pk => by simp [SigmaBoolean.beq]
  | .cor items => by simp [SigmaBoolean.beq, SigmaBoolean.beqList_refl items]
  | .cand items => by simp [SigmaBoolean.beq, SigmaBoolean.beqList_refl items]
  | .cthreshold k items => by simp [SigmaBoolean.beq, SigmaBoolean.beqList_refl items]

theorem SigmaBoolean.beqList_refl : ∀ items : List SigmaBoolean, SigmaBoolean.beqList items items = true
  | [] => by simp [SigmaBoolean.beqList]
  | sb :: rest => by simp [SigmaBoolean.beqList, SigmaBoolean.beq_refl sb, SigmaBoolean.beqList_refl rest]
end

mutual
theorem Value.beq_refl : ∀ v : Value, Value.beq v v = true
  | .vUnit => by simp [Value.beq]
  | .vBool _ => by simp [Value.beq]
  | .vByte _ => by simp [Value.beq]
  | .vShort _ => by simp [Value.beq]
  | .vInt _ => by simp [Value.beq]
  | .vLong _ => by simp [Value.beq]
  | .vBigInt _ => by simp [Value.beq]
  | .vGroupElement _ => by simp [Value.beq]
  | .vSigmaProp a => by simp [Value.beq, SigmaBoolean.beq_refl a]
  | .vBox a => by simp [Value.beq, Box.beq_refl a]
  | .vColl te vs => by simp [Value.beq, SType.beq_refl te, Value.beqList_refl vs]
  | .vTuple vs => by simp [Value.beq, Value.beqList_refl vs]
  | .vOption _ o =>
      match o with
      | none => by simp [Value.beq]
      | some x => by simp [Value.beq, Value.beq_refl x]

theorem Value.beqList_refl : ∀ vs : List Value, Value.beqList vs vs = true
  | [] => by simp [Value.beqList]
  | v :: vs => by simp [Value.beqList, Value.beq_refl v, Value.beqList_refl vs]

theorem Box.beq_refl : ∀ b : Box, Box.beq b b = true
  | ⟨_id, _v, _p, t, r⟩ => by simp [Box.beq, Box.beqTokens_refl t, Box.beqRegisters_refl r]

theorem Box.beqTokens_refl : ∀ t : List (List UInt8 × Int), Box.beqTokens t t = true
  | [] => by simp [Box.beqTokens]
  | _ :: xs => by simp [Box.beqTokens, Box.beqTokens_refl xs]

theorem Box.beqRegisters_refl : ∀ r : List (Nat × Value), Box.beqRegisters r r = true
  | [] => by simp [Box.beqRegisters]
  | (_, v) :: xs => by simp [Box.beqRegisters, Value.beq_refl v, Box.beqRegisters_refl xs]
end

/-- The one direction of "`beq` is lawful" actually needed: a `false`
    verdict really does mean the two `Value`s are unequal (the
    contrapositive of `Value.beq_refl`). -/
theorem Value.ne_of_beq_false {a b : Value} (h : Value.beq a b = false) : a ≠ b := by
  intro heq
  subst heq
  simp [Value.beq_refl] at h

theorem signedByteVal_beq (a b : UInt8) : (signedByteVal a == signedByteVal b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  unfold signedByteVal
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  by_cases hA : a.toNat ≥ 128 <;> by_cases hB : b.toNat ≥ 128 <;>
    simp only [hA, hB, if_true, if_false] <;>
    constructor <;> intro h <;>
    first
      | (apply UInt8.toNat.inj; omega)
      | (subst h; omega)
      | omega


theorem bytesToVColl_beq (a b : List UInt8) : Value.beq (bytesToVColl a) (bytesToVColl b) = (a == b) := by
  unfold bytesToVColl
  simp only [Value.beq, SType.beq, Bool.true_and]
  induction a generalizing b with
  | nil => cases b <;> simp [Value.beqList]
  | cons x xs ih =>
    cases b with
    | nil => simp [Value.beqList]
    | cons y ys =>
      simp only [List.map_cons, Value.beqList, Value.beq, signedByteVal_beq, ih ys, List.cons_beq_cons]


@[simp] theorem bytesToVColl_beq_true (a b : List UInt8) :
    Value.beq (bytesToVColl a) (bytesToVColl b) = true ↔ a = b := by
  rw [bytesToVColl_beq]; simp


/-- A list whose distinct-index pairs are all `Value.beq`-unequal is
    duplicate-free (the usual reading of a pairwise `!=` check). -/
theorem nodup_of_pairwise_beq_false (l : List Value)
    (h : ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j → Value.beq l[i] l[j] = false) :
    l.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hjlen
  have hilen : i < l.length := by omega
  have hbeq := h i j hilen hjlen (by omega)
  have hne := Value.ne_of_beq_false hbeq
  rw [List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen]
  simpa using hne




/-! `Value.beq` on constructor-headed scalars, for `eval_inv`. -/
section
variable (a b : Int)
@[simp] theorem Value.beq_vInt : Value.beq (.vInt a) (.vInt b) = (a == b) := by simp [Value.beq]
@[simp] theorem Value.beq_vLong : Value.beq (.vLong a) (.vLong b) = (a == b) := by simp [Value.beq]
@[simp] theorem Value.beq_vShort : Value.beq (.vShort a) (.vShort b) = (a == b) := by simp [Value.beq]
@[simp] theorem Value.beq_vByte : Value.beq (.vByte a) (.vByte b) = (a == b) := by simp [Value.beq]
@[simp] theorem Value.beq_vBigInt : Value.beq (.vBigInt a) (.vBigInt b) = (a == b) := by simp [Value.beq]
@[simp] theorem Value.beq_vBool (p q : Bool) : Value.beq (.vBool p) (.vBool q) = (p == q) := by
  simp [Value.beq]
@[simp] theorem Value.beq_vGroupElement (g h : List UInt8) :
    Value.beq (.vGroupElement g) (.vGroupElement h) = (g == h) := by simp [Value.beq]
end

/-- The shape `eval_sym` leaves for the pairwise-distinctness idiom
    `ks.indices.forall { i => ks.indices.forall { j => i == j || ks(i) != ks(j) } }`. -/
theorem nodup_of_pairwise_getElem?_beq_false (l : List Value)
    (h : ∀ i, i < l.length → ∀ j, j < l.length →
      i = j ∨ ¬ i = j ∧ ∃ a, l[i]? = some a ∧ ∃ b, l[j]? = some b ∧ Value.beq a b = false) :
    l.Nodup := by
  apply nodup_of_pairwise_beq_false
  intro i j hi hj hne
  rcases h i hi j hj with h | ⟨-, a, ha, b, hb, hab⟩
  · exact absurd h hne
  · rw [List.getElem?_eq_getElem hi] at ha; rw [List.getElem?_eq_getElem hj] at hb
    cases ha; cases hb; exact hab

theorem List.eq_singleton_of_length_getElem? {α : Type} {l : List α} {a : α}
    (hl : (l.length : Int) = 1) (h0 : l[0]? = some a) : l = [a] := by
  match l, hl with
  | [x], _ => simp at h0; rw [h0]

end ErgoTreeLean
