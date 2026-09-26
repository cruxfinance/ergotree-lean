/-
Generic facts about `holds` (`Sigma.lean`) against the normal forms `eval`
builds (`normalizeCand`/`normalizeCor`/`cthresholdReduce`). Moved here from
a per-contract lemma file (where they were first proved, downstream of
this repo) so every contract proof can use them; `holds_normalizeCand_iff`
is new.
-/
import ErgoTreeLean.Sigma
import ErgoTreeLean.Eval

namespace ErgoTreeLean

/-- `holdsAny`/`holdsAll` restated as a plain list quantifier — the
    natural bridge between the recursive `∨`/`∧`-chain definitions
    (`Sigma.lean`) and `List.filter`/`List.mem`-based reasoning below. -/
theorem holdsAny_iff_exists_mem (signers : List PK) (l : List SigmaBoolean) :
    holdsAny signers l ↔ ∃ sb ∈ l, holds signers sb := by
  induction l with
  | nil => simp [holdsAny]
  | cons x xs ih => simp [holdsAny, ih]

theorem holdsAll_iff_forall_mem (signers : List PK) (l : List SigmaBoolean) :
    holdsAll signers l ↔ ∀ sb ∈ l, holds signers sb := by
  induction l with
  | nil => simp [holdsAll]
  | cons x xs ih => simp [holdsAll, ih]

/-- A `SigmaBoolean` flagged `isTrivial true` always `holds`, for any
    `signers` — the fact that lets a `TrivialProp(true)` item vanish from
    `normalizeCand`'s survivor list without losing anything. -/
theorem holds_of_isTrivial_true (signers : List PK) {sb : SigmaBoolean}
    (h : isTrivial true sb = true) : holds signers sb := by
  cases sb with
  | trivial b =>
      simp only [isTrivial, beq_iff_eq] at h
      subst h; simp [holds]
  | _ => simp [isTrivial] at h

/-- Symmetric fact for `normalizeCor`: an `isTrivial false` item never
    `holds`, for any `signers` — this is what lets it be dropped from
    `normalizeCor`'s survivor list without changing whether *some* item
    holds. -/
theorem not_holds_of_isTrivial_false (signers : List PK) {sb : SigmaBoolean}
    (h : isTrivial false sb = true) : ¬ holds signers sb := by
  cases sb with
  | trivial b =>
      simp only [isTrivial, beq_iff_eq] at h
      subst h; simp [holds]
  | _ => simp [isTrivial] at h

/-- `holdsAll signers l` follows from `holdsAll signers` on the sub-list
    that survives dropping every `isTrivial true` item — dropped items
    hold for free (`holds_of_isTrivial_true`), so nothing is lost. -/
theorem holdsAll_filter_not_isTrivialTrue (signers : List PK) (l : List SigmaBoolean)
    (h : holdsAll signers (l.filter (fun sb => !isTrivial true sb))) : holdsAll signers l := by
  induction l with
  | nil => simp [holdsAll]
  | cons x xs ih =>
      by_cases hx : isTrivial true x = true
      · have hxfilter : (x :: xs).filter (fun sb => !isTrivial true sb)
            = xs.filter (fun sb => !isTrivial true sb) := by simp [hx]
        rw [hxfilter] at h
        exact ⟨holds_of_isTrivial_true signers hx, ih h⟩
      · have hx' : isTrivial true x = false := by
          cases h' : isTrivial true x with
          | true => exact absurd h' hx
          | false => rfl
        have hxfilter : (x :: xs).filter (fun sb => !isTrivial true sb)
            = x :: xs.filter (fun sb => !isTrivial true sb) := by simp [hx']
        rw [hxfilter] at h
        exact ⟨h.1, ih h.2⟩

/-- Dual fact for `normalizeCor`: `holdsAny signers l` follows from
    `holdsAny signers` on the sub-list surviving dropping every
    `isTrivial false` item — dropped items never hold
    (`not_holds_of_isTrivial_false`) so they could never have witnessed
    `holdsAny` anyway. -/
theorem holdsAny_filter_not_isTrivialFalse (signers : List PK) (l : List SigmaBoolean)
    (h : holdsAny signers (l.filter (fun sb => !isTrivial false sb))) : holdsAny signers l := by
  induction l with
  | nil => simp [holdsAny] at h
  | cons x xs ih =>
      by_cases hx : isTrivial false x = true
      · have hxfilter : (x :: xs).filter (fun sb => !isTrivial false sb)
            = xs.filter (fun sb => !isTrivial false sb) := by simp [hx]
        rw [hxfilter] at h
        exact Or.inr (ih h)
      · have hx' : isTrivial false x = false := by
          cases h' : isTrivial false x with
          | true => exact absurd h' hx
          | false => rfl
        have hxfilter : (x :: xs).filter (fun sb => !isTrivial false sb)
            = x :: xs.filter (fun sb => !isTrivial false sb) := by simp [hx']
        rw [hxfilter] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (ih h)

/-- **`normalizeCand` soundness (one direction, all we need):** if the
    normalized `Cand` `holds`, then every original item `holds` —
    mirrors `Cand::normalized`'s three cases (absorb/drop/wrap) exactly. -/
theorem holds_normalizeCand_imp (signers : List PK) (l : List SigmaBoolean)
    (h : holds signers (normalizeCand l)) : holdsAll signers l := by
  unfold normalizeCand at h
  by_cases habs : l.any (isTrivial false) = true
  · rw [if_pos habs] at h
    simp [holds] at h
  · rw [if_neg habs] at h
    apply holdsAll_filter_not_isTrivialTrue signers l
    rw [holdsAll_iff_forall_mem]
    generalize hsurv : l.filter (fun sb => !isTrivial true sb) = survivors at h
    rcases survivors with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · intro sb hsb; simp at hsb
    · intro sb hsb; simp only [List.mem_singleton] at hsb; subst hsb; exact h
    · intro sb hsb
      exact (holdsAll_iff_forall_mem signers (x :: y :: rest)).mp h sb hsb

/-- **`normalizeCor` soundness (one direction, all we need):** if the
    normalized `Cor` `holds`, then *some* original item `holds` — mirrors
    `Cor::normalized`'s three cases. -/
theorem holds_normalizeCor_imp (signers : List PK) (l : List SigmaBoolean)
    (h : holds signers (normalizeCor l)) : holdsAny signers l := by
  unfold normalizeCor at h
  by_cases habs : l.any (isTrivial true) = true
  · rw [if_pos habs] at h
    rw [holdsAny_iff_exists_mem]
    have := List.any_eq_true.mp habs
    obtain ⟨sb, hsb, hsbTrivial⟩ := this
    exact ⟨sb, hsb, holds_of_isTrivial_true signers hsbTrivial⟩
  · rw [if_neg habs] at h
    apply holdsAny_filter_not_isTrivialFalse signers l
    rw [holdsAny_iff_exists_mem]
    generalize hsurv : l.filter (fun sb => !isTrivial false sb) = survivors at h
    rcases survivors with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp [holds] at h
    · exact ⟨x, List.mem_singleton_self x, h⟩
    · exact (holdsAny_iff_exists_mem signers (x :: y :: rest)).mp h

/-- `holdsAny → holdsAtLeast 1` (`Cor` and threshold `k = 1` express the
    same thing: "some ≥1-of-n item holds"). -/
theorem holdsAny_imp_holdsAtLeast_one (signers : List PK) (l : List SigmaBoolean)
    (h : holdsAny signers l) : holdsAtLeast signers 1 l := by
  induction l with
  | nil => simp [holdsAny] at h
  | cons x xs ih =>
      rcases h with h | h
      · exact Or.inl ⟨h, by simp [holdsAtLeast]⟩
      · exact Or.inr (ih h)

/-- `holdsAll → holdsAtLeast l.length` (`Cand` and threshold `k = n`
    express the same thing: "every one of the n items holds"). -/
theorem holdsAll_imp_holdsAtLeast_length (signers : List PK) (l : List SigmaBoolean)
    (h : holdsAll signers l) : holdsAtLeast signers l.length l := by
  induction l with
  | nil => simp [holdsAtLeast]
  | cons x xs ih => exact Or.inl ⟨h.1, ih h.2⟩

theorem holdsAtLeast_one_of_holds_mem (signers : List PK) (l : List SigmaBoolean) (sb : SigmaBoolean)
    (hmem : sb ∈ l) (hsb : holds signers sb) : holdsAtLeast signers 1 l :=
  holdsAny_imp_holdsAtLeast_one signers l ((holdsAny_iff_exists_mem signers l).mpr ⟨sb, hmem, hsb⟩)

/-- **Monotonicity under insertion.** Inserting an *arbitrary* extra item
    anywhere into the pool can never break an existing `holdsAtLeast`
    witness — needed for `cthresholdGo_sound`'s "drop a `TrivialProp
    false` item" step: the induction hypothesis only talks about the pool
    with that item already removed, but the goal is about the pool with
    it still present (`res` sits *before* `remaining` in the real pool,
    so peeling `remaining`'s head is not peeling the pool's head unless
    `res = []`). -/
theorem holdsAtLeast_insert (signers : List PK) :
    ∀ (l1 l2 : List SigmaBoolean) (sb : SigmaBoolean) (k : Nat),
      holdsAtLeast signers k (l1 ++ l2) → holdsAtLeast signers k (l1 ++ sb :: l2)
  | [], _, _, k, h => by
      cases k with
      | zero => simp [holdsAtLeast]
      | succ m => exact Or.inr h
  | x :: xs, l2, sb, k, h => by
      cases k with
      | zero => simp [holdsAtLeast]
      | succ m =>
          rcases h with ⟨hx, hrest⟩ | hrest
          · exact Or.inl ⟨hx, holdsAtLeast_insert signers xs l2 sb m hrest⟩
          · exact Or.inr (holdsAtLeast_insert signers xs l2 sb (m + 1) hrest)

/-- **Credited insertion.** Same as `holdsAtLeast_insert`, but the
    inserted item is known to itself `hold`, so the threshold can rise by
    one — needed for the "consume a `TrivialProp true` item" step (the
    consumed item is at `remaining`'s head, again not the pool's head
    unless `res = []`). -/
theorem holdsAtLeast_insert_holds (signers : List PK) :
    ∀ (l1 l2 : List SigmaBoolean) (sb : SigmaBoolean) (k : Nat),
      holds signers sb → holdsAtLeast signers k (l1 ++ l2) → holdsAtLeast signers (k + 1) (l1 ++ sb :: l2)
  | [], _, sb, _, hsb, h => Or.inl ⟨hsb, h⟩
  | x :: xs, l2, sb, k, hsb, h => by
      cases k with
      | zero =>
          have hmem : sb ∈ (x :: xs) ++ sb :: l2 := by simp
          exact holdsAtLeast_one_of_holds_mem signers _ sb hmem hsb
      | succ m =>
          rcases h with ⟨hx, hrest⟩ | hrest
          · exact Or.inl ⟨hx, holdsAtLeast_insert_holds signers xs l2 sb m hsb hrest⟩
          · exact Or.inr (holdsAtLeast_insert_holds signers xs l2 sb (m + 1) hsb hrest)

/-- The main induction, mirroring `cthresholdGo`'s own recursion exactly
    (see its docstring in `Eval.lean`): `childrenLeft` is carried as an
    explicit hypothesis rather than re-derived, since it's exactly the
    loop invariant `Cthreshold::reduce`'s real Rust loop maintains
    (`res.length + remaining.length`, tracked incrementally rather than
    recomputed). -/
theorem cthresholdGo_sound (signers : List PK) :
    ∀ (currK childrenLeft : Nat) (res remaining : List SigmaBoolean),
      childrenLeft = (res ++ remaining).length →
      holds signers (cthresholdGo currK childrenLeft res remaining) →
      holdsAtLeast signers currK (res ++ remaining)
  | currK, childrenLeft, res, [], hlen, h => by
      subst hlen
      simp only [List.append_nil] at *
      by_cases h1 : currK = 1
      · subst h1
        simp only [cthresholdGo, beq_self_eq_true, if_true] at h
        exact holdsAny_imp_holdsAtLeast_one signers res (holds_normalizeCor_imp signers res h)
      · have hb1 : (currK == 1) = false := by simpa using h1
        by_cases h2 : currK = res.length
        · simp only [cthresholdGo, hb1] at h
          rw [if_neg (by simpa using hb1), if_pos (by simp [h2])] at h
          rw [h2]
          exact holdsAll_imp_holdsAtLeast_length signers res (holds_normalizeCand_imp signers res h)
        · have hb2 : (currK == res.length) = false := by simpa using h2
          simp only [cthresholdGo] at h
          rw [if_neg (by simpa using hb1), if_neg (by simpa using hb2)] at h
          simpa [holds] using h
  | currK, childrenLeft, res, sb :: rest, hlen, h => by
      by_cases hk0 : currK = 0
      · subst hk0; simp [holdsAtLeast]
      · by_cases h1 : currK = 1
        · subst h1
          simp only [cthresholdGo, beq_self_eq_true, if_true] at h
          exact holdsAny_imp_holdsAtLeast_one signers (res ++ sb :: rest)
            (holds_normalizeCor_imp signers (res ++ sb :: rest) h)
        · have hb1 : (currK == 1) = false := by simpa using h1
          by_cases h2 : currK = childrenLeft
          · subst h2
            simp only [cthresholdGo] at h
            rw [if_neg (by simpa using hb1), if_pos (by simp)] at h
            rw [hlen]
            exact holdsAll_imp_holdsAtLeast_length signers (res ++ sb :: rest)
              (holds_normalizeCand_imp signers (res ++ sb :: rest) h)
          · have hb2 : (currK == childrenLeft) = false := by simpa using h2
            simp only [cthresholdGo] at h
            rw [if_neg (by simpa using hb1), if_neg (by simpa using hb2)] at h
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            cases sb with
            | trivial b =>
                cases b with
                | true =>
                    have hlen' : childrenLeft - 1 = (res ++ rest).length := by
                      simp only [List.length_append, List.length_cons] at hlen
                      simp only [List.length_append]
                      omega
                    have ih := cthresholdGo_sound signers m (childrenLeft - 1) res rest hlen' h
                    exact holdsAtLeast_insert_holds signers res rest (SigmaBoolean.trivial true) m
                      (by simp [holds]) ih
                | false =>
                    have hlen' : childrenLeft - 1 = (res ++ rest).length := by
                      simp only [List.length_append, List.length_cons] at hlen
                      simp only [List.length_append]
                      omega
                    have ih := cthresholdGo_sound signers (m + 1) (childrenLeft - 1) res rest hlen' h
                    exact holdsAtLeast_insert signers res rest (SigmaBoolean.trivial false) (m + 1) ih
            | proveDlog pk =>
                have heq : (res ++ [SigmaBoolean.proveDlog pk]) ++ rest = res ++ SigmaBoolean.proveDlog pk :: rest := by simp
                have hlen' : childrenLeft = (res ++ [SigmaBoolean.proveDlog pk] ++ rest).length := by
                  rw [List.append_assoc]; simpa using hlen
                have ih := cthresholdGo_sound signers (m + 1) childrenLeft (res ++ [SigmaBoolean.proveDlog pk]) rest
                  (by simpa [List.append_assoc] using hlen') h
                rwa [heq] at ih
            | cor items =>
                have heq : (res ++ [SigmaBoolean.cor items]) ++ rest = res ++ SigmaBoolean.cor items :: rest := by simp
                have hlen' : childrenLeft = (res ++ [SigmaBoolean.cor items] ++ rest).length := by
                  rw [List.append_assoc]; simpa using hlen
                have ih := cthresholdGo_sound signers (m + 1) childrenLeft (res ++ [SigmaBoolean.cor items]) rest
                  (by simpa [List.append_assoc] using hlen') h
                rwa [heq] at ih
            | cand items =>
                have heq : (res ++ [SigmaBoolean.cand items]) ++ rest = res ++ SigmaBoolean.cand items :: rest := by simp
                have hlen' : childrenLeft = (res ++ [SigmaBoolean.cand items] ++ rest).length := by
                  rw [List.append_assoc]; simpa using hlen
                have ih := cthresholdGo_sound signers (m + 1) childrenLeft (res ++ [SigmaBoolean.cand items]) rest
                  (by simpa [List.append_assoc] using hlen') h
                rwa [heq] at ih
            | cthreshold k items =>
                have heq : (res ++ [SigmaBoolean.cthreshold k items]) ++ rest = res ++ SigmaBoolean.cthreshold k items :: rest := by simp
                have hlen' : childrenLeft = (res ++ [SigmaBoolean.cthreshold k items] ++ rest).length := by
                  rw [List.append_assoc]; simpa using hlen
                have ih := cthresholdGo_sound signers (m + 1) childrenLeft (res ++ [SigmaBoolean.cthreshold k items]) rest
                  (by simpa [List.append_assoc] using hlen') h
                rwa [heq] at ih
termination_by currK childrenLeft res remaining => remaining.length

/-- **The lemma `Theorems.lean` actually uses.** If the `atLeast`/
    `Cthreshold` normal form `holds`, then at least `k` of the original
    `children` hold, in the natural k-subset sense (`holdsAtLeast`). -/
theorem cthresholdReduce_sound (signers : List PK) (k : Nat) (children : List SigmaBoolean)
    (h : holds signers (cthresholdReduce k children)) : holdsAtLeast signers k children := by
  unfold cthresholdReduce at h
  by_cases hk0 : k = 0
  · subst hk0; simp [holdsAtLeast]
  · have hb0 : (k == 0) = false := by simpa using hk0
    by_cases hk1 : k > children.length
    · rw [if_neg (by simpa using hb0), if_pos (by simpa using hk1)] at h
      simp [holds] at h
    · rw [if_neg (by simpa using hb0), if_neg (by simpa using hk1)] at h
      have := cthresholdGo_sound signers k children.length [] children (by simp) h
      simpa using this
/-! ## Counting satisfied `proveDlog`s

Bridges `Sigma.lean`'s existential `holdsAtLeast` back to a plain count —
a downstream threshold-signature theorem states its conclusion as
`keys.countP (signers.contains ·) ≥ t`, the reading anyone would actually
check a signer set against, not the recursive existential `holdsAtLeast`
unfolds to. -/
theorem holdsAtLeast_proveDlog_imp_countP (signers : List PK) :
    ∀ (k : Nat) (keys : List (List UInt8)),
      holdsAtLeast signers k (keys.map SigmaBoolean.proveDlog) →
      k ≤ keys.countP (fun pk => signers.contains pk)
  | 0, _, _ => Nat.zero_le _
  | m + 1, [], h => by simp [holdsAtLeast] at h
  | m + 1, pk :: rest, h => by
      rcases h with ⟨hpk, hrest⟩ | hrest
      · have hcontains : signers.contains pk = true := by
          simpa [holds, List.contains_iff_mem] using hpk
        have hm := holdsAtLeast_proveDlog_imp_countP signers m rest hrest
        simp only [List.countP_cons, hcontains, if_true]
        omega
      · have hm1 := holdsAtLeast_proveDlog_imp_countP signers (m + 1) rest hrest
        simp only [List.countP_cons]
        omega


/-- `Cand` normalization is exact for `holds`: the normalized conjunction
    holds iff every item does. -/
theorem holds_normalizeCand_iff (signers : List PK) (l : List SigmaBoolean) :
    holds signers (normalizeCand l) ↔ ∀ sb ∈ l, holds signers sb := by
  constructor
  · intro h; exact (holdsAll_iff_forall_mem signers l).mp (holds_normalizeCand_imp signers l h)
  · intro h
    unfold normalizeCand
    by_cases habs : l.any (isTrivial false) = true
    · exfalso
      obtain ⟨sb, hsb, htriv⟩ := List.any_eq_true.mp habs
      exact not_holds_of_isTrivial_false signers htriv (h sb hsb)
    · rw [if_neg habs]
      have hf : ∀ sb ∈ l.filter (fun sb => !isTrivial true sb), holds signers sb :=
        fun sb hsb => h sb (List.mem_filter.mp hsb).1
      generalize l.filter (fun sb => !isTrivial true sb) = survivors at hf
      rcases survivors with _ | ⟨y, _ | ⟨z, rest⟩⟩
      · simp [holds]
      · exact hf y (by simp)
      · exact (holdsAll_iff_forall_mem signers _).mpr hf

end ErgoTreeLean
