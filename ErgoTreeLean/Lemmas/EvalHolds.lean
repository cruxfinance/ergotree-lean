/-
The sigma-proposition layer of the symbolic-evaluation tooling.

`EvalHolds c ctx env signers e` says `e` evaluates to a sigma-proposition the
holders of `signers` can satisfy. `spendable` is `EvalHolds` of the inlined
tree in the empty environment (`spendable_iff`), and the `@[eval_inv]` rules
below push `EvalHolds` through the sigma connectives, so a spendability
hypothesis about a whole contract breaks down into ordinary `eval … = .ok …`
facts about its boolean conditions, which `EvalInv.lean`'s rules then take
apart.

`sigmaAnd`, `boolToSigmaProp`, `createProveDlog`, `blockValue` and `ifExpr`
have exact (`↔`) rules. `sigmaOr` and `atLeast` only have forward rules
(`EvalHolds_sigmaOr_imp`, `EvalHolds_atLeast_proveDlogs`), because only
soundness of the `Cor`/`Cthreshold` normal forms is proved.
-/
import ErgoTreeLean.Lemmas.EvalInv
import ErgoTreeLean.Lemmas.SigmaHolds
import ErgoTreeLean.Lemmas.Beq

namespace ErgoTreeLean

/-- `e` evaluates, in `env`, to a sigma-proposition `signers` can satisfy. -/
def EvalHolds (c : List Value) (x : Context) (env : Env) (signers : List PK) (e : Expr) : Prop :=
  ∃ sb, eval c x env e = .ok (.vSigmaProp sb) ∧ holds signers sb

theorem spendable_iff (c : List Value) (x : Context) (signers : List PK) (tree : Expr) :
    spendable c x signers tree ↔ ∃ t, inlineFuns tree = some t ∧ EvalHolds c x [] signers t := by
  simp [spendable, EvalHolds]

/-- For a tree `inlineFuns` leaves unchanged (no `ValDef`-bound lambdas). -/
theorem spendable_of_inlineFuns_eq {c : List Value} {x : Context} {signers : List PK} {tree : Expr}
    (hinl : inlineFuns tree = some tree) (h : spendable c x signers tree) : EvalHolds c x [] signers tree := by
  obtain ⟨t, ht, hh⟩ := (spendable_iff c x signers tree).mp h
  rw [hinl] at ht; cases ht; exact hh

variable (c : List Value) (x : Context) (env : Env) (signers : List PK)

@[eval_inv] theorem EvalHolds_blockValue_nil (r : Expr) :
    EvalHolds c x env signers (.blockValue [] r) ↔ EvalHolds c x env signers r := by
  simp [EvalHolds, eval_blockValue_nil_ok]

@[eval_inv] theorem EvalHolds_blockValue_cons (i : Nat) (e : Expr) (rest : List (Nat × Expr)) (r : Expr) :
    EvalHolds c x env signers (.blockValue ((i, e) :: rest) r) ↔
      ∃ v, eval c x env e = .ok v ∧ EvalHolds c x ((i, v) :: env) signers (.blockValue rest r) := by
  simp only [EvalHolds, eval_blockValue_cons_ok]
  constructor
  · rintro ⟨sb, ⟨v, hv, h⟩, hh⟩; exact ⟨v, hv, sb, h, hh⟩
  · rintro ⟨v, hv, sb, h, hh⟩; exact ⟨sb, ⟨v, hv, h⟩, hh⟩

@[eval_inv] theorem EvalHolds_boolToSigmaProp (e : Expr) :
    EvalHolds c x env signers (.boolToSigmaProp e) ↔ eval c x env e = .ok (.vBool true) := by
  simp only [EvalHolds, eval_boolToSigmaProp_ok]
  constructor
  · rintro ⟨sb, ⟨b, hb, heq⟩, hh⟩
    simp only [Value.vSigmaProp.injEq] at heq; subst heq; cases b <;> simp_all [holds]
  · intro h; exact ⟨_, ⟨true, h, rfl⟩, by simp [holds]⟩

@[eval_inv] theorem EvalHolds_createProveDlog (e : Expr) :
    EvalHolds c x env signers (.createProveDlog e) ↔ ∃ g, eval c x env e = .ok (.vGroupElement g) ∧ g ∈ signers := by
  simp only [EvalHolds, eval_createProveDlog_ok]
  constructor
  · rintro ⟨sb, ⟨g, hg, heq⟩, hh⟩; simp only [Value.vSigmaProp.injEq] at heq; subst heq; exact ⟨g, hg, hh⟩
  · rintro ⟨g, hg, hh⟩; exact ⟨_, ⟨g, hg, rfl⟩, hh⟩

@[eval_inv] theorem EvalHolds_ifExpr (cnd t f : Expr) :
    EvalHolds c x env signers (.ifExpr cnd t f) ↔
      (eval c x env cnd = .ok (.vBool true) ∧ EvalHolds c x env signers t) ∨
      (eval c x env cnd = .ok (.vBool false) ∧ EvalHolds c x env signers f) := by
  simp only [EvalHolds, eval_ifExpr_ok]; aesop

theorem evalList_toSigmaProps_holdsAll (items : List Expr) :
    (∃ vs sbs, evalList c x env items = .ok vs ∧ toSigmaProps vs = .ok sbs ∧ ∀ sb ∈ sbs, holds signers sb) ↔
      ∀ e ∈ items, EvalHolds c x env signers e := by
  induction items with
  | nil => simp [evalList_nil_ok, toSigmaProps_nil_ok]
  | cons e rest ih =>
    rw [List.forall_mem_cons, ← ih]
    constructor
    · rintro ⟨vs0, sbs0, hvs0, hsbs0, hall⟩
      rw [evalList_cons_ok] at hvs0
      obtain ⟨v, vs, hv, hvs, rfl⟩ := hvs0
      rw [toSigmaProps_cons_ok] at hsbs0
      obtain ⟨sb, sbs, rfl, hsbs, rfl⟩ := hsbs0
      exact ⟨⟨sb, hv, hall sb (by simp)⟩, vs, sbs, hvs, hsbs, fun s hs => hall s (by simp [hs])⟩
    · rintro ⟨⟨sb, hv, hh⟩, vs, sbs, hvs, hsbs, hall⟩
      refine ⟨_, sb :: sbs, (evalList_cons_ok ..).mpr ⟨_, vs, hv, hvs, rfl⟩,
        (toSigmaProps_cons_ok ..).mpr ⟨sb, sbs, rfl, hsbs, rfl⟩, ?_⟩
      intro s hs; simp at hs; rcases hs with rfl | hs
      · exact hh
      · exact hall s hs

@[eval_inv] theorem EvalHolds_sigmaAnd (items : List Expr) :
    EvalHolds c x env signers (.sigmaAnd items) ↔ ∀ e ∈ items, EvalHolds c x env signers e := by
  rw [← evalList_toSigmaProps_holdsAll]
  simp only [EvalHolds, eval_sigmaAnd_ok]
  constructor
  · rintro ⟨sb, ⟨vs, sbs, hvs, hsbs, heq⟩, hh⟩
    cases heq
    exact ⟨vs, sbs, hvs, hsbs, (holds_normalizeCand_iff signers sbs).mp hh⟩
  · rintro ⟨vs, sbs, hvs, hsbs, hall⟩
    exact ⟨_, ⟨vs, sbs, hvs, hsbs, rfl⟩, (holds_normalizeCand_iff signers sbs).mpr hall⟩

theorem toSigmaProps_ok_mem {vs : List Value} {sbs : List SigmaBoolean} (h : toSigmaProps vs = .ok sbs) :
    ∀ sb ∈ sbs, .vSigmaProp sb ∈ vs := by
  induction vs generalizing sbs with
  | nil => simp [toSigmaProps_nil_ok] at h; simp [h]
  | cons v vs ih =>
    rw [toSigmaProps_cons_ok] at h
    obtain ⟨sb, sbs', rfl, h', rfl⟩ := h
    intro s hs; simp at hs; rcases hs with rfl | hs
    · simp
    · exact List.mem_cons_of_mem _ (ih h' s hs)

/-- `sigmaOr`, forward: some disjunct holds. -/
theorem EvalHolds_sigmaOr_imp (items : List Expr) (h : EvalHolds c x env signers (.sigmaOr items)) :
    ∃ e ∈ items, EvalHolds c x env signers e := by
  obtain ⟨sb, hev, hh⟩ := h
  rw [eval_sigmaOr_ok] at hev
  obtain ⟨vs, sbs, hvs, hsbs, heq⟩ := hev
  cases heq
  obtain ⟨s, hs, hsh⟩ := (holdsAny_iff_exists_mem signers sbs).mp (holds_normalizeCor_imp signers sbs hh)
  have hmem := toSigmaProps_ok_mem hsbs s hs
  clear hsbs
  induction items generalizing vs with
  | nil => simp [evalList_nil_ok] at hvs; subst hvs; simp at hmem
  | cons e rest ih =>
    rw [evalList_cons_ok] at hvs
    obtain ⟨v, vs', hv, hvs', rfl⟩ := hvs
    simp at hmem; rcases hmem with rfl | hmem
    · exact ⟨e, by simp, s, hv, hsh⟩
    · obtain ⟨e', he', hh'⟩ := ih vs' hvs' hmem
      exact ⟨e', List.mem_cons_of_mem _ he', hh'⟩

theorem mapHelper_createProveDlog_shape (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (τ : SType)
    (l : List Value) :
    ∀ out : List Value,
      mapHelper consts ctx env argId (Expr.createProveDlog (Expr.valUse argId τ)) l = Except.ok out →
      ∃ keys : List (List UInt8), l = keys.map Value.vGroupElement ∧
        out = keys.map (fun pk => Value.vSigmaProp (SigmaBoolean.proveDlog pk)) := by
  induction l with
  | nil =>
      intro out h
      simp only [mapHelper, pure, Pure.pure, Except.pure] at h
      exact ⟨[], rfl, by simpa using h.symm⟩
  | cons v vs ih =>
      intro out h
      cases hveq : v with
      | vGroupElement g =>
          have hv : eval consts ctx ((argId, Value.vGroupElement g) :: env)
              (Expr.createProveDlog (Expr.valUse argId τ)) = Except.ok (Value.vSigmaProp (SigmaBoolean.proveDlog g)) := by
            simp [eval, List.find?, beq_self_eq_true, Except.bind, bind, pure, Pure.pure, Except.pure]
          simp only [mapHelper, hveq, hv, Except.bind, bind] at h
          rcases hrest : mapHelper consts ctx env argId (Expr.createProveDlog (Expr.valUse argId τ)) vs with _ | restv
          · simp [hrest] at h
          · rw [hrest] at h
            simp only [Except.bind, bind, pure, Pure.pure, Except.pure] at h
            obtain ⟨keys, hl, hout⟩ := ih restv hrest
            have houtEq : out = Value.vSigmaProp (SigmaBoolean.proveDlog g) :: restv := by simpa using h.symm
            refine ⟨g :: keys, by simp [hveq, hl], ?_⟩
            simp [houtEq, hout]
      | _ =>
          exfalso
          have herr : eval consts ctx ((argId, v) :: env) (Expr.createProveDlog (Expr.valUse argId τ))
              = Except.error (EvalError.error "createProveDlog: not a GroupElement") := by
            simp [eval, hveq, List.find?, beq_self_eq_true, Except.bind, bind, pure, Pure.pure, Except.pure]
          simp [mapHelper, herr, Except.bind, bind] at h

/-- The multisig idiom `atLeast(k, keys.map { pk => proveDlog(pk) })`,
    forward: the bound and key collection evaluate, every key is a
    `GroupElement`, and at least `k` of them are among `signers`. -/
theorem EvalHolds_atLeast_proveDlogs (b coll : Expr) (a : Nat) (t t' et : SType)
    (h : EvalHolds c x env signers
      (.atLeast b (.mapOf coll (.funcValue [(a, t)] (.createProveDlog (.valUse a t'))) et))) :
    ∃ (k : Int) (τ : SType) (keys : List (List UInt8)), eval c x env b = .ok (.vInt k) ∧
      eval c x env coll = .ok (.vColl τ (keys.map Value.vGroupElement)) ∧
      k ≤ (keys.countP (fun pk => signers.contains pk) : Int) := by
  obtain ⟨sb, hev, hh⟩ := h
  rw [eval_atLeast_ok] at hev
  obtain ⟨k, τ, vs, sbs, hb, hm, hsbs, hk0, -, -, -, heq⟩ := hev
  simp only [Value.vSigmaProp.injEq] at heq; subst heq
  rw [eval_map_ok] at hm
  obtain ⟨τ', raw, out, hcoll, hmap, hvs⟩ := hm
  simp only [Value.vColl.injEq] at hvs; obtain ⟨-, rfl⟩ := hvs
  obtain ⟨keys, hraw, hout⟩ := mapHelper_createProveDlog_shape c x env a t' raw _ hmap
  subst hraw hout
  have hsb : sbs = keys.map SigmaBoolean.proveDlog := by
    clear hh hmap hcoll
    induction keys generalizing sbs with
    | nil => simpa [toSigmaProps_nil_ok] using hsbs
    | cons g gs ih =>
      simp only [List.map_cons, toSigmaProps_cons_ok] at hsbs
      obtain ⟨s, ss, hs, hss, rfl⟩ := hsbs
      cases hs; rw [ih ss hss]; rfl
  subst hsb
  have := holdsAtLeast_proveDlog_imp_countP signers k.toNat keys
    (cthresholdReduce_sound signers k.toNat _ hh)
  exact ⟨k, τ', keys, hb, hcoll, by omega⟩

end ErgoTreeLean
