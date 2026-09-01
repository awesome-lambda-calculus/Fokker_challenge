import FokkerChallenge.BetaCheck

/-!
# Terms using at most two variables at every node

Reading a closed term `t` as a tree, every node carries a set of *free* de
Bruijn indices: the enclosing binders whose variable is used somewhere in the
subtree at that node.  This file proves that

> if at every node of `t` at most **two** variables are used, then `t` is a
> β-reduct of a term that is nameable with the two variable names `x`, `y`,

hence (by `BetaReductOfNamable_not_basis`) `t` is not a one-point basis.

The proof is constructive.  A term is nameable with two names exactly when at
every abstraction node `λ.M` at most one *enclosing* binder is used in `M`
(`nameableNodes`); the extra binder introduced by the abstraction itself always
needs a name of its own.  So a term satisfying the weaker condition above may
fail to be nameable, but only because of binders that are *not used* in their
body.  Such a binder can be created by a β-step from `K = λx.λy.x`:

`K N ⭢β λ_.N`.

`namify t` performs this β-expansion at every unused binder of `t`; the two main
lemmas are that `namify t` reduces back to `t` (`namify_betaStar`) and that
`namify t` is nameable with two names (`namableXY_namify`).
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## Free de Bruijn indices -/

/-- The set of de Bruijn indices of `t` that point outside of `t`. -/
def fidx : Term String → Finset ℕ
  | .bvar i => {i}
  | .fvar _ => ∅
  | .app a b => fidx a ∪ fidx b
  | .abs t => ((fidx t).erase 0).image (· - 1)

theorem mem_fidx_abs {t : Term String} {i : ℕ} (hi : i ∈ fidx t) (h0 : i ≠ 0) :
    i - 1 ∈ fidx (Term.abs t) := by
  simp only [fidx, Finset.mem_image]
  exact ⟨i, Finset.mem_erase.2 ⟨h0, hi⟩, rfl⟩

/-- A term whose dangling indices are all `< d` is locally closed at `d`. -/
theorem lcAt_of_fidx : ∀ (t : Term String) (d : ℕ), (∀ i ∈ fidx t, i < d) → LcAt d t = true := by
  intro t
  induction t with
  | bvar i => intro d h; simpa [LcAt] using h i (by simp [fidx])
  | fvar x => intro d _; simp [LcAt]
  | abs t ih =>
      intro d h
      simp only [LcAt]
      refine ih (d + 1) (fun i hi => ?_)
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · omega
      · have := h _ (mem_fidx_abs hi (by omega))
        omega
  | app a b iha ihb =>
      intro d h
      simp only [LcAt, Bool.and_eq_true]
      exact ⟨iha d (fun i hi => h i (by simp [fidx, hi])),
        ihb d (fun i hi => h i (by simp [fidx, hi]))⟩

/-- An index that does not occur free is not touched by opening. -/
theorem openRec_eq_self_of_notMem_fidx : ∀ (t : Term String) (k : ℕ) (u : Term String),
    k ∉ fidx t → openRec k u t = t := by
  intro t
  induction t with
  | bvar i =>
      intro k u h
      simp only [fidx, Finset.mem_singleton] at h
      simp [openRec, h]
  | fvar x => intro k u _; rfl
  | abs t ih =>
      intro k u h
      have hk : k + 1 ∉ fidx t := fun hc => h (by simpa using mem_fidx_abs hc (by omega))
      simp [openRec, ih (k + 1) u hk]
  | app a b iha ihb =>
      intro k u h
      simp only [fidx, Finset.mem_union, not_or] at h
      simp [openRec, iha k u h.1, ihb k u h.2]

/-! ## Lowering all indices above a level -/

/-- `lowerRec k t` decrements every dangling index of `t` that is `> k`.  It
undoes the effect of inserting a binder at level `k` that is never used. -/
def lowerRec (k : ℕ) : Term String → Term String
  | .bvar i => .bvar (if k < i then i - 1 else i)
  | .fvar x => .fvar x
  | .app a b => .app (lowerRec k a) (lowerRec k b)
  | .abs t => .abs (lowerRec (k + 1) t)

theorem fidx_lowerRec : ∀ (t : Term String) (k : ℕ),
    fidx (lowerRec k t) = (fidx t).image (fun j => if k < j then j - 1 else j) := by
  intro t
  induction t with
  | bvar i => intro k; simp [fidx, lowerRec]
  | fvar x => intro k; simp [fidx, lowerRec]
  | abs t ih =>
      intro k
      ext m
      simp only [lowerRec, fidx, ih (k + 1), Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨a, ⟨ha0, j, hj, hja⟩, ham⟩
        have hj0 : j ≠ 0 := by
          intro hc; subst hc; simp at hja; omega
        refine ⟨j - 1, ⟨j, ⟨hj0, hj⟩, rfl⟩, ?_⟩
        split at hja <;> split <;> omega
      · rintro ⟨a, ⟨j, ⟨hj0, hj⟩, hja⟩, ham⟩
        subst hja
        refine ⟨if k + 1 < j then j - 1 else j, ⟨?_, j, hj, rfl⟩, ?_⟩
        · split <;> omega
        · split <;> split at ham <;> omega
  | app a b iha ihb =>
      intro k
      simp [fidx, lowerRec, iha k, ihb k, Finset.image_union]

/-! ## The two conditions -/

/-- `nodeTwoVars t` checks that at every node of `t` at most two variables are
used, i.e. that the body of every abstraction node has at most two free
indices. -/
def nodeTwoVars : Term String → Bool
  | .bvar _ => true
  | .fvar _ => false
  | .app a b => nodeTwoVars a && nodeTwoVars b
  | .abs M => decide ((fidx M).card ≤ 2) && nodeTwoVars M

/-- `closedNodeTwoVars t` additionally requires `t` to be closed. -/
def closedNodeTwoVars (t : Term String) : Bool := nodeTwoVars t && decide (fidx t = ∅)

/-- `nameableNodes t` checks that at every abstraction node `λ.M` of `t` at most
one *enclosing* binder is used inside `M`.  For a closed term this is exactly
nameability with two names (`namableXY_of_nameableNodes`). -/
def nameableNodes : Term String → Bool
  | .bvar _ => true
  | .fvar _ => false
  | .app a b => nameableNodes a && nameableNodes b
  | .abs M => decide (((fidx M).erase 0).card ≤ 1) && nameableNodes M

theorem nameableNodes_lowerRec : ∀ (t : Term String) (k : ℕ),
    nameableNodes t = true → nameableNodes (lowerRec k t) = true := by
  intro t
  induction t with
  | bvar i => intro k _; simp [nameableNodes, lowerRec]
  | fvar x => intro k h; simp [nameableNodes] at h
  | abs M ih =>
      intro k h
      simp only [nameableNodes, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [lowerRec, nameableNodes, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ih (k + 1) h.2⟩
      have hsub : (fidx (lowerRec (k + 1) M)).erase 0 ⊆
          ((fidx M).erase 0).image (fun j => if k + 1 < j then j - 1 else j) := by
        intro m hm
        simp only [Finset.mem_erase, fidx_lowerRec, Finset.mem_image] at hm ⊢
        obtain ⟨hm0, j, hj, hjm⟩ := hm
        have hj0 : j ≠ 0 := by
          intro hc; subst hc; simp at hjm; omega
        exact ⟨j, ⟨hj0, hj⟩, hjm⟩
      calc ((fidx (lowerRec (k + 1) M)).erase 0).card
          ≤ (((fidx M).erase 0).image (fun j => if k + 1 < j then j - 1 else j)).card :=
            Finset.card_le_card hsub
        _ ≤ ((fidx M).erase 0).card := Finset.card_image_le
        _ ≤ 1 := h.1
  | app a b iha ihb =>
      intro k h
      simp only [nameableNodes, Bool.and_eq_true] at h
      simp [lowerRec, nameableNodes, iha k h.1, ihb k h.2]

/-! ## Naming a term with two names -/

/-- The names that the enclosing binders used inside `M` carry, `ctx` listing
the names of the enclosing binders innermost first. -/
def outerNames (ctx : List String) (M : Term String) : Finset String :=
  ((fidx M).erase 0).image (fun i => ctx.getD (i - 1) "x")

/-- The name given to a binder whose body is `M`: any name not used by an
enclosing binder that occurs in `M`. -/
def pickName (ctx : List String) (M : Term String) : String :=
  if "x" ∈ outerNames ctx M then "y" else "x"

/-- The named term denoted by `t` in the context `ctx` of binder names. -/
def nameIt (ctx : List String) : Term String → NTerm
  | .bvar i => .var (ctx.getD i "x")
  | .fvar x => .var x
  | .app a b => .app (nameIt ctx a) (nameIt ctx b)
  | .abs M => .abs (pickName ctx M) (nameIt (pickName ctx M :: ctx) M)

theorem getD_of_lt (l : List String) (i : ℕ) (h : i < l.length) : l.getD i "x" = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem pickName_eq (ctx : List String) (M : Term String) :
    pickName ctx M = "x" ∨ pickName ctx M = "y" := by
  unfold pickName
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The name chosen for a binder differs from the name of every enclosing binder
that is used in its body. -/
theorem pickName_ne {ctx : List String} {M : Term String} {i : ℕ}
    (hcard : ((fidx M).erase 0).card ≤ 1) (hi : i ∈ fidx M) (hi0 : i ≠ 0) :
    pickName ctx M ≠ ctx.getD (i - 1) "x" := by
  have hmem : ctx.getD (i - 1) "x" ∈ outerNames ctx M := by
    simp only [outerNames, Finset.mem_image]
    exact ⟨i, Finset.mem_erase.2 ⟨hi0, hi⟩, rfl⟩
  have hone : (outerNames ctx M).card ≤ 1 :=
    le_trans Finset.card_image_le hcard
  unfold pickName
  split
  · rename_i hx
    intro hc
    have := Finset.card_le_one.1 hone _ hx _ hmem
    rw [← hc] at this
    exact absurd this (by decide)
  · rename_i hx
    intro hc
    exact hx (hc ▸ hmem)

/-- `nameIt` produces a well-scoped named term over `{x, y}` denoting `t`. -/
theorem nameIt_spec : ∀ (t : Term String) (ctx : List String),
    (∀ v ∈ ctx, v = "x" ∨ v = "y") →
    (∀ i ∈ fidx t, i < ctx.length ∧ ∀ j < i, ctx.getD j "x" ≠ ctx.getD i "x") →
    nameableNodes t = true →
      NTerm.WN ctx (nameIt ctx t) ∧ NTerm.toLN ctx (nameIt ctx t) = t := by
  intro t
  induction t with
  | bvar i =>
      intro ctx _ hg _
      obtain ⟨hlt, hsh⟩ := hg i (by simp [fidx])
      have hget : ctx[i]? = some (ctx.getD i "x") := by
        rw [getD_of_lt ctx i hlt, List.getElem?_eq_getElem hlt]
      have hidx : NTerm.idx (ctx.getD i "x") ctx = some i := by
        refine idx_of_get hget (fun j hj hc => ?_)
        have hjlt : j < ctx.length := by omega
        rw [List.getElem?_eq_getElem hjlt, Option.some.injEq] at hc
        exact hsh j hj (by rw [getD_of_lt ctx j hjlt, hc])
      refine ⟨?_, ?_⟩
      · show ctx.getD i "x" ∈ ctx
        rw [getD_of_lt ctx i hlt]
        exact List.getElem_mem hlt
      · simp only [nameIt, NTerm.toLN, hidx]
  | fvar x => intro ctx _ _ h; simp [nameableNodes] at h
  | abs M ih =>
      intro ctx hnames hg hnn
      simp only [nameableNodes, Bool.and_eq_true, decide_eq_true_eq] at hnn
      set v := pickName ctx M with hv
      have hnames' : ∀ w ∈ v :: ctx, w = "x" ∨ w = "y" := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact pickName_eq ctx M
        · exact hnames w hw
      have hg' : ∀ i ∈ fidx M,
          i < (v :: ctx).length ∧ ∀ j < i, (v :: ctx).getD j "x" ≠ (v :: ctx).getD i "x" := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exact ⟨by simp, by omega⟩
        · obtain ⟨hlt, hsh⟩ := hg (i - 1) (mem_fidx_abs hi (by omega))
          obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
          simp only [List.length_cons, List.getD_cons_succ] at *
          refine ⟨by omega, fun j hj => ?_⟩
          match j with
          | 0 =>
              simpa using pickName_ne (ctx := ctx) hnn.1 hi (by omega)
          | j + 1 =>
              simpa using hsh j (by omega)
      obtain ⟨hwn, htoln⟩ := ih (v :: ctx) hnames' hg' hnn.2
      refine ⟨⟨pickName_eq ctx M, hwn⟩, ?_⟩
      simp only [nameIt, NTerm.toLN, ← hv, htoln]
  | app a b iha ihb =>
      intro ctx hnames hg hnn
      simp only [nameableNodes, Bool.and_eq_true] at hnn
      obtain ⟨h1, h2⟩ := iha ctx hnames (fun i hi => hg i (by simp [fidx, hi])) hnn.1
      obtain ⟨h3, h4⟩ := ihb ctx hnames (fun i hi => hg i (by simp [fidx, hi])) hnn.2
      exact ⟨⟨h1, h3⟩, by simp only [nameIt, NTerm.toLN, h2, h4]⟩

/-- A closed term all of whose abstraction nodes use at most one enclosing
binder is nameable with the two names `x`, `y`. -/
theorem namableXY_of_nameableNodes {t : Term String}
    (hn : nameableNodes t = true) (hc : fidx t = ∅) : namableXY t = true := by
  obtain ⟨hwn, htoln⟩ := nameIt_spec t [] (by simp) (by rw [hc]; simp) hn
  have hok : NameOk [] t := by
    have hiff := nameOk_openMany_iff t [] (by simp) (by simp) (by simp)
    simp only [openMany, List.map_nil] at hiff
    exact hiff.2 ⟨nameIt [] t, hwn, htoln⟩
  rw [← isNamedOfXY_eq_namableXY]
  exact (nameOk_nil_iff_isNamedOfXY t).1 hok

/-! ## The β-expansion -/

/-- `K = λx.λy.x`. -/
def KTerm : Term String := .abs (.abs (.bvar 1))

/-- `namify t` replaces every abstraction of `t` whose binder is unused by an
application of `K`, which β-reduces back to it. -/
def namify : Term String → Term String
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .app a b => .app (namify a) (namify b)
  | .abs M => if 0 ∈ fidx M then .abs (namify M) else .app KTerm (lowerRec 0 (namify M))

@[simp] theorem fidx_KTerm : fidx KTerm = ∅ := by decide

theorem fidx_namify : ∀ t : Term String, fidx (namify t) = fidx t := by
  intro t
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | abs M ih =>
      by_cases h0 : 0 ∈ fidx M
      · simp [namify, h0, fidx, ih]
      · simp only [namify, ite_eq_right h0, fidx, fidx_lowerRec, ih, fidx_KTerm, Finset.empty_union]
        rw [Finset.erase_eq_of_notMem h0]
        refine Finset.image_congr ?_
        intro j hj
        have hj0 : j ≠ 0 := fun hc => h0 (hc ▸ hj)
        simp [Nat.pos_of_ne_zero hj0]
  | app a b iha ihb => simp [namify, fidx, iha, ihb]

theorem nameableNodes_namify : ∀ t : Term String,
    nodeTwoVars t = true → nameableNodes (namify t) = true := by
  intro t
  induction t with
  | bvar i => intro _; rfl
  | fvar x => intro h; simp [nodeTwoVars] at h
  | abs M ih =>
      intro h
      simp only [nodeTwoVars, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases h0 : 0 ∈ fidx M
      · simp only [namify, ite_eq_left h0, nameableNodes, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨?_, ih h.2⟩
        rw [fidx_namify, Finset.card_erase_of_mem h0]
        omega
      · simp only [namify, ite_eq_right h0, nameableNodes, Bool.and_eq_true]
        exact ⟨by decide, nameableNodes_lowerRec _ 0 (ih h.2)⟩
  | app a b iha ihb =>
      intro h
      simp only [nodeTwoVars, Bool.and_eq_true] at h
      simp [namify, nameableNodes, iha h.1, ihb h.2]

/-- Indices below the opening level are untouched. -/
theorem openMany_bvar_lt_base : ∀ (env : List (String × String)) (k i : ℕ), i < k →
    openMany k env (bvar i) = bvar i := by
  intro env
  induction env with
  | nil => intro k i _; rfl
  | cons e es ih =>
      intro k i h
      have hne : ¬ (k = i) := by omega
      simp only [openMany, openRec, ite_eq_right hne]
      exact ih (k + 1) i (by omega)

@[simp] theorem openMany_KTerm (k : ℕ) (env : List (String × String)) :
    openMany k env KTerm = KTerm := by
  simp only [KTerm, openMany_abs]
  rw [openMany_bvar_lt_base env (k + 1 + 1) 1 (by omega)]

theorem lc_KTerm : LC (KTerm : Term String) := by
  rw [← lcAt_iff_LC]
  decide

/-- Opening a lowered term is the same as opening the original one level up,
provided the removed index does not occur. -/
theorem openMany_lowerRec : ∀ (t : Term String) (k : ℕ) (env : List (String × String)),
    k ∉ fidx t → (∀ i ∈ fidx t, i < k + env.length + 1) →
      openMany k env (lowerRec k t) = openMany (k + 1) env t := by
  intro t
  induction t with
  | bvar i =>
      intro k env hk hb
      simp only [fidx, Finset.mem_singleton] at hk
      have hi : i < k + env.length + 1 := hb i (by simp [fidx])
      rcases Nat.lt_or_ge i k with hlt | hge
      · simp only [lowerRec, ite_eq_right (by omega : ¬ k < i)]
        rw [openMany_bvar_lt_base env k i hlt, openMany_bvar_lt_base env (k + 1) i (by omega)]
      · have hgt : k < i := by omega
        obtain ⟨m, rfl⟩ : ∃ m, i = k + 1 + m := ⟨i - k - 1, by omega⟩
        have hm : m < env.length := by simp at hi; omega
        obtain ⟨p, hp⟩ : ∃ p, env[m]? = some p := ⟨_, List.getElem?_eq_getElem hm⟩
        simp only [lowerRec, ite_eq_left hgt]
        rw [show k + 1 + m - 1 = k + m by omega]
        rw [openMany_bvar_lt env k m p hp, openMany_bvar_lt env (k + 1) m p hp]
  | fvar x => intro k env _ _; simp [lowerRec]
  | abs Y ih =>
      intro k env hk hb
      have hk' : k + 1 ∉ fidx Y := fun hc => hk (by simpa using mem_fidx_abs hc (by omega))
      have hb' : ∀ i ∈ fidx Y, i < (k + 1) + env.length + 1 := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · omega
        · have := hb _ (mem_fidx_abs hi (by omega))
          omega
      simp only [lowerRec, openMany_abs, ih (k + 1) env hk' hb']
  | app a b iha ihb =>
      intro k env hk hb
      simp only [fidx, Finset.mem_union, not_or] at hk
      simp only [lowerRec, openMany_app,
        iha k env hk.1 (fun i hi => hb i (by simp [fidx, hi])),
        ihb k env hk.2 (fun i hi => hb i (by simp [fidx, hi]))]

/-- Opening the outermost binder of a context is opening in the extended
context. -/
theorem openRec_openMany_cons (env : List (String × String)) (x v : String) (t : Term String) :
    openRec 0 (fvar x) (openMany 1 env t) = openMany 0 ((x, v) :: env) t := by
  rw [openRec_openMany env x 0 1 (by omega) t]
  rfl

theorem lc_of_fidx {t : Term String} {env : List (String × String)}
    (h : ∀ i ∈ fidx t, i < env.length) : LC (openMany 0 env t) :=
  lc_openMany_of_lcAt t env (lcAt_of_fidx t env.length h)

theorem namify_openMany_betaStar : ∀ (t : Term String) (env : List (String × String)),
    (∀ i ∈ fidx t, i < env.length) → openMany 0 env (namify t) ↠βᶠ openMany 0 env t := by
  intro t
  induction t with
  | bvar i => intro env _; exact Relation.ReflTransGen.refl
  | fvar x => intro env _; exact Relation.ReflTransGen.refl
  | abs M ih =>
      intro env hb
      have hbM : ∀ i ∈ fidx M, i < (("z", "x") :: env : List (String × String)).length := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simp
        · have := hb _ (mem_fidx_abs hi (by omega))
          simp only [List.length_cons]
          omega
      by_cases h0 : 0 ∈ fidx M
      · simp only [namify, ite_eq_left h0, openMany_abs]
        refine FullBeta.redex_abs_cong (∅ : Finset String) (fun x _ => ?_)
        show openRec 0 (fvar x) (openMany 1 env (namify M)) ↠βᶠ
          openRec 0 (fvar x) (openMany 1 env M)
        rw [openRec_openMany_cons env x "x", openRec_openMany_cons env x "x"]
        exact ih ((x, "x") :: env) (by simpa using hbM)
      · have hnf : 0 ∉ fidx (namify M) := by rwa [fidx_namify]
        have hbn : ∀ i ∈ fidx (namify M), i < 0 + env.length + 1 := by
          rw [fidx_namify]
          intro i hi
          have := hbM i hi
          simp only [List.length_cons] at this
          omega
        have hlow : openMany 0 env (lowerRec 0 (namify M)) = openMany 1 env (namify M) :=
          openMany_lowerRec (namify M) 0 env hnf hbn
        have hlc : LC (openMany 1 env (namify M)) := by
          rw [← hlow]
          refine lc_of_fidx (env := env) ?_
          intro i hi
          rw [fidx_lowerRec] at hi
          simp only [Finset.mem_image] at hi
          obtain ⟨j, hj, rfl⟩ := hi
          have hj0 : j ≠ 0 := fun hc => hnf (hc ▸ hj)
          have := hbn j hj
          split <;> omega
        simp only [namify, ite_eq_right h0, openMany_app, openMany_KTerm, openMany_abs, hlow]
        have hstep : FullBeta (Term.app KTerm (openMany 1 env (namify M)))
            (Term.abs (openMany 1 env (namify M))) := by
          have hb' := Xi.base (Beta.beta (M := Term.abs (Term.bvar 1))
            (N := openMany 1 env (namify M)) lc_KTerm hlc)
          simpa [openRec, KTerm] using hb'
        refine Relation.ReflTransGen.head hstep ?_
        refine FullBeta.redex_abs_cong (∅ : Finset String) (fun x _ => ?_)
        show openRec 0 (fvar x) (openMany 1 env (namify M)) ↠βᶠ
          openRec 0 (fvar x) (openMany 1 env M)
        rw [openRec_openMany_cons env x "x", openRec_openMany_cons env x "x"]
        exact ih ((x, "x") :: env) (by simpa using hbM)
  | app a b iha ihb =>
      intro env hb
      have hba : ∀ i ∈ fidx a, i < env.length := fun i hi => hb i (by simp [fidx, hi])
      have hbb : ∀ i ∈ fidx b, i < env.length := fun i hi => hb i (by simp [fidx, hi])
      have hbna : ∀ i ∈ fidx (namify a), i < env.length := by rw [fidx_namify]; exact hba
      have hbnb : ∀ i ∈ fidx (namify b), i < env.length := by rw [fidx_namify]; exact hbb
      simp only [namify, openMany_app]
      exact (FullBeta.redex_app_l_cong (iha env hba) (lc_of_fidx hbnb)).trans
        (FullBeta.redex_app_r_cong (ihb env hbb) (lc_of_fidx hba))

theorem namify_betaStar {t : Term String} (h : fidx t = ∅) : namify t ↠βᶠ t := by
  simpa using namify_openMany_betaStar t [] (by rw [h]; simp)

/-! ## The criterion -/

/-- **Main theorem.**  A closed term using at most two variables at every node is
a β-reduct of a term nameable with the two names `x`, `y`. -/
theorem betaReductOfNamable_of_closedNodeTwoVars {t : Term String}
    (h : closedNodeTwoVars t = true) : BetaReductOfNamable t := by
  simp only [closedNodeTwoVars, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨namify t, ?_, ?_⟩
  · exact namableXY_of_nameableNodes (nameableNodes_namify t h.1)
      (by rw [fidx_namify]; exact h.2)
  · exact namify_betaStar h.2

/-- The statement in terms of `isNamedOfXY`: if at most two variables are used
at every node of the closed term `t`, then `namify t` *is* nameable with the two
names `x`, `y`, and it β-reduces to `t`. -/
theorem isNamedOfXY_namify_and_betaStar {t : Term String} (h : closedNodeTwoVars t = true) :
    isNamedOfXY (namify t) = true ∧ namify t ↠βᶠ t := by
  simp only [closedNodeTwoVars, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, namify_betaStar h.2⟩
  rw [isNamedOfXY_eq_namableXY]
  exact namableXY_of_nameableNodes (nameableNodes_namify t h.1) (by rw [fidx_namify]; exact h.2)

/-- **A closed term using at most two variables at every node is not a one-point
basis.** -/
theorem closedNodeTwoVars_not_basis {t : Term String} (h : closedNodeTwoVars t = true) :
    not_basis t :=
  BetaReductOfNamable_not_basis (betaReductOfNamable_of_closedNodeTwoVars h)

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
