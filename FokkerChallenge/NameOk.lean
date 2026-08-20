import FokkerChallenge.TwoVarsAreNotEnough.TwoVarBlocks

/-!
# A locally nameless characterisation of two-name nameability

`isNamedOfXY t` (and its decision procedure `namableXY`) are phrased in terms of
de Bruijn indices and a context of binder *names*.  That formulation is awkward
to combine with the locally nameless reduction relations, which go under a
binder by *opening* it with a fresh free variable.

This file introduces `NameOk env t`, a locally nameless version of the same
property: `env` lists the free variables standing for the enclosing binders,
innermost first, together with the name (`"x"` or `"y"`) given to each of them.
A free variable is fine when it occurs in `env` and no *inner* binder of `env`
carries the same name; going under a binder is done by opening with a fresh
variable, exactly as in the reduction relations.

The main results are

* `nameOk_nil_iff_namableXY`  : `NameOk [] t ↔ namableXY t = true`,
* `isNamedOfXY_eq_namableXY`  : `isNamedOfXY t = namableXY t`,
* `nameOk_nil_iff_isNamedOfXY`: `NameOk [] t ↔ isNamedOfXY t = true`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


/-! ## Opening a whole context of binders -/

/-- `openMany k env t` opens the dangling indices `k, k+1, …` of `t` with the
variables of `env` (innermost binder first). -/
@[simp, scoped grind =]
def openMany (k : ℕ) : List (String × String) → Term String → Term String
  | [], t => t
  | e :: es, t => openMany (k + 1) es (openRec k (fvar e.1) t)

/-- Opening at two different indices with free variables commutes. -/
theorem openRec_openRec_comm {i j : ℕ} (hij : i ≠ j) (a b : String) (t : Term String) :
    openRec i (fvar a) (openRec j (fvar b) t) = openRec j (fvar b) (openRec i (fvar a) t) := by
  induction t generalizing i j with
  | bvar n =>
      by_cases h1 : n = i <;> by_cases h2 : n = j <;> simp_all [openRec]
      split <;> grind
      split <;> grind
  | fvar x => simp [openRec]
  | abs t ih => simp [openRec, ih (by omega : i + 1 ≠ j + 1)]
  | app t₁ t₂ ih₁ ih₂ => simp [openRec, ih₁ hij, ih₂ hij]

@[simp] theorem openMany_fvar (k : ℕ) (env : List (String × String)) (x : String) :
    openMany k env (fvar x) = fvar x := by
  induction env generalizing k with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

@[simp] theorem openMany_app (k : ℕ) (env : List (String × String)) (a b : Term String) :
    openMany k env (app a b) = app (openMany k env a) (openMany k env b) := by
  induction env generalizing k a b with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

@[simp] theorem openMany_abs (k : ℕ) (env : List (String × String)) (M : Term String) :
    openMany k env (abs M) = abs (openMany (k + 1) env M) := by
  induction env generalizing k M with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

/-- Opening an inner index commutes with opening the outer context. -/
theorem openRec_openMany (env : List (String × String)) (y : String) :
    ∀ (j k : ℕ), j < k → ∀ t : Term String,
      openRec j (fvar y) (openMany k env t) = openMany k env (openRec j (fvar y) t) := by
  induction env with
  | nil => intro j k _ t; rfl
  | cons e es ih =>
      intro j k hjk t
      simp only [openMany]
      rw [ih j (k + 1) (by omega), openRec_openRec_comm (by omega : j ≠ k) y e.1 t]

theorem openMany_bvar_lt : ∀ (env : List (String × String)) (k i : ℕ) (p : String × String),
    env[i]? = some p → openMany k env (bvar (k + i)) = fvar p.1 := by
  intro env
  induction env with
  | nil => intro k i p h; simp at h
  | cons e es ih =>
      intro k i p h
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp [openMany, openRec]
      | i + 1 =>
          simp only [List.getElem?_cons_succ] at h
          have hne : ¬ (k + (i + 1) = k) := by omega
          have := ih (k + 1) i p h
          simp only [openMany, openRec]
          rw [show k + (i + 1) = k + 1 + i by omega]
          grind

theorem openMany_bvar_ge : ∀ (env : List (String × String)) (k i : ℕ),
    env.length + k ≤ i → openMany k env (bvar i) = bvar i := by
  intro env
  induction env with
  | nil => intro k i _; rfl
  | cons e es ih =>
      intro k i h
      have hne : ¬ (i = k) := by simp at h; omega
      simp only [openMany, openRec]
      grind

/-! ## The locally nameless nameability predicate -/

/-- `Lookup env x v` says that the free variable `x` stands for a binder of
`env` that was named `v`, and that no binder *inside* that one carries the same
name (so the occurrence is not shadowed). -/
inductive Lookup : List (String × String) → String → String → Prop
  /-- The innermost binder. -/
  | here {env : List (String × String)} {x v : String} : Lookup ((x, v) :: env) x v
  /-- A binder further out, provided the one we skip is a different variable
  carrying a different name. -/
  | there {env : List (String × String)} {x v y w : String} (hxy : y ≠ x) (hvw : w ≠ v)
      (h : Lookup env x v) : Lookup ((y, w) :: env) x v

theorem Lookup.mem {env : List (String × String)} {x v : String} (h : Lookup env x v) :
    (x, v) ∈ env := by
  induction h with
  | here => simp
  | there _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- In a context with pairwise different variables, a variable determines its
name. -/
theorem pair_unique_of_nodup : ∀ {env : List (String × String)}, (env.map Prod.fst).Nodup →
    ∀ {x v w : String}, (x, v) ∈ env → (x, w) ∈ env → v = w := by
  intro env
  induction env with
  | nil => intro _ x v w h; simp at h
  | cons e es ih =>
      intro hnd x v w h1 h2
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      obtain ⟨hne, hnd'⟩ := hnd
      rcases List.mem_cons.1 h1 with h1' | h1' <;> rcases List.mem_cons.1 h2 with h2' | h2'
      · rw [← h1'] at h2'; simpa using h2'.symm
      · exact absurd ⟨(x, w), h2', by rw [← h1']⟩ hne
      · exact absurd ⟨(x, v), h1', by rw [← h2']⟩ hne
      · exact ih hnd' h1' h2'

theorem Lookup.unique_of_nodup {env : List (String × String)} (hnd : (env.map Prod.fst).Nodup)
    {x v w : String} (h1 : Lookup env x v) (h2 : Lookup env x w) : v = w :=
  pair_unique_of_nodup hnd h1.mem h2.mem

/-- `Lookup` is the locally nameless counterpart of `NTerm.idx`. -/
theorem exists_lookup_iff_idx : ∀ (env : List (String × String)), (env.map Prod.fst).Nodup →
    ∀ (i : ℕ) (x v : String), env[i]? = some (x, v) →
      ((∃ w, Lookup env x w) ↔ NTerm.idx v (env.map Prod.snd) = some i) := by
  intro env
  induction env with
  | nil => intro _ i x v h; simp at h
  | cons e es ih =>
      intro hnd i x v hi
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      obtain ⟨hne, hnd'⟩ := hnd
      have hnd'' : (es.map Prod.fst).Nodup := by simpa using hnd'
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          constructor
          · intro _; simp [NTerm.idx]
          · intro _; exact ⟨v, Lookup.here⟩
      | i + 1 =>
          simp only [List.getElem?_cons_succ] at hi
          have hmem : (x, v) ∈ es := List.mem_of_getElem? hi
          have hex : e.1 ≠ x := by
            intro hc; exact hne ⟨(x, v), hmem, hc.symm⟩
          have hIH := ih hnd'' i x v hi
          constructor
          · rintro ⟨w, hw⟩
            cases hw with
            | here => exact absurd rfl hex
            | there hxy hvw h' =>
                have hwv : w = v := pair_unique_of_nodup hnd'' h'.mem hmem
                subst hwv
                have := hIH.1 ⟨w, h'⟩
                simp only [List.map_cons, NTerm.idx]
                rw [ite_eq_right (by simpa using hvw), this]
                simp
          · intro hidx
            simp only [List.map_cons, NTerm.idx] at hidx
            by_cases hev : e.2 = v
            · rw [ite_eq_left hev] at hidx; simp at hidx
            · rw [ite_eq_right hev] at hidx
              simp only [Option.map_eq_some_iff] at hidx
              obtain ⟨j, hj, hji⟩ := hidx
              have hji' : j = i := by omega
              subst hji'
              obtain ⟨w, hw⟩ := hIH.2 hj
              have hwv : w = v := pair_unique_of_nodup hnd'' hw.mem hmem
              subst hwv
              refine ⟨w, ?_⟩
              have : e = (e.1, e.2) := rfl
              rw [this]
              exact Lookup.there hex hev hw

/-- `NameOk env t` says that the term `t`, whose free variables are listed
(innermost binder first) in `env` together with the name each binder was given,
can be written as a named term using only the names `"x"` and `"y"`. -/
inductive NameOk : List (String × String) → Term String → Prop
  /-- A free variable is fine when it is bound by `env`, unshadowed. -/
  | fvar {env : List (String × String)} {x v : String} (h : Lookup env x v) :
      NameOk env (fvar x)
  /-- Applications are checked componentwise. -/
  | app {env : List (String × String)} {a b : Term String} :
      NameOk env a → NameOk env b → NameOk env (app a b)
  /-- An abstraction is fine if for some choice of name `v ∈ {"x","y"}` its body,
  opened with a fresh variable standing for the new binder, is fine. -/
  | abs {env : List (String × String)} {M : Term String} (v : String)
      (hv : v = "x" ∨ v = "y") (xs : Finset String)
      (h : ∀ y ∉ xs, NameOk ((y, v) :: env) (M ^ fvar y)) :
      NameOk env (abs M)

/-! ## The bridge to the de Bruijn formulation -/

/-- The locally nameless predicate agrees with the named-term description. -/
theorem nameOk_openMany_iff : ∀ (t : Term String) (env : List (String × String)),
    (env.map Prod.fst).Nodup → (∀ p ∈ env, p.2 = "x" ∨ p.2 = "y") → (∀ p ∈ env, p.1 ∉ fv t) →
      (NameOk env (openMany 0 env t) ↔
        ∃ u : NTerm, NTerm.WN (env.map Prod.snd) u ∧ NTerm.toLN (env.map Prod.snd) u = t) := by
  intro t
  induction t with
  | bvar i =>
      intro env hnd _ _
      by_cases hlt : i < env.length
      · obtain ⟨p, hp⟩ : ∃ p, env[i]? = some p := ⟨_, List.getElem?_eq_getElem hlt⟩
        have hsnd : (env.map Prod.snd)[i]? = some p.2 := by
          simp [List.getElem?_map, hp]
        rw [show openMany 0 env (bvar i) = fvar p.1 by simpa using openMany_bvar_lt env 0 i p hp]
        have hiff := exists_lookup_iff_idx env hnd i p.1 p.2 (by simpa using hp)
        constructor
        · intro h
          cases h with
          | fvar hl =>
              have hidx := hiff.1 ⟨_, hl⟩
              exact ⟨.var p.2, List.mem_of_getElem? hsnd, by simp [NTerm.toLN, hidx]⟩
        · rintro ⟨u, hwn, heq⟩
          match u with
          | .var w =>
              simp only [NTerm.toLN] at heq
              have hidx : NTerm.idx w (env.map Prod.snd) = some i := by
                cases hw : NTerm.idx w (env.map Prod.snd) with
                | none => rw [hw] at heq; simp at heq
                | some j => rw [hw] at heq; simp at heq; rw [heq]
              have hwp : w = p.2 := by
                have := (idx_eq_some_get hidx).1
                rw [hsnd] at this; simpa using this.symm
              subst hwp
              obtain ⟨w', hw'⟩ := hiff.2 hidx
              exact NameOk.fvar hw'
          | .abs v b => simp [NTerm.toLN] at heq
          | .app u1 u2 => simp [NTerm.toLN] at heq
      · rw [openMany_bvar_ge env 0 i (by omega)]
        constructor
        · intro h; cases h
        · rintro ⟨u, hwn, heq⟩
          match u with
          | .var w =>
              simp only [NTerm.toLN] at heq
              cases hw : NTerm.idx w (env.map Prod.snd) with
              | none => rw [hw] at heq; simp at heq
              | some j =>
                  rw [hw] at heq
                  simp only [Term.bvar.injEq] at heq
                  have := idx_lt_length hw
                  simp only [List.length_map] at this
                  omega
          | .abs v b => simp [NTerm.toLN] at heq
          | .app u1 u2 => simp [NTerm.toLN] at heq
  | fvar x =>
      intro env _ _ hdisj
      rw [openMany_fvar]
      constructor
      · intro h
        cases h with
        | fvar hl =>
            exact absurd (by simp [fv] : x ∈ fv (fvar x : Term String))
              (hdisj (x, _) hl.mem)
      · rintro ⟨u, hwn, heq⟩
        match u with
        | .var w =>
            simp only [NTerm.toLN] at heq
            cases hw : NTerm.idx w (env.map Prod.snd) with
            | none =>
                have : (NTerm.idx w (env.map Prod.snd)).isSome := idx_isSome_of_mem hwn
                rw [hw] at this; simp at this
            | some j => rw [hw] at heq; simp at heq
        | .abs v b => simp [NTerm.toLN] at heq
        | .app u1 u2 => simp [NTerm.toLN] at heq
  | app a b iha ihb =>
      intro env hnd hxy hdisj
      have hda : ∀ p ∈ env, p.1 ∉ fv a := by
        intro p hp hc; exact hdisj p hp (by simp [fv, hc])
      have hdb : ∀ p ∈ env, p.1 ∉ fv b := by
        intro p hp hc; exact hdisj p hp (by simp [fv, hc])
      rw [openMany_app]
      constructor
      · intro h
        cases h with
        | app ha hb =>
            obtain ⟨u1, hw1, he1⟩ := (iha env hnd hxy hda).1 ha
            obtain ⟨u2, hw2, he2⟩ := (ihb env hnd hxy hdb).1 hb
            exact ⟨.app u1 u2, ⟨hw1, hw2⟩, by simp [NTerm.toLN, he1, he2]⟩
      · rintro ⟨u, hwn, heq⟩
        match u with
        | .var w =>
            simp only [NTerm.toLN] at heq
            cases hw : NTerm.idx w (env.map Prod.snd) with
            | none => rw [hw] at heq; simp at heq
            | some j => rw [hw] at heq; simp at heq
        | .abs v c => simp [NTerm.toLN] at heq
        | .app u1 u2 =>
            simp only [NTerm.toLN, Term.app.injEq] at heq
            obtain ⟨hw1, hw2⟩ := hwn
            exact NameOk.app ((iha env hnd hxy hda).2 ⟨u1, hw1, heq.1⟩)
              ((ihb env hnd hxy hdb).2 ⟨u2, hw2, heq.2⟩)
  | abs M ih =>
      intro env hnd hxy hdisj
      have hdM : ∀ p ∈ env, p.1 ∉ fv M := by
        intro p hp; simpa [fv] using hdisj p hp
      have hkey : ∀ (y v : String), (openMany 1 env M) ^ fvar y = openMany 0 ((y, v) :: env) M := by
        intro y v
        simp only [openMany]
        exact openRec_openMany env y 0 1 (by omega) M
      rw [openMany_abs]
      constructor
      · intro h
        cases h with
        | abs v hv xs hbody =>
            obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
              (xs ∪ (env.map Prod.fst).toFinset ∪ fv M)
            simp only [Finset.mem_union, not_or] at hy
            obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
            have hb := hbody y hy1
            rw [hkey y v] at hb
            have hnd' : (((y, v) :: env).map Prod.fst).Nodup := by
              simp only [List.map_cons, List.nodup_cons]
              exact ⟨by simpa using hy2, hnd⟩
            have hxy' : ∀ p ∈ (y, v) :: env, p.2 = "x" ∨ p.2 = "y" := by
              intro p hp
              rcases List.mem_cons.1 hp with rfl | hp
              · exact hv
              · exact hxy p hp
            have hdisj' : ∀ p ∈ (y, v) :: env, p.1 ∉ fv M := by
              intro p hp
              rcases List.mem_cons.1 hp with rfl | hp
              · exact hy3
              · exact hdM p hp
            obtain ⟨u, hwn, heq⟩ := (ih ((y, v) :: env) hnd' hxy' hdisj').1 hb
            exact ⟨.abs v u, ⟨hv, hwn⟩, by simpa [NTerm.toLN] using heq⟩
      · rintro ⟨u, hwn, heq⟩
        match u with
        | .var w =>
            simp only [NTerm.toLN] at heq
            cases hw : NTerm.idx w (env.map Prod.snd) with
            | none => rw [hw] at heq; simp at heq
            | some j => rw [hw] at heq; simp at heq
        | .app u1 u2 => simp [NTerm.toLN] at heq
        | .abs v u' =>
            simp only [NTerm.toLN, Term.abs.injEq] at heq
            obtain ⟨hv, hwn'⟩ := hwn
            refine NameOk.abs v hv ((env.map Prod.fst).toFinset ∪ fv M) (fun y hy => ?_)
            simp only [Finset.mem_union, not_or] at hy
            obtain ⟨hy1, hy2⟩ := hy
            rw [hkey y v]
            have hnd' : (((y, v) :: env).map Prod.fst).Nodup := by
              simp only [List.map_cons, List.nodup_cons]
              exact ⟨by simpa using hy1, hnd⟩
            have hxy' : ∀ p ∈ (y, v) :: env, p.2 = "x" ∨ p.2 = "y" := by
              intro p hp
              rcases List.mem_cons.1 hp with rfl | hp
              · exact hv
              · exact hxy p hp
            have hdisj' : ∀ p ∈ (y, v) :: env, p.1 ∉ fv M := by
              intro p hp
              rcases List.mem_cons.1 hp with rfl | hp
              · exact hy2
              · exact hdM p hp
            exact (ih ((y, v) :: env) hnd' hxy' hdisj').2 ⟨u', hwn', heq⟩

/-- `NameOk [] t` is exactly `namableXY t`. -/
theorem nameOk_nil_iff_namableXY (t : Term String) : NameOk [] t ↔ namableXY t = true := by
  rw [namableXY_iff]
  have h := nameOk_openMany_iff t [] (by simp) (by simp) (by simp)
  simp at h
  grind

/-! ## Completeness of `namedOf` -/

/-- `NameOk [] t` is exactly `isNamedOfXY t`. -/
theorem nameOk_nil_iff_isNamedOfXY (t : Term String) : NameOk [] t ↔ isNamedOfXY t = true := by
  rw [isNamedOfXY_eq_namableXY, nameOk_nil_iff_namableXY]
