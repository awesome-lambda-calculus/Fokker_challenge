import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.EtaToSpine
import FokkerChallenge.EnhancedCslib.AbsN

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# The precise shape of a β-normal form η-reducing to a spine

`betaNF_etaStar_absN_spine` says that a β-normal `M` with `M ↠ηᶠ x N₁ … Nₖ` has
the form `M = absN n (spine x l')` with `l'.length = k + n`, and
`betaNF_etaStar_absN_spine_len_one` specialises this to `k = 1`.

This file proves the *more accurate shape*: the argument list of `M` splits as
`l' = l₀ ++ E` where

* `l₀` has the same length as the target list `l`, its entries are locally
  closed and η-reduce to the corresponding entries of `l`;
* `E` consists of exactly `n` **η-expansions of the enclosing bound variables**
  (`EtaExpArgs`): the entry of `E` belonging to the `i`-th enclosing abstraction,
  opened at the corresponding index with a fresh variable `y`, η-reduces to `y`.

In particular every entry of the appended list `E` *contains a dangling
(unbound) bound variable* — it is not locally closed
(`EtaExpArgs.exists_hasBvar`, `EtaExpArgs.not_lc`).
-/


universe u

open Term

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

/-! ## Free variables are invariant under η-reduction -/

/-- If the bodies of two abstractions have related free variables after opening
with all sufficiently fresh variables, the bodies themselves do. -/
theorem fv_abs_body_subset {M N : Term Var} {xs : Finset Var}
    (h : ∀ z ∉ xs, fv (M ^ Term.fvar z) ⊆ fv (N ^ Term.fvar z)) : fv M ⊆ fv N := by
  intro y hy
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (xs ∪ fv M ∪ fv N ∪ {y})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
  obtain ⟨⟨⟨hzxs, _⟩, _⟩, hzy⟩ := hz
  have h1 : y ∈ fv (M ^ Term.fvar z) := by grind [open_preserve_not_fvar]
  have h2 : y ∈ fv (N ^ Term.fvar z) := h z hzxs h1
  grind [open_preserve_not_fvar]

/-- η-reduction neither creates nor destroys free variables. -/
theorem fullEta_fv_eq {a b : Term Var} (h : FullEta a b) : fv a = fv b := by
  induction h with
  | base hb => cases hb with
    | eta _ => simp [fv]
  | appL _ _ ih => simp [fv, ih]
  | appR _ _ ih => simp [fv, ih]
  | abs xs _ ih =>
      simp only [fv]
      exact Finset.Subset.antisymm
        (fv_abs_body_subset (xs := xs) (fun z hz => (ih z hz).subset))
        (fv_abs_body_subset (xs := xs) (fun z hz => (ih z hz).symm.subset))

theorem fullEtaStar_fv_eq {a b : Term Var} (h : a ↠ηᶠ b) : fv a = fv b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (fullEta_fv_eq hstep)

/-! ## Dangling bound variables -/

/-- `HasBvar k t` : the bound variable with de Bruijn index `k` occurs (unbound)
in `t`, counting from the top of `t`. -/
@[simp, scoped grind =]
def HasBvar (k : ℕ) : Term Var → Prop
  | Term.bvar i => i = k
  | Term.fvar _ => False
  | Term.abs t => HasBvar (k + 1) t
  | Term.app a b => HasBvar k a ∨ HasBvar k b

@[simp] theorem hasBvar_bvar {k i : ℕ} : HasBvar k (bvar i : Term Var) ↔ i = k := by
  simp [HasBvar]

@[simp] theorem hasBvar_fvar {k : ℕ} {x : Var} : ¬ HasBvar k (fvar x) := by
  simp [HasBvar]

@[simp] theorem hasBvar_abs {k : ℕ} {t : Term Var} : HasBvar k (abs t) ↔ HasBvar (k + 1) t := by
  simp [HasBvar]

@[simp] theorem hasBvar_app {k : ℕ} {a b : Term Var} :
    HasBvar k (app a b) ↔ HasBvar k a ∨ HasBvar k b := by
  simp [HasBvar]

/-- Opening a term at an index it does not use is the identity. -/
theorem openRec_eq_self_of_not_hasBvar {k : ℕ} {t u : Term Var} (h : ¬ HasBvar k t) :
    openRec k u t = t := by
  induction t generalizing k with
  | bvar i => rw [openRec_bvar]
              split <;>  grind
  | fvar y => rfl
  | abs t ih => simp only [HasBvar] at h; simp [openRec, ih h]
  | app a b iha ihb =>
      simp only [HasBvar, not_or] at h
      simp [openRec, iha h.1, ihb h.2]

/-- Opening at a *different* index preserves a dangling occurrence. -/
theorem hasBvar_openRec_of_ne {k j : ℕ} (hne : j ≠ k) {u t : Term Var} (h : HasBvar k t) :
    HasBvar k (openRec j u t) := by
  induction t generalizing k j with
  | bvar i => grind
  | fvar y => exact h.elim
  | abs t ih => exact ih (by omega) h
  | app a b iha ihb =>
      simp only [HasBvar] at h ⊢
      exact h.imp (iha hne) (ihb hne)

/-- A locally closed term has no dangling bound variables. -/
theorem Term.LC.not_hasBvar {t : Term Var} (h : LC t) (k : ℕ) : ¬ HasBvar k t := by
  induction h generalizing k with
  | fvar x => simp [HasBvar]
  | abs xs t hbody ih =>
      intro hb
      simp only [HasBvar] at hb
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset xs
      exact ih y hy (k + 1) (by
        have := hasBvar_openRec_of_ne (k := k + 1) (j := 0) (by omega) (u := Term.fvar y) hb
        grind)
  | app h1 h2 ih1 ih2 => simp only [HasBvar]; exact not_or.2 ⟨ih1 k, ih2 k⟩

/-- Opening at the index of a dangling bound variable introduces the opening
term's free variables: if `HasBvar k t` then `y` is free in `openRec k (fvar y) t`. -/
theorem mem_fv_openRec_of_hasBvar {k : ℕ} {t : Term Var} (y : Var)
    (h : HasBvar k t) : y ∈ fv (openRec k (fvar y) t) := by
  induction t generalizing k with
  | bvar i =>
      simp only [HasBvar] at h
      subst h
      simp [openRec, fv]
  | fvar z => simp [HasBvar] at h
  | abs t ih =>
      simp only [HasBvar] at h
      simpa [openRec, fv] using ih (k := k + 1) h
  | app a b iha ihb =>
      simp only [HasBvar] at h
      rcases h with h | h
      · simp only [openRec, fv, Finset.mem_union]
        exact Or.inl (iha h)
      · simp only [openRec, fv, Finset.mem_union]
        exact Or.inr (ihb h)

/-! ## η-expansions of a bound variable -/

/-- `EtaExpBvar k E` : opening `E` at index `k` with a fresh variable `y` yields
a term that η-reduces to `y`; i.e. `E` is an η-expansion of the bound variable
with index `k`. -/
def EtaExpBvar (k : ℕ) (E : Term Var) : Prop :=
  ∀ y : Var, y ∉ fv E → (openRec k (fvar y) E) ↠ηᶠ (fvar y)

/-- `EtaExpArgs n E` : `E = [E₀, …, E_{n-1}]` where `Eᵢ` is an η-expansion of the
bound variable of index `n - 1 - i`; these are the trailing arguments produced by
`n` nested η-expansions. -/
def EtaExpArgs : ℕ → List (Term Var) → Prop
  | 0, [] => True
  | (n + 1), (E :: l) => EtaExpBvar n E ∧ EtaExpArgs n l
  | _, _ => False

@[simp] theorem etaExpArgs_zero {E : List (Term Var)} : EtaExpArgs 0 E ↔ E = [] := by
  cases E <;> simp [EtaExpArgs]

@[simp] theorem etaExpArgs_succ {n : ℕ} {E : Term Var} {l : List (Term Var)} :
    EtaExpArgs (n + 1) (E :: l) ↔ EtaExpBvar n E ∧ EtaExpArgs n l := Iff.rfl

theorem EtaExpArgs.length {n : ℕ} {l : List (Term Var)} (h : EtaExpArgs n l) :
    l.length = n := by
  induction n generalizing l with
  | zero => simp only [etaExpArgs_zero] at h; simp [h]
  | succ m ih =>
      cases l with
      | nil => exact absurd h (by simp [EtaExpArgs])
      | cons E l => simpa using ih h.2

/-- An η-expansion of the bound variable `k` really does contain the dangling
bound variable `k`. -/
theorem EtaExpBvar.hasBvar {k : ℕ} {E : Term Var} (h : EtaExpBvar k E) : HasBvar k E := by
  by_contra hb
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (fv E)
  have hred := h y hy
  rw [openRec_eq_self_of_not_hasBvar hb] at hred
  have : fv E = ({y} : Finset Var) := by simpa [fv] using fullEtaStar_fv_eq hred
  exact hy (by simp [this])

/-- **Every entry of the appended argument list contains an unbound bound
variable.** -/
theorem EtaExpArgs.exists_hasBvar {n : ℕ} {l : List (Term Var)} (h : EtaExpArgs n l) :
    ∀ B ∈ l, ∃ k < n, HasBvar k B := by
  induction n generalizing l with
  | zero => simp only [etaExpArgs_zero] at h; simp [h]
  | succ m ih =>
      cases l with
      | nil => simp
      | cons E l =>
          intro B hB
          rcases List.mem_cons.1 hB with rfl | hB'
          · exact ⟨m, by omega, h.1.hasBvar⟩
          · obtain ⟨k, hk, hkB⟩ := ih h.2 B hB'
            exact ⟨k, by omega, hkB⟩

/-- Consequently no entry of the appended argument list is locally closed. -/
theorem EtaExpArgs.not_lc {n : ℕ} {l : List (Term Var)} (h : EtaExpArgs n l) :
    ∀ B ∈ l, ¬ LC B := by
  intro B hB hlc
  obtain ⟨k, _, hk⟩ := h.exists_hasBvar B hB
  exact Term.LC.not_hasBvar hlc k hk

/-! ## Auxiliary lemmas about opening, `absN` and spines -/

theorem fv_head_subset_foldl : ∀ (l : List (Term Var)) (h : Term Var),
    fv h ⊆ fv (l.foldl app h) := by
  intro l
  induction l with
  | nil => intro h; simp
  | cons c l ih =>
      intro h
      refine subset_trans ?_ (ih (app h c))
      intro y hy; simp only [fv, Finset.mem_union]; exact Or.inl hy

theorem fv_subset_foldl_app {A : Term Var} : ∀ (l : List (Term Var)) (h : Term Var),
    A ∈ l → fv A ⊆ fv (l.foldl app h) := by
  intro l
  induction l with
  | nil => intro h hA; cases hA
  | cons c l ih =>
      intro h hA
      rcases List.mem_cons.1 hA with rfl | hA'
      · refine subset_trans ?_ (fv_head_subset_foldl l (app h A))
        intro y hy; simp only [fv, Finset.mem_union]; exact Or.inr hy
      · exact ih _ hA'

theorem fv_subset_spine_arg {x : Var} {l : List (Term Var)} {A : Term Var} (hA : A ∈ l) :
    fv A ⊆ fv (spine x l) := fv_subset_foldl_app l (fvar x) hA

/-- The union of the free variables of a list of terms. -/
noncomputable def fvList (l : List (Term Var)) : Finset Var := l.foldr (fun t s => fv t ∪ s) ∅

theorem fv_subset_fvList {l : List (Term Var)} {A : Term Var} (hA : A ∈ l) :
    fv A ⊆ fvList l := by
  induction l with
  | nil => cases hA
  | cons c l ih =>
      rcases List.mem_cons.1 hA with rfl | hA'
      · intro y hy; simp only [fvList, List.foldr_cons, Finset.mem_union]; exact Or.inl hy
      · intro y hy
        simp only [fvList, List.foldr_cons, Finset.mem_union]
        exact Or.inr (ih hA' hy)

/-- If opening at `k` with `y` produces a term without `y` free, it was the
identity. -/
theorem openRec_fvar_eq_self_of_notMem {P : Term Var} {k : ℕ} {y : Var}
    (h : y ∉ fv (openRec k (fvar y) P)) : openRec k (fvar y) P = P := by
  induction P generalizing k with
  | bvar i =>
      by_cases hik : i = k
      · subst hik; simp [openRec, fv] at h
      · grind
  | fvar z => rfl
  | abs t ih => simp only [openRec, fv] at h ⊢; rw [ih h]
  | app a b iha ihb =>
      simp only [openRec, fv, Finset.mem_union, not_or] at h ⊢
      rw [iha h.1, ihb h.2]

theorem forall₂_snoc_right {α β : Type _} (R : α → β → Prop) (l₀ : List α) (l : List β) (b : β)
    (h : List.Forall₂ R l₀ (l ++ [b])) :
    ∃ l₀' a, l₀ = l₀' ++ [a] ∧ List.Forall₂ R l₀' l ∧ R a b := by
  induction l generalizing l₀ with
  | nil =>
      cases h with
      | cons hab hrest => cases hrest; exact ⟨[], _, rfl, List.Forall₂.nil, hab⟩
  | cons c l ih =>
      cases h with
      | cons hab hrest =>
          obtain ⟨l₀', a, rfl, h1, h2⟩ := ih _ hrest
          exact ⟨_ :: l₀', a, rfl, List.Forall₂.cons hab h1, h2⟩

/-- An η-expansion of a bound variable is unaffected by opening at any index:
apart from the index it expands, it has no dangling bound variables and no free
variables at all. -/
theorem EtaExpBvar.openRec_eq_self {j m : ℕ} {y : Var} {E : Term Var}
    (h : EtaExpBvar j (openRec m (fvar y) E)) : openRec m (fvar y) E = E := by
  set Q := openRec m (fvar y) E with hQ
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (fv Q)
  have hred := h z hz
  have hfv : fv (openRec j (fvar z) Q) = {z} := by simpa [fv] using fullEtaStar_fv_eq hred
  have hsub : fv Q ⊆ ({z} : Finset Var) := by grind [open_preserve_not_fvar]
  have hempty : y ∉ fv Q := by
    intro hy
    have : y = z := by simpa using hsub hy
    exact hz (this ▸ hy)
  exact openRec_fvar_eq_self_of_notMem hempty


theorem fullEtaStar_subst {M N : Term Var} (h : M ↠ηᶠ N) (x : Var) {u : Term Var}
    (hu : LC u) : (M[x:=u]) ↠ηᶠ (N[x:=u]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (FullEta.step_subst_cong_l _ _ _ hstep hu)

theorem forall₂_refl {α : Type _} {R : α → α → Prop} (l : List α) :
    List.Forall₂ (Relation.ReflTransGen R) l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons Relation.ReflTransGen.refl ih

theorem forall₂_trans {α : Type _} {R : α → α → Prop} {l₁ l₂ l₃ : List α}
    (h₁ : List.Forall₂ (Relation.ReflTransGen R) l₁ l₂)
    (h₂ : List.Forall₂ (Relation.ReflTransGen R) l₂ l₃) :
          List.Forall₂ (Relation.ReflTransGen R) l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
      cases h₂ with
      | cons hbc hrest => exact List.Forall₂.cons (hab.trans hbc) (ih hrest)

theorem forall₂_sub {α : Type _} {R1 R2 : α → α → Prop} {l₁ l₂ : List α}
    (h : R1  ≤  R2)
    (h₁ : List.Forall₂ R1 l₁ l₂) :
          List.Forall₂ R2 l₁ l₂  := by
  induction h₁ with
  | nil => exact List.Forall₂.nil
  | cons g _ ih => exact List.Forall₂.cons (h _ _ g) ih


theorem forall₂_concat {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β} {a : α}
    {b : β} (h : List.Forall₂ R as bs) (hab : R a b) :
    List.Forall₂ R (as ++ [a]) (bs ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hh _ ih => exact List.Forall₂.cons hh ih

theorem forall₂_exists_right {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : ∀ a ∈ as, ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp
  | @cons a b as bs hab _ ih =>
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨d, hd, hcd⟩ := ih c hc'
        exact ⟨d, by simp [hd], hcd⟩

/-- Opening a list of terms at an index none of them uses is the identity. -/
theorem map_openRec_eq_of_fresh {y : Var} {k : ℕ} : ∀ (as bs : List (Term Var)),
    as.map (openRec k (fvar y)) = bs → (∀ b ∈ bs, y ∉ fv b) → as = bs := by
  intro as
  induction as with
  | nil => intro bs h _; simpa using h.symm
  | cons a as ih =>
      intro bs h hfresh
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨h1, h2⟩ := h
          have ha : a = b := by
            rw [← h1]
            exact (openRec_fvar_eq_self_of_notMem (by rw [h1]; exact hfresh b (by simp))).symm
          rw [ha, ih bs h2 (fun c hc => hfresh c (by simp [hc]))]

/-- The trailing η-expansion arguments are unaffected by opening. -/
theorem etaExpArgs_of_map_openRec {n k : ℕ} {y : Var} : ∀ (E' : List (Term Var)),
    EtaExpArgs n (E'.map (openRec k (fvar y))) → EtaExpArgs n E' := by
  intro E'
  induction n generalizing E' with
  | zero => intro h; simp only [etaExpArgs_zero] at h ⊢; simpa using h
  | succ m ih =>
      intro h
      cases E' with
      | nil => exact absurd h (by simp [EtaExpArgs])
      | cons G E' =>
          simp only [List.map_cons, etaExpArgs_succ] at h
          have hG : openRec k (fvar y) G = G := h.1.openRec_eq_self
          exact ⟨by rw [← hG]; exact h.1, ih E' h.2⟩

/-! ## The main theorem -/

/-- **The precise shape of a normal form η-reducing to a spine.**  If `M` is
normal and `M ↠ηᶠ x N₁ … Nₖ`, then `M = λ…λ. x A₁ … A_k E₁ … E_n`, where the `Aᵢ`
are locally closed and η-reduce to the `Nᵢ`, and the appended arguments
`E₁ … E_n` are η-expansions of the `n` enclosing bound variables (so each of
them contains a dangling bound variable). -/
theorem Normal_etaStar_spine_shape {M : Term Var} (h : Normal M) :
    ∀ (x : Var) (l : List (Term Var)), M ↠ηᶠ (spine x l) →
      ∃ (n : ℕ) (l₀ E : List (Term Var)),
        M = Term.abs^[n] (spine x (l₀ ++ E)) ∧ List.Forall₂ (Relation.ReflTransGen FullEta) l₀ l ∧
          (∀ A ∈ l₀, LC A) ∧ EtaExpArgs n E := by
  induction h with
  | fvar z =>
      intro x l hred
      obtain ⟨hx, hl⟩ := spine_eq_fvar (fullEtaStar_fvar_inv hred)
      subst hl
      exact ⟨0, [], [], by simp [spine, hx], List.Forall₂.nil, by simp, by simp⟩
  | @app A B hA hAnotabs hB ihA _ =>
      intro x l hred
      obtain ⟨A', B', hEq, hAred, hBred⟩ := fullEtaStar_app_inv hred
      obtain ⟨l₁, hl, hA'⟩ := spine_eq_app hEq
      subst hA'
      obtain ⟨n, la, E, hAeq, hF, hLC, hE⟩ := ihA x l₁ hAred
      cases n with
      | succ m =>
      exfalso
      apply hAnotabs
      rw [add_comm, Function.iterate_add] at hAeq
      simp at hAeq
      grind
      | zero =>
          have hE' : E = [] := by simpa using hE
          subst hE'
          simp at hAeq
          refine ⟨0, la ++ [B], [], ?_, ?_, ?_, by simp⟩
          · simp
            grind
          · rw [hl]; exact forall₂_concat hF hBred
          · intro C hC
            rcases List.mem_append.1 hC with hC' | hC'
            · exact hLC C hC'
            · rw [List.mem_singleton.1 hC']; exact hB.lc
  | @abs xs T _ ih =>
      intro x l hred
      obtain ⟨W, ys, _, hWred, hopen⟩ := abs_escape hred (fun _ => spine_ne_abs)
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (xs ∪ ys ∪ {x} ∪ fv T ∪ fvList l)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      obtain ⟨⟨⟨⟨hyxs, hyys⟩, hyx⟩, hyT⟩, hyl⟩ := hy
      have h1 : (T ^ Term.fvar y) ↠ηᶠ (Term.app W (Term.fvar y)) := hopen y hyys
      have h2 : (Term.app W (Term.fvar y)) ↠ηᶠ (spine x (l ++ [Term.fvar y])) := by
        rw [spine_concat]
        exact FullEta.redex_app_l_cong hWred (LC.fvar y)
      obtain ⟨m, l₀, E, hEq, hF, hLC, hE⟩ := ih y hyxs x (l ++ [Term.fvar y]) (h1.trans h2)
      obtain ⟨args, hT, hmap⟩ := openRec_absN_spine_args (Ne.symm hyx) hEq
      obtain ⟨l₀', G, rfl, hFl, hGred⟩ := forall₂_snoc_right _ _ _ _ hF
      rw [List.append_assoc] at hmap
      obtain ⟨argsA, argsR, rfl, hmapA, hmapR⟩ := List.map_eq_append_iff.1 hmap
      obtain ⟨argsG, argsE, rfl, hmapG, hmapE⟩ := List.map_eq_append_iff.1 hmapR
      -- `argsG` is a single term `G'`
      obtain ⟨G', rfl⟩ : ∃ G', argsG = [G'] := by
        cases argsG with
        | nil => simp at hmapG
        | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t => simp at hmapG
      have hG : openRec (0 + m) (Term.fvar y) G' = G := by
        simpa using hmapG
      -- the head arguments are untouched by the opening
      have hfreshA : ∀ b ∈ l₀', y ∉ fv b := by
        intro b hb
        obtain ⟨c, hc, hbc⟩ := forall₂_exists_right hFl b hb
        rw [fullEtaStar_fv_eq hbc]
        exact fun hmem => hyl (fv_subset_fvList hc hmem)
      have hA : argsA = l₀' := map_openRec_eq_of_fresh argsA l₀' hmapA hfreshA
      subst hA
      -- `G'` does not contain `y`
      have hfvG : y ∉ fv G' := by
        intro hmem
        refine hyT ?_
        have hsub : fv G' ⊆ fv (spine x (argsA ++ ([G'] ++ argsE))) :=
          fv_subset_spine_arg (by simp)
        rw [hT, fv_absN]
        exact hsub hmem
      -- `G'` is an η-expansion of the bound variable of index `m`
      have hGexp : EtaExpBvar m G' := by
        intro z hz
        by_cases hzy : z = y
        · subst hzy
          rw [show openRec m (Term.fvar z) G' = G by simpa using hG]
          exact hGred
        · have hsub := fullEtaStar_subst hGred y (u := Term.fvar z) (LC.fvar z)
          rw [subst_fvar] at hsub
          rw [← show openRec (0 + m) (Term.fvar y) G' = G from hG] at hsub
          split at hsub <;> try grind
          rw [subst_openRec] at hsub
          . rw [subst_fvar] at hsub
            split at hsub <;> try grind
            rw [subst_fresh] at hsub <;> grind
          . grind
      have hEexp : EtaExpArgs m argsE :=
        etaExpArgs_of_map_openRec argsE (by rw [hmapE]; exact hE)
      refine ⟨m + 1, argsA, G' :: argsE, ?_, hFl, ?_, ⟨hGexp, hEexp⟩⟩
      · rw [add_comm, Function.iterate_add]
        rw [hT]
        rfl
      · intro C hC
        exact hLC C (by simp [hC])

/-- The same statement for a β-normal form. -/
theorem betaNF_etaStar_spine_shape {M : Term Var} {x : Var} {l : List (Term Var)}
    (hlc : LC M) (hM : Relation.Normal FullBeta M) (steps : M ↠ηᶠ (l.foldl app (fvar x))) :
    ∃ (n : ℕ) (l₀ E : List (Term Var)),
      M = abs^[n] ((l₀ ++ E).foldl app (fvar x)) ∧ List.Forall₂ (Relation.ReflTransGen FullEta) l₀ l ∧
        (∀ A ∈ l₀, LC A) ∧ EtaExpArgs n E :=
  Normal_etaStar_spine_shape (betaNF_normal hlc hM) x l steps

/-- **The accurate shape in the case `l.length = 1`.**  A β-normal `M` with
`M ↠ηᶠ x N` is `λ…λ. x A E₁ … E_n` where `A` is locally closed with `A ↠ηᶠ N`
and each `Eᵢ` is an η-expansion of the `i`-th enclosing bound variable; in
particular each `Eᵢ` contains a dangling bound variable. -/
theorem betaNF_etaStar_shape_len_one {M N : Term Var} {x : Var}
    (hlc : LC M) (hM : Relation.Normal FullBeta M) (steps : M ↠ηᶠ (app (fvar x) N)) :
    ∃ (n : ℕ) (A : Term Var) (E : List (Term Var)),
      M = abs^[n] ((A :: E).foldl app (fvar x)) ∧ LC A ∧ A ↠ηᶠ N ∧
        E.length = n ∧ EtaExpArgs n E ∧ (∀ B ∈ E, ∃ k < n, HasBvar k B ∧ ¬ LC B) := by
  have steps' : M ↠ηᶠ (([N] : List (Term Var)).foldl app (fvar x)) := steps
  obtain ⟨n, l₀, E, hEq, hF, hLC, hE⟩ := betaNF_etaStar_spine_shape hlc hM steps'
  obtain ⟨A, hAN, hnil⟩ : ∃ A, A ↠ηᶠ N ∧ l₀ = [A] := by
    cases hF with
    | cons hAN hrest =>
        cases hrest
        exact ⟨_, hAN, rfl⟩
  subst hnil
  refine ⟨n, A, E, by simpa using hEq, hLC A (by simp), hAN, hE.length, hE, ?_⟩
  intro B hB
  obtain ⟨k, hk, hkB⟩ := hE.exists_hasBvar B hB
  exact ⟨k, hk, hkB, fun hlcB =>  Term.LC.not_hasBvar hlcB k hkB⟩

/-- The same statement, phrased for a target list `l` of length `1`, matching
`betaNF_etaStar_absN_spine_len_one`.  Besides the length information
`l'.length = 1 + n` proved there, this pins down the *shape* of the argument
list: it is `A :: E` with `A` locally closed and η-reducing to the single target
argument, and `E` a list of `n` η-expansions of the `n` enclosing bound
variables, each of which therefore contains a dangling bound variable. -/
theorem betaNF_etaStar_shape_of_length_one {M : Term Var} {x : Var} {l : List (Term Var)}
    (hlc : LC M) (hM : Relation.Normal FullBeta M) (hl : l.length = 1)
    (steps : M ↠ηᶠ (l.foldl app (fvar x))) :
    ∃ (n : ℕ) (A : Term Var) (E : List (Term Var)),
      M = abs^[n] ((A :: E).foldl app (fvar x)) ∧ LC A ∧ List.Forall₂ (Relation.ReflTransGen FullEta) [A] l ∧
        E.length = n ∧ EtaExpArgs n E ∧ (∀ B ∈ E, ∃ k < n, HasBvar k B ∧ ¬ LC B) := by
  obtain ⟨N, rfl⟩ : ∃ N, l = [N] := List.length_eq_one_iff.1 hl
  obtain ⟨n, A, E, hEq, hA, hAN, hlen, hE, hdangling⟩ :=
    betaNF_etaStar_shape_len_one hlc hM (by simpa using steps)
  exact ⟨n, A, E, hEq, hA, List.Forall₂.cons hAN List.Forall₂.nil, hlen, hE, hdangling⟩
