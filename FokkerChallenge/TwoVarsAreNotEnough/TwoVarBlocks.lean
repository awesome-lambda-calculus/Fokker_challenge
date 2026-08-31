import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import FokkerChallenge.TwoVarsAreNotEnough.Q
import FokkerChallenge.TwoVarsAreNotEnough.U
import FokkerChallenge.TwoVarsAreNotEnough.Subterms
import FokkerChallenge.TwoVarsAreNotEnough.Nameable
import Mathlib.Data.Finset.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# Two-variable terms are β-reducts of combinations of binary blocks

A closed locally nameless term that can be written as a named term using only
the two variable names `x` and `y` never has more than one free variable under
any of its abstractions.  Consequently the usual λ-lifting translation only
ever needs *binary* supercombinators: abstractions `λ λ E` whose body `E`
mentions nothing but the two variables bound by those two abstractions
(together with further, closed, binary supercombinators).  Such terms are
exactly the ones recognised by `abs_two_vars_are_enough`.

The main theorem of this file, `exists_block_combination_betaStar`, says that
every term accepted by `isNamedOfXY` is a β-reduct of an application
combination of such blocks.
-/

/-! ## From `isNamedOfXY` to a named term -/

/-- `isNamedOfXY t` implies that `t` is the image of a closed named term over
the two names `x`, `y`. -/
theorem exists_named_of_isNamedOfXY {t : Term String} (h : isNamedOfXY t = true) :
    ∃ u : NTerm, NTerm.WN [] u ∧ NTerm.toLN [] u = t := by
  rw [isNamedOfXY] at h
  cases hn : namedOf? t with
  | none => rw [hn] at h; simp at h
  | some u₀ =>
      exact (namableXY_iff t).1 (namableXY_of_namedOf t u₀ hn)

/-! ## Auxiliary lemmas about `toLN` -/

theorem idx_lt_length {v : String} {ctx : List String} {i : ℕ}
    (h : NTerm.idx v ctx = some i) : i < ctx.length := by
  have h1 := (idx_eq_some_get h).1
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h1
  simp at h1

theorem idx_append_ne {z : String} : ∀ {ctx : List String} {v : String}, v ≠ z →
    NTerm.idx v (ctx ++ [z]) = NTerm.idx v ctx := by
  intro ctx
  induction ctx with
  | nil => intro v hv; simp [NTerm.idx, Ne.symm hv]
  | cons w ws ih =>
      intro v hv
      simp only [List.cons_append, NTerm.idx]
      by_cases hw : w = v
      · simp [hw]
      · simp [hw, ih hv]

theorem idx_append_self {z : String} : ∀ {ctx : List String}, z ∈ ctx →
    ∀ v, NTerm.idx v (ctx ++ [z]) = NTerm.idx v ctx := by
  intro ctx
  induction ctx with
  | nil => intro h; simp at h
  | cons w ws ih =>
      intro hz v
      simp only [List.cons_append, NTerm.idx]
      by_cases hw : w = v
      · simp [hw]
      · simp only [hw]
        by_cases hzs : z ∈ ws
        · rw [ih hzs]
        · have hwz : w = z := by
            rcases List.mem_cons.1 hz with h | h
            · exact h.symm
            · exact absurd h hzs
          rw [idx_append_ne (by rw [← hwz]; exact fun h => hw h.symm)]

theorem toLN_append_self {z : String} : ∀ (c : NTerm) {ctx : List String}, z ∈ ctx →
    NTerm.toLN (ctx ++ [z]) c = NTerm.toLN ctx c := by
  intro c
  induction c with
  | var v => intro ctx hz; simp only [NTerm.toLN, idx_append_self hz v]
  | abs w b ih =>
      intro ctx hz
      simp only [NTerm.toLN]
      have : w :: (ctx ++ [z]) = (w :: ctx) ++ [z] := by simp
      rw [this, ih (List.mem_cons_of_mem w hz)]
  | app a b iha ihb =>
      intro ctx hz
      simp only [NTerm.toLN, iha hz, ihb hz]

theorem subst_toLN_mem {z : String} {V : Term String} :
    ∀ (c : NTerm) {ctx : List String}, z ∈ ctx →
      (NTerm.toLN ctx c)[z:=V] = NTerm.toLN ctx c := by
  intro c
  induction c with
  | var v =>
      intro ctx hz
      simp only [NTerm.toLN]
      cases hv : NTerm.idx v ctx with
      | some i => split <;> grind
      | none =>
          split <;> try grind
          have hne : v ≠ z := by
            rintro rfl
            have := idx_isSome_of_mem hz
            rw [hv] at this
            simp at this
          grind
  | abs w b ih =>
      intro ctx hz
      simp only [NTerm.toLN]
      grind
  | app a b iha ihb =>
      intro ctx hz
      simp only [NTerm.toLN]
      grind

theorem openRec_toLN_ge {V : Term String} :
    ∀ (c : NTerm) {ctx : List String} {k : ℕ}, ctx.length ≤ k →
      Term.openRec k V (NTerm.toLN ctx c) = NTerm.toLN ctx c := by
  intro c
  induction c with
  | var v =>
      intro ctx k hk
      simp only [NTerm.toLN]
      cases hv : NTerm.idx v ctx with
      | some i =>
          have := idx_lt_length hv
          simp [Term.openRec]
          omega
      | none => simp [Term.openRec]
  | abs w b ih =>
      intro ctx k hk
      simp only [NTerm.toLN, Term.openRec]
      exact congrArg _ (ih (by simp; omega))
  | app a b iha ihb =>
      intro ctx k hk
      simp only [NTerm.toLN, Term.openRec, iha hk, ihb hk]

theorem idx_none_of_notMem {v : String} : ∀ {ctx : List String}, v ∉ ctx →
    NTerm.idx v ctx = none := by
  intro ctx
  induction ctx with
  | nil => intro _; rfl
  | cons w ws ih =>
      intro hv
      simp only [List.mem_cons, not_or] at hv
      simp [NTerm.idx, Ne.symm hv.1, ih hv.2]

theorem idx_append_notMem {z : String} : ∀ {ctx : List String}, z ∉ ctx →
    NTerm.idx z (ctx ++ [z]) = some ctx.length := by
  intro ctx
  induction ctx with
  | nil => intro _; simp [NTerm.idx]
  | cons w ws ih =>
      intro hz
      simp only [List.mem_cons, not_or] at hz
      have hwz : ¬ (w = z) := fun h => hz.1 h.symm
      simp [NTerm.idx, hwz, ih hz.2]

/-- Opening the last binder of a context is substitution for the corresponding
free variable. -/
theorem toLN_openRec_subst {V : Term String} :
    ∀ (c : NTerm) {ctx : List String} {z : String}, z ∉ ctx →
    Term.openRec ctx.length V (NTerm.toLN (ctx ++ [z]) c) = (NTerm.toLN ctx c)[z:=V] := by
  intro c
  induction c with
  | var v =>
      intro ctx z hz
      simp only [NTerm.toLN]
      by_cases hv : v = z
      · subst_vars
        rw [idx_append_notMem hz, idx_none_of_notMem hz]
        simp [Term.openRec]
        grind
      · rw [idx_append_ne hv]
        cases hi : NTerm.idx v ctx with
        | some i =>
            have := idx_lt_length hi
            simp [Term.openRec]
            split <;> grind
        | none => simp [Term.openRec]
                  grind
  | abs w b ih =>
      intro ctx z hz
      simp only [NTerm.toLN, Term.openRec]
      have hcons : w :: (ctx ++ [z]) = (w :: ctx) ++ [z] := by simp
      rw [hcons]
      by_cases hw : w = z
      · subst hw
        rw [toLN_append_self b (by simp), openRec_toLN_ge b (by simp), subst_abs, subst_toLN_mem b (by simp)]
      · have hlen : ((w :: ctx).length : ℕ) = ctx.length + 1 := by simp
        rw [← hlen]
        refine congrArg Term.abs (ih ?_)
        rintro h
        rcases List.mem_cons.1 h with rfl | h
        · exact hw rfl
        · exact hz h
  | app a b iha ihb =>
      intro ctx z hz
      simp only [NTerm.toLN, Term.openRec, iha hz, ihb hz]
      grind

theorem fv_toLN_eq_empty : ∀ (u : NTerm) {ctx : List String}, NTerm.WN ctx u →
    Term.fv (NTerm.toLN ctx u) = ∅ := by
  intro u
  induction u with
  | var v =>
      intro ctx h
      have hs := idx_isSome_of_mem (show v ∈ ctx from h)
      cases hv : NTerm.idx v ctx with
      | some i => simp [NTerm.toLN, hv, Term.fv]
      | none => rw [hv] at hs; simp at hs
  | abs w b ih =>
      intro ctx h
      exact ih h.2
  | app a b iha ihb =>
      intro ctx h
      simp [NTerm.toLN, Term.fv, iha h.1, ihb h.2]

theorem WN_mono : ∀ (u : NTerm) {ctx ctx' : List String}, (∀ v ∈ ctx, v ∈ ctx') →
    NTerm.WN ctx u → NTerm.WN ctx' u := by
  intro u
  induction u with
  | var v => intro ctx ctx' hsub h; exact hsub v h
  | abs w b ih =>
      intro ctx ctx' hsub h
      refine ⟨h.1, ih ?_ h.2⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub v hv)
  | app a b iha ihb =>
      intro ctx ctx' hsub h
      exact ⟨iha hsub h.1, ihb hsub h.2⟩

/-! ## Local closure of blocks -/

/-- A block `λ λ E` is locally closed as soon as opening it with two distinct
free variables is. -/
theorem lc_abs2_of {E : Term String}
    (h : ∀ f g : String, f ≠ g → LC (Term.openRec 0 (fvar g) (Term.openRec 1 (fvar f) E))) :
    LC (Term.abs (Term.abs E)) := by
  refine LC.abs ∅ _ ?_
  intro f _
  show LC (Term.openRec 0 (fvar f) (Term.abs E))
  simp only [Term.openRec]
  refine LC.abs {f} _ ?_
  intro g hg
  exact h f g (by simpa [eq_comm] using hg)

/-- Applying a block to two locally closed arguments gives a locally closed
term. -/
theorem lc_abs2_open {E A B : Term String} (hE : LC (Term.abs (Term.abs E)))
    (hA : LC A) (hB : LC B) : LC (Term.openRec 0 B (Term.openRec 1 A E)) := by
  rw [<- lcAt_iff_LC] at *
  rw [lcAt_openRec_iff_lcAt, lcAt_openRec_iff_lcAt]
  grind
  apply lcAt_le _ _ _ (by omega) hA
  grind

/-- The block `λ λ 1` is locally closed. -/
theorem lc_block_bvar1 : LC (Term.abs (Term.abs (Term.bvar 1)) : Term String) := by
  refine lc_abs2_of ?_
  intro f g _
  simpa [Term.openRec] using LC.fvar f

/-- The block `λ λ 0` is locally closed. -/
theorem lc_block_bvar0 : LC (Term.abs (Term.abs (Term.bvar 0)) : Term String) := by
  refine lc_abs2_of ?_
  intro f g _
  simpa [Term.openRec] using LC.fvar g

/-- Opening does not touch the (locally closed) head of an application. -/
theorem openRec_app_block {G W : Term String} (hG : LC G) (k : ℕ) (V : Term String) :
    Term.openRec k V (Term.app G W) = Term.app G (Term.openRec k V W) := by
  rw [show Term.openRec k V (Term.app G W)
        = Term.app (Term.openRec k V G) (Term.openRec k V W) from rfl, open_lc]
  grind

/-- A substituted variable no longer occurs free. -/
theorem notMem_fv_subst {p : String} {V T : Term String} (h : p ∉ Term.fv V) :
    p ∉ Term.fv (T[p:=V] ) := by
    grind [subst_preserve_not_fvar]

/-! ## The translation -/

/-- The terms that may be substituted for the two parameters: locally closed
terms not mentioning the names `x` and `y`. -/
@[simp, scoped grind unfold]
def AvoidXY (A : Term String) : Prop := "x" ∉ Term.fv A ∧ "y" ∉ Term.fv A

theorem AvoidXY.notMem {A : Term String} (hA : AvoidXY A) {p : String}
    (hp : p = "x" ∨ p = "y") : p ∉ Term.fv A := by
  rcases hp with rfl | rfl
  · exact hA.1
  · exact hA.2

/-- **Key lemma** (λ-lifting with binary supercombinators).  A named term whose
free variables are among the two names `p ≠ q` is computed by a block body `E`:
substituting `A` for the first and `B` for the second parameter of `E`
β-reduces to the term with `p := A`, `q := B`. -/
theorem exists_block_body : ∀ (u : NTerm) (p q : String), p ≠ q →
    (p = "x" ∨ p = "y") → (q = "x" ∨ q = "y") → NTerm.WN [p, q] u →
    ∃ E : Term String, two_vars_are_enough E = true ∧ LC (Term.abs (Term.abs E)) ∧
      ∀ A B : Term String, LC A → LC B → AvoidXY A → AvoidXY B →
(Term.openRec 0 B (Term.openRec 1 A E)) ↠βᶠ (((NTerm.toLN [] u)[q:=B])[p:=A]) := by
  intro u
  induction u with
  | var v =>
      intro p q hpq hp hq hwn
      have hv : v = p ∨ v = q := by simpa [NTerm.WN] using hwn
      have htv : NTerm.toLN [] (.var v) = Term.fvar v := rfl
      rcases hv with h | h
      · refine ⟨Term.bvar 1, by simp [two_vars_are_enough], lc_block_bvar1, ?_⟩
        intro A B hA hB hAx hBx
        rw [htv, h]
        have h1 : Term.openRec 0 B (Term.openRec 1 A (Term.bvar 1)) = A := by
          simp [Term.openRec]
          grind
        have h2 : ((Term.fvar p)[q:=B])[p:=A] = A := by
          grind
        rw [h1, h2]
      · refine ⟨Term.bvar 0, by simp [two_vars_are_enough], lc_block_bvar0, ?_⟩
        intro A B hA hB hAx hBx
        rw [htv, h]
        have h1 : Term.openRec 0 B (Term.openRec 1 A (Term.bvar 0)) = B := by
          simp [Term.openRec]
        have h2 : ((Term.fvar q)[q:=B])[p:=A] = B := by
          have hqq : (Term.fvar q)[q:=B] = B := by grind
          rw [hqq]
          apply Term.subst_fresh _ _ _ (hBx.notMem hp)
        rw [h1, h2]
  | app a b iha ihb =>
      intro p q hpq hp hq hwn
      obtain ⟨Ea, hEa, hLa, hRa⟩ := iha p q hpq hp hq hwn.1
      obtain ⟨Eb, hEb, hLb, hRb⟩ := ihb p q hpq hp hq hwn.2
      refine ⟨Term.app Ea Eb, by simp [two_vars_are_enough, hEa, hEb], ?_, ?_⟩
      · refine lc_abs2_of ?_
        intro f g _
        simp only [Term.openRec]
        exact LC.app (lc_abs2_open hLa (LC.fvar f) (LC.fvar g))
          (lc_abs2_open hLb (LC.fvar f) (LC.fvar g))
      · intro A B hA hB hAx hBx
        simp only [Term.openRec, NTerm.toLN]
        have h1 := hRa A B hA hB hAx hBx
        have h2 := hRb A B hA hB hAx hBx
        have lcXb := lc_abs2_open hLb hA hB
        refine (FullBeta.redex_app_l_cong h1 lcXb).trans (FullBeta.redex_app_r_cong h2 ?_)
        cases FullBeta.steps_lc_or_rfl h1 with
        | inl h => grind
        | inr h => grind [lc_abs2_open hLa hA hB]
  | abs z c ih =>
      intro p q hpq hp hq hwn
      obtain ⟨hz, hwnc⟩ := hwn
      have hzpq : z = p ∨ z = q := by
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
          rcases hz with rfl | rfl <;> simp_all
      have hmem : ∀ v ∈ z :: [p, q], v ∈ [p, q] := by
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · rcases hzpq with rfl | rfl <;> simp
        · exact hv
      have hmem' : ∀ v ∈ z :: [p, q], v ∈ [q, p] := by
        intro v hv
        have := hmem v hv
        simp at this ⊢
        tauto
      have hc1 : NTerm.WN [p, q] c := WN_mono c hmem hwnc
      have hc2 : NTerm.WN [q, p] c := WN_mono c hmem' hwnc
      rcases hzpq with hzp | hzq
      · -- the binder is named `p`; the block's parameters are `(q, p)`
        obtain ⟨Ec, hEc, hLc, hRc⟩ := ih q p (Ne.symm hpq) hq hp hc2
        refine ⟨Term.app (Term.abs (Term.abs Ec)) (Term.bvar 0), ?_, ?_, ?_⟩
        · simp [two_vars_are_enough, hEc]
        · refine lc_abs2_of ?_
          intro f g _
          have he : Term.openRec 0 (Term.fvar g)
              (Term.openRec 1 (Term.fvar f) (Term.app (Term.abs (Term.abs Ec)) (Term.bvar 0)))
              = Term.app (Term.abs (Term.abs Ec)) (Term.fvar g) := by
            rw [openRec_app_block hLc, openRec_app_block hLc]
            simp [Term.openRec]
          rw [he]
          exact LC.app hLc (LC.fvar g)
        · intro A B hA hB hAx hBx
          have hopen : Term.openRec 0 B
              (Term.openRec 1 A (Term.app (Term.abs (Term.abs Ec)) (Term.bvar 0)))
              = Term.app (Term.abs (Term.abs Ec)) B := by
            rw [openRec_app_block hLc, openRec_app_block hLc]
            simp [Term.openRec]
          rw [hopen]
          have hstep : FullBeta (Term.app (Term.abs (Term.abs Ec)) B)
              (Term.abs (Term.openRec 1 B Ec)) := by
            have := Xi.base (Beta.beta (M := Term.abs Ec) (N := B) hLc hB)
            grind
          refine Relation.ReflTransGen.head hstep ?_
          have htarget : ((NTerm.toLN [] (.abs z c))[q:=B])[p:=A]
              = Term.abs (((NTerm.toLN [p] c)[q:=B])[p:=A]) := by
            rw [hzp]
            simp [NTerm.toLN]
            grind
          rw [htarget]
          refine FullBeta.redex_abs_cong ({"x", "y"} : Finset String) ?_
          intro f hf
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
          have hfp : f ≠ p := by rcases hp with rfl | rfl; exacts [hf.1, hf.2]
          have hfq : f ≠ q := by rcases hq with rfl | rfl; exacts [hf.1, hf.2]
          have hAvf : AvoidXY (Term.fvar f) := by
            constructor <;> simp [Term.fv] <;> tauto
          have hL := hRc B (Term.fvar f) hB (LC.fvar f) hBx hAvf
          have e1 : (Term.fvar f)[p:=A] = Term.fvar f := by grind
          have e2 : (Term.fvar f)[q:=B] = Term.fvar f := by grind
          have hpnot : p ∉ Term.fv (((NTerm.toLN [] c)[p:=Term.fvar f])[q:=B]) := by
            intro hcc
            cases (@subst_preserve_not_fvar _ _ q (NTerm.toLN [] c)[p:=Term.fvar f] B) <;>
            cases (@subst_preserve_not_fvar _ _ p (NTerm.toLN [] c) (Term.fvar f))
            . grind
            . grind
            . grind
            . rename_i h1 h2
              rw [h1, h2] at hcc
              simp at hcc
              cases hcc <;> grind
          have hRHS : (((NTerm.toLN [p] c)[q:=B])[p:=A]) ^ Term.fvar f
              = ((NTerm.toLN [] c)[p:=Term.fvar f])[q:=B] := by
            calc (((NTerm.toLN [p] c)[q:=B])[p:=A]) ^ Term.fvar f
                = Term.openRec 0 ((Term.fvar f)[p:=A])
                    (((NTerm.toLN [p] c)[q:=B])[p:=A]) := by rw [e1]
              _ = (Term.openRec 0 (Term.fvar f)
                    ((NTerm.toLN [p] c)[q:=B]))[p:=A] := by grind
              _ = ((Term.openRec 0 (Term.fvar f) (NTerm.toLN [p] c))[q:=B])[p:=A] := by grind
              _ = (((NTerm.toLN [] c)[p:=Term.fvar f])[q:=B])[p:=A] := by
                    have := toLN_openRec_subst (V := Term.fvar f) c (ctx := []) (z := p) (by simp)
                    grind
              _ = ((NTerm.toLN [] c)[p:=Term.fvar f])[q:=B] := Term.subst_fresh _ _ _ hpnot
          rw [hRHS]
          grind
      · -- the binder is named `q`; the block's parameters are `(p, q)`
        obtain ⟨Ec, hEc, hLc, hRc⟩ := ih p q hpq hp hq hc1
        refine ⟨Term.app (Term.abs (Term.abs Ec)) (Term.bvar 1), ?_, ?_, ?_⟩
        · simp [two_vars_are_enough, hEc]
        · refine lc_abs2_of ?_
          intro f g _
          have he : Term.openRec 0 (Term.fvar g)
              (Term.openRec 1 (Term.fvar f) (Term.app (Term.abs (Term.abs Ec)) (Term.bvar 1)))
              = Term.app (Term.abs (Term.abs Ec)) (Term.fvar f) := by
            rw [openRec_app_block hLc, openRec_app_block hLc]
            simp [Term.openRec]
          rw [he]
          exact LC.app hLc (LC.fvar f)
        · intro A B hA hB hAx hBx
          have hopen : Term.openRec 0 B
              (Term.openRec 1 A (Term.app (Term.abs (Term.abs Ec)) (Term.bvar 1)))
              = Term.app (Term.abs (Term.abs Ec)) A := by
            rw [openRec_app_block hLc, openRec_app_block hLc]
            simp [Term.openRec]
            grind
          rw [hopen]
          have hstep : FullBeta (Term.app (Term.abs (Term.abs Ec)) A)
              (Term.abs (Term.openRec 1 A Ec)) := by
            have := Xi.base (Beta.beta (M := Term.abs Ec) (N := A) hLc hA)
            grind
          refine Relation.ReflTransGen.head hstep ?_
          have htarget : ((NTerm.toLN [] (.abs z c))[q:=B])[p:=A]
              = Term.abs (((NTerm.toLN [q] c)[q:=B])[p:=A]) := by
            rw [hzq]
            simp [NTerm.toLN]
            grind
          rw [htarget]
          refine FullBeta.redex_abs_cong ({"x", "y"} : Finset String) ?_
          intro f hf
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
          have hfp : f ≠ p := by rcases hp with rfl | rfl; exacts [hf.1, hf.2]
          have hfq : f ≠ q := by rcases hq with rfl | rfl; exacts [hf.1, hf.2]
          have hAvf : AvoidXY (Term.fvar f) := by
            constructor <;> simp [Term.fv] <;> tauto
          have hL := hRc A (Term.fvar f) hA (LC.fvar f) hAx hAvf
          have e1 : (Term.fvar f)[p:=A] = Term.fvar f := by grind
          have e2 : (Term.fvar f)[q:=B] = Term.fvar f := by grind
          have hqnot : q ∉ Term.fv ((NTerm.toLN [] c)[q:=Term.fvar f]) :=
            notMem_fv_subst (by simp [Term.fv]; tauto)
          have hRHS : (((NTerm.toLN [q] c)[q:=B])[p:=A]) ^ Term.fvar f
              = ((NTerm.toLN [] c)[q:=Term.fvar f])[p:=A] := by
            calc (((NTerm.toLN [q] c)[q:=B])[p:=A]) ^ Term.fvar f
                = Term.openRec 0 ((Term.fvar f)[p:=A])
                    (((NTerm.toLN [q] c)[q:=B])[p:=A]) := by rw [e1]
              _ = (Term.openRec 0 (Term.fvar f) ((NTerm.toLN [q] c)[q:=B]))[p:=A] := by grind
                    -- (Term.subst_openRec hA 0 (Term.fvar f) _).symm
              _ = ((Term.openRec 0 (Term.fvar f) (NTerm.toLN [q] c))[q:=B])[p:=A] := by grind
                    -- rw [Term.subst_openRec hB 0 (Term.fvar f), e2]
              _ = (((NTerm.toLN [] c)[q:=Term.fvar f])[q:=B])[p:=A] := by
                    have := toLN_openRec_subst (V := Term.fvar f) c (ctx := []) (z := q) (by simp)
                    simpa using congrArg (fun X => (X[q:=B])[p:=A]) this
              _ = ((NTerm.toLN [] c)[q:=Term.fvar f])[p:=A] := by
                    rw [Term.subst_fresh _ _ _ hqnot]
          rw [hRHS]
          grind

/-- **Main theorem**: a term nameable with the two names `x` and `y` is a
β-reduct of an application combination of binary blocks. -/
theorem exists_block_combination_betaStar (t : Term String) (h : isNamedOfXY t = true) :
    ∃ s : Term String,
      ClosedUnderAppBool abs_two_vars_are_enough s ∧ s ↠βᶠ t := by
  obtain ⟨u, hwn, rfl⟩ := exists_named_of_isNamedOfXY h
  have hwn2 : NTerm.WN ["x", "y"] u := WN_mono u (by simp) hwn
  obtain ⟨E, hE, hLE, hR⟩ :=
    exists_block_body u "x" "y" (by decide) (Or.inl rfl) (Or.inr rfl) hwn2
  refine ⟨Term.app (Term.app (Term.abs (Term.abs E)) (Term.abs (Term.abs (Term.bvar 1))))
    (Term.abs (Term.abs (Term.bvar 1))), ?_, ?_⟩
  · have hK : abs_two_vars_are_enough (Term.abs (Term.abs (Term.bvar 1))) = true := by decide
    have hG : abs_two_vars_are_enough (Term.abs (Term.abs E)) = true := hE
    unfold ClosedUnderAppBool
    grind
  · have hKlc : LC (Term.abs (Term.abs (Term.bvar 1)) : Term String) := lc_block_bvar1
    have hKav : AvoidXY (Term.abs (Term.abs (Term.bvar 1)) : Term String) := by
      constructor <;> simp [Term.fv]
    have step1 : FullBeta
        (Term.app (Term.abs (Term.abs E)) (Term.abs (Term.abs (Term.bvar 1))))
        (Term.abs (Term.openRec 1 (Term.abs (Term.abs (Term.bvar 1))) E)) := by
      have := Xi.base (Beta.beta (M := Term.abs E)
        (N := (Term.abs (Term.abs (Term.bvar 1)) : Term String)) hLE hKlc)
      grind
    have hlc : LC (Term.abs (Term.openRec 1 (Term.abs (Term.abs (Term.bvar 1))) E)) := by
      rw [<- lcAt_iff_LC] at *
      unfold LcAt
      rw [lcAt_openRec_iff_lcAt]
      grind
      grind
    have step2 : FullBeta
        (Term.app (Term.abs (Term.openRec 1 (Term.abs (Term.abs (Term.bvar 1))) E))
          (Term.abs (Term.abs (Term.bvar 1))))
        (Term.openRec 0 (Term.abs (Term.abs (Term.bvar 1)))
          (Term.openRec 1 (Term.abs (Term.abs (Term.bvar 1))) E)) := by
      have := Xi.base (Beta.beta (M := Term.openRec 1 (Term.abs (Term.abs (Term.bvar 1))) E)
        (N := (Term.abs (Term.abs (Term.bvar 1)) : Term String)) hlc hKlc)
      grind
    have hR' := hR _ _ hKlc hKlc hKav hKav
    have hfv : Term.fv (NTerm.toLN [] u) = ∅ := fv_toLN_eq_empty u hwn
    have hsubst : ((NTerm.toLN [] u)["y":=(Term.abs (Term.abs (Term.bvar 1)) : Term String)])["x":= (Term.abs (Term.abs (Term.bvar 1)) : Term String)]
        = NTerm.toLN [] u := by
      have hy :  (NTerm.toLN [] u)["y":= (Term.abs (Term.abs (Term.bvar 1)))]
          = NTerm.toLN [] u := Term.subst_fresh _ _ _ (by simp [hfv])
      rw [hy, Term.subst_fresh _ _ _ (by simp [hfv])]
    rw [hsubst] at hR'
    exact (Relation.ReflTransGen.head (Xi.appR hKlc step1)
      (Relation.ReflTransGen.single step2)).trans hR'

/-! ### Examples -/

section Examples

/-- `λ λ (1 0)` can be named with the two names `x`, `y`. -/
example : isNamedOfXY (Term.abs (Term.abs (Term.app (Term.bvar 1) (Term.bvar 0)))) = true := by
  decide

/-- Hence the main theorem applies to it: it is the β-reduct of a combination of
binary blocks. -/
example : ∃ s : Term String,
    ClosedUnderAppBool abs_two_vars_are_enough s ∧
    s ↠βᶠ (Term.abs (Term.abs (Term.app (Term.bvar 1) (Term.bvar 0)))) :=
  exists_block_combination_betaStar _ (by decide)

/-- `λa. λb. λc. a b` genuinely needs three names and is rejected. -/
example :
    isNamedOfXY (Term.abs (Term.abs (Term.abs (Term.app (Term.bvar 2) (Term.bvar 1)))))
      = false := by
  decide

end Examples
