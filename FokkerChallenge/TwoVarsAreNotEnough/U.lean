import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FlipApp
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import FokkerChallenge.EnhancedCslib.ReflTransGenWithSteps
import FokkerChallenge.EnhancedCslib.HeadRed
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
def U (n : Nat) (x z : String) (a: Term String) : Prop :=
  a = fvar x \/
  (a.abs_two_vars_are_enough /\ a.depth < n) \/
  ∃ l : List _, a = l.foldl (flip app) (fvar z) /\ ∀ x ∈ l, x.abs_two_vars_are_enough /\ x.depth <= n

theorem U.LC {n x z }: ∀ N, U n x z N -> N.LC := by
  intros N h
  rcases h with _|_|⟨l, _, _⟩
  . grind
  . grind
  . subst_vars
    rw [flip_app_lc]
    grind

theorem two_vars_are_enough_openRec_U {n t N1 N0 x z}
  (g : two_vars_are_enough t)
  (ht : t.depth < n)
  (h1: ClosedUnderApp (U n x z) N1)
  (h2: ClosedUnderApp (U n x z) N0) :
  ClosedUnderApp (U n x z) (t⟦1 ↝ N1⟧⟦0 ↝ N0⟧) := by
  induction t with
  | fvar _ => grind
  | app _ _ iha ihb =>  simp at ht
                        exact .app (iha (by grind) (by grind)) (ihb (by grind) (by grind))
  | abs t => cases t with
    | abs _ => grind
    | bvar _ => unfold two_vars_are_enough at g
                grind
    | fvar _ => unfold two_vars_are_enough at g
                grind
    | app _ _ =>  unfold two_vars_are_enough at g
                  grind
  | bvar a => unfold two_vars_are_enough at g
              have h : a = 0 \/ a = 1 := by grind
              cases h <;> subst_vars
              . grind
              . simp [openRec]
                rw [open_lc]
                . grind
                . apply closedunderapp_lc U.LC h1

theorem HeadReduction2_step_preserve_closedUnderApp_U {M N n x z}
  (hmn: HeadReduction2 M N)
  (hm : ClosedUnderApp (U n x z) M) :
  ClosedUnderApp (U n x z) N  := by
  induction hmn with
  | appL h _ => cases hm with
    | app => grind
    | base hm =>  rcases hm with _|_|⟨l, hl, g⟩
                  . grind
                  . grind
                  . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
                    . grind
                    . subst_vars
                      rw [List.foldl_concat] at hl
                      unfold flip at hl
                      cases hl
                      rename_i M _ _
                      specialize g M (by grind)
                      cases h <;> grind
  | base => cases hm with
    | base hm =>  rcases hm with _|⟨_, _⟩|⟨l, hl, g⟩
                  . grind
                  . grind
                  . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
                    . grind
                    . subst_vars
                      rw [List.foldl_concat] at hl
                      unfold flip at hl
                      cases hl
                      rename_i M N
                      specialize g (M.abs.abs.app N) (by grind)
                      grind
    | app hm _ => cases hm with
      | app hm _ => cases hm with | base hm =>
                    rcases hm with _|_|⟨l, hl, h⟩
                    . grind
                    . apply two_vars_are_enough_openRec_U <;> grind
                    . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
                      . grind
                      . subst_vars
                        rw [List.foldl_concat] at hl
                        unfold flip at hl
                        cases hl
      | base hm =>  rcases hm with _|⟨_, _⟩|⟨l, hl, g⟩
                    . grind
                    . grind
                    . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
                      . grind
                      . subst_vars
                        rw [List.foldl_concat] at hl
                        unfold flip at hl
                        cases hl
                        rename_i M _ _
                        apply two_vars_are_enough_openRec_U
                        . specialize g M.abs.abs (by grind)
                          grind
                        . specialize g M.abs.abs (by grind)
                          grind
                        . refine .base ?_
                          right
                          right
                          refine ⟨l, ?_, by grind⟩
                          unfold flip
                          grind
                        . grind

theorem HeadReduction2_steps_preserve_closedUnderApp_U {M N n x z}
  (steps : M ↠𝒽 N)
  (hm : ClosedUnderApp (U n x z) M) :
  ClosedUnderApp (U n x z) N  := by
  induction steps with grind [HeadReduction2_step_preserve_closedUnderApp_U]


theorem closedUnderApp_reduce_to_head_apps (x z n) {M N}
  (hxz : x ≠ z)
  (hm : ClosedUnderApp (U n x z) M)
  (hx : x ∈ N.fv)
  (hmn : unroll M N) :
  ∃ l: List _, M ↠βᶠ l.foldl (flip app) N /\
               ∀ x ∈ l, x.abs_two_vars_are_enough /\ x.depth < n := by
  induction hmn using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by grind⟩
  | head h' h ih => cases h' with
  | reflTrans h' =>
  obtain ⟨l, ih, _⟩ := ih (HeadReduction2_step_preserve_closedUnderApp_U h' hm)
  exact ⟨l, .trans (HeadReduction2.step_2_beta h' (closedunderapp_lc U.LC hm)) ih, by grind⟩
  | throughAbsApp => cases hm with
    | app hn hc => cases hn with | base hn =>
        specialize ih hc
        rcases hn with _|_|⟨l, hl, _⟩
        . grind
        . rename_i Z _
          obtain ⟨l, ih, _⟩ := ih
          refine ⟨l ++ [Z.abs], ?_, by grind⟩
          rw [List.foldl_concat]
          unfold flip
          apply FullBeta.redex_app_r_cong ih (by grind)
        . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
          . grind
          . subst_vars
            rw [List.foldl_concat] at hl
            unfold flip at hl
            grind
    | base hm =>  rcases hm with _|⟨hm, _⟩|⟨l, heq, _⟩
                  . grind
                  . cases hm
                  . exfalso
                    have g := congrArg fv heq
                    have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
                    rw [<- List.map_eq_replicate_iff] at h5
                    rw [flip_app_fv, h5, foldl_union_replicate_empty] at g
                    apply unroll.fv at h
                    specialize h hx
                    have : x ∈ ({z} : Finset String) := by grind
                    grind

theorem U_le_fvar_or_combinator{i y z} : U i y z ≤ ClosedUnderApp fvar_or_combinator := by
  intro x hx
  rcases hx with _|_|⟨l, h, _⟩
  . grind
  . grind
  . subst x
    induction l using List.reverseRecOn with
    | nil => grind
    | append_singleton l a _ =>
    rw [List.foldl_concat]
    simp [flip]
    exact .app (by grind) (by grind)

theorem U_replicate {n x z i M} :
  ClosedUnderApp (U n x z) M ->
  ClosedUnderApp (U n x z) (List.foldl app M (List.replicate i (fvar x))) := by
  induction i generalizing M with grind

theorem U_foldl_z {Z l n x z}
  (h : ClosedUnderApp (U n x z) (List.foldl app (fvar z) (Z :: l))):
  ClosedUnderApp (U n x z) Z := by
  induction l using List.reverseRecOn with
  | nil =>  simp_all
            cases h with
            | app _ _ => grind
            | base h => rcases h with _|_|⟨l, h, hl⟩
                        . grind
                        . grind
                        . exfalso
                          induction l using List.reverseRecOn with
                          | nil => simp_all
                          | append_singleton l a _ =>
                          simp_all [flip]
                          obtain ⟨_, h⟩ := h
                          subst_vars
                          specialize hl (fvar z) (by grind)
                          grind
  | append_singleton l a _ =>
  simp at h
  cases h with
  | app _ _ => grind
  | base h => rcases h with _|_|⟨l, h, hl⟩
              . grind
              . grind
              . exfalso
                induction l using List.reverseRecOn with
                | nil => simp_all
                | append_singleton _ a _ =>
                simp_all [flip]
                obtain ⟨_, h⟩ := h
                subst_vars
                obtain ⟨_, _⟩ := hl (List.foldl app ((fvar z).app Z) l) (by grind)
                induction l  using List.reverseRecOn with grind

theorem U_foldl_x {Z l n x z}
  (h : ClosedUnderApp (U n x z) (List.foldl app (fvar x) (Z :: l))):
  ClosedUnderApp (U n x z) Z := by
  induction l using List.reverseRecOn with
  | nil =>  simp_all
            cases h with
            | app _ _ => grind
            | base h => rcases h with _|_|⟨l, h, hl⟩
                        . grind
                        . grind
                        . exfalso
                          induction l using List.reverseRecOn with
                          | nil => simp_all
                          | append_singleton l a _ =>
                          simp_all [flip]
                          obtain ⟨_, h⟩ := h
                          subst_vars
                          specialize hl (fvar x) (by grind)
                          grind
  | append_singleton l a _ =>
  simp at h
  cases h with
  | app _ _ => grind
  | base h => rcases h with _|_|⟨l, h, hl⟩
              . grind
              . grind
              . exfalso
                induction l using List.reverseRecOn with
                | nil => simp_all
                | append_singleton _ a _ =>
                simp_all [flip]
                obtain ⟨_, h⟩ := h
                subst_vars
                obtain ⟨_, _⟩ := hl (List.foldl app ((fvar x).app Z) l) (by grind)
                induction l  using List.reverseRecOn with grind

theorem U_subst_x {n x z y M} (h : (U n x z) M) (hxz : x ≠ z) :
  (U n y z) M[x:=fvar y] := by
  rcases h with _|_|⟨l, h, _⟩
  . grind
  . rw [subst_fresh] <;> grind
  . right
    right
    refine ⟨l, ?_, by grind⟩
    subst M
    rw [subst_fresh]; try grind
    rw [flip_app_fv]
    have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
    rw [<- List.map_eq_replicate_iff] at h5
    rw [h5, foldl_union_replicate_empty]
    grind

theorem U_subst_x_closedunderapp (y) {n x z M} (hxz : x ≠ z) (h : ClosedUnderApp (U n x z) M):
  ClosedUnderApp (U n y z) M[x:=fvar y] := by
  induction h with grind [U_subst_x]

theorem U_subst_z {n x z y M} (h : (U n x z) M) (hxz : x ≠ z) :
  (U n x y) M[z:=fvar y] := by
  rcases h with _|_|⟨l, h, _⟩
  . grind
  . rw [subst_fresh] <;> grind
  . right
    right
    refine ⟨l, ?_, by grind⟩
    subst M
    rw [multiapp_subst, subst_fvar]
    split <;> try grind
    apply congr rfl
    induction l with
    | nil => grind
    | cons head tail ih =>  simp
                            rw [subst_fresh] <;> grind

theorem U_subst_z_closedunderapp (y) {n x z M} (hxz : x ≠ z) (h : ClosedUnderApp (U n x z) M):
  ClosedUnderApp (U n x y) M[z:=fvar y] := by
  induction h with grind [U_subst_z]

theorem U_fv {n x z M}  (h : U n x z M): M.fv ⊆ {x, z} := by
  rcases h with _|_|⟨l, h, _⟩
  . grind
  . grind
  . subst_vars
    rw [flip_app_fv]
    have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
    rw [<- List.map_eq_replicate_iff] at h5
    rw [h5, foldl_union_replicate_empty]
    grind

theorem app_U_fv {n x z M} (h : ClosedUnderApp (U n x z) M):
   M.fv ⊆ {x, z} := by
   induction h with grind [U_fv]

theorem U_transform (x) {n z} : U n z z ≤ U n x z := by
  intros M h
  rcases h with _|_|⟨l, h, _⟩
  . right
    right
    use []
    grind
  . grind
  . grind

theorem app_U_transform (x) {n z} : ClosedUnderApp (U n z z) ≤ ClosedUnderApp (U n x z) := by
  intros M h
  induction h with
  | base h => exact .base (U_transform _ _ h)
  | app _ _ _ _ => grind

theorem U0 {x y} : U 0 x y ≤ (fun t => t.IsFvar \/ t.IsBvar) := by
  intros M h
  rcases h with _|_|⟨l, h, hl⟩
  . grind
  . grind
  . cases l with
    | nil => grind
    | cons head tail => specialize hl head (by grind)
                        grind

theorem app_U0 {x y} : ClosedUnderApp (U 0 x y) ≤ ClosedUnderApp (fun t => t.IsFvar \/ t.IsBvar) := by
  intros M h
  induction h with
  | base h => exact .base (U0 _ h)
  | app _ _ _ _ => grind
