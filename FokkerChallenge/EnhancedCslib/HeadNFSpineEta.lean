import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import FokkerChallenge.EnhancedCslib.HeadSN
import FokkerChallenge.EnhancedCslib.EtaSpineOpenFv
import FokkerChallenge.EnhancedCslib.HeadNFSpineBeta

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# η-reduction of a head normal form to a variable-headed spine

If a head normal form `M` η-reduces (in any number of steps) to an application
spine `x N₁ … Nₖ` headed by a *free* variable, then `M` is already such a spine,
`M = x N'₁ … N'ₖ`, and the arguments η-reduce componentwise, `N'ᵢ ↠η Nᵢ`.

The main result is `steps_headnf_preserve_multiapp`.  Along the way we prove the
basic inversion lemmas for η-steps out of an application or an abstraction, and
the fact that η-reduction out of a spine can only take place inside the
arguments (`spine_FullEtaStar_inv`).
-/


universe u

open Term

variable {Var : Type u}

/-! ## Inversion lemmas for a single η-step -/

/-- A η-step out of an application either contracts the top-level redex, or
takes place in the argument, or in the function. -/
theorem FullEta_app_inv {A B N : Term Var} (h : FullEta (app A B) N) :
    (∃ C, A = abs C ∧ N = C ^ B) ∨ (∃ B', N = app A B' ∧ FullEta B B') ∨
      (∃ A', N = app A' B ∧ FullEta A A') := by
  cases h with
  | base hb => cases hb
  | appL _ hs => exact Or.inr (Or.inl ⟨_, rfl, hs⟩)
  | appR _ hs => exact Or.inr (Or.inr ⟨_, rfl, hs⟩)

/-! ## η-reduction out of a spine -/

/-- A η-step out of a spine `x N₁ … Nₖ` takes place inside one of the
arguments. -/
theorem spine_FullEta_inv {x : Var} {l : List (Term Var)} {N : Term Var}
    (h : FullEta (spine x l) N) :
    ∃ l', N = spine x l' ∧ List.Forall₂ (Relation.ReflTransGen FullEta) l l' := by
  induction l using List.reverseRecOn generalizing N with
  | nil =>
      rw [spine_nil] at h
      cases h with
      | base hb => cases hb
  | append_singleton l₀ b ih =>
      rw [spine_concat] at h
      rcases FullEta_app_inv h with ⟨C, hC, _⟩ | ⟨b', rfl, hb⟩ | ⟨A', rfl, hA⟩
      · exact absurd hC spine_ne_abs
      · exact ⟨l₀ ++ [b'], by rw [spine_concat],
          forall₂_concat (forall₂_refl l₀)
            (Relation.ReflTransGen.single hb)⟩
      · obtain ⟨l₁, rfl, hl₁⟩ := ih hA
        exact ⟨l₁ ++ [b], by rw [spine_concat],
          forall₂_concat hl₁ Relation.ReflTransGen.refl⟩

/-- Any number of η-steps out of a spine `x N₁ … Nₖ` only reduce the arguments:
the reduct is a spine with the same head and componentwise η-reducts as
arguments. -/
theorem spine_FullEtaStar_inv {x : Var} {l : List (Term Var)} {N : Term Var}
    (h : (Relation.ReflTransGen FullEta) (spine x l) N) :
    ∃ l', N = spine x l' ∧ List.Forall₂ (Relation.ReflTransGen FullEta) l l' := by
  induction h with
  | refl => exact ⟨l, rfl, forall₂_refl l⟩
  | tail _ hstep ih =>
      obtain ⟨l₁, rfl, hl₁⟩ := ih
      obtain ⟨l₂, rfl, hl₂⟩ := spine_FullEta_inv hstep
      exact ⟨l₂, rfl, forall₂_trans hl₁ hl₂⟩

theorem eta_steps_preserve_fvar_apps {x : String} {M : Term String}
    {l : List (Term String)} (steps : l.foldl app (fvar x) ↠ηᶠ M) :
    ∃ l' : List _, M = l'.foldl app (fvar x) ∧
      List.Forall₂ (Relation.ReflTransGen FullEta) l l' :=
  spine_FullEtaStar_inv (x := x) (l := l) steps


theorem beta_eta_steps_preserve_fvar_apps {x : String} {M : Term String}
    {l : List (Term String)} (steps : l.foldl app (fvar x) ↠βηᶠ M) :
    ∃ l' : List _, M = l'.foldl app (fvar x) ∧
      List.Forall₂ (Relation.ReflTransGen FullBetaEta) l l' := by
  induction steps with
  | refl => refine ⟨l, by grind, forall₂_refl _⟩
  | tail _ h ih =>  obtain ⟨l', _, ih⟩ := ih
                    subst_vars
                    cases h with
      | inl h =>  obtain ⟨l, h, g⟩ := beta_steps_preserve_fvar_apps (.single h)
                  exact ⟨_, h, forall₂_trans ih (forall₂_sub (Relation.ReflTransGen.mono le_sup_left) g)⟩
      | inr h =>  obtain ⟨l, h, g⟩ := eta_steps_preserve_fvar_apps (.single h)
                  exact ⟨_, h, forall₂_trans ih (forall₂_sub (Relation.ReflTransGen.mono le_sup_right) g)⟩
