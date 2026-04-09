import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

private lemma key_lemma {M T : Term String} {x : String}
    (h_lc : M.LC) (h_fv : x ∉ M.fv)
    (h_red : Relation.ReflTransGen FullBeta (Term.app M (Term.fvar x)) T) :
    (∃ M', T = Term.app M' (Term.fvar x) ∧
        Relation.ReflTransGen FullBeta M M' ∧ x ∉ M'.fv ∧ M'.LC)
    ∨ (∃ N, Relation.ReflTransGen FullBeta M (Term.abs N) ∧ N.abs.LC) := by
  induction h_red with
  | refl =>
    left
    exact ⟨M, rfl, Relation.ReflTransGen.refl, h_fv, h_lc⟩
  | tail h_red h_step ih =>
    cases ih with
    | inl h =>
      obtain ⟨M', hM_eq, h_M_red, h_fv', h_lc'⟩ := h
      subst hM_eq
      cases FullBeta.invert_step_app_fvar h_step with
      | inl h2 =>
        obtain ⟨M'', h_eq', h_step'⟩ := h2
        left
        refine ⟨M'', h_eq', ?_, ?_, ?_⟩
        · exact Relation.ReflTransGen.tail h_M_red h_step'
        · grind [FullBeta.step_not_fv h_step']
        · exact FullBeta.step_lc_r h_step'
      | inr h2 =>
        obtain ⟨M1, h_eq', h_T_eq⟩ := h2
        right
        subst h_eq'
        exact ⟨M1, h_M_red, h_lc'⟩
    | inr h =>
      right
      exact h

theorem ReductionToAbstraction {M Y} {x : String} :
    M.LC →
    x ∉ M.fv →
    Relation.ReflTransGen FullBeta (Term.app M (Term.fvar x)) (Term.app (Term.fvar x) Y) →
    ∃ N, Relation.ReflTransGen FullBeta M (Term.abs N) ∧ N.abs.LC := by
  intros h_lc h_fv h_red
  cases key_lemma h_lc h_fv h_red with
  | inl h =>
    obtain ⟨M', h_eq, _, h_fv', _⟩ := h
    have h1 : M' = Term.fvar x := by
      injection h_eq.symm with h1 _
    rw [h1] at h_fv'
    simp at h_fv'
  | inr h => exact h

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
