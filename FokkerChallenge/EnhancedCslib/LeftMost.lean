import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem leftmost_multiapp (f a: Term String) (l) : f.abs.LC -> a.LC ->
  (a :: l).foldl Term.app f.abs ⭢ℓ l.foldl Term.app (f^a) := by
  induction l using List.reverseRecOn generalizing f a with
  | nil => apply BetaAt.outer
  | append_singleton l a _ => intros _ _
                              simp
                              apply BetaAt.appNoAbsL
                              grind
                              intros h
                              generalize heq : (List.foldl app (f.abs.app a) l) = Q
                              rw [heq] at h
                              cases h
                              induction l using List.reverseRecOn with grind

theorem leftstar_cases {M N Q : Term String} (h : M.app N ↠ℓ Q) :
 (∃ M' N', M ↠ℓ M' /\ N ↠ℓ N' /\ Q = M'.app N') \/ ∃ M', M ↠ℓ Term.abs M' :=  by
  induction h with
  | refl => grind
  | tail _ g ih => cases ih with
    | inr h => grind
    | inl h => induction g using Leftmost.induction_rule <;> grind

theorem betastar_of_non_abs {M N : Term String} (hm : ∀ M', M ↠ℓ M' -> M'.IsAbs -> False) :
  ∀ Q, M.app N ↠ℓ Q -> ∃ M' N', M ↠ℓ M' /\ N ↠ℓ N' /\ Q = M'.app N' :=  by
  grind [leftstar_cases]

theorem normalizable_app_implies_normalizable_or_reduces_to_abs {M N : Term String}
  (h : Relation.Normalizable Leftmost (Term.app M N)):
  Relation.Normalizable Leftmost M \/ ∃ M', M'.IsAbs /\ M ↠ℓ M' := by
  by_contra hcontra
  simp at hcontra
  obtain ⟨hm, _⟩ := hcontra
  obtain ⟨Q, h, g⟩ := h
  have g_back := g
  obtain ⟨M', N', hmm', _, _⟩ := @betastar_of_non_abs M N (by grind) Q h
  apply g_back
  obtain ⟨M'', h⟩ := hm M' hmm'
  exists M''.app N'
  subst Q
  apply BetaAt.appNoAbsL <;> grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
