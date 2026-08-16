import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem Leftmost.induction_rule
    {motive : ∀ {a b : Term String}, Leftmost a b → Prop}
    {a b : Term String}
    (h : Leftmost a b)
    (h_outer :
      ∀ (M N : Term String)(hm : M.abs.LC)(hn : N.LC), motive (BetaAt.outer (M:=M) (N:=N) hm hn))
      (h_appL :
  ∀ {M M' N : Term String}
    (h : Leftmost M M')
    (hi : ¬ IsAbs M),
    motive h →
    @motive (M.app N) (M'.app N) (by simpa [Leftmost, hi] using (BetaAt.appL h)))
      (h_appR :
  ∀  {M M' N : Term String}
    (h : Leftmost M M')
    (hi : ¬ IsAbs N)
    (g : N.countRedexes = 0),
    motive h →
    @motive (N.app M) (N.app M') (by
      have hidx : (N.countRedexes + if N.IsAbs then 1 else 0) = 0 := by grind
      unfold Leftmost
      simpa [hidx] using (@BetaAt.appR _ _ _ _ N h)
      ))
    (h_abs :
      ∀ (M M': Term String) (xs : Finset String)
        (h :
          ∀ x ∉ xs,
            Leftmost (M ^ fvar x) (M' ^ fvar x)),
      (∀ x hx, motive (h x hx)) →
      motive (BetaAt.abs xs h))
    : motive h := by
  unfold Leftmost at h
  generalize hi : 0 = i
  rw [hi] at h
  induction h with
  | outer => grind
  | appL h ih =>
      rename_i i _ _ _ _
      have : i = 0 := by omega
      subst i
      apply h_appL
      grind
      grind
      exact h
  | appR h =>
      rename_i i _ _ _ _ _
      have : i = 0 := by omega
      subst i
      apply h_appR
      grind
      grind
      grind
      exact h
  | abs xs h ih =>
      subst_vars
      exact h_abs _ _ xs
        (by
          intro x hx
          exact h x hx)
        (by
          intro x hx
          apply ih _ hx
          omega)

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
