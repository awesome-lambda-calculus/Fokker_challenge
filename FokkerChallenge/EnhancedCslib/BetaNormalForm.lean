import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def has_beta_redex: Term String → Bool
  | Term.bvar _ => false
  | Term.fvar _ => false
  | Term.abs t => has_beta_redex t
  | Term.app (Term.abs _) _ => true
  | Term.app t1 t2 => has_beta_redex t1 || has_beta_redex t2

lemma has_beta_redex_openRec (i : ℕ) (x : String) (M : Term String) :
    has_beta_redex (Term.openRec i (Term.fvar x) M) = has_beta_redex M := by
  induction M generalizing i with
  | bvar j =>
    show has_beta_redex (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs t ih =>
    show has_beta_redex (Term.openRec (i + 1) (Term.fvar x) t) = has_beta_redex t
    exact ih (i + 1)
  | app l r ih_l ih_r =>
    cases l with
    | bvar j =>
      show has_beta_redex (Term.app (if i = j then Term.fvar x else Term.bvar j)
            (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
      split
      · show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
        rw [ih_r]; rfl
      · show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
        rw [ih_r]; rfl
    | fvar _ =>
      show (false || has_beta_redex (Term.openRec i (Term.fvar x) r)) = has_beta_redex r
      rw [ih_r]; rfl
    | abs _ => rfl
    | app l1 l2 =>
      show (has_beta_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            || has_beta_redex (Term.openRec i (Term.fvar x) r))
            = (has_beta_redex (Term.app l1 l2) || has_beta_redex r)
      rw [show
            has_beta_redex (Term.app (Term.openRec i (Term.fvar x) l1)
              (Term.openRec i (Term.fvar x) l2))
            = has_beta_redex (Term.app l1 l2)
          from ih_l i, ih_r i]

lemma has_beta_redex_of_full_beta {M N : Term String} (h : FullBeta M N) :
    has_beta_redex M = true := by
  induction h with
  | base h_b =>
    cases h_b with | beta _ _ => rfl
  | @appL Z M' _ _ _ ih =>
    cases Z with
    | abs _ => rfl
    | bvar _ =>
      show (false || has_beta_redex M') = true
      simp [ih]
    | fvar _ =>
      show (false || has_beta_redex M') = true
      simp [ih]
    | app a b =>
      show (has_beta_redex (Term.app a b) || has_beta_redex M') = true
      simp [ih]
  | @appR Z M' _ _ _ ih =>
    cases M' with
    | abs _ => rfl
    | bvar _ => simp [has_beta_redex] at ih
    | fvar _ => simp [has_beta_redex] at ih
    | app a b =>
      show (has_beta_redex (Term.app a b) || has_beta_redex Z) = true
      simp [ih]
  | @abs M' _ xs _ ih =>
    show has_beta_redex M' = true
    have ⟨x, hx⟩ := fresh_exists xs
    rw [← has_beta_redex_openRec 0 x M']
    exact ih x hx

theorem has_beta_redex_equiv_full_beta {M : Term String} :
    (has_beta_redex M ∧ M.LC) ↔ ∃ N, FullBeta M N := by
  constructor
  · rintro ⟨h_redex, h_lc⟩
    induction h_lc with
    | fvar _ => simp [has_beta_redex] at h_redex
    | @abs L e h_body ih =>
      have h_redex_e : has_beta_redex e = true := h_redex
      have ⟨x, hx⟩ := fresh_exists (L ∪ e.fv : Finset String)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨hxL, hxe⟩ := hx
      have h_redex_open : has_beta_redex (e ^ Term.fvar x) = true := by
        show has_beta_redex (Term.openRec 0 (Term.fvar x) e) = true
        rw [has_beta_redex_openRec]; exact h_redex_e
      have ⟨N, hN⟩ := ih x hxL h_redex_open
      have hclose : ((e ^ Term.fvar x) ^* x).abs ⭢βᶠ (N ^* x).abs :=
        FullBeta.step_abs_close hN
      rw [show (e ^ Term.fvar x) ^* x = e from (open_close_var x e hxe).symm] at hclose
      exact ⟨_, hclose⟩
    | @app l r lc_l lc_r ih_l ih_r =>
      cases l with
      | bvar i => cases lc_l
      | fvar y =>
        have hr : has_beta_redex r = true := h_redex
        have ⟨N, hN⟩ := ih_r hr
        exact ⟨_, Xi.appL lc_l hN⟩
      | abs t =>
        exact ⟨t ^ r, .base (.beta lc_l lc_r)⟩
      | app l1 l2 =>
        have h_or : (has_beta_redex (Term.app l1 l2) || has_beta_redex r) = true := h_redex
        by_cases hl : has_beta_redex (Term.app l1 l2) = true
        · have ⟨N, hN⟩ := ih_l hl
          exact ⟨_, Xi.appR lc_r hN⟩
        · have hl_false : has_beta_redex (Term.app l1 l2) = false := by
            cases hh : has_beta_redex (Term.app l1 l2)
            · rfl
            · exact absurd hh hl
          rw [hl_false] at h_or
          have hr : has_beta_redex r = true := h_or
          have ⟨N, hN⟩ := ih_r hr
          exact ⟨_, Xi.appL lc_l hN⟩
  · rintro ⟨N, hN⟩
    exact ⟨has_beta_redex_of_full_beta hN, FullBeta.step_lc_l hN⟩

theorem normal_fullBeta_iff_no_beta_redex {N}: (N.has_beta_redex = false \/ ¬ N.LC) <-> Relation.Normal FullBeta N := by grind [has_beta_redex_equiv_full_beta]


@[scoped grind]
axiom betanormal_iff {M : Term String} : BetaNormal M <-> Relation.Normal FullBeta M

theorem normal_app (t : Term String) (hlc : t.LC) (habs: ¬ IsAbs t) (hfv : t.fv = ∅) : ¬t.BetaNormal := by
  induction t with cases hlc
  | abs _ _ => grind
  | fvar _ => unfold fv at hfv
              simp at hfv
  | app a _ ihl _ =>  by_cases a.IsAbs
                      . grind [BetaNormal, countRedexes]
                      . specialize ihl (by grind) (by grind) (by grind)
                        intro h
                        apply BetaNormal.app_inv at h
                        grind [BetaNormal, countRedexes]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
