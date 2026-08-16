import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.EnhancedCslib.CountBvar
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- `is_eta_pattern t` recognises the body of an η-redex: `t = app A (bvar 0)`
where `A` does not reference `bvar 0`. -/
@[simp, scoped grind =]
def is_eta_pattern : Term String → Bool
  | Term.app A (Term.bvar 0) => count_bvar 0 A = 0
  | _ => false

/-- `has_eta_redex M` returns `true` iff `M` contains a sub-term of the form
`abs (app A (bvar 0))` where `A` does not reference the immediately binding
abstraction. After fully opening the surrounding binders such a sub-term
becomes a real η-redex. -/
@[simp, scoped grind =]
def has_eta_redex : Term String → Bool
  | Term.bvar _ => false
  | Term.fvar _ => false
  | Term.abs t => is_eta_pattern t || has_eta_redex t
  | Term.app l r => has_eta_redex l || has_eta_redex r


lemma is_eta_pattern_openRec {i : ℕ} {x : String} (t : Term String)
    (h : i ≠ 0) :
    is_eta_pattern (Term.openRec i (Term.fvar x) t) = is_eta_pattern t := by
  cases t with
  | bvar j =>
    show is_eta_pattern (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs _ => rfl
  | app l r =>
    show is_eta_pattern (Term.app (Term.openRec i (Term.fvar x) l)
                                  (Term.openRec i (Term.fvar x) r))
        = is_eta_pattern (Term.app l r)
    cases r with
    | bvar j =>
      show is_eta_pattern (Term.app (Term.openRec i (Term.fvar x) l)
                                    (if i = j then Term.fvar x else Term.bvar j))
          = is_eta_pattern (Term.app l (Term.bvar j))
      split
      case isTrue h_eq =>
        -- i = j and i ≠ 0, so j ≠ 0, both sides `false`.
        have hj : j ≠ 0 := h_eq ▸ h
        simp [is_eta_pattern, hj]
      case isFalse _ =>
        cases j with
        | zero =>
          unfold is_eta_pattern
          split
          . rename_i heq
            cases heq
            rw [count_bvar_openRec_fvar]
            omega
          . grind
        | succ _ => rfl
    | fvar _ => rfl
    | abs _ => rfl
    | app _ _ => rfl

lemma has_eta_redex_openRec (i : ℕ) (x : String) (M : Term String) :
    has_eta_redex (Term.openRec i (Term.fvar x) M) = has_eta_redex M := by
  induction M generalizing i with
  | bvar j =>
    show has_eta_redex (if i = j then Term.fvar x else Term.bvar j) = false
    split <;> rfl
  | fvar _ => rfl
  | abs t ih =>
    show (is_eta_pattern (Term.openRec (i + 1) (Term.fvar x) t)
          || has_eta_redex (Term.openRec (i + 1) (Term.fvar x) t))
        = (is_eta_pattern t || has_eta_redex t)
    rw [ih (i + 1), is_eta_pattern_openRec t (by omega)]
  | app l r ihl ihr =>
    show (has_eta_redex (Term.openRec i (Term.fvar x) l)
          || has_eta_redex (Term.openRec i (Term.fvar x) r))
        = (has_eta_redex l || has_eta_redex r)
    rw [ihl, ihr]

lemma has_eta_redex_of_full_eta {M N : Term String} (h : FullEta M N) :
    has_eta_redex M = true := by
  induction h with
  | base h_e =>
    cases h_e with
    | eta lc_A =>
      rename_i A
      show (is_eta_pattern (Term.app A (Term.bvar 0)) || has_eta_redex _) = true
      have : count_bvar 0 A = 0 := count_bvar_0_of_locally_closed lc_A 0
      simp [is_eta_pattern, this]
  | @appL Z M' _ _ _ ih =>
    show (has_eta_redex Z || has_eta_redex M') = true
    simp [ih]
  | @appR Z M' _ _ _ ih =>
    show (has_eta_redex M' || has_eta_redex Z) = true
    simp [ih]
  | @abs M' _ xs _ ih =>
    show (is_eta_pattern M' || has_eta_redex M') = true
    have ⟨x, hx⟩ := fresh_exists xs
    have h1 : has_eta_redex (M' ^ Term.fvar x) = true := ih x hx
    rw [show (M' ^ Term.fvar x) = Term.openRec 0 (Term.fvar x) M' from rfl,
        has_eta_redex_openRec] at h1
    simp [h1]


/--
A term has an η-redex (syntactically) and is locally closed iff a single
`FullEta` step applies to it. The `M.LC` hypothesis is necessary: without it
e.g. `M := abs (app (bvar 1) (bvar 0))` satisfies `has_eta_redex M = true`
(since `count_bvar 0 (bvar 1) = 0`) but no `FullEta` step applies because the
inner `bvar 1` is not locally closed.
-/
theorem has_eta_redex_equiv_full_eta {M : Term String} :
    has_eta_redex M ∧ M.LC ↔ ∃ N, FullEta M N := by
  constructor
  · rintro ⟨h_redex, h_lc⟩
    induction h_lc with
    | fvar _ => simp [has_eta_redex] at h_redex
    | @abs L e h_body ih =>
      have h_redex_e : (is_eta_pattern e || has_eta_redex e) = true := h_redex
      rcases (Bool.or_eq_true _ _).mp h_redex_e with h_pat | h_inner
      · -- e is itself an η-pattern: e = app A (bvar 0) with count_bvar 0 A = 0
        cases e with
        | bvar _ => simp [is_eta_pattern] at h_pat
        | fvar _ => simp [is_eta_pattern] at h_pat
        | abs _ => simp [is_eta_pattern] at h_pat
        | app A r =>
          cases r with
          | bvar k =>
            cases k with
            | zero =>
              have hcb : count_bvar 0 A = 0 := by
                simpa [is_eta_pattern] using h_pat
              have ⟨x, hx⟩ := fresh_exists L
              have h_lc_open : LC ((Term.app A (Term.bvar 0)) ^ Term.fvar x) :=
                h_body x hx
              have h_eq : (Term.app A (Term.bvar 0)) ^ Term.fvar x
                          = Term.app A (Term.fvar x) := by
                show Term.openRec 0 (Term.fvar x) (Term.app A (Term.bvar 0))
                    = Term.app A (Term.fvar x)
                show Term.app (Term.openRec 0 (Term.fvar x) A)
                              (Term.openRec 0 (Term.fvar x) (Term.bvar 0))
                    = Term.app A (Term.fvar x)
                rw [openRec_noop_of_count_bvar_zero 0 hcb]
                rfl
              rw [h_eq] at h_lc_open
              cases h_lc_open with
              | app lc_A _ => exact ⟨A, Xi.base (.eta lc_A)⟩
            | succ _ => simp [is_eta_pattern] at h_pat
          | fvar _ => simp [is_eta_pattern] at h_pat
          | abs _ => simp [is_eta_pattern] at h_pat
          | app _ _ => simp [is_eta_pattern] at h_pat
      · -- η-redex strictly inside e
        have ⟨x, hx⟩ := fresh_exists (L ∪ e.fv : Finset String)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨hxL, hxe⟩ := hx
        have h_redex_open : has_eta_redex (e ^ Term.fvar x) = true := by
          show has_eta_redex (Term.openRec 0 (Term.fvar x) e) = true
          rw [has_eta_redex_openRec]; exact h_inner
        have ⟨N, hN⟩ := ih x hxL h_redex_open
        have hclose : ((e ^ Term.fvar x) ^* x).abs ⭢ηᶠ (N ^* x).abs :=
          FullEta.step_abs_close hN
        rw [show (e ^ Term.fvar x) ^* x = e from (open_close_var x e hxe).symm] at hclose
        exact ⟨_, hclose⟩
    | @app l r lc_l lc_r ih_l ih_r =>
      have h_or : (has_eta_redex l || has_eta_redex r) = true := h_redex
      by_cases hl : has_eta_redex l = true
      · have ⟨N, hN⟩ := ih_l hl
        exact ⟨_, Xi.appR lc_r hN⟩
      · have hl_false : has_eta_redex l = false := by
          cases hh : has_eta_redex l
          · rfl
          · exact absurd hh hl
        rw [hl_false] at h_or
        have hr : has_eta_redex r = true := h_or
        have ⟨N, hN⟩ := ih_r hr
        exact ⟨_, Xi.appL lc_l hN⟩
  · rintro ⟨N, hN⟩
    exact ⟨has_eta_redex_of_full_eta hN, FullEta.step_lc_l hN⟩

theorem normal_fullEta_iff_no_eta_redex {N} : N.has_eta_redex = false \/ ¬ N.LC <-> Relation.Normal FullEta N := by grind [has_eta_redex_equiv_full_eta]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
