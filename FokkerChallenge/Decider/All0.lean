import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.FvarSubset
import FokkerChallenge.FamousCombinator

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def all0: Term String -> Bool
  | Term.bvar n => n = 0
  | Term.fvar _ => true
  | Term.abs t => all0 t
  | Term.app t1 t2 => all0 t1 && all0 t2

theorem all0_openrec {M N}: (i: Nat) -> all0 N -> all0 M -> all0 (openRec i N M) := by
  induction M with grind [openRec, all0]

theorem all0_no_bvar_above_zero {M}: (i: Nat) -> i > 0 -> M.all0 -> count_bvar i M = 0 := by
  induction M with grind [count_bvar, all0]

theorem beta_preserves_all0: r_preserves all0 Beta := by
  intros M N hmn hnd
  cases hmn
  rename_i M N h lcn
  unfold all0 at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold all0 at g
  apply all0_openrec <;> assumption

theorem eta_preserves_all0: r_preserves all0 Eta := by
  intros M N hmn hnd
  cases hmn
  rename_i lcn
  unfold all0 at hnd
  unfold all0 at hnd
  simp at hnd
  tauto

def no_fvar_inside_abs : Term String -> Bool
  | Term.bvar _ => true
  | Term.fvar _ => true
  | Term.abs t => t.fv = ∅
  | Term.app t1 t2 => no_fvar_inside_abs t1 && no_fvar_inside_abs t2

theorem no_fvar_inside_abs_of_empty_fv {M: Term String}: M.fv = ∅ -> M.no_fvar_inside_abs := by
  induction M with
  | bvar _ => tauto
  | fvar _ => tauto
  | abs _ _ => grind [no_fvar_inside_abs]
  | app _ _ _ _ => grind [no_fvar_inside_abs]

theorem no_fvar_inside_abs_of_open_rev {M x} : (M ^ fvar x).no_fvar_inside_abs -> M.no_fvar_inside_abs := by
  induction M with
  | fvar _ => grind
  | bvar _ => grind [no_fvar_inside_abs]
  | app _ _ _ _ => grind [no_fvar_inside_abs]
  | abs M ih => unfold open' openRec
                unfold no_fvar_inside_abs
                simp
                intros h1
                have h := open_preserve_not_fvar 1 M (fvar x)
                cases h with grind

theorem no_fvar_inside_abs_of_open {M N}: M.all0 -> N.no_fvar_inside_abs -> M.no_fvar_inside_abs -> (M ^ N).no_fvar_inside_abs := by
  induction M with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ _ _ => grind [all0, no_fvar_inside_abs]
  | abs M _ =>  intros h1 _ h
                unfold open' openRec no_fvar_inside_abs
                unfold no_fvar_inside_abs at h
                unfold all0 at h1
                simp
                rw [openRec_noop_of_count_bvar_zero]
                . simp_all
                . apply all0_no_bvar_above_zero <;> omega

def r_preserves_no_fvar_inside_abs (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → all0 M -> no_fvar_inside_abs M → no_fvar_inside_abs N


theorem beta_preserves_no_fvar_inside_abs: r_preserves_no_fvar_inside_abs Beta := by
  intros M N hmn _ hnd
  cases hmn
  rename_i M N h lcn _
  unfold no_fvar_inside_abs at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold no_fvar_inside_abs at g
  rename_i h1 h2
  unfold all0 at h1
  simp at h1
  obtain ⟨h1, _⟩ := h1
  unfold all0 at h1
  apply no_fvar_inside_abs_of_open <;> try tauto
  apply no_fvar_inside_abs_of_empty_fv
  simp_all


theorem eta_preserves_no_fvar_inside_abs: r_preserves_no_fvar_inside_abs Eta := by
  intros M N hmn _ hnd
  cases hmn
  unfold no_fvar_inside_abs at hnd
  unfold fv at hnd
  conv at hnd =>
    left
    right
    left
    right
    unfold fv
  apply no_fvar_inside_abs_of_empty_fv
  simp_all


theorem all0_openrec_rev {x M}: (i: Nat) -> M⟦i ↝ fvar x⟧.all0 = true → M⟦i ↝ fvar x⟧.fv = ∅ → M.all0 := by
  induction M with
  | fvar _ => grind
  | bvar _ => unfold openRec
              intros i h1 h2
              split at h1 <;> split at h2 <;> try grind
              simp [fv] at h2
  | app _ _ ih1 ih2 =>  unfold openRec all0
                        intros _  _ h
                        unfold fv at h
                        simp_all
                        constructor
                        . apply ih1 <;> tauto
                        . apply ih2 <;> tauto
  | abs h ih => unfold openRec
                unfold all0
                intros i h1 h2
                unfold fv at h2
                apply ih <;> assumption

theorem all0_of_open_all0 {M x} : (M ^ (fvar x)).all0 -> (M ^ (fvar x)).no_fvar_inside_abs -> M.all0 := by
  induction M with
  | bvar _ => grind [open', openRec, all0]
  | fvar _ => grind [open', openRec, all0]
  | app _ _ _ _ =>  unfold open' openRec all0 no_fvar_inside_abs
                    intros _ h
                    grind
  | abs M ih => unfold open' openRec all0 no_fvar_inside_abs
                simp
                intros _ _
                apply all0_openrec_rev <;> tauto


def all0_no_fvar_inside_abs (M : Term String) : Bool := M.all0 && M.no_fvar_inside_abs

theorem all0_no_fvar_inside_abs_of_open_rev {M x} :
  all0_no_fvar_inside_abs (M ^ (fvar x)) -> all0_no_fvar_inside_abs M := by
  unfold all0_no_fvar_inside_abs
  simp
  intros h1 h2
  constructor
  . apply all0_of_open_all0 <;> assumption
  . apply no_fvar_inside_abs_of_open_rev h2

theorem all0_no_fvar_inside_abs_of_open {M x} :
  all0_no_fvar_inside_abs M -> all0_no_fvar_inside_abs (M ^ (fvar x)) := by
  unfold all0_no_fvar_inside_abs
  simp
  intros h1 h2
  constructor
  . apply all0_openrec <;> try assumption
    unfold all0
    tauto
  . apply no_fvar_inside_abs_of_open <;> try assumption
    unfold no_fvar_inside_abs
    tauto

theorem all0_no_fvar_inside_abs_abs_rev {M} :
  all0_no_fvar_inside_abs M.abs -> all0_no_fvar_inside_abs M := by
  unfold all0_no_fvar_inside_abs
  intros h
  unfold no_fvar_inside_abs at h
  unfold all0 at h
  simp_all
  obtain ⟨_, h⟩ := h
  apply no_fvar_inside_abs_of_empty_fv at h
  tauto

theorem xi_preserves_all0_no_fvar_inside_abs {R: Term String → Term String → Prop} :
  r_preserves_fvar_subset (Xi R) ->
  r_preserves all0_no_fvar_inside_abs R →
  r_preserves all0_no_fvar_inside_abs (Xi R) := by
  intros hsubset hR M N hxi hnd
  induction hxi with
  | base _ => tauto
  | appL _ _ _ => grind [all0_no_fvar_inside_abs, no_fvar_inside_abs, all0]
  | appR _ _ _ => grind [all0_no_fvar_inside_abs, no_fvar_inside_abs, all0]
  | abs xs h ih =>  rename_i M N
                    have h4 : ∃ x : String, x ∉ xs := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨x, hx⟩ := h4
                    have g := all0_no_fvar_inside_abs_abs_rev hnd
                    apply all0_no_fvar_inside_abs_of_open at g
                    apply ih at g
                    apply all0_no_fvar_inside_abs_of_open_rev at g
                    unfold all0_no_fvar_inside_abs at hnd
                    unfold no_fvar_inside_abs at hnd
                    unfold all0_no_fvar_inside_abs
                    unfold no_fvar_inside_abs
                    simp_all
                    obtain ⟨_, hnd⟩ := hnd
                    have hx: Xi R M.abs N.abs := by apply Xi.abs _ h
                    specialize hsubset _ _ hx
                    unfold fv at hsubset
                    rw [hnd] at hsubset
                    simp_all
                    unfold all0
                    grind [all0_no_fvar_inside_abs]
                    assumption


theorem beta_preserves_all0_no_fvar_inside_abs: r_preserves all0_no_fvar_inside_abs Beta := by
  intros M N h pm
  unfold all0_no_fvar_inside_abs
  simp
  constructor
  . apply beta_preserves_all0
    any_goals assumption
    grind [all0_no_fvar_inside_abs, all0]
  . apply beta_preserves_no_fvar_inside_abs
    any_goals assumption
    grind [all0_no_fvar_inside_abs, all0]
    grind [all0_no_fvar_inside_abs, all0]

theorem eta_preserves_all0_no_fvar_inside_abs: r_preserves all0_no_fvar_inside_abs Eta := by
  intros M N h pm
  unfold all0_no_fvar_inside_abs
  simp
  constructor
  . apply eta_preserves_all0
    any_goals assumption
    grind [all0_no_fvar_inside_abs, all0]
  . apply eta_preserves_no_fvar_inside_abs
    any_goals assumption
    grind [all0_no_fvar_inside_abs, all0]
    grind [all0_no_fvar_inside_abs, all0]

theorem fullbeta_preserves_all0_no_fvar_inside_abs {M N} :
  FullBeta M N → all0_no_fvar_inside_abs M → all0_no_fvar_inside_abs N := by
  apply xi_preserves_all0_no_fvar_inside_abs beta_preserves_fvar_subset beta_preserves_all0_no_fvar_inside_abs

theorem fullbetastar_preserves_all0_no_fvar_inside_abs {M N} :
  Relation.ReflTransGen FullBeta M N → all0_no_fvar_inside_abs M → all0_no_fvar_inside_abs N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fullbeta_preserves_all0_no_fvar_inside_abs <;> assumption

theorem fulleta_preserves_all0_no_fvar_inside_abs {M N} :
  FullEta M N → all0_no_fvar_inside_abs M → all0_no_fvar_inside_abs N := by
  apply xi_preserves_all0_no_fvar_inside_abs eta_preserves_fvar_subset eta_preserves_all0_no_fvar_inside_abs

theorem fulletastar_preserves_all0_no_fvar_inside_abs {M N} :
  Relation.ReflTransGen FullEta M N → all0_no_fvar_inside_abs M → all0_no_fvar_inside_abs N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fulleta_preserves_all0_no_fvar_inside_abs <;> assumption

theorem fullBetaEtastar_preserves_all0_no_fvar_inside_abs {M N} :
  Relation.ReflTransGen FullBetaEta M N → all0_no_fvar_inside_abs M → all0_no_fvar_inside_abs N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        cases hstar with
                        | inl h =>  apply fullbeta_preserves_all0_no_fvar_inside_abs at h
                                    apply h ih
                        | inr h =>  apply fulleta_preserves_all0_no_fvar_inside_abs at h
                                    apply h ih


theorem Gen_all0_no_fvar_inside_abs {Y M : Term String} :
  Gen Y M → all0_no_fvar_inside_abs Y -> all0_no_fvar_inside_abs M := by
  intro h
  induction h with
  | base => simp
  | app hM hN ihM ihN =>  intro h
                          specialize ihM h
                          specialize ihN h
                          grind [all0_no_fvar_inside_abs, all0, no_fvar_inside_abs]

theorem all0_no_fvar_inside_abs_not_reaches_S {X} (h: X.all0_no_fvar_inside_abs) :
  not_basis X := by
  exists S
  refine ⟨?_, ?_, ?_⟩
  . rw [← lcAt_iff_LC]
    decide
  . grind [S]
  . intros Y hgen hred
    apply Gen_all0_no_fvar_inside_abs at hgen
    apply hgen at h
    have := fullBetaEtastar_preserves_all0_no_fvar_inside_abs hred h
    grind [S, all0_no_fvar_inside_abs, all0]
