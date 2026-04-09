import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Mathlib.Data.Set.Card
import FokkerChallenge.EnhancedCslib.CountBvar

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def count_fvar (s : String) : Term String → Nat
  | bvar _ => 0
  | app M N => count_fvar s M + count_fvar s N
  | abs M   => count_fvar s M
  | fvar x => if x = s then 1 else 0

theorem count_fvar_eq_zero_of_not_in_fv {M x} :
  x ∉ M.fv <-> count_fvar x M = 0 := by
  induction M with
  | bvar _ => tauto
  | fvar _ => unfold count_fvar fv
              split <;> simp <;> tauto
  | abs _ _ =>  unfold count_fvar fv
                tauto
  | app _ _ _ _ =>  unfold count_fvar fv
                    simp
                    tauto

theorem count_fvar_openRec_distrib {M N x} :
(i: Nat) -> count_fvar x (openRec i N M) = (count_bvar i M) * (count_fvar x N) + count_fvar x M := by
  induction M with
  | bvar _ => intros i
              unfold openRec
              unfold count_bvar
              split <;> split
              any_goals tauto
              unfold count_fvar
              split
              all_goals omega
  | fvar _ => intros i
              unfold openRec
              unfold count_bvar
              unfold count_fvar
              split
              all_goals omega
  | app a b ha hb =>  intros i
                      unfold openRec
                      simp only [count_bvar]
                      conv =>
                        lhs
                        unfold count_fvar
                      conv =>
                        rhs
                        rhs
                        unfold count_fvar
                      rw [ha, hb]
                      grind
  | abs _ ih => intros i
                unfold openRec
                unfold count_bvar
                conv =>
                  lhs
                  unfold count_fvar
                conv =>
                  rhs
                  rhs
                  unfold count_fvar
                apply ih (i + 1)
