import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.EtaNormalForm
import FokkerChallenge.EnhancedCslib.BetaEtaNormalForm
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import Mathlib.Data.Finset.Lattice.Basic

/-!
This file is a sample template code.
Remove this file when more terms are proved.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


def Term_LA0L1 : Term String := .abs (.app (.bvar 0) (.abs (.bvar 1)))

theorem normal_LA0L1 : Relation.Normal FullBetaEta Term_LA0L1 := by
  rw [<- normal_fullBetaEta_iff_no_beta_eta_redex]
  decide

private theorem gen_term_reduces_to_normal {X} (h: Gen Term_LA0L1 X) : Relation.ReflTransGen FullBetaEta X Term_LA0L1 := by
  induction h with
  | base => grind
  | app _ _ ihm ihn =>  rename_i M N _ _
                        apply Relation.ReflTransGen.trans
                        . apply FullBetaEta.redex_app_l_cong
                          assumption
                          apply gen_lc
                          assumption
                          rw [← lcAt_iff_LC]
                          decide
                        . apply Relation.ReflTransGen.trans
                          . apply FullBetaEta.redex_app_r_cong
                            assumption
                            rw [← lcAt_iff_LC]
                            decide
                          . apply Relation.ReflTransGen.trans
                            . apply Relation.ReflTransGen.single
                              left
                              apply Xi.base
                              unfold Term_LA0L1
                              constructor
                              rw [← lcAt_iff_LC]
                              decide
                              rw [← lcAt_iff_LC]
                              decide
                            . unfold open' openRec openRec
                              simp
                              unfold openRec
                              simp
                              . apply Relation.ReflTransGen.trans
                                . apply Relation.ReflTransGen.single
                                  left
                                  constructor
                                  constructor
                                  rw [← lcAt_iff_LC]
                                  decide
                                  rw [← lcAt_iff_LC]
                                  decide
                                . unfold open' openRec openRec
                                  simp
                                  unfold openRec
                                  simp
                                  . apply Relation.ReflTransGen.trans
                                    . apply Relation.ReflTransGen.single
                                      left
                                      apply Xi.base
                                      constructor
                                      rw [← lcAt_iff_LC]
                                      decide
                                      rw [← lcAt_iff_LC]
                                      decide
                                    . unfold open' openRec
                                      tauto


theorem LA0L1_is_not_basis : not_basis Term_LA0L1 := by
  exists K
  refine ⟨?_, ?_, ?_⟩
  . rw [← lcAt_iff_LC]
    decide
  . grind [K, fv]
  . intros Y h1 h2
    apply gen_term_reduces_to_normal at h1
    apply Relation.ReflTransGen.to_eqvGen at h1
    apply Relation.ReflTransGen.to_eqvGen at h2
    have g := Relation.ChurchRosser.normal_eq (Relation.Confluent.toChurchRosser confluent_beta_eta) normal_K normal_LA0L1 (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h2) h1)
    cases g
