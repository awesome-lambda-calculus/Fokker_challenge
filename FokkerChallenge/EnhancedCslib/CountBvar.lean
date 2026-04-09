import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Mathlib.Data.Set.Card
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FvarSubset

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def count_bvar (k : Nat) : Term String → Nat
  | bvar n   => if n = k then 1 else 0
  | app M N => count_bvar k M + count_bvar k N
  | abs M   => count_bvar (k + 1) M
  | fvar _ => 0

@[simp, scoped grind =]
theorem openRec_noop_of_count_bvar_zero {M N} :
  (i: Nat) -> count_bvar i M = 0 -> openRec i N M = M := by
  induction M with
  | bvar M => intros i h
              unfold openRec
              split
              . subst M
                unfold count_bvar at h
                simp at h
              . simp
  | fvar M => intros i h
              unfold openRec
              rfl
  | app a b ha hb =>  intros i h
                      unfold count_bvar at h
                      have g: count_bvar i a = 0 := by omega
                      specialize ha _ g
                      have g: count_bvar i b = 0 := by omega
                      specialize hb _ g
                      unfold openRec
                      rw [ha, hb]
  | abs _ ih =>   intros i h
                  unfold count_bvar at h
                  unfold openRec
                  simp
                  apply ih
                  assumption


theorem count_bvar_openRec_fvar {x M} :
  (i j : Nat) → ¬ j = i → count_bvar j (M⟦i ↝ (fvar x)⟧) = count_bvar j M := by
  induction M with
  | fvar _ => simp [count_bvar, openRec]
  | abs M hM => intros i j h
                simp [count_bvar, openRec]
                apply hM
                omega
  | bvar M => intros i j _
              simp [count_bvar, openRec]
              split <;> split
              any_goals subst M
              any_goals subst j
              any_goals omega
              all_goals unfold count_bvar
              any_goals omega
              all_goals split
              all_goals tauto
  | app a b ha hb =>  intros i j h
                      simp [count_bvar, openRec]
                      specialize ha i j h
                      specialize hb i j h
                      rw [ha, hb]

theorem openRec_fv_union {M N} : (i: Nat) -> count_bvar i M > 0 -> (openRec i N M).fv = M.fv ∪ N.fv := by
  induction M with intros i h
  | bvar _ => unfold openRec
              split
              . subst i
                conv =>
                  right
                  left
                  unfold fv
                simp
              . unfold count_bvar at h
                split at h
                all_goals omega
  | fvar _ => unfold count_bvar at h
              omega
  | abs _ ih => unfold count_bvar at h
                unfold openRec
                conv =>
                  right
                  left
                  unfold fv
                conv =>
                  left
                  unfold fv
                apply ih
                assumption
  | app a b ha hb =>  unfold count_bvar at h
                      unfold openRec
                      conv =>
                        left
                        unfold fv
                      conv =>
                        right
                        left
                        unfold fv
                      have ga: count_bvar i a > 0 \/ count_bvar i a = 0 := by omega
                      have gb: count_bvar i b > 0 \/ count_bvar i b = 0 := by omega
                      cases ga <;> cases gb
                      any_goals omega
                      all_goals rename_i ga gb
                      any_goals try specialize ha _ ga
                      any_goals try specialize hb _ gb
                      . rw [ha]
                        rw [hb]
                        simp
                        apply congr
                        all_goals simp
                      . rw [ha]
                        apply (@openRec_noop_of_count_bvar_zero _ N) at gb
                        rw [gb]
                        simp
                        apply congr
                        simp
                        apply Finset.union_comm
                      . rw [hb]
                        apply (@openRec_noop_of_count_bvar_zero _ N) at ga
                        rw [ga]
                        simp_all

@[simp, scoped grind =]
theorem count_bvar_0_of_locally_closed {N} (hn: N.LC) : (j: Nat) -> count_bvar j N = 0 := by
  induction hn with
  | fvar x => unfold count_bvar
              simp
  | app _ _ hi hj =>  unfold count_bvar
                      intros j
                      specialize hi j
                      specialize hj j
                      omega
  | abs L e h ih => unfold count_bvar
                    intros j
                    have h4 : ∃ x : String, x ∉ L := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨x, hx⟩ := h4
                    specialize ih x hx (j+1)
                    unfold open' at ih
                    rw [count_bvar_openRec_fvar] at ih
                    assumption
                    omega

theorem count_bvar_preserved_under_open {M N} :
  (i j : Nat) → ¬ j = i -> N.LC → count_bvar j M = count_bvar j (M⟦i ↝ N⟧) := by
  induction M with
  | bvar M => intros i j
              simp [count_bvar, openRec]
              split
              any_goals subst M
              any_goals split
              all_goals intros
              any_goals subst i
              any_goals omega
              . unfold count_bvar
                simp
              . symm
                apply count_bvar_0_of_locally_closed (by assumption)
              . unfold count_bvar
                split <;> omega
  | fvar _ => simp [count_bvar, openRec]
  | abs M hM => intros i j h
                simp [count_bvar, openRec]
                apply hM
                omega
  | app a b ha hb =>
                intros i j _ h
                simp [count_bvar, openRec]
                rw [ha, hb]
                all_goals assumption

theorem count_bvar_lcat {M i j} (h: i <= j) : LcAt i M → count_bvar j M = 0 := by
  induction M generalizing i j with grind

@[simp, scoped grind =]
def count_bvar_all: Term String → Nat
| bvar _ => 1
| fvar _ => 0
| app t1 t2 => count_bvar_all t1 + count_bvar_all t2
| abs t => count_bvar_all t

theorem count_bvar_le_count_bvar_all {M i}: count_bvar i M ≤ count_bvar_all M := by
  induction M generalizing i with grind

theorem count_bvar_j_zero_after_openrec_i {i j M N} (hn: N.LC) : count_bvar i M = M.count_bvar_all ->
  count_bvar j (M⟦i ↝ N⟧) = 0 := by
  induction M generalizing i j with
  | fvar _ => grind
  | abs _ _ => grind
  | bvar _ => unfold count_bvar
              unfold count_bvar_all
              unfold openRec
              split
              . split <;> rename_i heq <;> split at heq <;> subst_vars <;> try grind
                . cases hn
                . cases hn
                  grind
                . intros _
                  rw [<- lcAt_iff_LC] at hn
                  simp at hn
                  refine count_bvar_lcat ?_ hn
                  omega
              . grind
  | app a b ha hb =>  intros h
                      unfold count_bvar at h
                      unfold count_bvar_all at h
                      have := @count_bvar_le_count_bvar_all a i
                      have := @count_bvar_le_count_bvar_all b i
                      grind

theorem openRec_bvar_all_eq_zero_of_count_bvar_eq_total {x M i}: count_bvar i M = M.count_bvar_all <-> count_bvar_all (openRec i (fvar x) M) = 0 := by
  induction M generalizing i with grind [count_bvar_le_count_bvar_all]

theorem beta_preserves_count_bvar_all_eq_0 : r_preserves (fun x => count_bvar_all x = 0) Beta := by
  intro M N h g
  grind [count_bvar_le_count_bvar_all]

theorem eta_preserves_count_bvar_all_eq_0 : r_preserves (fun x => count_bvar_all x = 0) Eta := by
  intro M N h g
  cases h
  simp at g

theorem xi_preserves_count_bvar_all_eq_0 {R: Term String → Term String → Prop} :
  r_preserves_fvar_subset (Xi R) ->
  r_preserves (fun x => count_bvar_all x = 0) R ->
  r_preserves (fun x => count_bvar_all x = 0) (Xi R) := by
  intro h9 h8 M N h
  induction h with
  | base _ => tauto
  | appL _ _ _ => grind
  | appR _ _ _ => grind
  | abs xs h ih =>  rename_i M N
                    simp
                    intros hm
                    have h2: count_bvar 0 M = 0 := by grind [count_bvar_le_count_bvar_all]
                    have h4 : ∃ x: String, x ∉ xs ∪ N.fv ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨y, h4⟩ := h4
                    specialize ih y (by grind)
                    specialize h y (by grind)
                    apply openRec_noop_of_count_bvar_zero at h2
                    pick_goal 2
                    exact (fvar y)
                    unfold open' at h ih
                    rw [h2] at h ih
                    specialize h9 _ _ h
                    simp at ih
                    specialize ih (by grind)
                    have g: count_bvar 0 N = 0 \/ count_bvar 0 N > 0 := by omega
                    cases g with
                    | inl g => grind
                    | inr g =>  apply openRec_fv_union at g
                                pick_goal 2
                                exact (fvar y)
                                grind
