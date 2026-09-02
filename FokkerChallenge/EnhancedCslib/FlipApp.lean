import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import FokkerChallenge.EnhancedCslib.EtaSpineOpenFv
import FokkerChallenge.EnhancedCslib.AbsN

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

lemma step_flip_app_l {R} {M M'} {Ns : List (Term String)} (steps : Xi R M M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    Xi R (Ns.foldl (flip app) M) (Ns.foldl (flip app) M') := by
  induction Ns generalizing M M' with
  | nil => grind
  | cons head tail ih =>  simp [flip]
                          apply ih <;> grind

lemma steps_flip_app_l {R} {M M'} {Ns : List (Term String)} (steps : Relation.ReflTransGen (Xi R) M M')
    (lc_Ns : ∀ N ∈ Ns, LC N) :
    Relation.ReflTransGen (Xi R) (Ns.foldl (flip app) M) (Ns.foldl (flip app) M') := by
  induction steps <;> grind [step_flip_app_l]

lemma flip_app_fv {M} {Ns : List (Term String)}:
  (Ns.foldl (flip app) M).fv = (Ns.map fv).foldl Union.union M.fv := by
    induction Ns generalizing M with
    | nil => grind
    | cons head tail ih =>
      simp [flip]
      specialize @ih (head.app M)
      grind

lemma app_lcat {M i} {l : List (Term String)}:
  LcAt i (l.foldl app M) <-> LcAt i M /\ ∀ x ∈ l, LcAt i x := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  simp
                          specialize @ih (M.app head)
                          rw [ih]
                          constructor
                          . intros h
                            cases h with | intro h _ =>
                            unfold LcAt at h
                            simp at h
                            cases h
                            grind
                          . grind

lemma flip_app_lc {M} {l : List (Term String)}:
  (l.foldl (flip app) M).LC <-> M.LC /\ ∀ x ∈ l, x.LC := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  simp [flip]
                          specialize @ih (head.app M)
                          rw [ih]
                          constructor
                          . intros h
                            cases h with | intro h _ =>
                            cases h
                            grind
                          . grind

lemma flip_app_eq {x y} {l l': List (Term String)}:
  l.foldl (flip app) (fvar x) = l'.foldl (flip app) (fvar y) ->
  x = y := by
  induction l using List.reverseRecOn generalizing l' with
  | nil => cases l' using List.reverseRecOn <;> simp [flip]
  | append_singleton l a _ => cases l' using List.reverseRecOn with
    | nil => simp [flip]
    | append_singleton l a _ => simp [flip]; grind

lemma app_eq {x y} {l l': List (Term String)}:
  l.foldl app (fvar x) = l'.foldl app (fvar y) ->
  x = y := by
  induction l using List.reverseRecOn generalizing l' with
  | nil => cases l' using List.reverseRecOn <;> simp
  | append_singleton l a _ => cases l' using List.reverseRecOn with
    | nil => simp
    | append_singleton l a _ => simp; grind

/-
lemma beta_step_preserve_fvar_apps {x M} {l: List (Term String)}
  (step : l.foldl app (fvar x) ⭢βᶠ M)  :
  ∃ l': List _, M = l'.foldl app (fvar x) := by
  induction l using List.reverseRecOn generalizing M with
  | nil =>  cases step with | base h => cases h
  | append_singleton l a ih =>
  simp at step
  cases step with
  | base h => exfalso
              generalize heq : (List.foldl app (fvar x) l) = M
              rw [heq] at h
              cases h
              cases l using List.reverseRecOn <;> grind
  | appL h ih =>
    rename_i N
    use (l ++ [N])
    grind
  | appR h g => obtain ⟨l', ih⟩ := ih g
                use (l' ++ [a])
                grind
-/

lemma MultiApp_exists (P : Term String -> Prop) (Ns : List (Term String))
  (h_lc : ∀ M ∈ Ns, LC M)
  (h : ∀ t ∈ Ns, ∃ t', t ↠βᶠ t' /\ P t') :
  ∃ Ns', Ns ↠lβᶠ Ns' /\ ∀ t ∈ Ns', P t := by
  induction Ns with
  | nil =>  use []
            grind
  | cons head tail ih =>
  obtain ⟨Ns', h1, _⟩ := ih (by grind) (by grind)
  simp at h
  obtain ⟨⟨t', h, _⟩, _⟩ := h
  exact ⟨t' :: Ns', .trans (listFullBeta_cons_r h1 (by grind)) (listFullBeta_cons_l h (multiApp_steps_lc h1 (by grind))), by grind⟩

lemma multiapp_openrec {M N i} {l : List (Term String)}:
   (l.foldl app M)⟦i ↝ N⟧ = (l.map (openRec i N)).foldl app (M⟦i ↝ N⟧) := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  obtain h := @ih (M.app head)
                          grind

/-
theorem iterate_app {M M' Z : Term String} (n) (h: M ↠βᶠ M') (z_lc :Z.LC):
  (fun a => a.app Z)^[n] M ↠βᶠ (fun a => a.app Z)^[n] M' := by
  induction n generalizing M M' with simp
  | zero => grind
  | succ n ih => exact ih (FullBeta.redex_app_l_cong h z_lc)

theorem recursive_app_lc {M y : Term String} {i} (hm : M.LC) (hy : y.LC) : ((fun a => a.app y)^[i] M).LC := by
  induction i generalizing M with (simp; grind)
-/

theorem redex_n_apps_n_abs_of_apps (y : String) (M n)
  (h_lc : (abs^[n] M).LC) :
  (List.replicate n (fvar y)).foldl app (abs^[n] M) ↠βᶠ (openDown n (fvar y) M) := by
  induction n generalizing M with
  | zero => simp; grind
  | succ n ih =>
  nth_rewrite 1 [add_comm]
  rw [List.replicate_succ, Function.iterate_add abs]
  simp
  refine .head (step_multiApp_l ((.base (.beta ?_ (by grind)))) (by grind)) ?_
  . rw [add_comm, Function.iterate_add abs] at h_lc
    simp at h_lc
    grind
  . unfold open'
    rw [absn_openrec]
    refine .trans (ih _ ?_) .refl
    rw [<- lcAt_iff_LC, absn_lcat] at *
    grind

theorem multiapp_subst {M N : Term String} {l} {z : String} :
  (List.foldl (flip app) M l)[z := N] =
  (List.foldl (flip app) M[z := N] (l.map (fun x => x[z := N]))) := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  simp [flip]
                          grind
