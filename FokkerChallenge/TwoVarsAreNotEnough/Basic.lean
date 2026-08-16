import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FlipApp
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import FokkerChallenge.EnhancedCslib.HeadNFSpineEta
import FokkerChallenge.EnhancedCslib.ReflTransGenWithSteps
import FokkerChallenge.EnhancedCslib.HeadRed
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind =]
def two_vars_are_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => false
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | Term.app t1 t2 => two_vars_are_enough t1 && two_vars_are_enough t2
  | _ => false

@[scoped grind]
theorem two_vars_are_enough_lc {t} (g : two_vars_are_enough t) : t.abs.abs.LC := by
  rw [<- lcAt_iff_LC]
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n ih => cases t with
  | fvar => grind
  | bvar => grind
  | app => grind
  | abs t => cases t with
    | bvar => grind
    | fvar => grind
    | app => grind
    | abs t =>  specialize @ih _ ?_ t ?_ rfl
                grind
                grind
                unfold LcAt
                unfold LcAt
                refine lcAt_le _ _ _ (by omega) ih

theorem two_vars_are_enough_depth {M N1 N2: Term String}
  (hm : M.two_vars_are_enough)
  (h1 : N1.LC) (h2 : N2.LC) :
  M⟦1 ↝ N1⟧⟦0 ↝ N2⟧.depth <= M.depth.max (N1.depth.max N2.depth) := by
  induction h : M.fokker_size using Nat.strong_induction_on generalizing M with | h n ih =>
  cases M with
  | fvar _ => grind
  | bvar _ => grind
  | abs M => cases M <;> grind
  | app a b =>
      have := @ih _ (by grind) a (by grind) rfl
      have := @ih _ (by grind) b (by grind) rfl
      rw [openRec_app, openRec_app]
      grind

@[scoped grind =]
theorem two_vars_are_enough_fv {t} (h: two_vars_are_enough t) : t.fv = ∅ := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => induction t with grind


/-
theorem two_vars_are_enough_openRec {i x t} (g : two_vars_are_enough t) :
  two_vars_are_enough (t⟦i ↝ fvar x⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind
-/

@[scoped grind =]
def abs_two_vars_are_enough: Term String → Bool
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | _ => false

theorem abs_two_vars_are_enough_weak {t} (h: abs_two_vars_are_enough t) :
  t.two_vars_are_enough := by
  unfold abs_two_vars_are_enough at h
  grind

@[scoped grind =]
theorem abs_two_vars_are_enough_fv {t} (h: abs_two_vars_are_enough t) : t.fv = ∅ :=
  two_vars_are_enough_fv (abs_two_vars_are_enough_weak h)

@[scoped grind]
theorem abs_two_vars_are_enough_lc {t} (h: abs_two_vars_are_enough t) : t.LC := by
  unfold abs_two_vars_are_enough at h
  split at h <;> grind


/-
@[scoped grind]
inductive GenFinset (atoms: Finset (Term String)) : Term String → Prop where
  | base : ∀ atom ∈ atoms, GenFinset atoms atom
  | app {M N}  : GenFinset atoms M → GenFinset atoms N → GenFinset atoms (app M N)

@[scoped grind]
theorem genFinset_lc (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.LC) {t} (ht: GenFinset fs t) : t.LC := by
  induction ht with grind

@[scoped grind]
theorem genFinset_fv (fs : Finset (Term String))
  (hfv : ∀ t ∈ fs, t.fv = ∅)
   {t} (ht: GenFinset fs t) : t.fv = ∅ := by
  induction ht with grind

theorem gen_abs_2_vars_are_enough {atom M : Term String} (h : Gen atom M) (g : atom.abs_two_vars_are_enough):
  GenFinset atom.subterms M := by
  induction h with
  | base => apply GenFinset.base
            unfold abs_two_vars_are_enough at g
            grind
  | app _ _ _ _ => grind


theorem genFinset_open2 (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.LC)
  {x : Term String}
  (hx : x.two_vars_are_enough)
  (hsubset : x.subterms ⊆ fs)
  (hfv : x.fv = ∅) :
  ∀ y z, GenFinset fs y -> GenFinset fs z -> GenFinset fs (x⟦1 ↝ y⟧⟦0 ↝ z⟧) := by
  induction h : x.fokker_size using Nat.strong_induction_on generalizing x with
  | h n ih => cases x with intros y z hy hz
  | bvar n => clear ih
              rw [openRec_bvar]
              split
              . rw [open_lc] <;> grind
              . grind
  | fvar _ => simp at hfv
  | app _ _ =>  rw [openRec_app]
                apply GenFinset.app <;> apply ih
                any_goals rfl
                all_goals grind
  | abs t => cases t with
    | bvar _ => clear ih; grind
    | fvar _ => clear ih; grind
    | app _ _ => clear ih; grind
    | abs t =>  rw [open_lc, open_lc]
                · apply GenFinset.base
                  grind
                · grind
                · rw [open_lc] <;> grind

theorem genFinset_list (fs : Finset (Term String))
  {f} {l : List (Term String)}
  (ht: GenFinset fs f)
  (hl : ∀ x ∈ l, GenFinset fs x) : GenFinset fs (l.foldl Term.app f) := by
  induction l generalizing f with grind
-/


axiom BetaAt.step_fv {M N: Term String} {i} : BetaAt i M N -> N.fv ⊆ M.fv


@[scoped grind]
def fvar_or_combinator (a: Term String) : Prop :=  a.IsFvar \/ a.abs_two_vars_are_enough

theorem two_vars_are_enough_openRec {t N1 N0}
  (g : two_vars_are_enough t)
  (h1: ClosedUnderApp fvar_or_combinator N1)
  (h2: ClosedUnderApp fvar_or_combinator N0) :
  ClosedUnderApp fvar_or_combinator (t⟦1 ↝ N1⟧⟦0 ↝ N0⟧) := by
  induction t with
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t <;> grind
  | bvar a => unfold two_vars_are_enough at g
              have h : a = 0 \/ a = 1 := by grind
              cases h <;> subst_vars
              . grind
              . simp [openRec]
                rw [open_lc] <;> grind

/-
theorem recursive_app_fvar_fvar_or_combinator {i y M}
  (hm : ClosedUnderApp fvar_or_combinator M):
  ClosedUnderApp fvar_or_combinator ((fun a => a.app (fvar y))^[i] (M)) := by
  induction i generalizing M with (simp; grind)
-/


@[scoped grind]
def contain_x (M : Term String) := ∀ Y, M ↠βηᶠ Y -> "x" ∈ Y.fv

theorem beta_eta_nf_contain_x {M N : Term String}
  (steps : M ↠βηᶠ N)
  (h : Relation.Normal FullBetaEta N)
  (hn : "x" ∈ N.fv) : contain_x M  := by
    intros t ht
    obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta ht steps
    have := Relation.Normal.reflTransGen_eq h hz2
    subst_vars
    apply FullBetaEta.steps_fv at hz1
    apply hz1
    grind

theorem beta_eta_spline_contain_x {Ns : List _} {M : Term String}
  (steps : M ↠βηᶠ (Ns.foldl app (fvar "x"))) : contain_x M  := by
    intros t ht
    obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta ht steps
    obtain ⟨l, _, _⟩ := beta_eta_steps_preserve_fvar_apps hz2
    subst_vars
    apply FullBetaEta.steps_fv at hz1
    apply hz1
    rw [multiapp_fv]
    grind [union_foldl]


/-
theorem HeadReduction2.head_nf_exists {M : Term String} {x : String} {l : List (Term String)}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : Relation.ReflTransGen Leftmost M (l.foldl app (fvar x))) :
  ∃ l' : List _, Relation.ReflTransGen HeadReduction2 M (l'.foldl app (fvar x)) := by
  generalize heq : List.foldl app (fvar x) l = N
  rw [heq] at h
  induction h using Relation.ReflTransGen.head_induction_on₂ generalizing l with
  | refl => grind
  | single h => subst_vars
                exfalso
                sorry
  | head₂ h₁ h₂ h ih => induction h₁ using Leftmost.induction_rule with
    | h_outer M N hm hn => cases hm with
      | base hm => cases hm <;> grind
      | app hm _ => cases hm with | base hm => cases hm with
        | inl hm => grind
        | inr hm => unfold abs_two_vars_are_enough at hm
                    split at hm <;> try grind
                    rename_i heq
                    cases heq
                    exfalso
                    sorry
    | h_appL h hi _ => sorry
    | h_appR h hi g _ => sorry
    | h_abs M M' xs h _ => sorry
-/



  /-
  induction hm generalizing l x with
  | app _ _ _ _ => sorry
  | base hm => cases hm with
    | inl hm => use []
                simp
                cases hm
                generalize heq : List.foldl app (fvar x) l = N
                rw [heq] at h
                rcases Relation.ReflTransGen.cases_head h with h|⟨_, g, h2⟩
                . rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
                  . grind
                  . subst_vars
                    rw [List.foldl_concat] at heq
                    cases heq
                . generalize hi : 0 = i
                  unfold Leftmost at g
                  rw [hi] at g
                  cases g
    | inr hm =>
    unfold abs_two_vars_are_enough at hm
    split at hm <;> try grind
    have g :=  Leftmost.steps_isAbs_r h (by grind)
    rcases (List.eq_nil_or_concat' l) with _| ⟨l, b, h⟩
    . grind
    . subst_vars
      rw [List.foldl_concat] at g
      cases g
  -/

/-
@[scoped grind]
def P (fs : Finset (Term String)) (t : Term String) : Prop :=
  let (h, args) := spine t
  h ∈ fs /\ ∀ x ∈ args, GenFinset fs x


@[scoped grind]
theorem genfinset_P {fs : Finset (Term String)}
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  {t: Term String} :
  GenFinset fs t <-> P fs t := by
  constructor
  . intros h
    induction h with
    | base atom _ =>  unfold P
                      split
                      rename_i h _ _ _ heq
                      unfold spine at heq
                      split at heq <;> grind
    | app _ _ _ _ => grind
  . intros h
    unfold P at h
    split at h
    rename_i l _
    induction t generalizing l with
    | bvar _ => grind only [spine, GenFinset.base]
    | fvar _ => grind only [spine, GenFinset.base]
    | abs _ _ => grind only [spine, GenFinset.base]
    | app _ _ _ _ => grind only [spine, GenFinset.app, = List.mem_append, = List.mem_cons]


@[scoped grind]
theorem P_fv(fs : Finset (Term String))
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
   {t} (ht: P fs t) : t.fv = ∅ := by
  apply genFinset_fv _ hfv
  rw [genfinset_P]
  grind
  grind


theorem closedUnderApp_reduce_to_head_apps {M n}
  (hdepth : M.depth = n)
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : M ↠βᶠ H n) : False:= by
  induction n using Nat.strong_induction_on generalizing M with | h n ih =>
  cases n with
  | zero => cases Relation.ReflTransGen.cases_head h with
    | inl h => grind
    | inr h =>  obtain ⟨N, h, _⟩ := h
                apply FullBeta.depth0 h hdepth
  | succ n =>
  have g := Relation.ReflTransGen.trans (FullBeta.redex_app_l_cong (FullBeta.redex_app_l_cong h (LC.fvar "x")) (LC.fvar "y")) H_succ_reduce
  -- have := closedUnderApp_unroll (by grind) hm
  sorry
-/


/-

theorem size_dichotomy (t : Term String) :
    (∀ t', t ↠ℓℓ t' → t'.spine.2.length ≥ 2) ∨
    (∃ t', t ↠ℓℓ t' ∧ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1)) := by
  by_cases h : ∃ t', t ↠ℓℓ t' ∧ t'.spine.2.length ≤ 1
  · right
    obtain ⟨t', hstep, hsize⟩ := h
    exact ⟨t', hstep, by omega⟩
  · left
    intro t' hstep
    by_contra hcon
    exact h ⟨t', hstep, by omega⟩

lemma step_lc_r {M M' : Term String} (redex : M ⭢ℓℓ M') : LC M -> LC M' := by
  cases redex
  grind

@[scoped grind]
lemma steps_lc_r {M M' : Term String} (redex : M ↠ℓℓ  M') : LC M -> LC M' := by
  induction redex with grind

@[scoped grind]
theorem leftmostMulti_to_multi {M N} (h : M ↠ℓℓ N) : M ↠βᶠ N := by
  induction h with
  | refl => grind
  | tail h1 h2 h3 =>  cases h2 with


theorem leftmost2_preserves_P_l {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (step : t ⭢ℓℓ t')
  (h5 : P fs t) :
  P fs t' := by
  cases step with | base h4 h7 =>
  rename_i M1 M2 M3 N
  have h6 := spine_def_2 ((M1.app M2).app M3)
  generalize hl: ((M1.app M2).app M3).spine.2 = l
  rw [hl] at h6
  rw [<- h6] at h4
  cases l <;> try grind
  rename_i a l
  cases l <;> try grind
  rename_i b l
  have h7 := h2 ((M1.app M2).app M3).spine.1 (by grind)
  unfold abs_two_vars_are_enough at h7
  split at h7 <;> try grind
  rename_i f heq
  rw [heq] at h4
  have : GenFinset fs a := by grind
  have : GenFinset fs b := by grind
  have h8 := leftmost_multiapp f.abs a (b::l) (by grind) (by grind)
  have := BetaAt.unique h8 h4
  subst N
  have h8 := leftmost_multiapp (f⟦1 ↝ a⟧) b l (by grind) (by grind)
  have := BetaAt.unique h8 h7
  rw [<- genfinset_P]
  subst t'
  apply genFinset_list
  apply genFinset_open2
  all_goals grind


theorem step_leftmost2_preserves_P_r {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (step : t ⭢ℓℓ t')
  (pt: P fs t):
  P fs t' := by
  cases t with
  | bvar _ => grind
  | fvar _ => grind
  | abs _ =>  cases step
  | app M _ => cases M with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ =>  apply leftmost2_preserves_P_l
                  any_goals grind
                  · exact step
                  · grind
    | abs _ =>  cases pt with | intro left right =>
                specialize h2 _ left
                unfold abs_two_vars_are_enough at h2
                split at h2 <;> try grind
                rename_i heq
                rw [heq] at step
                cases step

theorem steps_leftmost2_preserves_P_r {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (steps : t ↠ℓℓ t')
  (pt: P fs t):
  P fs t' := by
  induction steps with grind [leftmost2_preserves_P_l]

theorem leftmost_rtc_cases {M N}
  (h : ∀ t', M ↠ℓℓ t' → t'.spine.2.length ≥ 2)
  (hmn : M ↠ℓ N) : M ↠ℓℓ N \/ ∃ Q, M ↠ℓℓ Q /\ Q ⭢ℓ N := by
  induction hmn with
  | refl => grind
  | tail _ _ ih => cases ih with
  | inl => grind
  | inr ih => left
              obtain ⟨Q, hmq, hqb⟩ := ih
              refine .tail (by assumption) ?_
              specialize h _ hmq
              have h3 := spine_def_2 Q
              generalize hq : Q.spine.2 = l
              cases (List.eq_nil_or_concat' l) <;> try grind
              rename_i heq
              obtain ⟨L, b, _⟩ := heq
              subst l
              rename_i heq
              rw [heq] at h3
              rw [List.foldl_concat] at h3
              cases (List.eq_nil_or_concat' L) <;> try grind
              rename_i heq
              obtain ⟨l, b, _⟩ := heq
              subst L
              rw [List.foldl_concat] at h3
              rw [<- h3]
              rw [<- h3] at hqb
              constructor <;> assumption

theorem leftmost2_neither_abs_nor_beta_normal {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  (t : Term String)
  (ht : P fs t)
  (h : ∀ t', t ↠ℓℓ t' → t'.spine.2.length ≥ 2) :
  ∀ t'', t ↠ℓ t'' → ¬ t''.IsAbs /\ ¬ t''.BetaNormal := by
  intros t'' g
  cases (leftmost_rtc_cases h g) with
  | inl g =>  specialize h _ g
              have h3 := spine_def_2 t''
              generalize heq: t''.spine.2 = l
              rw [heq] at h3 h
              constructor
              . grind [IsAbs, BetaNormal]
              . cases l <;> try grind
                rename_i l
                cases l <;> try grind
                have : GenFinset fs t := by grind
                have : t.LC := by grind
                apply normal_app
                · grind
                · grind
                · apply Leftmost2.steps_fv at g
                  grind
  | inr g =>  obtain ⟨t', g, g2⟩ := g
              have : t.fv = ∅ := by grind
              have : t'.fv = ∅ := by apply Leftmost2.steps_fv at g; grind
              have : t''.fv = ∅ := by apply BetaAt.step_fv at g2; grind
              specialize h _ g
              have h3 := spine_def_2 t'
              generalize heq: t'.spine.2 = l
              rw [heq] at h h3
              cases l <;> try grind
              rename_i a l
              cases l <;> try grind
              rename_i b l
              rw [<- h3] at g2
              have : GenFinset fs t := by grind
              have : P fs t := by grind
              have : t.LC := by grind
              have : t'.LC := by grind
              have : t''.LC := by grind [BetaAt.lc_r]
              have : t.spine.1 ∈ fs := by grind
              have := steps_leftmost2_preserves_P_r hidempotent h2 hfv g (by grind)
              have h3 := h2 t'.spine.1 (by grind)
              unfold abs_two_vars_are_enough at h3
              split at h3 <;> try grind
              rename_i heq
              rw [heq] at g2
              rename_i t
              have : GenFinset fs a := by grind
              have h4 := leftmost_multiapp t.abs a (b :: l) (by grind) (by grind)
              have heq := BetaAt.unique h4 g2
              constructor
              . induction l using List.reverseRecOn with grind [IsAbs, BetaNormal]
              . induction l using List.reverseRecOn with
                | nil =>  intro hnormal
                          unfold List.foldl at heq
                          unfold List.foldl at heq
                          unfold open' openRec at heq
                          subst t''
                          apply BetaNormal.app_inv at hnormal
                          grind
                | append_singleton l a _ =>
                          unfold List.foldl at heq
                          rw [List.foldl_concat] at heq
                          apply normal_app <;> grind


theorem P_progress_to_simple_spine_or_stuck_nonabs {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t} (ht: P fs t)
  : (∃ t', t ↠ℓ t' /\ P fs t' /\ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1)) \/ (∀ t', t ↠ℓ t' -> ¬ IsAbs t' /\ ¬ BetaNormal t') := by
  cases size_dichotomy t with
  | inl h => right
             apply leftmost2_neither_abs_nor_beta_normal hidempotent h2 hfv _ ht h
  | inr h =>  left
              obtain ⟨t', h, _⟩ := h
              refine ⟨t', by grind, steps_leftmost2_preserves_P_r hidempotent h2 hfv h ht, by grind⟩



theorem exists_leftSpine_reduct {atom : Term String}
  (h2: atom.abs_two_vars_are_enough)
  (hfv : atom.fv = ∅)
  {t}
  (ht : Gen atom t)
  (hnormal: Relation.Normalizable Leftmost ((t.app (fvar "x")).app (fvar "y"))) :
  ∃ t', t ↠ℓ t' /\ P atom.subterms t' /\ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1) := by
  have h := @P_progress_to_simple_spine_or_stuck_nonabs atom.subterms subterms_idempotent (subterms_two_vars_are_enough (abs_two_vars_are_enough_weak h2)) (subterms_fv hfv) t ?_
  cases h with
  | inl h => grind
  | inr h =>  exfalso
              cases normalizable_app_implies_normalizable_or_reduces_to_abs hnormal with
      | inr h3 => obtain ⟨M, _, g⟩ := h3
                  cases leftstar_cases g <;> grind
      | inl h3 => cases normalizable_app_implies_normalizable_or_reduces_to_abs h3 with
      | inr h3 => grind
      | inl h3 => obtain ⟨t'', h3, _⟩ := h3
                  obtain ⟨_, h⟩ := h t'' h3
                  apply h
                  rw [betanormal_iff]
                  sorry
  rw [<- genfinset_P]
  apply gen_abs_2_vars_are_enough ht
  grind
  apply subterms_two_vars_are_enough (abs_two_vars_are_enough_weak h2)


-- this should be trival
-- I am blocked by next theorems
theorem exists_leftSpine_reduct2 {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t} (ht: P fs t)
  {t head : Term String}
  (hh : head ∈ fs)
  (ht : GenFinset fs t)
  (hnormal: Relation.ReflTransGen Leftmost (((head.app t).app (fvar "x")).app (fvar "y"))
                                           (((fvar "x").app (fvar "y")).app (H 100))) :
  ∃ head' t', head' ∈ fs /\ ((head.app t).app (fvar "x")) ↠ℓ head'.app t' /\ P fs t' := by
  sorry
-/

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
