import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import FokkerChallenge.EnhancedCslib.HeadRed
import FokkerChallenge.EnhancedCslib.InternalPar
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# Takahashi's `*`-sequences and the Main Lemma

Following Takahashi, *Parallel reductions in λ-calculus* (1995), Lemma 2.2, we
introduce the relation `StarSeq M N` (written `M * N` in the paper): there is a
head reduction sequence

`M ≡ M₀ ⟶h M₁ ⟶h ⋯ ⟶h Mₘ`

such that `Mₘ` reduces to `N` by an *internal* parallel reduction, and every
`Mⱼ` parallel-reduces to `N`.

The Main Lemma is `parBeta_starSeq`: every parallel β-reduction `M ⟹ N` is a
`*`-sequence.  In particular `M ⟶h* P` with `P ⟹ᵢ N` for some `P`.
-/


universe u

open Term

variable {Var : Type u}

/-- A Takahashi `*`-sequence from `M` to `N`: a (possibly empty) head reduction
from `M`, ending in a term that reduces to `N` internally, all of whose terms
parallel-reduce to `N`. -/
inductive StarSeq : Term Var → Term Var → Prop
  /-- The empty head reduction: an internal parallel step. -/
  | nil {M N : Term Var} : IPar M N → StarSeq M N
  /-- Prefix a head reduction step. -/
  | cons {M M' N : Term Var} :
      Parallel M N → HeadStep M M' → StarSeq M' N → StarSeq M N

theorem StarSeq.toParBeta {M N : Term Var} (h : StarSeq M N) : Parallel M N := by
  cases h with
  | nil hi => exact hi.toParallel
  | cons hp _ _ => exact hp

/-- A `*`-sequence is a head reduction followed by an internal parallel step. -/
theorem StarSeq.head_star {M N : Term Var} (h : StarSeq M N) :
    ∃ P, HeadStepStar M P ∧ IPar P N := by
  induction h with
  | nil hi => exact ⟨_, Relation.ReflTransGen.refl, hi⟩
  | cons _ hstep _ ih =>
      obtain ⟨P, hP, hiP⟩ := ih
      exact ⟨P, Relation.ReflTransGen.head hstep hP, hiP⟩

theorem starSeq_app_abs {M N P Q : Term Var} (hpar : Parallel M N) (hM : M.IsAbs)
    (hPQ : Parallel P Q) : StarSeq (Term.app M P) (Term.app N Q) := by
    cases hM
    cases hpar with
    | abs xs hbody => exact StarSeq.nil (IPar.appAbs xs hbody hPQ)

/-- Takahashi's property (2) (Lemma 2.3). -/
theorem StarSeq.app {M N P Q : Term Var} (h : StarSeq M N) (hPQ : Parallel P Q) :
    StarSeq (Term.app M P) (Term.app N Q) := by
  induction h with
  | @nil M N hi =>
      by_cases hM : M.IsAbs
      · exact starSeq_app_abs hi.toParallel hM hPQ
      · exact StarSeq.nil (IPar.app hM hi hPQ)
  | @cons M M' N hp hstep _ ih =>
      by_cases hM : M.IsAbs
      · exact starSeq_app_abs hp hM hPQ
      · exact StarSeq.cons (Parallel.app hp hPQ)
          (HeadStep.app hM hstep (para_lc_l hPQ)) ih

variable  [HasFresh Var] [DecidableEq Var]

/-- `*`-sequences are stable under renaming. -/
theorem StarSeq.rename {A B : Term Var} (h : StarSeq A B) (x y : Var) :
    StarSeq (A[x:=(Term.fvar y)]) (B[x:=(Term.fvar y)]) := by
  induction h with
  | nil hi => exact StarSeq.nil (hi.rename x y)
  | cons hp hstep _ ih =>
      exact StarSeq.cons (hp.rename x y) (hstep.subst x (Term.LC.fvar y)) ih

/-- `*`-sequences lift under a binder, via closing. -/
theorem StarSeq.abs_close (x : Var) {A B : Term Var} (h : StarSeq A B) :
    StarSeq (Term.abs (closeRec 0 x A)) (Term.abs (closeRec 0 x B)) := by
  induction h with
  | nil hi => exact StarSeq.nil (hi.abs_close x)
  | cons hp hstep _ ih =>
      exact StarSeq.cons (hp.abs_close x) (hstep.abs_close x) ih

/-- Takahashi's property (1): `*`-sequences lift under a binder. -/
theorem StarSeq.abs_cofinite {M M' : Term Var} (xs : Finset Var)
    (h : ∀ x ∉ xs, StarSeq (M ^ Term.fvar x) (M' ^ Term.fvar x)) :
    StarSeq (Term.abs M) (Term.abs M') := by
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (xs ∪ (fv M ∪ fv M'))
  simp only [Finset.mem_union, not_or] at hz
  have h2 := StarSeq.abs_close z (h z hz.1)
  unfold open' at h2
  rw [<- open_close, <- open_close] at h2
  grind
  grind
  grind

/-- Takahashi's property (3) (Lemma 2.4), internal case. -/
theorem IPar.starSeq_subst {A B C D : Term Var} (z : Var) (h : IPar A B)
    (hCD : StarSeq C D) : StarSeq (A[z:= C]) (B[z := D]) := by
  have hC : LC C := (para_lc_l hCD.toParBeta)
  have hD : LC D := (para_lc_r hCD.toParBeta)
  induction h with
  | fvar x =>   rw [subst_fvar, subst_fvar]
                split <;> try grind
                apply StarSeq.nil (IPar.fvar (Var := Var) x)
  | @app M M' N N' _ _ hN ih =>
      exact StarSeq.app ih (para_subst z hN hCD.toParBeta)
  | @appAbs xs M M' N N' hbody hN =>
      refine StarSeq.nil (IPar.appAbs (xs ∪ {z}) ?_ (para_subst z hN hCD.toParBeta))
      intro x hx
      have := para_subst z (hbody x (by grind)) hCD.toParBeta
      grind
  | @abs xs M M' _ ih =>
      refine StarSeq.abs_cofinite (xs ∪ {z}) ?_
      intro x hx
      grind [ih x (by grind)]

/-- Takahashi's property (3) (Lemma 2.4). -/
theorem StarSeq.subst {A B C D : Term Var} (z : Var) (h : StarSeq A B)
    (hCD : StarSeq C D) : StarSeq (A[z:=C]) (B[z:=D]) := by
  have hC : LC C := (para_lc_l hCD.toParBeta)
  induction h with
  | nil hi => exact hi.starSeq_subst z hCD
  | cons hp hstep _ ih =>
      exact StarSeq.cons (para_subst z hp hCD.toParBeta) (hstep.subst z hC) ih

/-- The opening version of Takahashi's property (3). -/
theorem StarSeq.open_star {A A' C D : Term Var} (xs : Finset Var)
    (hbody : ∀ x ∉ xs, StarSeq (A ^ Term.fvar x) (A' ^ Term.fvar x))
    (hCD : StarSeq C D) : StarSeq (A ^ C) (A' ^ D) := by
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  have := StarSeq.subst z (hbody z (by grind)) hCD
  grind

/-- **Main Lemma** (Takahashi, Lemma 2.2), auxiliary form with a size bound. -/
theorem parBeta_starSeq_aux :
    ∀ (n : ℕ) {M N : Term Var}, Term.size M ≤ n → Parallel M N → StarSeq M N := by
  intro n
  induction n with
  | zero =>
      intro M N hs _
      exact absurd hs (by cases M <;> simp [Term.size])
  | succ n ih =>
      intro M N hs h
      cases h with
      | fvar x => exact StarSeq.nil (IPar.fvar x)
      | @app A A' B B' hA hB =>
          refine StarSeq.app (ih ?_ hA) hB
          simp only [Term.size] at hs; omega
      | abs xs hbody =>
          refine StarSeq.abs_cofinite xs (fun x hx => ih ?_ (hbody x hx))
          simp only [Term.size, size_open_fvar] at hs ⊢; omega
      | @beta B' A A' B xs hbody hB =>
          refine StarSeq.cons (Parallel.beta xs hbody hB)
            (HeadStep.beta (Term.LC.abs xs B' fun x hx => (para_lc_l (hbody x hx)))
              (para_lc_l hB)) ?_
          refine StarSeq.open_star xs (fun x hx => ih ?_ (hbody x hx)) (ih ?_ hB)
          · simp only [Term.size, size_open_fvar] at hs ⊢; omega
          · simp only [Term.size] at hs; omega

/-- **Main Lemma** (Takahashi, Lemma 2.2): every parallel β-reduction is a
`*`-sequence, i.e. a head reduction followed by an internal parallel step. -/
theorem parBeta_starSeq {M N : Term Var} (h : Parallel M N) : StarSeq M N :=
  parBeta_starSeq_aux (Term.size M) le_rfl h

/-- Every parallel β-reduction factors as a head reduction followed by an
internal parallel reduction. -/
theorem parBeta_head_internal {M N : Term Var} (h : Parallel M N) :
    ∃ P, HeadStepStar M P ∧ IPar P N := (parBeta_starSeq h).head_star
