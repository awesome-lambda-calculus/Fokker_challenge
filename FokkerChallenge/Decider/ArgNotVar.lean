import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.GenFinset
import FokkerChallenge.FamousCombinator
import FokkerChallenge.Decider.TailNotVar

/-!
# The "some argument is not a variable" decider

This is the λ-calculus form of the key step of Bellot's proof of Craig's
theorem (*A New Proof for Craig's Theorem*, JSL 50 (1985) 395–396): a proper
combinator whose contractum is not a variable can never produce a variable, so
it cannot supply the projections that a basis needs.

Call a term *argument-safe* (`argOk`) when every abstraction block of it

```
λ x₁ … λ x_s . E M₁ … M_k
```

has `k ≥ 1` arguments and either its head `E` is itself an abstraction, or one
of its arguments `M₁, …, M_k` is **not a variable** — and when all the parts
`E, M₁, …, M_k` are argument-safe again.

This strictly generalises the decider of `FokkerChallenge.Decider.TailNotVar`,
which asks the *last* argument of every block to be a non-variable.  The point
of the weaker requirement is that it is still preserved by reduction:

* a non-variable argument stays a non-variable argument under substitution, and
  β-contracting the head redex of a block merges the head's own block — which
  again has a non-variable argument — into the block;
* an η-step `λx. E M₁ … M_{k-1} x ⟶ E M₁ … M_{k-1}` removes the *variable*
  argument `x`, so a non-variable argument (and hence at least one argument)
  always survives;
* `K = λx.λy.x` has a block with no argument at all, so `argOk K = false`.

Consequently no applicative combination of an argument-safe term βη-reduces to
`K`, i.e. an argument-safe term is not a one-point basis (`argOk_not_basis`).
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

mutual

/-- `argOk M`: every abstraction block of `M` is of the shape `λ … λ. E M₁ … M_k`
with `k ≥ 1` and with an abstraction head or a non-variable argument, all parts
being argument-safe. -/
def argOk : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .app f a => argOk f && argOk a
  | .abs t => spineOk t

/-- `spineOk t`: `t` is a legitimate body of an abstraction block, i.e. either
another abstraction (with a legitimate body) or an application `E M₁ … M_k`
(`k ≥ 1`) whose head is an abstraction or which has a non-variable argument,
all parts being argument-safe. -/
def spineOk : Term String → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .abs t => spineOk t
  | .app f a => argOk a && (spineOk f || (argOk f && !isVar a))

end

@[simp] theorem argOk_bvar {i} : argOk (.bvar i) = true := by rw [argOk]
@[simp] theorem argOk_fvar {x} : argOk (.fvar x) = true := by rw [argOk]
@[simp] theorem argOk_app {f a} : argOk (.app f a) = (argOk f && argOk a) := by rw [argOk]
@[simp] theorem argOk_abs {t} : argOk (.abs t) = spineOk t := by rw [argOk]
@[simp] theorem spineOk_bvar {i} : spineOk (.bvar i) = false := by rw [spineOk]
@[simp] theorem spineOk_fvar {x} : spineOk (.fvar x) = false := by rw [spineOk]
@[simp] theorem spineOk_abs {t} : spineOk (.abs t) = spineOk t := by rw [spineOk]
@[simp] theorem spineOk_app {f a} :
    spineOk (.app f a) = (argOk a && (spineOk f || (argOk f && !isVar a))) := by rw [spineOk]

/-! ## Elementary consequences -/

/-- A legitimate block body is never a variable. -/
theorem not_isVar_of_spineOk {T : Term String} (h : spineOk T) : isVar T = false := by
  match T with
  | .bvar _ => simp at h
  | .fvar _ => simp at h
  | .abs _ => rfl
  | .app _ _ => rfl

/-- A legitimate block body is in particular argument-safe. -/
theorem argOk_of_spineOk {T : Term String} (h : spineOk T) : argOk T := by
  match T with
  | .bvar _ => simp at h
  | .fvar _ => simp at h
  | .abs t => simpa using h
  | .app f a =>
      simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨ha, hf⟩ := h
      simp only [argOk_app, Bool.and_eq_true]
      refine ⟨?_, ha⟩
      rcases hf with hf | hf
      · exact argOk_of_spineOk hf
      · exact hf.1

/-! ## Opening with a free variable does not change argument-safety -/

mutual

theorem argOk_openRec_fvar {M : Term String} {x : String} :
    ∀ i, argOk (M⟦i ↝ Term.fvar x⟧) = argOk M := by
  intro i
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h]
  | .fvar _ => rfl
  | .app f a =>
      simp [openRec, argOk_openRec_fvar (M := f) i, argOk_openRec_fvar (M := a) i]
  | .abs t => simpa [openRec] using spineOk_openRec_fvar (M := t) (i + 1)

theorem spineOk_openRec_fvar {M : Term String} {x : String} :
    ∀ i, spineOk (M⟦i ↝ Term.fvar x⟧) = spineOk M := by
  intro i
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h]
  | .fvar _ => rfl
  | .abs t => simpa [openRec] using spineOk_openRec_fvar (M := t) (i + 1)
  | .app f a =>
      simp [openRec, isVar_openRec_fvar (M := a) (i := i) (x := x),
        argOk_openRec_fvar (M := f) i, argOk_openRec_fvar (M := a) i,
        spineOk_openRec_fvar (M := f) i]

end

/-! ## Substitution -/

mutual

theorem argOk_openRec {M U : Term String} (hU : argOk U) :
    ∀ i, argOk M → argOk (M⟦i ↝ U⟧) := by
  intro i hM
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h, hU]
  | .fvar _ => simp [openRec]
  | .app f a =>
      simp only [argOk_app, Bool.and_eq_true] at hM
      simp [openRec, argOk_openRec hU i hM.1, argOk_openRec hU i hM.2]
  | .abs t =>
      simp only [argOk_abs] at hM
      simpa [openRec] using spineOk_openRec hU (i + 1) hM

theorem spineOk_openRec {M U : Term String} (hU : argOk U) :
    ∀ i, spineOk M → spineOk (M⟦i ↝ U⟧) := by
  intro i hM
  match M with
  | .bvar _ => simp at hM
  | .fvar _ => simp at hM
  | .abs t =>
      simp only [spineOk_abs] at hM
      simpa [openRec] using spineOk_openRec hU (i + 1) hM
  | .app f a =>
      simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true] at hM
      obtain ⟨ha, hf⟩ := hM
      simp only [openRec, spineOk_app, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨argOk_openRec hU i ha, ?_⟩
      rcases hf with hf | hf
      · exact Or.inl (spineOk_openRec hU i hf)
      · simp only [Bool.not_eq_true'] at hf
        exact Or.inr (by
          simp [argOk_openRec hU i hf.1, isVar_openRec (i := i) (U := U) hf.2])

end

/-- Contracting a β-redex whose function part is an argument-safe abstraction. -/
theorem spineOk_open_of_spineOk {T U : Term String} (hU : argOk U) (hT : spineOk T) :
    spineOk (T ^ U) :=
  spineOk_openRec hU 0 hT

theorem argOk_open_of_spineOk {T U : Term String} (hU : argOk U) (hT : spineOk T) :
    argOk (T ^ U) :=
  argOk_of_spineOk (spineOk_open_of_spineOk hU hT)

/-! ## Preservation under reduction -/

/-- The three statements that are proved simultaneously by induction on a
congruence step. -/
def ArgPreserves (M N : Term String) : Prop :=
  (argOk M → argOk N) ∧ (spineOk M → spineOk N) ∧
    (argOk M → isVar M = false → isVar N = false)

theorem argPreserves_xi {R : Term String → Term String → Prop}
    (hbase : ∀ {M N}, R M N → ArgPreserves M N) {M N : Term String} (h : Xi R M N) :
    ArgPreserves M N := by
  induction h with
  | base hR => exact hbase hR
  | @appL Z M0 N0 _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [argOk_app, Bool.and_eq_true] at hM ⊢
        exact ⟨hM.1, ih.1 hM.2⟩
      · intro hM
        simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true] at hM ⊢
        obtain ⟨ha, hf⟩ := hM
        refine ⟨ih.1 ha, ?_⟩
        rcases hf with hf | hf
        · exact Or.inl hf
        · simp only [Bool.not_eq_true'] at hf
          exact Or.inr (by simp [hf.1, ih.2.2 ha hf.2])
      · intro _ _; rfl
  | @appR M0 N0 Z _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [argOk_app, Bool.and_eq_true] at hM ⊢
        exact ⟨ih.1 hM.1, hM.2⟩
      · intro hM
        simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true] at hM ⊢
        obtain ⟨ha, hf⟩ := hM
        refine ⟨ha, ?_⟩
        rcases hf with hf | hf
        · exact Or.inl (ih.2.1 hf)
        · simp only [Bool.not_eq_true'] at hf
          exact Or.inr (by simp [ih.1 hf.1, hf.2])
      · intro _ _; rfl
  | @abs T T' xs _ ih =>
      have key : spineOk T → spineOk T' := by
        intro hT
        obtain ⟨y, hy⟩ : ∃ y : String, y ∉ xs := Finset.exists_notMem _
        have := (ih y hy).2.1 (by rw [open', spineOk_openRec_fvar]; exact hT)
        rwa [open', spineOk_openRec_fvar] at this
      exact ⟨fun hM => by simpa using key (by simpa using hM), key, fun _ _ => rfl⟩

theorem argPreserves_beta {M N : Term String} (h : Beta M N) : ArgPreserves M N := by
  cases h with
  | @beta T U _ _ =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [argOk_app, argOk_abs, Bool.and_eq_true] at hM
        exact argOk_open_of_spineOk hM.2 hM.1
      · intro hM
        simp only [spineOk_app, argOk_abs, spineOk_abs, Bool.and_eq_true, Bool.or_eq_true] at hM
        obtain ⟨hU, hf⟩ := hM
        have hT : spineOk T := by
          rcases hf with hf | hf
          · exact hf
          · exact hf.1
        exact spineOk_open_of_spineOk hU hT
      · intro hM _
        simp only [argOk_app, argOk_abs, Bool.and_eq_true] at hM
        exact not_isVar_of_spineOk (spineOk_open_of_spineOk hM.2 hM.1)

theorem argPreserves_eta {M N : Term String} (h : Eta M N) : ArgPreserves M N := by
  cases h with
  | eta _ =>
      have key : spineOk (Term.abs (Term.app N (Term.bvar 0))) → spineOk N := by
        intro h
        simp only [spineOk_abs, spineOk_app, argOk_bvar, isVar, Bool.and_eq_true,
          Bool.or_eq_true, Bool.not_true, Bool.and_false] at h
        simpa using h
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        exact argOk_of_spineOk (key (by simpa using hM))
      · intro hM
        exact key (by simpa using hM)
      · intro hM _
        exact not_isVar_of_spineOk (key (by simpa using hM))

theorem argOk_fullBeta {M N : Term String} (h : FullBeta M N) (hM : argOk M) : argOk N :=
  (argPreserves_xi argPreserves_beta h).1 hM

theorem argOk_fullEta {M N : Term String} (h : FullEta M N) (hM : argOk M) : argOk N :=
  (argPreserves_xi argPreserves_eta h).1 hM

theorem argOk_fullBetaEta {M N : Term String} (h : FullBetaEta M N) (hM : argOk M) : argOk N := by
  rcases h with h | h
  · exact argOk_fullBeta h hM
  · exact argOk_fullEta h hM

theorem argOk_fullBetaEta_star {M N : Term String} (h : M ↠βηᶠ N) (hM : argOk M) : argOk N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact argOk_fullBetaEta hstep ih

/-! ## Argument-safety is closed under application, `K` is not argument-safe -/

theorem argOk_genFinset {fs : List (Term String)} {M : Term String}
    (hfs : ∀ t ∈ fs, argOk t) (h : GenFinset fs M) : argOk M := by
  induction h with
  | base ht => exact hfs _ ht
  | app _ _ iha ihb => simp [iha, ihb]

theorem argOk_K : argOk K = false := by decide

/-- **The argument-safety decider.**  An argument-safe term is not a one-point
basis: no applicative combination of it βη-reduces to `K = λx.λy.x`. -/
theorem argOk_not_basises (fs : List (Term String)) (hfs : ∀ t ∈ fs, argOk t) :
    not_basises fs := by
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← lcAt_iff_LC]; decide
  · decide
  · intro Y hgen hred
    have h1 := argOk_genFinset hfs hgen
    have h2 := argOk_fullBetaEta_star hred h1
    rw [argOk_K] at h2
    exact Bool.noConfusion h2

theorem argOk_not_basis {X : Term String} (h : argOk X) : not_basis X := by
  apply argOk_not_basises
  grind

mutual

/-- Every tail-applied term (the decider of `FokkerChallenge.Decider.TailNotVar`)
is argument-safe: the present decider strictly generalises it. -/
theorem argOk_of_tailOk : ∀ {T : Term String}, tailOk T → argOk T := by
  intro T
  match T with
  | .bvar _ => intro _; simp
  | .fvar _ => intro _; simp
  | .app f a =>
      intro h
      simp only [tailOk_app, Bool.and_eq_true] at h
      simp [argOk_of_tailOk h.1, argOk_of_tailOk h.2]
  | .abs t =>
      intro h
      simp only [tailOk_abs] at h
      simpa using spineOk_of_tailOkBody h

theorem spineOk_of_tailOkBody : ∀ {T : Term String}, tailOkBody T → spineOk T := by
  intro T
  match T with
  | .bvar _ => intro h; simp at h
  | .fvar _ => intro h; simp at h
  | .abs t =>
      intro h
      simp only [tailOkBody_abs] at h
      simpa using spineOk_of_tailOkBody h
  | .app f a =>
      intro h
      simp only [tailOkBody_app, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨ha, hf⟩, ha'⟩ := h
      simp [spineOk_app, argOk_of_tailOk hf, argOk_of_tailOk ha', ha]

end

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
