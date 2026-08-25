import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.GenFinset
import FokkerChallenge.FamousCombinator

/-!
# The "applied tail" decider

Call a term *tail-applied* (`tailOk`) when every abstraction of it is the
outermost abstraction of a block

```
λ x₁ … λ x_s . z M₁ … M_k
```

with `k ≥ 1` arguments whose **last argument `M_k` is not a variable**, and when
all the parts `z, M₁, …, M_k` are tail-applied again.

Two things make this notion useful.

* `K = λx.λy.x` is not tail-applied: its block has no argument at all.  The
  same holds for every η-expansion `λ x y z₁ … z_m. x z₁ … z_m` of `K`, because
  their last argument is the variable `z_m`.
* Tail-applied terms have **no η-redex** at all — an η-redex `λx. M x` is a
  block whose last argument is the variable `x` — and they are closed under
  β-reduction and under application.

Consequently no applicative combination of a tail-applied term can ever
βη-reduce to `K`, so a tail-applied term is not a one-point basis
(`tailOk_not_basis`).

Preservation under β holds because substitution can never turn a non-variable
into a variable and because contracting a redex `(λ x. P) Q` puts the body `P`
— which, being a block body, is an application or an abstraction — in its
place.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- Is the term a (bound or free) variable? -/
def isVar : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | _ => false

mutual

/-- `tailOk M`: every abstraction block of `M` is of the shape
`λ … λ. z M₁ … M_k` with `k ≥ 1`, with `M_k` not a variable, and with all parts
tail-applied. -/
def tailOk : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .app f a => tailOk f && tailOk a
  | .abs t => tailOkBody t

/-- `tailOkBody t`: `t` is a legitimate body of an abstraction block, i.e.
either another abstraction (with a legitimate body) or an application whose last
argument is not a variable and whose two parts are tail-applied. -/
def tailOkBody : Term String → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .abs t => tailOkBody t
  | .app f a => !isVar a && tailOk f && tailOk a

end

@[simp] theorem tailOk_bvar {i} : tailOk (.bvar i) = true := by rw [tailOk]
@[simp] theorem tailOk_fvar {x} : tailOk (.fvar x) = true := by rw [tailOk]
@[simp] theorem tailOk_app {f a} : tailOk (.app f a) = (tailOk f && tailOk a) := by rw [tailOk]
@[simp] theorem tailOk_abs {t} : tailOk (.abs t) = tailOkBody t := by rw [tailOk]
@[simp] theorem tailOkBody_bvar {i} : tailOkBody (.bvar i) = false := by rw [tailOkBody]
@[simp] theorem tailOkBody_fvar {x} : tailOkBody (.fvar x) = false := by rw [tailOkBody]
@[simp] theorem tailOkBody_abs {t} : tailOkBody (.abs t) = tailOkBody t := by rw [tailOkBody]
@[simp] theorem tailOkBody_app {f a} :
    tailOkBody (.app f a) = (!isVar a && tailOk f && tailOk a) := by rw [tailOkBody]

/-! ## Non-variables -/

/-- A block body is never a variable. -/
theorem not_isVar_of_tailOkBody {T : Term String} (h : tailOkBody T) : isVar T = false := by
  match T with
  | .bvar _ => simp at h
  | .fvar _ => simp at h
  | .abs _ => rfl
  | .app _ _ => rfl

/-- Opening never turns a non-variable into a variable. -/
theorem isVar_openRec {M U : Term String} {i : ℕ} (h : isVar M = false) :
    isVar (M⟦i ↝ U⟧) = false := by
  match M with
  | .bvar _ => simp [isVar] at h
  | .fvar _ => simp [isVar] at h
  | .abs _ => rfl
  | .app _ _ => rfl

/-- Opening with a variable does not change being a variable. -/
theorem isVar_openRec_fvar {M : Term String} {i : ℕ} {x : String} :
    isVar (M⟦i ↝ Term.fvar x⟧) = isVar M := by
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h, isVar]
  | .fvar _ => rfl
  | .abs _ => rfl
  | .app _ _ => rfl

/-! ## Opening with a free variable does not change tail-applicability -/

mutual

theorem tailOk_openRec_fvar {M : Term String} {x : String} :
    ∀ i, tailOk (M⟦i ↝ Term.fvar x⟧) = tailOk M := by
  intro i
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h]
  | .fvar _ => rfl
  | .app f a =>
      simp [openRec, tailOk_openRec_fvar (M := f) i, tailOk_openRec_fvar (M := a) i]
  | .abs t => simpa [openRec] using tailOkBody_openRec_fvar (T := t) (i + 1)

theorem tailOkBody_openRec_fvar {T : Term String} {x : String} :
    ∀ i, tailOkBody (T⟦i ↝ Term.fvar x⟧) = tailOkBody T := by
  intro i
  match T with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h]
  | .fvar _ => rfl
  | .abs t => simpa [openRec] using tailOkBody_openRec_fvar (T := t) (i + 1)
  | .app f a =>
      simp [openRec, isVar_openRec_fvar (M := a) (i := i) (x := x),
        tailOk_openRec_fvar (M := f) i, tailOk_openRec_fvar (M := a) i]

end

/-! ## Substitution -/

mutual

theorem tailOk_openRec {M U : Term String} (hU : tailOk U) :
    ∀ i, tailOk M → tailOk (M⟦i ↝ U⟧) := by
  intro i hM
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h, hU]
  | .fvar _ => simp [openRec]
  | .app f a =>
      simp only [tailOk_app, Bool.and_eq_true] at hM
      simp [openRec, tailOk_openRec hU i hM.1, tailOk_openRec hU i hM.2]
  | .abs t =>
      simp only [tailOk_abs] at hM
      simpa [openRec] using tailOkBody_openRec hU (i + 1) hM

theorem tailOkBody_openRec {T U : Term String} (hU : tailOk U) :
    ∀ i, tailOkBody T → tailOkBody (T⟦i ↝ U⟧) := by
  intro i hT
  match T with
  | .bvar _ => simp at hT
  | .fvar _ => simp at hT
  | .abs t =>
      simp only [tailOkBody_abs] at hT
      simpa [openRec] using tailOkBody_openRec hU (i + 1) hT
  | .app f a =>
      simp only [tailOkBody_app, Bool.and_eq_true, Bool.not_eq_true'] at hT
      obtain ⟨⟨ha, hf⟩, ha'⟩ := hT
      simp [openRec, isVar_openRec (i := i) (U := U) ha, tailOk_openRec hU i hf,
        tailOk_openRec hU i ha']

end

/-- Contracting a β-redex whose function part is a tail-applied abstraction. -/
theorem tailOk_open_of_tailOkBody {T U : Term String} (hU : tailOk U) (hT : tailOkBody T) :
    tailOk (T ^ U) := by
  match T with
  | .bvar _ => simp at hT
  | .fvar _ => simp at hT
  | .abs t =>
      simp only [tailOkBody_abs] at hT
      simpa [open', openRec] using tailOkBody_openRec hU 1 hT
  | .app f a =>
      simp only [tailOkBody_app, Bool.and_eq_true, Bool.not_eq_true'] at hT
      obtain ⟨⟨_, hf⟩, ha⟩ := hT
      simp [open', openRec, tailOk_openRec hU 0 hf, tailOk_openRec hU 0 ha]

/-- The same, for the body of a block: the contractum of a redex sitting at the
end of a block is again a legitimate block body. -/
theorem tailOkBody_open_of_tailOkBody {T U : Term String} (hU : tailOk U) (hT : tailOkBody T) :
    tailOkBody (T ^ U) :=
  tailOkBody_openRec hU 0 hT

/-! ## Preservation under reduction -/

/-- The three statements that are proved simultaneously by induction on a
congruence step. -/
def TailPreserves (M N : Term String) : Prop :=
  (tailOk M → tailOk N) ∧ (tailOkBody M → tailOkBody N) ∧
    (tailOk M → isVar M = false → isVar N = false)

theorem tailPreserves_xi {R : Term String → Term String → Prop}
    (hbase : ∀ {M N}, R M N → TailPreserves M N) {M N : Term String} (h : Xi R M N) :
    TailPreserves M N := by
  induction h with
  | base hR => exact hbase hR
  | @appL Z M0 N0 _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [tailOk_app, Bool.and_eq_true] at hM ⊢
        exact ⟨hM.1, ih.1 hM.2⟩
      · intro hM
        simp only [tailOkBody_app, Bool.and_eq_true, Bool.not_eq_true'] at hM ⊢
        exact ⟨⟨ih.2.2 hM.2 hM.1.1, hM.1.2⟩, ih.1 hM.2⟩
      · intro _ _; rfl
  | @appR M0 N0 Z _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [tailOk_app, Bool.and_eq_true] at hM ⊢
        exact ⟨ih.1 hM.1, hM.2⟩
      · intro hM
        simp only [tailOkBody_app, Bool.and_eq_true, Bool.not_eq_true'] at hM ⊢
        exact ⟨⟨hM.1.1, ih.1 hM.1.2⟩, hM.2⟩
      · intro _ _; rfl
  | @abs T T' xs _ ih =>
      have key : tailOkBody T → tailOkBody T' := by
        intro hT
        obtain ⟨y, hy⟩ : ∃ y : String, y ∉ xs := Finset.exists_notMem _
        have := (ih y hy).2.1 (by rw [open', tailOkBody_openRec_fvar]; exact hT)
        rwa [open', tailOkBody_openRec_fvar] at this
      exact ⟨fun hM => by simpa using key (by simpa using hM), key, fun _ _ => rfl⟩

theorem tailPreserves_beta {M N : Term String} (h : Beta M N) : TailPreserves M N := by
  cases h with
  | @beta T U _ _ =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [tailOk_app, tailOk_abs, Bool.and_eq_true] at hM
        exact tailOk_open_of_tailOkBody hM.2 hM.1
      · intro hM
        simp only [tailOkBody_app, tailOk_abs, Bool.and_eq_true] at hM
        exact tailOkBody_open_of_tailOkBody hM.2 hM.1.2
      · intro hM _
        simp only [tailOk_app, tailOk_abs, Bool.and_eq_true] at hM
        exact isVar_openRec (not_isVar_of_tailOkBody hM.1)

theorem tailPreserves_eta {M N : Term String} (h : Eta M N) : TailPreserves M N := by
  cases h with
  | @eta P _ =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM; simp [isVar] at hM
      · intro hM; simp [isVar] at hM
      · intro hM; simp [isVar] at hM

theorem tailOk_fullBeta {M N : Term String} (h : FullBeta M N) (hM : tailOk M) : tailOk N :=
  (tailPreserves_xi tailPreserves_beta h).1 hM

theorem tailOk_fullEta {M N : Term String} (h : FullEta M N) (hM : tailOk M) : tailOk N :=
  (tailPreserves_xi tailPreserves_eta h).1 hM

theorem tailOk_fullBetaEta {M N : Term String} (h : FullBetaEta M N) (hM : tailOk M) : tailOk N := by
  rcases h with h | h
  · exact tailOk_fullBeta h hM
  · exact tailOk_fullEta h hM

theorem tailOk_fullBetaEta_star {M N : Term String} (h : M ↠βηᶠ N) (hM : tailOk M) : tailOk N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact tailOk_fullBetaEta hstep ih

/-! ## Tail-applicability is closed under application, `K` is not tail-applied -/

theorem tailOk_genFinset {fs : List (Term String)} {M : Term String}
    (hfs : ∀ t ∈ fs, tailOk t) (h : GenFinset fs M) : tailOk M := by
  induction h with
  | base ht => exact hfs _ ht
  | app _ _ iha ihb => simp [iha, ihb]

theorem tailOk_K : tailOk K = false := by decide

/-- **The applied-tail decider.**  A tail-applied term is not a one-point basis:
no applicative combination of it βη-reduces to `K = λx.λy.x`. -/
theorem tailOk_not_basises (fs : List (Term String)) (hfs : ∀ t ∈ fs, tailOk t) :
    not_basises fs := by
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← lcAt_iff_LC]; decide
  · decide
  · intro Y hgen hred
    have h1 := tailOk_genFinset hfs hgen
    have h2 := tailOk_fullBetaEta_star hred h1
    rw [tailOk_K] at h2
    exact Bool.noConfusion h2

theorem tailOk_not_basis {X : Term String} (h : tailOk X) : not_basis X := by
  apply tailOk_not_basises
  grind

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
