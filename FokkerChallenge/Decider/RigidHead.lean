import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.GenFinset
import FokkerChallenge.FamousCombinator

/-!
# The rigid-head decider

A term is *rigid-headed* (`rigid`) when every abstraction of it is the outermost
abstraction of a block `λ … λ. z M₁ … Mₖ` whose head variable `z` is the
*innermost* binder of that block and which has at least one argument, and when
all the arguments `Mᵢ` are rigid-headed again.

The point of this notion is that it is preserved by β- and by η-reduction and
that it is closed under application, while `K = λx.λy.x` is *not* rigid-headed.
Consequently no applicative combination of a rigid-headed term can ever reduce
to `K`, so a rigid-headed term is not a one-point basis (`rigid_not_basis`).

Preservation under β holds because a rigid-headed block never has a redex in
head position (its head is a bound variable), so a β-step only ever rewrites an
argument or instantiates the binders of a block from the outside in — which
never touches the innermost binder that sits at the head.  Preservation under η
holds because an η-redex `λx. M x` requires `x` not to occur in `M`, whereas in
a rigid-headed block the innermost binder occurs at the head.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The head of the application spine `M` is the de Bruijn index `0`. -/
def headB0 : Term String → Bool
  | .bvar i => i == 0
  | .app f _ => headB0 f
  | _ => false

/-- The head of the application spine `M` is the free variable `x`. -/
def headFX (x : String) : Term String → Bool
  | .fvar y => y == x
  | .app f _ => headFX x f
  | _ => false

mutual

/-- `rigid M`: every abstraction block of `M` is of the shape `λ … λ. z M₁ … Mₖ`
with `k ≥ 1`, `z` the innermost binder of the block, and all `Mᵢ` rigid. -/
def rigid : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .app f a => rigid f && rigid a
  | .abs t => rigidBody t

/-- `rigidBody t`: `t` is the body of an abstraction block, i.e. either another
abstraction (with a rigid body) or an application whose spine head is the
innermost bound variable and whose parts are rigid. -/
def rigidBody : Term String → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .abs t => rigidBody t
  | .app f a => headB0 f && rigid f && rigid a

end

/-- The variant of `rigidBody` for a body whose outermost binder has been opened
with the free variable `x`. -/
def rigidBodyX (x : String) : Term String → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .abs t => rigidBody t
  | .app f a => headFX x f && rigid f && rigid a

@[simp] theorem rigid_bvar {i} : rigid (.bvar i) = true := by rw [rigid]
@[simp] theorem rigid_fvar {x} : rigid (.fvar x) = true := by rw [rigid]
@[simp] theorem rigid_app {f a} : rigid (.app f a) = (rigid f && rigid a) := by rw [rigid]
@[simp] theorem rigid_abs {t} : rigid (.abs t) = rigidBody t := by rw [rigid]
@[simp] theorem rigidBody_abs {t} : rigidBody (.abs t) = rigidBody t := by rw [rigidBody]
@[simp] theorem rigidBody_app {f a} :
    rigidBody (.app f a) = (headB0 f && rigid f && rigid a) := by rw [rigidBody]
@[simp] theorem rigidBody_bvar {i} : rigidBody (.bvar i) = false := by rw [rigidBody]
@[simp] theorem rigidBody_fvar {x} : rigidBody (.fvar x) = false := by rw [rigidBody]

/-! ## Basic facts about the head predicates -/

theorem headB0_of_lc {U : Term String} (h : LC U) : headB0 U = false := by
  induction h with
  | fvar x => rfl
  | abs xs _ _ => rfl
  | app _ _ ih _ => simpa [headB0] using ih

/-- Opening at a level different from `0` does not change the head of a spine,
provided the inserted term is locally closed. -/
theorem headB0_openRec {M U : Term String} {i : ℕ} (hi : i ≠ 0) (hU : LC U) :
    headB0 (M⟦i ↝ U⟧) = headB0 M := by
  induction M with
  | bvar j =>
      by_cases h : i = j
      · subst h
        simp [openRec, headB0, headB0_of_lc hU]
        omega
      · simp [openRec, h, headB0]
  | fvar x => rfl
  | abs t _ => rfl
  | app f a ihf _ => simpa [openRec, headB0] using ihf

/-- After opening with a fresh variable `x`, "the head is the innermost bound
variable" becomes "the head is `x`". -/
theorem headFX_open_eq_headB0 {f : Term String} {x : String} (hx : x ∉ f.fv) :
    headFX x (f⟦0 ↝ Term.fvar x⟧) = headB0 f := by
  induction f with
  | bvar j =>
      by_cases h : (0 : ℕ) = j
      · subst h; simp [openRec, headFX, headB0]
      · simp [openRec, h, headFX, headB0]
        omega
  | fvar y => simp [fv] at hx; simp [openRec, headFX, headB0]; grind
  | abs t _ => rfl
  | app g a ihg _ =>
      simp only [fv, Finset.mem_union, not_or] at hx
      simpa [openRec, headFX, headB0] using ihg hx.1

/-! ## Opening with a free variable does not change rigidity -/

mutual

theorem rigid_openRec_fvar {M : Term String} {x : String} :
    ∀ i, rigid (M⟦i ↝ Term.fvar x⟧) = rigid M := by
  intro i
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h]
  | .fvar y => rfl
  | .app f a => simp [openRec, rigid_openRec_fvar (M := f) i, rigid_openRec_fvar (M := a) i]
  | .abs t => simpa [openRec] using rigidBody_openRec_fvar (T := t) i

theorem rigidBody_openRec_fvar {T : Term String} {x : String} :
    ∀ i, rigidBody (T⟦i + 1 ↝ Term.fvar x⟧) = rigidBody T := by
  intro i
  match T with
  | .bvar j => by_cases h : i + 1 = j <;> simp [openRec, h]
  | .fvar y => rfl
  | .abs t =>
      have := rigidBody_openRec_fvar (T := t) (x := x) (i + 1)
      simpa [openRec] using this
  | .app f a =>
      have h1 : headB0 (f⟦i + 1 ↝ Term.fvar x⟧) = headB0 f :=
        headB0_openRec (by omega) (LC.fvar x)
      simp [openRec, h1, rigid_openRec_fvar (M := f) (i+1), rigid_openRec_fvar (M := a) (i+1)]

end

/-- The key bridge: `rigidBody` of a body equals `rigidBodyX` of the body opened
with a fresh variable. -/
theorem rigidBodyX_open {T : Term String} {x : String} (hx : x ∉ T.fv) :
    rigidBodyX x (T ^ Term.fvar x) = rigidBody T := by
  match T with
  | .bvar j =>
      by_cases h : (0 : ℕ) = j <;> simp [open', openRec, h, rigidBodyX]
  | .fvar y => simp [open', openRec, rigidBodyX]
  | .abs t => simpa [open', openRec, rigidBodyX] using rigidBody_openRec_fvar (T := t) (x := x) 0
  | .app f a =>
      simp only [fv, Finset.mem_union, not_or] at hx
      have h1 : headFX x (f⟦0 ↝ Term.fvar x⟧) = headB0 f := headFX_open_eq_headB0 hx.1
      simp [open', openRec, rigidBodyX, h1, rigid_openRec_fvar (M := f) 0,
        rigid_openRec_fvar (M := a) 0]

/-! ## Substitution -/

mutual

theorem rigid_openRec {M U : Term String} (hU : LC U) (hrU : rigid U) :
    ∀ i, rigid M → rigid (M⟦i ↝ U⟧) := by
  intro i hM
  match M with
  | .bvar j => by_cases h : i = j <;> simp [openRec, h, hrU]
  | .fvar y => simp [openRec]
  | .app f a =>
      simp only [rigid_app, Bool.and_eq_true] at hM
      simp [openRec, rigid_openRec hU hrU i hM.1, rigid_openRec hU hrU i hM.2]
  | .abs t =>
      simp only [rigid_abs] at hM
      simpa [openRec] using rigidBody_openRec hU hrU i hM

theorem rigidBody_openRec {T U : Term String} (hU : LC U) (hrU : rigid U) :
    ∀ i, rigidBody T → rigidBody (T⟦i + 1 ↝ U⟧) := by
  intro i hT
  match T with
  | .bvar j => simp at hT
  | .fvar y => simp at hT
  | .abs t =>
      simp only [rigidBody_abs] at hT
      have := rigidBody_openRec (T := t) hU hrU (i + 1) hT
      simpa [openRec] using this
  | .app f a =>
      simp only [rigidBody_app, Bool.and_eq_true] at hT
      obtain ⟨⟨h0, hf⟩, ha⟩ := hT
      have h1 : headB0 (f⟦i + 1 ↝ U⟧) = headB0 f := headB0_openRec (by omega) hU
      simp [openRec, h1, h0, rigid_openRec hU hrU (i+1) hf, rigid_openRec hU hrU (i+1) ha]

end

/-- Contracting a β-redex whose function part is a rigid abstraction. -/
theorem rigid_open_of_rigidBody {T U : Term String} (hU : LC U) (hrU : rigid U)
    (hT : rigidBody T) : rigid (T ^ U) := by
  match T with
  | .bvar j => simp at hT
  | .fvar y => simp at hT
  | .abs t =>
      simp only [rigidBody_abs] at hT
      simpa [open', openRec] using rigidBody_openRec (T := t) hU hrU 0 hT
  | .app f a =>
      simp only [rigidBody_app, Bool.and_eq_true] at hT
      obtain ⟨⟨_, hf⟩, ha⟩ := hT
      simp [open', openRec, rigid_openRec hU hrU 0 hf, rigid_openRec hU hrU 0 ha]

/-! ## Preservation under reduction -/

/-- The three statements that are proved simultaneously by induction on a
congruence step. -/
def Preserves (M N : Term String) : Prop :=
  (rigid M → rigid N) ∧ (∀ x, rigidBodyX x M → rigidBodyX x N) ∧
    (∀ x, headFX x M → headFX x N)

theorem preserves_xi {R : Term String → Term String → Prop}
    (hbase : ∀ {M N}, R M N → Preserves M N) {M N : Term String} (h : Xi R M N) :
    Preserves M N := by
  induction h with
  | base hR => exact hbase hR
  | @appL Z M0 N0 _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [rigid_app, Bool.and_eq_true] at hM ⊢
        exact ⟨hM.1, ih.1 hM.2⟩
      · intro x hM
        simp only [rigidBodyX, Bool.and_eq_true] at hM ⊢
        exact ⟨⟨hM.1.1, hM.1.2⟩, ih.1 hM.2⟩
      · intro x hM
        simpa [headFX] using hM
  | @appR M0 N0 Z _ _ ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [rigid_app, Bool.and_eq_true] at hM ⊢
        exact ⟨ih.1 hM.1, hM.2⟩
      · intro x hM
        simp only [rigidBodyX, Bool.and_eq_true] at hM ⊢
        exact ⟨⟨ih.2.2 x hM.1.1, ih.1 hM.1.2⟩, hM.2⟩
      · intro x hM
        simp only [headFX] at hM ⊢
        exact ih.2.2 x hM
  | @abs T T' xs hstep ih =>
      have key : rigidBody T → rigidBody T' := by
        intro hT
        obtain ⟨y, hy⟩ : ∃ y : String, y ∉ xs ∪ T.fv ∪ T'.fv :=
          Finset.exists_notMem _
        have hy1 : y ∉ xs := by simp at hy; tauto
        have hy2 : y ∉ T.fv := by simp at hy; tauto
        have hy3 : y ∉ T'.fv := by simp at hy; tauto
        have := (ih y hy1).2.1 y (by rw [rigidBodyX_open hy2]; exact hT)
        rw [rigidBodyX_open hy3] at this
        exact this
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simpa using key (by simpa using hM)
      · intro x hM
        simp only [rigidBodyX] at hM ⊢
        exact key hM
      · intro x hM
        simp [headFX] at hM

theorem preserves_beta {M N : Term String} (h : Beta M N) : Preserves M N := by
  cases h with
  | @beta T U hT hU =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp only [rigid_app, rigid_abs, Bool.and_eq_true] at hM
        exact rigid_open_of_rigidBody hU hM.2 hM.1
      · intro x hM
        simp [rigidBodyX, headFX] at hM
      · intro x hM
        simp [headFX] at hM

theorem preserves_eta {M N : Term String} (h : Eta M N) : Preserves M N := by
  cases h with
  | @eta P hP =>
      refine ⟨?_, ?_, ?_⟩
      · intro hM
        simp [rigid_abs, rigidBody_app, headB0_of_lc hP] at hM
      · intro x hM
        simp [rigidBodyX, rigidBody_app, headB0_of_lc hP] at hM
      · intro x hM
        simp [headFX] at hM

theorem rigid_fullBeta {M N : Term String} (h : FullBeta M N) (hM : rigid M) : rigid N :=
  (preserves_xi preserves_beta h).1 hM

theorem rigid_fullEta {M N : Term String} (h : FullEta M N) (hM : rigid M) : rigid N :=
  (preserves_xi preserves_eta h).1 hM

theorem rigid_fullBetaEta {M N : Term String} (h : FullBetaEta M N) (hM : rigid M) : rigid N := by
  rcases h with h | h
  · exact rigid_fullBeta h hM
  · exact rigid_fullEta h hM

theorem rigid_fullBetaEta_star {M N : Term String} (h : M ↠βηᶠ N) (hM : rigid M) : rigid N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact rigid_fullBetaEta hstep ih

/-! ## Rigidity is closed under application, `K` is not rigid -/

theorem rigid_genFinset {fs : List (Term String)} {M : Term String}
    (hfs : ∀ t ∈ fs, rigid t) (h : GenFinset fs M) : rigid M := by
  induction h with
  | base ht => exact hfs _ ht
  | app _ _ iha ihb => simp [iha, ihb]

theorem rigid_K : rigid K = false := by decide

/-- **The rigid-head decider.**  A rigid-headed term is not a one-point basis:
no applicative combination of it βη-reduces to `K = λx.λy.x`. -/
theorem rigid_not_basises (fs : List (Term String)) (hfs : ∀ t ∈ fs, rigid t) :
    not_basises fs := by
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← lcAt_iff_LC]; decide
  · decide
  · intro Y hgen hred
    have h1 := rigid_genFinset hfs hgen
    have h2 := rigid_fullBetaEta_star hred h1
    rw [rigid_K] at h2
    exact Bool.noConfusion h2

theorem rigid_not_basis {X : Term String} (h : rigid X) : not_basis X := by
  apply rigid_not_basises
  grind

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
