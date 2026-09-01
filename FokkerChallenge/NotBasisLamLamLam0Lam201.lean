import FokkerChallenge.Undecided8HNF
import FokkerChallenge.BetaCheck
import FokkerChallenge.FamousCombinator

/-!
# `λλλ0(λ201)` is not a one-point basis

The term

```
X = λλλ0(λ201) = λx y z. z (λw. y w z)
```

is one of the terms of `undecided_terms.json` whose one-point-basis status was open.
This file settles it in the negative: **no applicative combination of `X` βη-reduces to
`I = λx. x`** (`gen_not_betaEtaStar_I`), so `X` is not a one-point basis
(`not_basis_lamlamlam0lam201`).

## The machine

The basic head reductions of `X` are already established in
`FokkerChallenge.Undecided8HNF`.  Writing `X₁ = λ y z. z (λw. y w z)` (`Xc1`),
`F B = λz. z (λw. B w z)` (`Xc2`) and `⟨B,C⟩ = λw. B w C` (`pairT`), they read

```
X A Γ       ⭢h  X₁ Γ            X₁ B Γ    ⭢h  F B Γ
F B C Γ     ⭢h  C ⟨B,C⟩ Γ       ⟨B,C⟩ U Γ ⭢h  B U C Γ
```

so that a combination of `X`, applied to a stack of arguments, evolves like a little
stack machine whose "heads" are `X`, `X₁`, `F B` and `⟨B,C⟩`.

## The values

Every applicative combination of `X` either βη-reduces to one of

```
X,   X₁,   F A     (`Val`)
```

or is unsolvable in a strong sense (`Bad`: it βη-reduces to a term which, with **any**
stack of further arguments, has no head normal form).  This dichotomy (`Good`) is closed
under application (`good_app`), which is the heart of the file.  The multiplication rules
are

```
X · N       ↠  X₁                    X₁ · N      ↠  F N
F A · X     ↠  X₁                    F A · X₁    ↠  F ⟨A,X₁⟩
F X · F P   ↠  F (F P)               F A · F P   diverges for `A ≠ X`
```

## The divergence

The unsolvability statement is proved for the family of states

```
H B Δ… (F P) Γ…
```

where the head `H` and the arguments `B, Δ…` range over the classes `ROk`/`QOk` — the
terms built from `X₁`, `F` and `⟨·,·⟩` (and already unsolvable terms), with `X` allowed in
head position and in the first component of a pair, but *not* as an argument: `X` is the
only eraser, and an eraser in argument position is exactly what stops the loop.  This
family head reduces to itself (`divOrStuck_step`), so by the head normalization theorem of
`FokkerChallenge.EnhancedCslib.HeadSN` none of its members has a head normal form.

## Conclusion

`X` and `X₁` are βη-normal and differ from `I`, and `F A · X ↠β X₁` shows `F A` is not
βη-equal to `I` either (it would force `X₁ = X`).  Unsolvable terms have no βη-normal
form at all.  Hence no combination of `X` βη-reduces to `I`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

namespace LamLamLam0Lam201

/-- `X = λλλ0(λ201) = λx y z. z (λw. y w z)`. -/
def Xc : Term String := db! "λλλ0(λ201)"

/-- The body of `X`, i.e. `X A` for any `A` (the first argument is discarded). -/
def Xc1 : Term String := db! "λλ0(λ201)"

/-- `X A B = λz. z (λw. B w z)`. -/
def Xc2 (B : Term String) : Term String :=
  .abs (.app (.bvar 0) (.abs (.app (.app B (.bvar 0)) (.bvar 1))))

theorem lc_Xc : LC Xc := by rw [← lcAt_iff_LC]; decide

theorem lc_Xc1 : LC Xc1 := by rw [← lcAt_iff_LC]; decide

theorem headStep_Xc {A : Term String} (hA : LC A) : HeadStep (.app Xc A) Xc1 :=
  HeadStep.beta lc_Xc hA

theorem headStep_Xc1 {B : Term String} (hB : LC B) : HeadStep (.app Xc1 B) (Xc2 B) :=
  HeadStep.beta lc_Xc1 hB

theorem lc_Xc2 {B : Term String} (hB : LC B) : LC (Xc2 B) := by
  refine .abs ∅ _ (fun x _ => ?_)
  simp only [open', openRec]
  rw [open_lc 1 (fvar x) B hB]
  refine .app (.fvar x) (.abs ∅ _ (fun y _ => ?_))
  simp only [open', openRec]
  rw [open_lc 0 (fvar y) B hB]
  exact .app (.app hB (.fvar y)) (.fvar x)

theorem headStep_Xc2 {B C : Term String} (hB : LC B) (hC : LC C) :
    HeadStep (.app (Xc2 B) C) (.app C (pairT B C)) := by
  have h := HeadStep.beta (M := (.app (.bvar 0) (.abs (.app (.app B (.bvar 0)) (.bvar 1)))))
    (N := C) (lc_Xc2 hB) hC
  have he : (Term.app (.bvar 0) (.abs (.app (.app B (.bvar 0)) (.bvar 1)))) ^ C
      = .app C (pairT B C) := by
    simp only [open', openRec, pairT]
    rw [open_lc 1 C B hB]
    simp
  rwa [he] at h


/-! ## Generalities -/

theorem lc_apps {M : Term String} (hM : LC M) :
    ∀ Γ : List (Term String), (∀ t ∈ Γ, LC t) → LC (apps M Γ)
  | [], _ => hM
  | a :: Γ, h =>
      lc_apps (.app hM (h a (by simp))) Γ (fun t ht => h t (by simp [ht]))

theorem normal_Xc : Relation.Normal FullBetaEta Xc := by
  rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide

theorem normal_Xc1 : Relation.Normal FullBetaEta Xc1 := by
  rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide

theorem hasHNF_Xc : HasHNF Xc :=
  hasHNF_of_normalizable lc_Xc ⟨Xc, Relation.ReflTransGen.refl, normal_Xc⟩

/-! ## Head steps with a stack of arguments -/

theorem headStep_Xc_apps {A : Term String} (hA : LC A) (Γ : List (Term String))
    (hΓ : ∀ t ∈ Γ, LC t) : HeadStep (apps Xc (A :: Γ)) (apps Xc1 Γ) :=
  headStep_apps (headStep_Xc hA) (by rintro ⟨⟩) Γ hΓ

theorem headStep_Xc1_apps {B : Term String} (hB : LC B) (Γ : List (Term String))
    (hΓ : ∀ t ∈ Γ, LC t) : HeadStep (apps Xc1 (B :: Γ)) (apps (Xc2 B) Γ) :=
  headStep_apps (headStep_Xc1 hB) (by rintro ⟨⟩) Γ hΓ

theorem headStep_Xc2_apps {B C : Term String} (hB : LC B) (hC : LC C)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStep (apps (Xc2 B) (C :: Γ)) (apps C (pairT B C :: Γ)) :=
  headStep_apps (headStep_Xc2 hB hC) (by rintro ⟨⟩) Γ hΓ

/-! ## The classes of admissible heads and arguments -/

/-- `AOk true M` (`QOk M`) says that `M` is an admissible *argument*: it is built from
`X₁`, `F` and `⟨·,·⟩` — or is already unsolvable with any stack.  `AOk false M`
(`ROk M`) additionally allows `M = X`.  The point of the distinction is that `X` erases
its argument, which is what makes a state terminate. -/
inductive AOk : Bool → Term String → Prop
  | t0 : AOk false Xc
  | t1 {b} : AOk b Xc1
  | div {b} {M : Term String} : LC M → NoHNFStack M → AOk b M
  | fa {b} {M : Term String} : AOk false M → AOk b (Xc2 M)
  | ga {b} {M N : Term String} : AOk false M → AOk true N → AOk b (pairT M N)

/-- Admissible arguments. -/
abbrev QOk (M : Term String) : Prop := AOk true M

/-- Admissible heads: admissible arguments together with `X` itself. -/
abbrev ROk (M : Term String) : Prop := AOk false M

theorem ROk_of_QOk {M : Term String} (h : QOk M) : ROk M := by
  cases h with
  | t1 => exact .t1
  | div h1 h2 => exact .div h1 h2
  | fa h => exact .fa h
  | ga h1 h2 => exact .ga h1 h2

theorem ROk.eq_Xc_or_QOk {M : Term String} (h : ROk M) : M = Xc ∨ QOk M := by
  cases h with
  | t0 => exact Or.inl rfl
  | t1 => exact Or.inr .t1
  | div h1 h2 => exact Or.inr (.div h1 h2)
  | fa h => exact Or.inr (.fa h)
  | ga h1 h2 => exact Or.inr (.ga h1 h2)

theorem lc_of_AOk {b : Bool} {M : Term String} (h : AOk b M) : LC M := by
  induction h with
  | t0 => exact lc_Xc
  | t1 => exact lc_Xc1
  | div h _ => exact h
  | fa _ ih => exact lc_Xc2 ih
  | ga _ _ ih1 ih2 => exact lc_pairT ih1 ih2

theorem QOk.ne_Xc {M : Term String} (h : QOk M) : M ≠ Xc := by
  cases h with
  | t1 => decide
  | div h1 h2 =>
      intro he
      exact h2 [] (by simp) (he ▸ hasHNF_Xc)
  | fa h => intro he; simp [Xc2, Xc] at he
  | ga h1 h2 => intro he; simp [pairT, Xc] at he

/-! ## The diverging states -/

/-- A diverging state `H B Δ… (F P) Γ…`: an admissible head `H`, at least one admissible
argument `B`, further admissible arguments `Δ`, then an argument of the special shape
`F P`, then an arbitrary stack `Γ`.  If the head is the eraser `X`, at least two
admissible arguments are required before `F P`. -/
def DivSt (M : Term String) : Prop :=
  ∃ (H B P : Term String) (Δ Γ : List (Term String)),
    ROk H ∧ QOk B ∧ (∀ t ∈ Δ, QOk t) ∧ ROk P ∧ (∀ t ∈ Γ, LC t) ∧
      (H = Xc → Δ ≠ []) ∧ M = apps H (B :: (Δ ++ Xc2 P :: Γ))

/-- Either a diverging state, or an already known term without head normal form. -/
def DivOrStuck (M : Term String) : Prop := DivSt M ∨ (LC M ∧ ¬ HasHNF M)

theorem stuck_step {M : Term String} (hlc : LC M) (h : ¬ HasHNF M) :
    ∃ N, Relation.TransGen HeadStep M N ∧ DivOrStuck N := by
  have hnf : ¬ HeadNF M := fun hn => h ⟨M, Relation.ReflTransGen.refl, hn⟩
  obtain ⟨N, hN⟩ := exists_headStep_of_not_headNF hlc hnf
  refine ⟨N, Relation.TransGen.single hN, Or.inr ⟨(HeadStep.regular hN).2, ?_⟩⟩
  intro hHN
  obtain ⟨P, hP, hnfP⟩ := hHN
  exact h ⟨P, Relation.ReflTransGen.head hN.toFullBeta hP, hnfP⟩

/-- **Every diverging state head reduces, in at least one step, to a diverging state**
(or is already known to have no head normal form). -/
theorem divOrStuck_step : ∀ M, DivOrStuck M →
    ∃ N, Relation.TransGen HeadStep M N ∧ DivOrStuck N := by
  rintro M (hdiv | ⟨hlc, hnf⟩)
  swap
  · exact stuck_step hlc hnf
  obtain ⟨H, B, P, Δ, Γ, hH, hB, hΔ, hP, hΓ, hne, rfl⟩ := hdiv
  have hlcB : LC B := lc_of_AOk hB
  have hlcP : LC P := lc_of_AOk hP
  have hlcΔ : ∀ t ∈ Δ, LC t := fun t ht => lc_of_AOk (hΔ t ht)
  have hlcTail : ∀ t ∈ Δ ++ Xc2 P :: Γ, LC t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hlcΔ t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact lc_Xc2 hlcP
    · exact hΓ t ht
  cases hH with
  | t0 =>
      -- head `X`: it erases `B`, and `Δ` is nonempty by hypothesis
      obtain ⟨B', Δ', rfl⟩ : ∃ B' Δ', Δ = B' :: Δ' := by
        cases Δ with
        | nil => exact absurd rfl (hne rfl)
        | cons a l => exact ⟨a, l, rfl⟩
      refine ⟨apps Xc1 (B' :: (Δ' ++ Xc2 P :: Γ)), Relation.TransGen.single ?_, Or.inl ?_⟩
      · exact headStep_Xc_apps hlcB _ (by simpa using hlcTail)
      · exact ⟨Xc1, B', P, Δ', Γ, .t1, hΔ B' (by simp), fun t ht => hΔ t (by simp [ht]),
          hP, hΓ, by intro h; exact absurd h (by decide), rfl⟩
  | @div _ M hlcM hnoM =>
      have hlcStack : ∀ t ∈ B :: (Δ ++ Xc2 P :: Γ), LC t := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hlcB
        · exact hlcTail t ht
      exact stuck_step (lc_apps hlcM _ hlcStack) (hnoM _ hlcStack)
  | t1 =>
      cases Δ with
      | cons B' Δ' =>
          refine ⟨apps (Xc2 B) (B' :: (Δ' ++ Xc2 P :: Γ)), Relation.TransGen.single ?_,
            Or.inl ?_⟩
          · exact headStep_Xc1_apps hlcB _ (by simpa using hlcTail)
          · exact ⟨Xc2 B, B', P, Δ', Γ, .fa (ROk_of_QOk hB), hΔ B' (by simp),
              fun t ht => hΔ t (by simp [ht]), hP, hΓ,
              by intro he; simp [Xc2, Xc] at he, rfl⟩
      | nil =>
          -- the four step loop
          set U : Term String := pairT B (Xc2 P)
          have hlcU : LC U := lc_pairT hlcB (lc_Xc2 hlcP)
          set W : Term String := pairT P U
          have hlcW : LC W := lc_pairT hlcP hlcU
          have s1 : HeadStep (apps Xc1 (B :: (Xc2 P :: Γ))) (apps (Xc2 B) (Xc2 P :: Γ)) :=
            headStep_Xc1_apps hlcB _ (by simpa using hlcTail)
          have s2 : HeadStep (apps (Xc2 B) (Xc2 P :: Γ)) (apps (Xc2 P) (U :: Γ)) :=
            headStep_Xc2_apps hlcB (lc_Xc2 hlcP) Γ hΓ
          have s3 : HeadStep (apps (Xc2 P) (U :: Γ)) (apps U (W :: Γ)) :=
            headStep_Xc2_apps hlcP hlcU Γ hΓ
          have s4 : HeadStep (apps U (W :: Γ)) (apps B (W :: Xc2 P :: Γ)) :=
            headStep_pairT_apps hlcB (lc_Xc2 hlcP) hlcW Γ hΓ
          refine ⟨apps B (W :: ([] ++ Xc2 P :: Γ)), ?_, Or.inl ?_⟩
          · simpa using (((Relation.TransGen.single s1).tail s2).tail s3).tail s4
          · exact ⟨B, W, P, [], Γ, ROk_of_QOk hB, .ga hP (.ga (ROk_of_QOk hB) (.fa hP)),
              by simp, hP, hΓ, fun he => absurd he hB.ne_Xc, rfl⟩
  | @fa _ M hM =>
      have hlcM : LC M := lc_of_AOk hM
      refine ⟨apps B (pairT M B :: (Δ ++ Xc2 P :: Γ)), Relation.TransGen.single ?_, Or.inl ?_⟩
      · exact headStep_Xc2_apps hlcM hlcB _ hlcTail
      · exact ⟨B, pairT M B, P, Δ, Γ, ROk_of_QOk hB, .ga hM hB, hΔ, hP, hΓ,
          fun he => absurd he hB.ne_Xc, rfl⟩
  | @ga _ M N hM hN =>
      have hlcM : LC M := lc_of_AOk hM
      have hlcN : LC N := lc_of_AOk hN
      refine ⟨apps M (B :: (N :: Δ ++ Xc2 P :: Γ)), Relation.TransGen.single ?_, Or.inl ?_⟩
      · exact headStep_pairT_apps hlcM hlcN hlcB _ hlcTail
      · exact ⟨M, B, P, N :: Δ, Γ, hM, hB, by
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hN
          · exact hΔ t ht, hP, hΓ, by simp, rfl⟩

theorem divSt_not_hasHNF {M : Term String} (h : DivSt M) : ¬ HasHNF M :=
  not_hasHNF_of_reaches divOrStuck_step Relation.ReflTransGen.refl (Or.inl h)

/-! ## The diverging products -/

/-- **`F A · F P` diverges, with any stack of arguments**, as soon as `A` is an admissible
argument (in particular `A ≠ X`). -/
theorem noHNFStack_Xc2_Xc2 {A P : Term String} (hA : QOk A) (hP : ROk P) :
    NoHNFStack (.app (Xc2 A) (Xc2 P)) := by
  intro Γ hΓ
  have hlcA : LC A := lc_of_AOk hA
  have hlcP : LC P := lc_of_AOk hP
  set U : Term String := pairT A (Xc2 P)
  have hlcU : LC U := lc_pairT hlcA (lc_Xc2 hlcP)
  set W : Term String := pairT P U
  have hlcW : LC W := lc_pairT hlcP hlcU
  have s1 : HeadStep (apps (Xc2 A) (Xc2 P :: Γ)) (apps (Xc2 P) (U :: Γ)) :=
    headStep_Xc2_apps hlcA (lc_Xc2 hlcP) Γ hΓ
  have s2 : HeadStep (apps (Xc2 P) (U :: Γ)) (apps U (W :: Γ)) :=
    headStep_Xc2_apps hlcP hlcU Γ hΓ
  have s3 : HeadStep (apps U (W :: Γ)) (apps A (W :: Xc2 P :: Γ)) :=
    headStep_pairT_apps hlcA (lc_Xc2 hlcP) hlcW Γ hΓ
  refine not_hasHNF_of_headStepStar
    (((Relation.ReflTransGen.single s1).tail s2).tail s3) (divSt_not_hasHNF ?_)
  exact ⟨A, W, P, [], Γ, ROk_of_QOk hA, .ga hP (.ga (ROk_of_QOk hA) (.fa hP)), by simp,
    hP, hΓ, fun he => absurd he hA.ne_Xc, by simp⟩

/-- If `N` diverges with any stack, so does `F A · N`. -/
theorem noHNFStack_Xc2_app {A N : Term String} (hA : LC A) (hN : LC N) (h : NoHNFStack N) :
    NoHNFStack (.app (Xc2 A) N) := by
  intro Γ hΓ
  refine not_hasHNF_of_headStepStar
    (Relation.ReflTransGen.single (headStep_Xc2_apps hA hN Γ hΓ)) (h (pairT A N :: Γ) ?_)
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact lc_pairT hA hN
  · exact hΓ t ht

/-- Diverging with any stack is inherited by applications. -/
theorem noHNFStack_app {M N : Term String} (h : NoHNFStack M) (hN : LC N) :
    NoHNFStack (.app M N) := by
  intro Γ hΓ
  refine h (N :: Γ) ?_
  intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hN, hΓ t ht]

/-! ## The converging products -/

theorem betaStar_Xc_app {N : Term String} (hN : LC N) : (Term.app Xc N) ↠βᶠ Xc1 :=
  Relation.ReflTransGen.single (headStep_Xc hN).toFullBeta

theorem betaStar_Xc1_app {N : Term String} (hN : LC N) : (Term.app Xc1 N) ↠βᶠ Xc2 N :=
  Relation.ReflTransGen.single (headStep_Xc1 hN).toFullBeta

/-- `F A · X ↠β X₁`. -/
theorem betaStar_Xc2_Xc {A : Term String} (hA : LC A) : (Term.app (Xc2 A) Xc) ↠βᶠ Xc1 := by
  refine Relation.ReflTransGen.head (headStep_Xc2 hA lc_Xc).toFullBeta ?_
  exact Relation.ReflTransGen.single (headStep_Xc (lc_pairT hA lc_Xc)).toFullBeta

/-- `F A · X₁ ↠β F ⟨A, X₁⟩`. -/
theorem betaStar_Xc2_Xc1 {A : Term String} (hA : LC A) :
    (Term.app (Xc2 A) Xc1) ↠βᶠ Xc2 (pairT A Xc1) := by
  refine Relation.ReflTransGen.head (headStep_Xc2 hA lc_Xc1).toFullBeta ?_
  exact Relation.ReflTransGen.single (headStep_Xc1 (lc_pairT hA lc_Xc1)).toFullBeta

/-- `F X · F P ↠β F (F P)`. -/
theorem betaStar_Xc2Xc_Xc2 {P : Term String} (hP : LC P) :
    (Term.app (Xc2 Xc) (Xc2 P)) ↠βᶠ Xc2 (Xc2 P) := by
  set U : Term String := pairT Xc (Xc2 P)
  have hlcU : LC U := lc_pairT lc_Xc (lc_Xc2 hP)
  set W : Term String := pairT P U
  have hlcW : LC W := lc_pairT hP hlcU
  have s1 : HeadStep (apps (Xc2 Xc) (Xc2 P :: [])) (apps (Xc2 P) (U :: [])) :=
    headStep_Xc2_apps lc_Xc (lc_Xc2 hP) [] (by simp)
  have s2 : HeadStep (apps (Xc2 P) (U :: [])) (apps U (W :: [])) :=
    headStep_Xc2_apps hP hlcU [] (by simp)
  have s3 : HeadStep (apps U (W :: [])) (apps Xc (W :: Xc2 P :: [])) :=
    headStep_pairT_apps lc_Xc (lc_Xc2 hP) hlcW [] (by simp)
  have s4 : HeadStep (apps Xc (W :: Xc2 P :: [])) (apps Xc1 (Xc2 P :: [])) :=
    headStep_Xc_apps hlcW _ (by intro t ht; simp at ht; exact ht ▸ lc_Xc2 hP)
  have s5 : HeadStep (apps Xc1 (Xc2 P :: [])) (apps (Xc2 (Xc2 P)) []) :=
    headStep_Xc1_apps (lc_Xc2 hP) [] (by simp)
  have := (((((Relation.ReflTransGen.single s1.toFullBeta).tail s2.toFullBeta).tail
    s3.toFullBeta).tail s4.toFullBeta).tail s5.toFullBeta)
  simpa [apps] using this

/-! ## The invariant -/

/-- The values: `X`, `X₁` and `F A` for an admissible `A`. -/
def Val (M : Term String) : Prop := M = Xc ∨ M = Xc1 ∨ ∃ A, ROk A ∧ M = Xc2 A

theorem ROk_of_Val {V : Term String} (h : Val V) : ROk V := by
  rcases h with rfl | rfl | ⟨A, hA, rfl⟩
  exacts [.t0, .t1, .fa hA]

theorem lc_of_Val {V : Term String} (h : Val V) : LC V := lc_of_AOk (ROk_of_Val h)

/-- The invariant of the clone generated by `X`. -/
def Good (M : Term String) : Prop := (∃ V, M ↠βηᶠ V ∧ Val V) ∨ Bad M

/-- **The invariant is closed under application.** -/
theorem good_app {M N : Term String} (hlcN : LC N) (hM : Good M) (hN : Good N) :
    Good (Term.app M N) := by
  rcases hM with ⟨V, hMV, hV⟩ | ⟨M', hMs, hlcM', hnoM'⟩
  swap
  · exact Or.inr ⟨Term.app M' N, FullBetaEta.steps_app_l_cong hMs hlcN, .app hlcM' hlcN,
      noHNFStack_app hnoM' hlcN⟩
  have hstep : Term.app M N ↠βηᶠ Term.app V N := FullBetaEta.steps_app_l_cong hMV hlcN
  have hlcV : LC V := lc_of_Val hV
  rcases hV with rfl | rfl | ⟨A, hA, rfl⟩
  · -- `V = X`: the argument is discarded
    exact Or.inl ⟨Xc1, .trans hstep (FullBetaEta.from_beta _ _ (betaStar_Xc_app hlcN)),
      Or.inr (Or.inl rfl)⟩
  · -- `V = X₁`
    rcases hN with ⟨W, hNW, hW⟩ | ⟨N', hNs, hlcN', hnoN'⟩
    · refine Or.inl ⟨Xc2 W, ?_, Or.inr (Or.inr ⟨W, ROk_of_Val hW, rfl⟩)⟩
      exact .trans (.trans hstep (FullBetaEta.steps_app_r_cong hNW lc_Xc1))
        (FullBetaEta.from_beta _ _ (betaStar_Xc1_app (lc_of_Val hW)))
    · refine Or.inl ⟨Xc2 N', ?_, Or.inr (Or.inr ⟨N', .div hlcN' hnoN', rfl⟩)⟩
      exact .trans (.trans hstep (FullBetaEta.steps_app_r_cong hNs lc_Xc1))
        (FullBetaEta.from_beta _ _ (betaStar_Xc1_app hlcN'))
  · -- `V = F A`
    have hlcA : LC A := lc_of_AOk hA
    rcases hN with ⟨W, hNW, hW⟩ | ⟨N', hNs, hlcN', hnoN'⟩
    · have hstep2 : Term.app M N ↠βηᶠ Term.app (Xc2 A) W :=
        .trans hstep (FullBetaEta.steps_app_r_cong hNW hlcV)
      rcases hW with rfl | rfl | ⟨P, hP, rfl⟩
      · exact Or.inl ⟨Xc1, .trans hstep2 (FullBetaEta.from_beta _ _ (betaStar_Xc2_Xc hlcA)),
          Or.inr (Or.inl rfl)⟩
      · exact Or.inl ⟨Xc2 (pairT A Xc1),
          .trans hstep2 (FullBetaEta.from_beta _ _ (betaStar_Xc2_Xc1 hlcA)),
          Or.inr (Or.inr ⟨pairT A Xc1, .ga hA .t1, rfl⟩)⟩
      · rcases hA.eq_Xc_or_QOk with rfl | hQA
        · exact Or.inl ⟨Xc2 (Xc2 P),
            .trans hstep2 (FullBetaEta.from_beta _ _ (betaStar_Xc2Xc_Xc2 (lc_of_AOk hP))),
            Or.inr (Or.inr ⟨Xc2 P, .fa hP, rfl⟩)⟩
        · exact Or.inr ⟨Term.app (Xc2 A) (Xc2 P), hstep2,
            .app hlcV (lc_Xc2 (lc_of_AOk hP)), noHNFStack_Xc2_Xc2 hQA hP⟩
    · refine Or.inr ⟨Term.app (Xc2 A) N', ?_, .app hlcV hlcN',
        noHNFStack_Xc2_app hlcA hlcN' hnoN'⟩
      exact .trans hstep (FullBetaEta.steps_app_r_cong hNs hlcV)

theorem lc_of_gen {M : Term String} (h : Gen Xc M) : LC M := by
  refine genfinset_lc h ?_
  intro t ht
  simp only [List.mem_singleton] at ht
  exact ht ▸ lc_Xc

/-- **Every applicative combination of `X` satisfies the invariant.** -/
theorem gen_good {M : Term String} (h : Gen Xc M) : Good M := by
  induction h with
  | base hmem =>
      rename_i a
      simp only [List.mem_singleton] at hmem
      exact Or.inl ⟨a, Relation.ReflTransGen.refl, Or.inl hmem⟩
  | @app a b ha hb iha ihb => exact good_app (lc_of_gen hb) iha ihb

/-! ## `λλλ0(λ201)` is not a one-point basis -/

/-- No value is βη-equal to `I`. -/
theorem val_not_betaEtaStar_I {V : Term String} (hV : Val V) : ¬ (V ↠βηᶠ I) := by
  intro h
  rcases hV with rfl | rfl | ⟨A, hA, rfl⟩
  · exact absurd (normal_Xc.reflTransGen_eq h) (by decide)
  · exact absurd (normal_Xc1.reflTransGen_eq h) (by decide)
  · -- `F A · X ↠β X₁`, while `I · X ↠β X`
    have hlcA : LC A := lc_of_AOk hA
    have h1 : (Term.app (Xc2 A) Xc) ↠βηᶠ Xc1 :=
      FullBetaEta.from_beta _ _ (betaStar_Xc2_Xc hlcA)
    have h2 : (Term.app (Xc2 A) Xc) ↠βηᶠ Xc := by
      refine .trans (FullBetaEta.steps_app_l_cong h lc_Xc) ?_
      refine FullBetaEta.from_beta _ _ (Relation.ReflTransGen.single ?_)
      have hI : HeadStep (Term.app I Xc) Xc := by
        have h := HeadStep.beta (M := Term.bvar 0) (N := Xc)
          (by rw [← lcAt_iff_LC]; decide) lc_Xc
        simpa [I, open', openRec] using h
      exact hI.toFullBeta
    obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta h1 h2
    exact absurd ((normal_Xc1.reflTransGen_eq hZ1).trans (normal_Xc.reflTransGen_eq hZ2).symm)
      (by decide)

/-- **No applicative combination of `λλλ0(λ201)` βη-reduces to `I = λx. x`.** -/
theorem gen_not_betaEtaStar_I {M : Term String} (hM : Gen Xc M) : ¬ (M ↠βηᶠ I) := by
  intro h
  rcases gen_good hM with ⟨V, hMV, hV⟩ | ⟨M', hMs, hlcM', hnoM'⟩
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMV h
    exact val_not_betaEtaStar_I hV (normal_Icomb.reflTransGen_eq hZ2 ▸ hZ1)
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMs h
    have hM'I : M' ↠βηᶠ I := normal_Icomb.reflTransGen_eq hZ2 ▸ hZ1
    exact hnoM' [] (by simp) (hasHNF_of_normalizable hlcM' ⟨I, hM'I, normal_Icomb⟩)

/-- No value is βη-equal to `K`. -/
theorem val_not_betaEtaStar_K {V : Term String} (hV : Val V) : ¬ (V ↠βηᶠ K) := by
  intro h
  have hnormalKX : Relation.Normal FullBetaEta (Term.abs Xc) := by
    rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide
  have hKX : HeadStep (Term.app K Xc) (Term.abs Xc) := by
    have h := HeadStep.beta (M := Term.abs (Term.bvar 1)) (N := Xc)
      (by rw [← lcAt_iff_LC]; decide) lc_Xc
    simpa [K, open', openRec] using h
  rcases hV with rfl | rfl | ⟨A, hA, rfl⟩
  · exact absurd (normal_Xc.reflTransGen_eq h) (by decide)
  · exact absurd (normal_Xc1.reflTransGen_eq h) (by decide)
  · -- `F A · X ↠β X₁`, while `K · X ↠β λ_. X`
    have hlcA : LC A := lc_of_AOk hA
    have h1 : (Term.app (Xc2 A) Xc) ↠βηᶠ Xc1 :=
      FullBetaEta.from_beta _ _ (betaStar_Xc2_Xc hlcA)
    have h2 : (Term.app (Xc2 A) Xc) ↠βηᶠ Term.abs Xc :=
      .trans (FullBetaEta.steps_app_l_cong h lc_Xc)
        (FullBetaEta.from_beta _ _ (Relation.ReflTransGen.single hKX.toFullBeta))
    obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta h1 h2
    exact absurd ((normal_Xc1.reflTransGen_eq hZ1).trans (hnormalKX.reflTransGen_eq hZ2).symm)
      (by decide)

/-- **No applicative combination of `λλλ0(λ201)` βη-reduces to `K = λx y. x`.** -/
theorem gen_not_betaEtaStar_K {M : Term String} (hM : Gen Xc M) : ¬ (M ↠βηᶠ K) := by
  intro h
  rcases gen_good hM with ⟨V, hMV, hV⟩ | ⟨M', hMs, hlcM', hnoM'⟩
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMV h
    exact val_not_betaEtaStar_K hV (normal_K.reflTransGen_eq hZ2 ▸ hZ1)
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMs h
    have hM'K : M' ↠βηᶠ K := normal_K.reflTransGen_eq hZ2 ▸ hZ1
    exact hnoM' [] (by simp) (hasHNF_of_normalizable hlcM' ⟨K, hM'K, normal_K⟩)

/-- **No applicative combination of `λλλ0(λ201)` is βη-equal to `I = λx. x`.** -/
theorem gen_not_eqv_I {M : Term String} (hM : Gen Xc M) :
    ¬ Relation.EqvGen FullBetaEta M I := fun h =>
  gen_not_betaEtaStar_I hM
    ((reflTransGen_iff_eqvGen_of_normal (by decide) (by decide)).mpr h)

/-- **No applicative combination of `λλλ0(λ201)` is βη-equal to `K = λx y. x`.** -/
theorem gen_not_eqv_K {M : Term String} (hM : Gen Xc M) :
    ¬ Relation.EqvGen FullBetaEta M K := fun h =>
  gen_not_betaEtaStar_K hM
    ((reflTransGen_iff_eqvGen_of_normal (by decide) (by decide)).mpr h)

/-- **`X = λλλ0(λ201)` is not a one-point basis for the λ-calculus under βη.** -/
theorem not_basis_lamlamlam0lam201 : not_basis (db! "λλλ0(λ201)") := by
  refine ⟨I, by rw [← lcAt_iff_LC]; decide, by decide, ?_⟩
  intro t ht hred
  exact gen_not_betaEtaStar_I ht hred

end LamLamLam0Lam201

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
