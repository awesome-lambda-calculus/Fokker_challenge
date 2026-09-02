import FokkerChallenge.PairT
import FokkerChallenge.BetaCheck
import FokkerChallenge.FamousCombinator

/-!
# `λλλ0(λ102)` is not a one-point basis

The term

```
Y = λλλ0(λ102) = λx y z. z (λw. z w y)
```

is one of the terms of `undecided_terms.json` whose one-point-basis status was open.
This file settles it in the negative: **no applicative combination of `Y` βη-reduces to
`I = λx. x`** (`gen_not_betaEtaStar_I`), so `Y` is not a one-point basis
(`not_basis_lamlamlam0lam102`).

## The machine

Writing `Y₁ = λ y z. z (λw. z w y)` (`Yc1`), `G B = λz. z (λw. z w B)` (`Yc2`) and
`⟨R,S⟩ = λw. R w S` (`pairT`, from `FokkerChallenge.PairT`), the head reductions
of `Y` are

```
Y A Γ       ⭢h  Y₁ Γ            Y₁ B Γ    ⭢h  G B Γ
G B C Γ     ⭢h  C ⟨C,B⟩ Γ       ⟨R,S⟩ U Γ ⭢h  R U S Γ
```

so a combination of `Y`, applied to a stack of arguments, evolves like a little stack
machine whose "heads" are `Y`, `Y₁`, `G B` and `⟨R,S⟩`.  Note the third rule: the argument
`C` becomes the new head, and the pair it creates has `C` — not `B` — as its first
component.  This is the only difference from the machine of
`FokkerChallenge.NotBasisLamLamLam0Lam201`, and it is what makes the divergence argument
below simpler: the second components of the pairs are only ever pushed onto the stack, so
they never come to the head, and the eraser `Y` in that position is harmless.

## The values

Every applicative combination of `Y` either βη-reduces to one of

```
Y,   Y₁,   G A     (`Val`)
```

or is unsolvable in a strong sense (`Bad`: it βη-reduces to a term which, with **any**
stack of further arguments, has no head normal form).  This dichotomy (`Good`) is closed
under application (`good_app`), which is the heart of the file.  The multiplication rules
are

```
Y · N       ↠  Y₁                    Y₁ · N      ↠  G N
G A · Y     ↠  Y₁                    G A · Y₁    ↠  G ⟨Y₁,A⟩
G A · G P   diverges
```

## The divergence

`G A · G P` head reduces to `G P ⟨G P, A⟩`, which belongs to the family (`DivSt`) of states

```
H W Γ…      with   H = G P  or  H a `Chain P` pair,   W a `Chain P` pair
```

where `Chain P` is the class of pairs `⟨⟨…⟨G P, N₁⟩…⟩, N_k⟩` whose first components
descend to `G P` (`Chain`); `Γ` is an arbitrary stack.  Both machine rules keep a state in
this family, and each takes at least one step (`divSt_step`), so by the head normalization
theorem of `FokkerChallenge.EnhancedCslib.HeadSN` no member of the family has a head
normal form.  Carrying the arbitrary stack `Γ` is what makes unsolvability closed under
application.

## Conclusion

`Y` and `Y₁` are βη-normal and differ from `I` and `K`, and `G A · Y ↠β Y₁` rules out
`G A` (it would force `Y₁ = Y`, resp. `Y₁ = λ_. Y`).  Unsolvable terms have no βη-normal
form at all.  Hence no combination of `Y` βη-reduces to `I` (or to `K`).
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

namespace LamLamLam0Lam102

/-! ## The terms -/

/-- `Y = λλλ0(λ102) = λx y z. z (λw. z w y)`. -/
def Yc : Term String := db! "λλλ0(λ102)"

/-- The body of `Y`, i.e. `Y A` for any `A` (the first argument is discarded). -/
def Yc1 : Term String := db! "λλ0(λ102)"

/-- `G B = Y A B = λz. z (λw. z w B)`. -/
def Yc2 (B : Term String) : Term String :=
  .abs (.app (.bvar 0) (.abs (.app (.app (.bvar 1) (.bvar 0)) B)))

/-! ## Local closure -/

theorem lc_Yc : LC Yc := by rw [← lcAt_iff_LC]; decide

theorem lc_Yc1 : LC Yc1 := by rw [← lcAt_iff_LC]; decide

theorem lc_Yc2 {B : Term String} (hB : LC B) : LC (Yc2 B) := by
  refine .abs ∅ _ (fun x _ => ?_)
  simp only [open', openRec]
  rw [open_lc 1 (fvar x) B hB]
  refine .app (.fvar x) (.abs ∅ _ (fun y _ => ?_))
  simp only [open', openRec]
  rw [open_lc 0 (fvar y) B hB]
  exact .app (.app (.fvar x) (.fvar y)) hB

theorem lc_apps {M : Term String} (hM : LC M) :
    ∀ Γ : List (Term String), (∀ t ∈ Γ, LC t) → LC (multiApp M Γ)
  | [], _ => hM
  | a :: Γ, h =>
      lc_apps (.app hM (h a (by simp))) Γ (fun t ht => h t (by simp [ht]))

/-! ## Normality -/

theorem normal_Yc : Relation.Normal FullBetaEta Yc := by
  rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide

theorem normal_Yc1 : Relation.Normal FullBetaEta Yc1 := by
  rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide

/-! ## The basic head steps -/

theorem headStep_Yc {A : Term String} (hA : LC A) : HeadStep (.app Yc A) Yc1 :=
  HeadStep.beta lc_Yc hA

theorem headStep_Yc1 {B : Term String} (hB : LC B) : HeadStep (.app Yc1 B) (Yc2 B) :=
  HeadStep.beta lc_Yc1 hB

/-- `G B C ⭢h C ⟨C,B⟩`. -/
theorem headStep_Yc2 {B C : Term String} (hB : LC B) (hC : LC C) :
    HeadStep (.app (Yc2 B) C) (.app C (pairT C B)) := by
  have h := HeadStep.beta (M := (.app (.bvar 0) (.abs (.app (.app (.bvar 1) (.bvar 0)) B))))
    (N := C) (lc_Yc2 hB) hC
  have he : (Term.app (.bvar 0) (.abs (.app (.app (.bvar 1) (.bvar 0)) B))) ^ C
      = .app C (pairT C B) := by
    simp only [open', openRec, pairT]
    rw [open_lc 1 C B hB]
    simp
  rwa [he] at h

/-! ## Head steps with a stack of arguments -/

theorem headStep_Yc_apps {A : Term String} (hA : LC A) (Γ : List (Term String))
    (hΓ : ∀ t ∈ Γ, LC t) : HeadStep (multiApp Yc (A :: Γ)) (multiApp Yc1 Γ) :=
  headStep_apps (headStep_Yc hA) (by rintro ⟨⟩) Γ hΓ

theorem headStep_Yc1_apps {B : Term String} (hB : LC B) (Γ : List (Term String))
    (hΓ : ∀ t ∈ Γ, LC t) : HeadStep (multiApp Yc1 (B :: Γ)) (multiApp (Yc2 B) Γ) :=
  headStep_apps (headStep_Yc1 hB) (by rintro ⟨⟩) Γ hΓ

theorem headStep_Yc2_apps {B C : Term String} (hB : LC B) (hC : LC C)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStep (multiApp (Yc2 B) (C :: Γ)) (multiApp C (pairT C B :: Γ)) :=
  headStep_apps (headStep_Yc2 hB hC) (by rintro ⟨⟩) Γ hΓ

/-! ## The diverging states -/

/-- The pairs whose chain of first components descends to `G P`:
`⟨G P, N₁⟩`, `⟨⟨G P, N₁⟩, N₂⟩`, … -/
inductive Chain (P : Term String) : Term String → Prop
  | base {N : Term String} : LC N → Chain P (pairT (Yc2 P) N)
  | step {W N : Term String} : Chain P W → LC N → Chain P (pairT W N)

theorem lc_of_Chain {P W : Term String} (hP : LC P) (h : Chain P W) : LC W := by
  induction h with
  | base hN => exact lc_pairT (lc_Yc2 hP) hN
  | step _ hN ih => exact lc_pairT ih hN

/-- A diverging state `H W Γ…`: the head `H` is either `G P` or a `Chain P` pair, the
first argument `W` is a `Chain P` pair, and `Γ` is an arbitrary stack. -/
def DivSt (M : Term String) : Prop :=
  ∃ (P H W : Term String) (Γ : List (Term String)),
    LC P ∧ (H = Yc2 P ∨ Chain P H) ∧ Chain P W ∧ (∀ t ∈ Γ, LC t) ∧ M = multiApp H (W :: Γ)

/-- **Every diverging state head reduces, in at least one step, to a diverging state.** -/
theorem divSt_step : ∀ M, DivSt M → ∃ N, Relation.TransGen HeadStep M N ∧ DivSt N := by
  rintro M ⟨P, H, W, Γ, hP, hH, hW, hΓ, rfl⟩
  have hlcW : LC W := lc_of_Chain hP hW
  rcases hH with rfl | hHchain
  · -- head `G P`: the argument `W` becomes the head and a new link is added
    refine ⟨multiApp W (pairT W P :: Γ), Relation.TransGen.single (headStep_Yc2_apps hP hlcW Γ hΓ),
      ?_⟩
    exact ⟨P, W, pairT W P, Γ, hP, Or.inr hW, .step hW hP, hΓ, rfl⟩
  · -- head a `Chain P` pair: the pair rule peels one link off the head
    cases hHchain with
    | @base N hN =>
        refine ⟨multiApp (Yc2 P) (W :: N :: Γ),
          Relation.TransGen.single (headStep_pairT_apps (lc_Yc2 hP) hN hlcW Γ hΓ), ?_⟩
        refine ⟨P, Yc2 P, W, N :: Γ, hP, Or.inl rfl, hW, ?_, rfl⟩
        intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hN, hΓ t ht]
    | @step W' N hW' hN =>
        refine ⟨multiApp W' (W :: N :: Γ),
          Relation.TransGen.single
            (headStep_pairT_apps (lc_of_Chain hP hW') hN hlcW Γ hΓ), ?_⟩
        refine ⟨P, W', W, N :: Γ, hP, Or.inr hW', hW, ?_, rfl⟩
        intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hN, hΓ t ht]

theorem divSt_not_hasHNF {M : Term String} (h : DivSt M) : ¬ HasHNF M :=
  not_hasHNF_of_reaches divSt_step Relation.ReflTransGen.refl h

/-! ## The diverging products -/

/-- **`G A · G P` diverges, with any stack of arguments.** -/
theorem noHNFStack_Yc2_Yc2 {A P : Term String} (hA : LC A) (hP : LC P) :
    NoHNFStack (.app (Yc2 A) (Yc2 P)) := by
  intro Γ hΓ
  refine not_hasHNF_of_headStepStar
    (Relation.ReflTransGen.single (headStep_Yc2_apps hA (lc_Yc2 hP) Γ hΓ))
    (divSt_not_hasHNF ?_)
  exact ⟨P, Yc2 P, pairT (Yc2 P) A, Γ, hP, Or.inl rfl, .base hA, hΓ, rfl⟩

/-- If `N` diverges with any stack, so does `G A · N`. -/
theorem noHNFStack_Yc2_app {A N : Term String} (hA : LC A) (hN : LC N) (h : NoHNFStack N) :
    NoHNFStack (.app (Yc2 A) N) := by
  intro Γ hΓ
  refine not_hasHNF_of_headStepStar
    (Relation.ReflTransGen.single (headStep_Yc2_apps hA hN Γ hΓ)) (h (pairT N A :: Γ) ?_)
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact lc_pairT hN hA
  · exact hΓ t ht

/-- Diverging with any stack is inherited by applications. -/
theorem noHNFStack_app {M N : Term String} (h : NoHNFStack M) (hN : LC N) :
    NoHNFStack (.app M N) := by
  intro Γ hΓ
  refine h (N :: Γ) ?_
  intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hN, hΓ t ht]

/-! ## The converging products -/

theorem betaStar_Yc_app {N : Term String} (hN : LC N) : (Term.app Yc N) ↠βᶠ Yc1 :=
  Relation.ReflTransGen.single (headStep_Yc hN).toFullBeta

theorem betaStar_Yc1_app {N : Term String} (hN : LC N) : (Term.app Yc1 N) ↠βᶠ Yc2 N :=
  Relation.ReflTransGen.single (headStep_Yc1 hN).toFullBeta

/-- `G A · Y ↠β Y₁`. -/
theorem betaStar_Yc2_Yc {A : Term String} (hA : LC A) : (Term.app (Yc2 A) Yc) ↠βᶠ Yc1 := by
  refine Relation.ReflTransGen.head (headStep_Yc2 hA lc_Yc).toFullBeta ?_
  exact Relation.ReflTransGen.single (headStep_Yc (lc_pairT lc_Yc hA)).toFullBeta

/-- `G A · Y₁ ↠β G ⟨Y₁, A⟩`. -/
theorem betaStar_Yc2_Yc1 {A : Term String} (hA : LC A) :
    (Term.app (Yc2 A) Yc1) ↠βᶠ Yc2 (pairT Yc1 A) := by
  refine Relation.ReflTransGen.head (headStep_Yc2 hA lc_Yc1).toFullBeta ?_
  exact Relation.ReflTransGen.single (headStep_Yc1 (lc_pairT lc_Yc1 hA)).toFullBeta

/-! ## The invariant -/

/-- The values: `Y`, `Y₁` and `G A`. -/
def Val (M : Term String) : Prop := M = Yc ∨ M = Yc1 ∨ ∃ A, LC A ∧ M = Yc2 A

theorem lc_of_Val {V : Term String} (h : Val V) : LC V := by
  rcases h with rfl | rfl | ⟨A, hA, rfl⟩
  exacts [lc_Yc, lc_Yc1, lc_Yc2 hA]

/-- The invariant of the clone generated by `Y`. -/
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
  · -- `V = Y`: the argument is discarded
    exact Or.inl ⟨Yc1, .trans hstep (Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc_app hlcN)),
      Or.inr (Or.inl rfl)⟩
  · -- `V = Y₁`
    rcases hN with ⟨W, hNW, hW⟩ | ⟨N', hNs, hlcN', hnoN'⟩
    · refine Or.inl ⟨Yc2 W, ?_, Or.inr (Or.inr ⟨W, lc_of_Val hW, rfl⟩)⟩
      exact .trans (.trans hstep (FullBetaEta.steps_app_r_cong hNW lc_Yc1))
        (Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc1_app (lc_of_Val hW)))
    · refine Or.inl ⟨Yc2 N', ?_, Or.inr (Or.inr ⟨N', hlcN', rfl⟩)⟩
      exact .trans (.trans hstep (FullBetaEta.steps_app_r_cong hNs lc_Yc1))
        (Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc1_app hlcN'))
  · -- `V = G A`
    rcases hN with ⟨W, hNW, hW⟩ | ⟨N', hNs, hlcN', hnoN'⟩
    · have hstep2 : Term.app M N ↠βηᶠ Term.app (Yc2 A) W :=
        .trans hstep (FullBetaEta.steps_app_r_cong hNW hlcV)
      rcases hW with rfl | rfl | ⟨P, hP, rfl⟩
      · exact Or.inl ⟨Yc1, .trans hstep2 (Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc2_Yc hA)),
          Or.inr (Or.inl rfl)⟩
      · exact Or.inl ⟨Yc2 (pairT Yc1 A),
          .trans hstep2 (Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc2_Yc1 hA)),
          Or.inr (Or.inr ⟨pairT Yc1 A, lc_pairT lc_Yc1 hA, rfl⟩)⟩
      · exact Or.inr ⟨Term.app (Yc2 A) (Yc2 P), hstep2, .app hlcV (lc_Yc2 hP),
          noHNFStack_Yc2_Yc2 hA hP⟩
    · refine Or.inr ⟨Term.app (Yc2 A) N', ?_, .app hlcV hlcN',
        noHNFStack_Yc2_app hA hlcN' hnoN'⟩
      exact .trans hstep (FullBetaEta.steps_app_r_cong hNs hlcV)

theorem lc_of_gen {M : Term String} (h : Gen Yc M) : LC M := by
  refine genfinset_lc h ?_
  intro t ht
  simp only [List.mem_singleton] at ht
  exact ht ▸ lc_Yc

/-- **Every applicative combination of `Y` satisfies the invariant.** -/
theorem gen_good {M : Term String} (h : Gen Yc M) : Good M := by
  induction h with
  | base hmem =>
      rename_i a
      simp only [List.mem_singleton] at hmem
      exact Or.inl ⟨a, Relation.ReflTransGen.refl, Or.inl hmem⟩
  | @app a b ha hb iha ihb => exact good_app (lc_of_gen hb) iha ihb

/-! ## `λλλ0(λ102)` is not a one-point basis -/

/-- No value is βη-equal to `I`. -/
theorem val_not_betaEtaStar_I {V : Term String} (hV : Val V) : ¬ (V ↠βηᶠ I) := by
  intro h
  rcases hV with rfl | rfl | ⟨A, hA, rfl⟩
  · exact absurd (normal_Yc.reflTransGen_eq h) (by decide)
  · exact absurd (normal_Yc1.reflTransGen_eq h) (by decide)
  · -- `G A · Y ↠β Y₁`, while `I · Y ↠β Y`
    have h1 : (Term.app (Yc2 A) Yc) ↠βηᶠ Yc1 :=
      Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc2_Yc hA)
    have h2 : (Term.app (Yc2 A) Yc) ↠βηᶠ Yc := by
      refine .trans (FullBetaEta.steps_app_l_cong h lc_Yc) ?_
      refine Relation.ReflTransGen.mono le_sup_left _ _ (Relation.ReflTransGen.single ?_)
      have hI : HeadStep (Term.app I Yc) Yc := by
        have h := HeadStep.beta (M := Term.bvar 0) (N := Yc)
          (by rw [← lcAt_iff_LC]; decide) lc_Yc
        simpa [I, open', openRec] using h
      exact hI.toFullBeta
    obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta h1 h2
    exact absurd ((normal_Yc1.reflTransGen_eq hZ1).trans (normal_Yc.reflTransGen_eq hZ2).symm)
      (by decide)

/-- **No applicative combination of `λλλ0(λ102)` βη-reduces to `I = λx. x`.** -/
theorem gen_not_betaEtaStar_I {M : Term String} (hM : Gen Yc M) : ¬ (M ↠βηᶠ I) := by
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
  have hnormalKY : Relation.Normal FullBetaEta (Term.abs Yc) := by
    rw [← normal_fullBetaEta_iff_no_beta_eta_redex]; decide
  have hKY : HeadStep (Term.app K Yc) (Term.abs Yc) := by
    have h := HeadStep.beta (M := Term.abs (Term.bvar 1)) (N := Yc)
      (by rw [← lcAt_iff_LC]; decide) lc_Yc
    simpa [K, open', openRec] using h
  rcases hV with rfl | rfl | ⟨A, hA, rfl⟩
  · exact absurd (normal_Yc.reflTransGen_eq h) (by decide)
  · exact absurd (normal_Yc1.reflTransGen_eq h) (by decide)
  · -- `G A · Y ↠β Y₁`, while `K · Y ↠β λ_. Y`
    have h1 : (Term.app (Yc2 A) Yc) ↠βηᶠ Yc1 :=
      Relation.ReflTransGen.mono le_sup_left _ _ (betaStar_Yc2_Yc hA)
    have h2 : (Term.app (Yc2 A) Yc) ↠βηᶠ Term.abs Yc :=
      .trans (FullBetaEta.steps_app_l_cong h lc_Yc)
        (Relation.ReflTransGen.mono le_sup_left _ _ (Relation.ReflTransGen.single hKY.toFullBeta))
    obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta h1 h2
    exact absurd ((normal_Yc1.reflTransGen_eq hZ1).trans (hnormalKY.reflTransGen_eq hZ2).symm)
      (by decide)

/-- **No applicative combination of `λλλ0(λ102)` βη-reduces to `K = λx y. x`.** -/
theorem gen_not_betaEtaStar_K {M : Term String} (hM : Gen Yc M) : ¬ (M ↠βηᶠ K) := by
  intro h
  rcases gen_good hM with ⟨V, hMV, hV⟩ | ⟨M', hMs, hlcM', hnoM'⟩
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMV h
    exact val_not_betaEtaStar_K hV (normal_K.reflTransGen_eq hZ2 ▸ hZ1)
  · obtain ⟨Z, hZ1, hZ2⟩ := confluent_beta_eta hMs h
    have hM'K : M' ↠βηᶠ K := normal_K.reflTransGen_eq hZ2 ▸ hZ1
    exact hnoM' [] (by simp) (hasHNF_of_normalizable hlcM' ⟨K, hM'K, normal_K⟩)

/-- **No applicative combination of `λλλ0(λ102)` is βη-equal to `I = λx. x`.** -/
theorem gen_not_eqv_I {M : Term String} (hM : Gen Yc M) :
    ¬ Relation.EqvGen FullBetaEta M I := fun h =>
  gen_not_betaEtaStar_I hM
    ((reflTransGen_iff_eqvGen_of_normal (by decide) (by decide)).mpr h)

/-- **No applicative combination of `λλλ0(λ102)` is βη-equal to `K = λx y. x`.** -/
theorem gen_not_eqv_K {M : Term String} (hM : Gen Yc M) :
    ¬ Relation.EqvGen FullBetaEta M K := fun h =>
  gen_not_betaEtaStar_K hM
    ((reflTransGen_iff_eqvGen_of_normal (by decide) (by decide)).mpr h)

/-- **`Y = λλλ0(λ102)` is not a one-point basis for the λ-calculus under βη.** -/
theorem not_basis_lamlamlam0lam102 : not_basis (db! "λλλ0(λ102)") := by
  refine ⟨I, by rw [← lcAt_iff_LC]; decide, by decide, ?_⟩
  intro t ht hred
  exact gen_not_betaEtaStar_I ht hred

end LamLamLam0Lam102

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
