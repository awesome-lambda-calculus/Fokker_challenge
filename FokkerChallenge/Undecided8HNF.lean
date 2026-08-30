import FokkerChallenge.DBNotation
import FokkerChallenge.EnhancedCslib.HeadSN
import FokkerChallenge.EnhancedCslib.GenFinset

/-!
# `λλλ0(λ201)` does **not** always have a head normal form

The term

```
X = λλλ0(λ201) = λx y z. z (λw. y w z)
```

is one of the four terms of `undecided_terms.json` whose one-point-basis status is open.
This file answers the question whether *every applicative combination of `X` has a head
normal form* — equivalently, whether every such combination is solvable — in the
**negative**:

* `hnfDivergeStart = X X (X X) (X X X)` is an applicative combination of `X`
  (`hnfDivergeStart_gen`) whose head reduction never terminates
  (`hnfDivergeStart_not_hasHNF`), so it has no head normal form;
* `exists_gen_not_hasHNF` / `not_forall_gen_hasHNF` are the summary statements.

## The divergence

Write `⟨B,C⟩ := λw. B w C` (`pairT`), `P := X X X` and set

```
T 0       = ⟨X X, P⟩,      T (n+1) = ⟨T n, P⟩.
```

The head reduction of `X` obeys two rules, both proved below:

```
X A B C Γ  ↠h  C ⟨B,C⟩ Γ         (`headStepStar_Xc3`)
⟨B,C⟩ U Γ  ⭢h  B U C Γ           (`headStep_pairT`)
```

(the first one because `X` discards its first argument).  With them, the "state"

```
S n Γ := T n ⟨X, T n⟩ Γ
```

head-reduces to `S (n+1) (Pⁿ Γ)` in `n + 8` steps (`headTransGen_state`), so head
reduction from `S 0 []` never terminates, and `X X (X X) (X X X) ↠h S 0 []`
(`hnfDivergeStart_headStepStar_state`).  By the head normalization theorem of
`FokkerChallenge.EnhancedCslib.HeadSN` a term whose head reduction diverges has no head
normal form.

Note that this is *not* an obstruction to `X` being a one-point basis — on the contrary,
a one-point basis must have unsolvable combinations.  What it does show is that the
"every combination has a head normal form" route to a negative answer is closed for `X`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## The terms -/

/-- `X = λλλ0(λ201) = λx y z. z (λw. y w z)`. -/
def Xc : Term String := db! "λλλ0(λ201)"

/-- The body of `X`, i.e. `X A` for any `A` (the first argument is discarded). -/
def Xc1 : Term String := db! "λλ0(λ201)"

/-- `X A B = λz. z (λw. B w z)`. -/
def Xc2 (B : Term String) : Term String :=
  .abs (.app (.bvar 0) (.abs (.app (.app B (.bvar 0)) (.bvar 1))))

/-- `⟨B,C⟩ = λw. B w C`. -/
def pairT (B C : Term String) : Term String := .abs (.app (.app B (.bvar 0)) C)

/-- `P = X X X`. -/
def Pc : Term String := .app (.app Xc Xc) Xc

/-- The tower `T 0 = ⟨X X, P⟩`, `T (n+1) = ⟨T n, P⟩`. -/
def Tw : ℕ → Term String
  | 0 => pairT (.app Xc Xc) Pc
  | n + 1 => pairT (Tw n) Pc

/-- `apps M [A₁, …, Aₖ] = M A₁ … Aₖ`. -/
def apps (M : Term String) (Γ : List (Term String)) : Term String :=
  Γ.foldl app M

theorem apps_append (M : Term String) (Γ Δ : List (Term String)) :
    apps M (Γ ++ Δ) = apps (apps M Γ) Δ := by
  simp [apps, List.foldl_append]

/-! ## Local closure -/

theorem lc_Xc : LC Xc := by rw [← lcAt_iff_LC]; decide

theorem lc_Xc1 : LC Xc1 := by rw [← lcAt_iff_LC]; decide

theorem lc_Pc : LC Pc := .app (.app lc_Xc lc_Xc) lc_Xc

theorem lc_pairT {B C : Term String} (hB : LC B) (hC : LC C) : LC (pairT B C) := by
  refine .abs ∅ _ (fun x _ => ?_)
  simp only [open', openRec]
  rw [open_lc 0 (fvar x) B hB, open_lc 0 (fvar x) C hC]
  exact .app (.app hB (.fvar x)) hC

theorem lc_Xc2 {B : Term String} (hB : LC B) : LC (Xc2 B) := by
  refine .abs ∅ _ (fun x _ => ?_)
  simp only [open', openRec]
  rw [open_lc 1 (fvar x) B hB]
  refine .app (.fvar x) (.abs ∅ _ (fun y _ => ?_))
  simp only [open', openRec]
  rw [open_lc 0 (fvar y) B hB]
  exact .app (.app hB (.fvar y)) (.fvar x)

theorem lc_Tw : ∀ n, LC (Tw n)
  | 0 => lc_pairT (.app lc_Xc lc_Xc) lc_Pc
  | n + 1 => lc_pairT (lc_Tw n) lc_Pc

/-! ## The basic head steps -/

theorem headStep_Xc {A : Term String} (hA : LC A) : HeadStep (.app Xc A) Xc1 :=
  HeadStep.beta lc_Xc hA

theorem headStep_Xc1 {B : Term String} (hB : LC B) : HeadStep (.app Xc1 B) (Xc2 B) :=
  HeadStep.beta lc_Xc1 hB

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

theorem headStep_pairT {B C U : Term String} (hB : LC B) (hC : LC C) (hU : LC U) :
    HeadStep (.app (pairT B C) U) (.app (.app B U) C) := by
  have h := HeadStep.beta (M := (.app (.app B (.bvar 0)) C)) (N := U) (lc_pairT hB hC) hU
  have he : (Term.app (.app B (.bvar 0)) C) ^ U = .app (.app B U) C := by
    simp only [open', openRec]
    rw [open_lc 0 U B hB, open_lc 0 U C hC]
    simp
  rwa [he] at h

/-! ## Lifting a head step through a stack of arguments -/

theorem headStep_apps {M M' : Term String} (h : HeadStep M M') (hM : ¬ M.IsAbs)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) : HeadStep (apps M Γ) (apps M' Γ) := by
  induction Γ generalizing M M' with
  | nil => exact h
  | cons a Γ ih =>
      refine ih (HeadStep.app hM h (hΓ a (by simp))) (by rintro ⟨⟩) ?_
      intro t ht
      exact hΓ t (by simp [ht])

/-! ## The two machine rules -/

/-- `X A B C Γ ↠h C ⟨B,C⟩ Γ`: `X` discards its first argument and reassociates the other
two. -/
theorem headStepStar_Xc3 {A B C : Term String} (hA : LC A) (hB : LC B) (hC : LC C)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStepStar (apps Xc (A :: B :: C :: Γ)) (apps (.app C (pairT B C)) Γ) := by
  have h1 : HeadStep (apps Xc (A :: B :: C :: Γ)) (apps Xc1 (B :: C :: Γ)) := by
    have := headStep_apps (headStep_Xc hA) (by rintro ⟨⟩) (B :: C :: Γ)
      (by intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hB,
        (by rcases List.mem_cons.mp ht with rfl | ht; exacts [hC, hΓ t ht])])
    exact this
  have h2 : HeadStep (apps Xc1 (B :: C :: Γ)) (apps (Xc2 B) (C :: Γ)) := by
    exact headStep_apps (headStep_Xc1 hB) (by rintro ⟨⟩) (C :: Γ)
      (by intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [hC, hΓ t ht])
  have h3 : HeadStep (apps (Xc2 B) (C :: Γ)) (apps (.app C (pairT B C)) Γ) :=
    headStep_apps (headStep_Xc2 hB hC) (by rintro ⟨⟩) Γ hΓ
  exact .head h1 (.head h2 (.single h3))

/-- `⟨B,C⟩ U Γ ⭢h B U C Γ`. -/
theorem headStep_pairT_apps {B C U : Term String} (hB : LC B) (hC : LC C) (hU : LC U)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStep (apps (pairT B C) (U :: Γ)) (apps B (U :: C :: Γ)) :=
  headStep_apps (headStep_pairT hB hC hU) (by rintro ⟨⟩) Γ hΓ

/-! ## The diverging states -/

/-- The state `S n Γ = T n ⟨X, T n⟩ Γ`. -/
def stateT (n : ℕ) (Γ : List (Term String)) : Term String :=
  apps (Tw n) (pairT Xc (Tw n) :: Γ)

/-- The descent `T n U Γ ↠h T 0 U Pⁿ Γ`. -/
theorem headStepStar_descent (n : ℕ) {U : Term String} (hU : LC U)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStepStar (apps (Tw n) (U :: Γ)) (apps (Tw 0) (U :: (List.replicate n Pc ++ Γ))) := by
  induction n generalizing Γ with
  | zero =>
      simp only [List.replicate_zero, List.nil_append]
      exact .refl
  | succ n ih =>
      have h1 : HeadStep (apps (Tw (n + 1)) (U :: Γ)) (apps (Tw n) (U :: Pc :: Γ)) :=
        headStep_pairT_apps (lc_Tw n) lc_Pc hU Γ hΓ
      have h2 := ih (Γ := Pc :: Γ)
        (by intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [lc_Pc, hΓ t ht])
      refine .head h1 ?_
      have : List.replicate n Pc ++ Pc :: Γ = List.replicate (n + 1) Pc ++ Γ := by
        rw [List.replicate_succ']
        simp
      rwa [this] at h2

/-- **The key transition.**  From the state `S n Γ` head reduction reaches, in `n + 8`
steps, the state `S (n+1) (Pⁿ Γ)`. -/
theorem headTransGen_state (n : ℕ) (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    Relation.TransGen HeadStep (stateT n Γ)
      (stateT (n + 1) (List.replicate n Pc ++ Γ)) := by
  set U : Term String := pairT Xc (Tw n) with hUdef
  have hU : LC U := lc_pairT lc_Xc (lc_Tw n)
  set Δ : List (Term String) := List.replicate n Pc ++ Γ with hΔdef
  have hΔ : ∀ t ∈ Δ, LC t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]; exact lc_Pc
    · exact hΓ t ht
  -- the descent to `T 0`
  have hdesc : HeadStepStar (stateT n Γ) (apps (Tw 0) (U :: Δ)) :=
    headStepStar_descent n hU Γ hΓ
  -- the seven-step cycle
  have hV : LC (pairT U Pc) := lc_pairT hU lc_Pc
  set V : Term String := pairT Xc (pairT U Pc) with hVdef
  have hVlc : LC V := lc_pairT lc_Xc hV
  have s1 : HeadStep (apps (Tw 0) (U :: Δ)) (apps Xc (Xc :: U :: Pc :: Δ)) := by
    have := headStep_pairT_apps (B := .app Xc Xc) (C := Pc) (U := U)
      (.app lc_Xc lc_Xc) lc_Pc hU Δ hΔ
    exact this
  have s2 : HeadStepStar (apps Xc (Xc :: U :: Pc :: Δ)) (apps Xc (Xc :: Xc :: pairT U Pc :: Δ)) := by
    have := headStepStar_Xc3 (A := Xc) (B := U) (C := Pc) lc_Xc hU lc_Pc Δ hΔ
    exact this
  have s3 : HeadStepStar (apps Xc (Xc :: Xc :: pairT U Pc :: Δ))
      (apps (pairT U Pc) (V :: Δ)) := by
    have := headStepStar_Xc3 (A := Xc) (B := Xc) (C := pairT U Pc) lc_Xc lc_Xc hV Δ hΔ
    exact this
  have s4 : HeadStep (apps (pairT U Pc) (V :: Δ)) (apps U (V :: Pc :: Δ)) :=
    headStep_pairT_apps hU lc_Pc hVlc Δ hΔ
  have s5 : HeadStep (apps U (V :: Pc :: Δ)) (apps Xc (V :: Tw n :: Pc :: Δ)) := by
    have := headStep_pairT_apps (B := Xc) (C := Tw n) (U := V) lc_Xc (lc_Tw n) hVlc (Pc :: Δ)
      (by intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exacts [lc_Pc, hΔ t ht])
    exact this
  have s6 : HeadStepStar (apps Xc (V :: Tw n :: Pc :: Δ))
      (apps Xc (Xc :: Xc :: Tw (n + 1) :: Δ)) := by
    have := headStepStar_Xc3 (A := V) (B := Tw n) (C := Pc) hVlc (lc_Tw n) lc_Pc Δ hΔ
    exact this
  have s7 : HeadStepStar (apps Xc (Xc :: Xc :: Tw (n + 1) :: Δ)) (stateT (n + 1) Δ) := by
    have := headStepStar_Xc3 (A := Xc) (B := Xc) (C := Tw (n + 1)) lc_Xc lc_Xc (lc_Tw (n + 1))
      Δ hΔ
    exact this
  exact Relation.TransGen.trans_right hdesc (Relation.TransGen.head' s1
    (((((s2.trans s3).trans (.single s4)).trans (.single s5)).trans s6).trans s7))

/-! ## Divergence -/

/-- The set of diverging states. -/
def DivState (M : Term String) : Prop :=
  ∃ (n : ℕ) (Γ : List (Term String)), (∀ t ∈ Γ, LC t) ∧ M = stateT n Γ

theorem DivState.transGen {M : Term String} (h : DivState M) :
    ∃ N, Relation.TransGen HeadStep M N ∧ DivState N := by
  obtain ⟨n, Γ, hΓ, rfl⟩ := h
  refine ⟨stateT (n + 1) (List.replicate n Pc ++ Γ), headTransGen_state n Γ hΓ, ?_⟩
  refine ⟨n + 1, _, ?_, rfl⟩
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · rw [List.eq_of_mem_replicate ht]; exact lc_Pc
  · exact hΓ t ht

/-- A term whose head reduction terminates cannot reach a diverging state. -/
theorem not_divState_of_acc {M : Term String} (hacc : Relation.SN HeadStep M) :
    ∀ N, HeadStepStar M N → ¬ DivState N := by
  induction hacc with
  | intro A _ ih =>
      intro N hAN hN
      obtain ⟨N', hstep, hN'⟩ := hN.transGen
      obtain ⟨y, hy, hy'⟩ :=
        Relation.TransGen.head'_iff.mp (Relation.TransGen.trans_right hAN hstep)
      exact ih y hy N' hy' hN'

/-- A term from which a diverging state is reachable admits no terminating head
reduction. -/
theorem not_acc_of_headStepStar_divState {M N : Term String} (hMN : HeadStepStar M N)
    (hN : DivState N) : ¬ Relation.SN HeadStep M := fun hacc => not_divState_of_acc hacc N hMN hN

theorem not_hasHNF_of_divState {M : Term String} (h : DivState M) : ¬ HasHNF M := by
  intro hHNF
  obtain ⟨P, hP, hnfP⟩ := hasHNF_iff_headStepStar_headNF.mp hHNF
  exact not_acc_of_headStepStar_divState .refl h (headTerminating_of_headStepStar_headNF hP hnfP)

/-! ## The combination `X X (X X) (X X X)` -/

/-- The combination `X X (X X) (X X X)`. -/
def hnfDivergeStart : Term String := apps Xc [Xc, .app Xc Xc, Pc]

theorem hnfDivergeStart_gen : Gen Xc hnfDivergeStart := by
  have hb : GenFinset [Xc] Xc := ClosedUnderApp.base (by simp)
  exact ((hb.app hb).app (hb.app hb)).app ((hb.app hb).app hb)

theorem hnfDivergeStart_headStepStar_state :
    HeadStepStar hnfDivergeStart (stateT 0 []) := by
  have h1 : HeadStepStar hnfDivergeStart (apps Xc [Xc, Xc, Tw 0]) := by
    have := headStepStar_Xc3 (A := Xc) (B := .app Xc Xc) (C := Pc) lc_Xc (.app lc_Xc lc_Xc)
      lc_Pc [] (by simp)
    exact this
  have h2 : HeadStepStar (apps Xc [Xc, Xc, Tw 0]) (stateT 0 []) := by
    have := headStepStar_Xc3 (A := Xc) (B := Xc) (C := Tw 0) lc_Xc lc_Xc (lc_Tw 0) [] (by simp)
    exact this
  exact h1.trans h2

/-- **`X X (X X) (X X X)` has no head normal form.** -/
theorem hnfDivergeStart_not_hasHNF : ¬ HasHNF hnfDivergeStart := by
  intro hHNF
  obtain ⟨P, hP, hnfP⟩ := hasHNF_iff_headStepStar_headNF.mp hHNF
  exact not_acc_of_headStepStar_divState hnfDivergeStart_headStepStar_state
    ⟨0, [], by simp, rfl⟩ (headTerminating_of_headStepStar_headNF hP hnfP)

/-- **Not every applicative combination of `λλλ0(λ201)` has a head normal form.** -/
theorem exists_gen_not_hasHNF :
    ∃ M : Term String, Gen (db! "λλλ0(λ201)") M ∧ ¬ HasHNF M :=
  ⟨hnfDivergeStart, hnfDivergeStart_gen, hnfDivergeStart_not_hasHNF⟩

/-- The same statement, phrased as the refutation of the "always a head normal form"
claim. -/
theorem not_forall_gen_hasHNF :
    ¬ ∀ M : Term String, Gen (db! "λλλ0(λ201)") M → HasHNF M := by
  intro h
  exact hnfDivergeStart_not_hasHNF (h hnfDivergeStart hnfDivergeStart_gen)

/-- `M` has no head normal form, and neither has `M` applied to any stack of arguments. -/
def NoHNFStack (M : Term String) : Prop :=
  ∀ Γ : List (Term String), (∀ t ∈ Γ, LC t) → ¬ HasHNF (apps M Γ)

/-- `M` βη-reduces to a term which, with any stack of arguments, has no head normal
form. -/
def Bad (M : Term String) : Prop := ∃ M', M ↠βηᶠ M' ∧ LC M' ∧ NoHNFStack M'

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
