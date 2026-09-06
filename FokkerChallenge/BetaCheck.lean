import FokkerChallenge.DeBruijnParse
import FokkerChallenge.TwoVarsAreNotEnough.Final

/-!
# A certified checker for β-reduction steps between closed de Bruijn terms

The question addressed by this file and by `RequestProject.LiftSearch` /
`RequestProject.FokkerUndecided` is:

> given a closed term `T`, is `T` a β-reduct of a term that can be named with
> only the two variable names `x` and `y`?

The predicate is `BetaReductOfNamable`.  To certify a positive answer one has to
exhibit a term `S` with `namableXY S = true` and `S ↠βᶠ T`.  Since a search
procedure produces the candidate `S` (and the intermediate terms) as *data*, all
that is needed on the Lean side is a **checker**: a boolean function
`betaCheck S T` that verifies `S ⭢βᶠ T` by inspecting the two terms, together
with the soundness theorem `betaCheck_sound`.

Because the reduction relations of the locally nameless presentation go under a
binder by *opening* with a fresh free variable, the checker does the same: when
comparing `abs a` with `abs b` it opens both with a variable that is fresh for
the two bodies.  Hence, at the point where a redex is contracted, all terms
involved are locally closed and `openRec 0 M B` is the honest contractum.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## Deciding local closure -/

/-! ## Computing a fresh variable -/

/-- The maximal length of a free-variable name occurring in `t`. -/
def maxNameLen : Term String → ℕ
  | .bvar _ => 0
  | .fvar x => x.length
  | .abs t => maxNameLen t
  | .app a b => max (maxNameLen a) (maxNameLen b)

/-- A name of length `n + 1`, consisting of `n + 1` copies of `'z'`. -/
def freshOf (n : ℕ) : String := String.ofList (List.replicate (n + 1) 'z')

theorem freshOf_length (n : ℕ) : (freshOf n).length = n + 1 := by
  simp [freshOf]

theorem length_le_maxNameLen (inst : DecidableEq String) {t : Term String} {y : String}
    (h : y ∈ @fv String inst t) : y.length ≤ maxNameLen t := by
  induction t with
  | bvar i => simp [fv] at h
  | fvar x => simp [fv] at h; subst h; simp [maxNameLen]
  | abs t ih => exact ih (by simpa [fv] using h)
  | app a b iha ihb =>
      simp only [fv, Finset.mem_union] at h
      rcases h with h | h
      · exact le_trans (iha h) (le_max_left _ _)
      · exact le_trans (ihb h) (le_max_right _ _)

theorem freshOf_notMem_fv (inst : DecidableEq String) {t : Term String} {n : ℕ}
    (h : maxNameLen t ≤ n) : freshOf n ∉ @fv String inst t := by
  intro hmem
  have := length_le_maxNameLen inst hmem
  rw [freshOf_length] at this
  omega

/-! ## The checker -/

/-- Check that contracting the redex `app f u` at the root yields `T`. -/
def redexCheck (f u T : Term String) : Bool :=
  match f with
  | .abs B => LcAt 1 B && LcAt 0 u && (T == openRec 0 u B)
  | _ => false

theorem redexCheck_sound {f u T : Term String} (h : redexCheck f u T = true) :
    FullBeta (.app f u) T := by
  match f with
  | .bvar _ => simp [redexCheck] at h
  | .fvar _ => simp [redexCheck] at h
  | .app _ _ => simp [redexCheck] at h
  | .abs B =>
      simp only [redexCheck, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hB, hu⟩, hT⟩ := h
      subst hT
      exact Xi.base (Beta.beta (by rw [<- lcAt_iff_LC]; grind) (by rw [<- lcAt_iff_LC]; grind))

/-- `betaCheckF n S T` checks that `S` β-reduces to `T` in one step, using `n`
as fuel (`n` bounds the depth of the position of the contracted redex).  The
fuel makes the definition structurally recursive, hence reducible by the
kernel. -/
def betaCheckF : ℕ → Term String → Term String → Bool
  | 0, _, _ => false
  | n + 1, .abs a, .abs b =>
      betaCheckF n (openRec 0 (.fvar (freshOf (max (maxNameLen a) (maxNameLen b)))) a)
                   (openRec 0 (.fvar (freshOf (max (maxNameLen a) (maxNameLen b)))) b)
  | n + 1, .app f u, .app f' u' =>
      redexCheck f u (.app f' u') ||
        ((f == f' && LcAt 0 f && betaCheckF n u u') || (u == u' && LcAt 0 u && betaCheckF n f f'))
  | _ + 1, .app f u, T => redexCheck f u T
  | _ + 1, _, _ => false

theorem betaCheckF_sound : ∀ (n : ℕ) (S T : Term String), betaCheckF n S T = true →
    FullBeta S T := by
  intro n
  induction n with
  | zero => intro S T h; simp [betaCheckF] at h
  | succ n ih =>
      intro S T h
      match S, T with
      | .bvar _, _ => simp [betaCheckF] at h
      | .fvar _, _ => simp [betaCheckF] at h
      | .abs _, .bvar _ => simp [betaCheckF] at h
      | .abs _, .fvar _ => simp [betaCheckF] at h
      | .abs _, .app _ _ => simp [betaCheckF] at h
      | .abs a, .abs b =>
          simp only [betaCheckF] at h
          have hstep := ih _ _ h
          have hcl := FullBeta.step_abs_close (x:=(freshOf (max (maxNameLen a) (maxNameLen b)))) hstep
          rw [<- open_close, <- open_close] at hcl
          grind
          grind [freshOf_notMem_fv _ (le_max_right _ _)]
          grind [freshOf_notMem_fv _ (le_max_left _ _)]
      | .app f u, .bvar _ => exact redexCheck_sound (by simpa [betaCheckF] using h)
      | .app f u, .fvar _ => exact redexCheck_sound (by simpa [betaCheckF] using h)
      | .app f u, .abs _ => exact redexCheck_sound (by simpa [betaCheckF] using h)
      | .app f u, .app f' u' =>
          simp only [betaCheckF, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with h | h | h
          · exact redexCheck_sound h
          · obtain ⟨⟨rfl, hf⟩, hu⟩ := h
            exact Xi.appL (by rw [<- lcAt_iff_LC]; grind) (ih _ _ hu)
          · obtain ⟨⟨rfl, hu⟩, hf⟩ := h
            exact Xi.appR (by rw [<- lcAt_iff_LC]; grind) (ih _ _ hf)

/-- `betaCheck S T` checks that `S` β-reduces to `T` in one step. -/
def betaCheck (S T : Term String) : Bool := betaCheckF S.size S T

theorem betaCheck_sound (S T : Term String) (h : betaCheck S T = true) : FullBeta S T :=
  betaCheckF_sound _ S T h

/-! ## Chains of β-steps -/

/-- Check that the list is a chain of β-steps (its `head` reduces to its last
element). -/
def betaChainCheck : List (Term String) → Bool
  | [] => false
  | [_] => true
  | a :: b :: r => betaCheck a b && betaChainCheck (b :: r)

theorem betaChainCheck_sound : ∀ (l : List (Term String)) (S T : Term String),
    l.head? = some S → l.getLast? = some T → betaChainCheck l = true → S ↠βᶠ T := by
  intro l
  induction l with
  | nil => intro S T h; simp at h
  | cons a l ih =>
      match l with
      | [] =>
          intro S T h1 h2 _
          simp only [List.head?_cons, Option.some.injEq] at h1
          simp only [List.getLast?_singleton, Option.some.injEq] at h2
          subst h1; subst h2
          exact Relation.ReflTransGen.refl
      | b :: r =>
          intro S T h1 h2 h
          simp only [List.head?_cons, Option.some.injEq] at h1
          subst h1
          simp only [betaChainCheck, Bool.and_eq_true] at h
          exact Relation.ReflTransGen.head (betaCheck_sound _ _ h.1)
            (ih b T rfl (by simpa using h2) h.2)

/-! ## The predicate -/

/-- `BetaReductOfNamable T` says that the closed term `T` is a β-reduct of a term
that can be named using only the two variable names `x` and `y`. -/
def BetaReductOfNamable (T : Term String) : Prop :=
  ∃ S, namableXY S = true ∧ S ↠βᶠ T

theorem BetaReductOfNamable.lc {T : Term String} (h : BetaReductOfNamable T) : LC T := by
  obtain ⟨S, hS, hred⟩ := h
  cases FullBeta.steps_lc_or_rfl hred <;> grind [lc_of_namableXY hS]

theorem BetaReductOfNamable.app {A B : Term String}
    (hA : BetaReductOfNamable A) (hB : BetaReductOfNamable B) :
    BetaReductOfNamable (Term.app A B) := by
  obtain ⟨SA, hSA, hA'⟩ := hA
  obtain ⟨SB, hSB, hB'⟩ := hB
  refine ⟨Term.app SA SB, namableXY_app hSA hSB, ?_⟩
  have hLCA : LC A := by cases FullBeta.steps_lc_or_rfl hA' <;> grind [lc_of_namableXY hSA]
  have step₁ : (Term.app SA SB) ↠βᶠ (Term.app A SB) := FullBeta.redex_app_l_cong hA' (lc_of_namableXY hSB)
  have step₂ : (Term.app A SB) ↠βᶠ (Term.app A B) := FullBeta.redex_app_r_cong hB' hLCA
  exact step₁.trans step₂

theorem BetaReductOfNamable_not_basis {M} (hm : BetaReductOfNamable M) : not_basis M := by
  have := BetaReductOfNamable.lc hm
  obtain ⟨S, hm, steps⟩ := hm
  obtain ⟨N, hlc, hfv, hm⟩ := namableXY_not_basis hm
  refine ⟨N, hlc, hfv, ?_⟩
  intros t ht steps
  obtain ⟨s, hs, h⟩ := genfinset_forall2_of_lc (l1:=[S]) (l2:=[M]) (hn:=ht) (.cons (by grind) .nil) (genfinset_lc ht (by grind))
  apply hm s hs (.trans (Relation.ReflTransGen.mono le_sup_left _ _ h)  steps)

/-- Every applicative combination of terms of the class stays in the class. -/
theorem BetaReductOfNamable.closedUnderApp {t : Term String}
    (h : ClosedUnderApp BetaReductOfNamable t) : BetaReductOfNamable t := by
  induction h with
  | base hb => exact hb
  | app _ _ iha ihb => exact iha.app ihb


/-- A nameable term is trivially a β-reduct of a nameable term. -/
theorem betaReductOfNamable_of_namableXY {T : Term String} (h : namableXY T = true) :
    BetaReductOfNamable T :=
  ⟨T, h, Relation.ReflTransGen.refl⟩

/-- Certificate format: a nonempty list of terms whose head is nameable and
whose consecutive elements are β-steps. -/
def chainCheck (l : List (Term String)) : Bool :=
  match l with
  | [] => false
  | S :: _ => namableXY S && betaChainCheck l

theorem betaReductOfNamable_of_chainCheck {l : List (Term String)} {T : Term String}
    (hT : l.getLast? = some T) (h : chainCheck l = true) : BetaReductOfNamable T := by
  match l with
  | [] => simp [chainCheck] at h
  | S :: r =>
      simp only [chainCheck, Bool.and_eq_true] at h
      exact ⟨S, h.1, betaChainCheck_sound _ S T rfl hT h.2⟩


/-- `certifies T l` checks that the list `l` is a certificate for
`BetaReductOfNamable T`: its head is nameable with two names, its consecutive
elements are β-steps, and its last element is `T`. -/
def certifies (T : Term String) (l : List (Term String)) : Bool :=
  chainCheck l && (l.getLast? == some T)

/-- Every list of terms with a valid certificate is a β-reduct of a nameable term. -/
theorem betaReductOfNamable_of_certifies {T : Term String} {l : List (Term String)}
    (h : certifies T l = true) : BetaReductOfNamable T := by
  simp only [certifies, Bool.and_eq_true, beq_iff_eq] at h
  exact betaReductOfNamable_of_chainCheck h.2 h.1

/-- A table of certificates, one for each term of a list. -/
def entriesOK (es : List (Term String × List (Term String))) : Bool :=
  es.all (fun p => certifies p.1 p.2)

@[simp] theorem entriesOK_append (a b : List (Term String × List (Term String))) :
    entriesOK (a ++ b) = (entriesOK a && entriesOK b) := by
  simp [entriesOK, List.all_append]

theorem betaReductOfNamable_of_entriesOK {es : List (Term String × List (Term String))}
    (h : entriesOK es = true) : ∀ T ∈ es.map Prod.fst, BetaReductOfNamable T := by
  intro T hT
  simp only [List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  simp only [entriesOK, List.all_eq_true] at h
  exact betaReductOfNamable_of_certifies (h p hp)
