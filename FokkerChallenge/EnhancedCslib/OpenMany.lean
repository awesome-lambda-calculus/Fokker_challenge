import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## Opening a whole context of binders -/

/-- `openMany k env t` opens the dangling indices `k, k+1, …` of `t` with the
variables of `env` (innermost binder first). -/
@[simp, scoped grind =]
def openMany (k : ℕ) : List (String × String) → Term String → Term String
  | [], t => t
  | e :: es, t => openMany (k + 1) es (openRec k (fvar e.1) t)

@[simp] theorem openMany_fvar (k : ℕ) (env : List (String × String)) (x : String) :
    openMany k env (fvar x) = fvar x := by
  induction env generalizing k with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

@[simp] theorem openMany_app (k : ℕ) (env : List (String × String)) (a b : Term String) :
    openMany k env (app a b) = app (openMany k env a) (openMany k env b) := by
  induction env generalizing k a b with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

@[simp] theorem openMany_abs (k : ℕ) (env : List (String × String)) (M : Term String) :
    openMany k env (abs M) = abs (openMany (k + 1) env M) := by
  induction env generalizing k M with
  | nil => rfl
  | cons e es ih => simp [openMany, openRec, ih]

/-- Opening an inner index commutes with opening the outer context. -/
theorem openRec_openMany (env : List (String × String)) (y : String) :
    ∀ (j k : ℕ), j < k → ∀ t : Term String,
      openRec j (fvar y) (openMany k env t) = openMany k env (openRec j (fvar y) t) := by
  induction env with
  | nil => intro j k _ t; rfl
  | cons e es ih =>
      intro j k hjk t
      simp only [openMany]
      rw [ih j (k + 1) (by omega), swap_open _ _ _ _ _ (by omega : j ≠ k) (by grind) (by grind)]

theorem openMany_bvar_lt : ∀ (env : List (String × String)) (k i : ℕ) (p : String × String),
    env[i]? = some p → openMany k env (bvar (k + i)) = fvar p.1 := by
  intro env
  induction env with
  | nil => intro k i p h; simp at h
  | cons e es ih =>
      intro k i p h
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp [openMany, openRec]
      | i + 1 =>
          simp only [List.getElem?_cons_succ] at h
          have hne : ¬ (k + (i + 1) = k) := by omega
          have := ih (k + 1) i p h
          simp only [openMany, openRec]
          rw [show k + (i + 1) = k + 1 + i by omega]
          grind

theorem openMany_bvar_ge : ∀ (env : List (String × String)) (k i : ℕ),
    env.length + k ≤ i → openMany k env (bvar i) = bvar i := by
  intro env
  induction env with
  | nil => intro k i _; rfl
  | cons e es ih =>
      intro k i h
      have hne : ¬ (i = k) := by simp at h; omega
      simp only [openMany, openRec]
      grind

theorem lc_openMany_of_lcAt : ∀ (t : Term String) (env : List (String × String)),
    LcAt env.length t = true → LC (openMany 0 env t) := by
  intro t
  induction t with
  | bvar i =>
      intro env h
      simp only [LcAt, decide_eq_true_eq] at h
      obtain ⟨p, hp⟩ : ∃ p, env[i]? = some p :=
        ⟨env[i]'h, by simp [List.getElem?_eq_getElem h]⟩
      have := openMany_bvar_lt env 0 i p hp
      simp only [Nat.zero_add] at this
      rw [this]
      exact LC.fvar _
  | fvar x => intro env _; simpa using LC.fvar x
  | abs t ih =>
      intro env h
      simp only [LcAt] at h
      rw [openMany_abs]
      refine LC.abs ∅ _ (fun x _ => ?_)
      have hcomm := openRec_openMany env x 0 1 (by omega) t
      unfold open'
      rw [hcomm]
      have := ih ((x, "x") :: env) (by simpa using h)
      simpa [openMany] using this
  | app a b iha ihb =>
      intro env h
      simp only [LcAt, Bool.and_eq_true] at h
      rw [openMany_app]
      exact LC.app (iha env h.1) (ihb env h.2)

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
