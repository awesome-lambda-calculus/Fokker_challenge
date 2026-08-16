
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.EtaToSpine

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

universe u

open Term

variable {Var : Type u} [DecidableEq Var]

theorem fv_absN (n : ℕ) (t : Term Var) : fv (abs^[n] t) = fv t := by
  induction n with
  | zero => rfl
  | succ m ih =>  rw [add_comm, Function.iterate_add]
                  simp
                  grind

theorem absn_openrec {i n} {N M : Term String} :
  (abs^[n] M)⟦i ↝ N⟧ = abs^[n] (M⟦n+i ↝ N⟧) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih => simp; grind

theorem absn_lcat {i n} {M : Term String} :
  LcAt i (abs^[n] M) = LcAt (n+i) M := by
  induction n generalizing M with
  | zero => simp
  | succ n ih => simp; grind

/-- Refinement of `openRec_absN_spine`: opening reflects the shape
`absN n (spine x l)` *argument by argument*. -/
theorem openRec_absN_spine_args {T : Term Var} {k n : ℕ} {x y : Var} {l : List (Term Var)}
    (hxy : x ≠ y) (h : openRec k (fvar y) T = abs^[n] (spine x l)) :
    ∃ l', T = abs^[n] (spine x l') ∧ l'.map (openRec (k + n) (fvar y)) = l := by
  induction T generalizing k n l with
  | bvar i =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          split_ifs at h
          · exact absurd (spine_eq_fvar h.symm).1 hxy
          · exact absurd h.symm spine_ne_bvar
      | succ m =>
          rw [add_comm, Function.iterate_add, openRec_bvar] at h
          simp at h
          split_ifs at h
  | fvar z =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          obtain ⟨hx, hl⟩ := spine_eq_fvar h.symm
          exact ⟨[], by rw [spine_nil, hx], by simp [hl]⟩
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp only [openRec] at h
          cases h
  | abs S ih =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          exact absurd h.symm spine_ne_abs
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp only [openRec] at h
          obtain ⟨l', hS, hmap⟩ := ih (by injection h)
          refine ⟨l', by rw [add_comm, Function.iterate_add, hS]; simp, ?_⟩
          rw [show k + (m + 1) = k + 1 + m by omega]
          exact hmap
  | app P Q ihP _ =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          obtain ⟨l₀, hl, hP'⟩ := spine_eq_app h.symm
          obtain ⟨l₀', hP, hmap⟩ := ihP (n := 0) (l := l₀) (by simp; exact hP')
          refine ⟨l₀' ++ [Q], ?_, ?_⟩
          · simp_all
          · simp only [List.map_append, List.map_cons, List.map_nil]
            simp only [Nat.add_zero] at hmap
            rw [hmap, hl]
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp only [openRec] at h
          cases h
