import FokkerChallenge.GenTerms

/-!
# Enumerating all terms of bounded Fokker size, without local closure

`GenTerms.lean` enumerates the *locally closed* closed terms of a given Fokker size.
Here we drop the local-closure requirement: we enumerate every term that

* has no free variable (`M.fv = ∅`),
* has Fokker size `< n`,
* and whose de Bruijn indices are all `< n` (`M.bvar_bound ≤ n`).

The last condition is what keeps the list finite once local closure is dropped: a
dangling index may be anything, so it has to be bounded somewhere, and `n` is the
natural bound to pick.

The main definitions are `gen_terms_bvar` (terms with a fixed number of
abstractions and applications) and `terms_fokker_lt`, and the main result is
`mem_terms_fokker_lt`, an exact characterisation of the produced list.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- `bvar_bound M` is the least `b` such that every de Bruijn index occurring in `M`
is `< b`. (Binders are *not* taken into account: this bounds the raw indices.) -/
@[simp]
def bvar_bound : Term String → Nat
  | bvar i => i + 1
  | fvar _ => 0
  | abs M => bvar_bound M
  | app M N => max (bvar_bound M) (bvar_bound N)

/-- `gen_terms_bvar b lams apps` lists every term with no free variable, exactly
`lams` abstractions, exactly `apps` applications, and all de Bruijn indices `< b`.
Unlike `gen_terms`, the bound on indices is *not* increased when going under a
binder, so the produced terms need not be locally closed. -/
def gen_terms_bvar (b : Nat) : Nat → Nat → List (Term String)
  | 0, 0 => (List.range b).map Term.bvar
  | lams, apps =>
      let lambda_terms := if lams > 0 then
        (gen_terms_bvar b (lams - 1) apps).map Term.abs
      else
        []

      let app_terms := if apps > 0 then
        (List.range (lams + 1)).attach.flatMap fun ⟨left_l, hl⟩ =>
        (List.range apps).attach.flatMap fun ⟨left_a, ha⟩ =>
        have _hl : left_l < lams + 1 := List.mem_range.mp hl
        have _ha : left_a < apps := List.mem_range.mp ha
        (gen_terms_bvar b left_l left_a).flatMap fun left =>
        (gen_terms_bvar b (lams - left_l) (apps - 1 - left_a)).map fun right =>
        Term.app left right
      else
        []
      lambda_terms ++ app_terms
termination_by lams apps => lams + apps
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Every term with no free variable, Fokker size `< n` and all de Bruijn indices
`< n`, listed. Local closure is *not* required. -/
def terms_fokker_lt (n : Nat) : List (Term String) :=
  (List.range n).flatMap fun lams =>
    (List.range (n - lams)).flatMap fun apps =>
      gen_terms_bvar n lams apps

/-- Completeness of `gen_terms_bvar`. -/
theorem gen_terms_bvar_complete : ∀ (M : Term String) (b : Nat),
    M.fv = ∅ → M.bvar_bound ≤ b →
    M ∈ gen_terms_bvar b M.abs_count M.app_count := by
  intro M
  induction M with
  | bvar i =>
    intro b _ hb
    show bvar i ∈ gen_terms_bvar b 0 0
    unfold gen_terms_bvar
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by simpa using hb), rfl⟩
  | fvar x =>
    intro _ hfv _
    simp [fv] at hfv
  | abs M ih =>
    intro b hfv hb
    have hfv' : M.fv = ∅ := by simpa [fv] using hfv
    have hb' : M.bvar_bound ≤ b := by simpa using hb
    have ihM := ih b hfv' hb'
    show abs M ∈ gen_terms_bvar b (1 + M.abs_count) M.app_count
    rw [gen_terms_bvar.eq_2 _ _ _ (by intro h; omega)]
    simp only [show (1 + M.abs_count) > 0 from by omega, ite_true,
      show (1 + M.abs_count) - 1 = M.abs_count from by omega]
    exact List.mem_append_left _ (List.mem_map_of_mem ihM)
  | app L R ihL ihR =>
    intro b hfv hb
    have hfv_union : L.fv ∪ R.fv = ∅ := by simpa [fv] using hfv
    have hfvL : L.fv = ∅ := (Finset.union_eq_empty.mp hfv_union).1
    have hfvR : R.fv = ∅ := (Finset.union_eq_empty.mp hfv_union).2
    have hbL : L.bvar_bound ≤ b := le_trans (le_max_left _ _) (by simpa using hb)
    have hbR : R.bvar_bound ≤ b := le_trans (le_max_right _ _) (by simpa using hb)
    have ihL' := ihL b hfvL hbL
    have ihR' := ihR b hfvR hbR
    show app L R ∈
      gen_terms_bvar b (L.abs_count + R.abs_count) (1 + L.app_count + R.app_count)
    rw [gen_terms_bvar.eq_2 _ _ _ (by intro _ h; omega)]
    apply List.mem_append_right
    simp only [show (1 + L.app_count + R.app_count) > 0 from by omega, ite_true]
    refine List.mem_flatMap.mpr ⟨⟨L.abs_count, ?_⟩, List.mem_attach _ _, ?_⟩
    · rw [List.mem_range]; omega
    · refine List.mem_flatMap.mpr ⟨⟨L.app_count, ?_⟩, List.mem_attach _ _, ?_⟩
      · rw [List.mem_range]; omega
      · refine List.mem_flatMap.mpr ⟨L, ihL', ?_⟩
        have hRl : (L.abs_count + R.abs_count) - L.abs_count = R.abs_count := by omega
        have hRa : (1 + L.app_count + R.app_count) - 1 - L.app_count = R.app_count := by omega
        simp only [hRl, hRa]
        exact List.mem_map_of_mem ihR'

/-- Soundness of `gen_terms_bvar`. -/
theorem gen_terms_bvar_sound :
    ∀ (tot b n_lams n_apps : Nat), n_lams + n_apps = tot →
    ∀ (M : Term String), M ∈ gen_terms_bvar b n_lams n_apps →
    M.fv = ∅ ∧ M.bvar_bound ≤ b ∧ M.abs_count = n_lams ∧ M.app_count = n_apps := by
  intro tot
  induction tot using Nat.strong_induction_on with | _ tot ih
  intro b n_lams n_apps htot M hmem
  by_cases hb : n_lams = 0 ∧ n_apps = 0
  · obtain ⟨hl, ha⟩ := hb
    subst hl; subst ha
    simp [gen_terms_bvar] at hmem
    obtain ⟨a, ha, hab⟩ := hmem
    subst M
    refine ⟨rfl, by simpa using ha, rfl, rfl⟩
  · rw [gen_terms_bvar.eq_2 _ _ _ (by intro h; tauto)] at hmem
    rcases List.mem_append.mp hmem with hlam | happ_mem
    · split_ifs at hlam with hl_pos
      · rw [List.mem_map] at hlam
        obtain ⟨N, hN_mem, habs⟩ := hlam
        subst habs
        have hsmaller : (n_lams - 1) + n_apps < tot := by omega
        obtain ⟨hfv, hbb, habsN, happN⟩ := ih _ hsmaller b (n_lams - 1) n_apps rfl N hN_mem
        exact ⟨by simp [fv]; exact hfv, by simpa using hbb, by simp [abs_count]; omega, happN⟩
      · cases hlam
    · split_ifs at happ_mem with happ_pos
      · rw [List.mem_flatMap] at happ_mem
        obtain ⟨⟨left_l, hl_mem⟩, _, hmem2⟩ := happ_mem
        rw [List.mem_flatMap] at hmem2
        obtain ⟨⟨left_a, ha_mem⟩, _, hmem3⟩ := hmem2
        rw [List.mem_flatMap] at hmem3
        obtain ⟨left, hL_mem, hmem4⟩ := hmem3
        rw [List.mem_map] at hmem4
        obtain ⟨right, hR_mem, hM⟩ := hmem4
        cases hM
        rw [List.mem_range] at hl_mem
        rw [List.mem_range] at ha_mem
        have hsmaller_L : left_l + left_a < tot := by omega
        have hsmaller_R : (n_lams - left_l) + (n_apps - 1 - left_a) < tot := by omega
        obtain ⟨hfvL, hbL, habsL, happL⟩ := ih _ hsmaller_L b left_l left_a rfl left hL_mem
        obtain ⟨hfvR, hbR, habsR, happR⟩ :=
          ih _ hsmaller_R b (n_lams - left_l) (n_apps - 1 - left_a) rfl right hR_mem
        refine ⟨by simp [fv, hfvL, hfvR], ?_, ?_, ?_⟩
        · simp only [bvar_bound, max_le_iff]; exact ⟨hbL, hbR⟩
        · show left.abs_count + right.abs_count = n_lams
          rw [habsL, habsR]; omega
        · show 1 + left.app_count + right.app_count = n_apps
          rw [happL, happR]; omega
      · cases happ_mem

/-- `terms_fokker_lt n` contains exactly the terms with no free variable, Fokker size
`< n`, and all de Bruijn indices `< n`. -/
theorem mem_terms_fokker_lt (n : Nat) (M : Term String) :
    M ∈ terms_fokker_lt n ↔ M.fv = ∅ ∧ M.fokker_size < n ∧ M.bvar_bound ≤ n := by
  constructor
  · intro hmem
    unfold terms_fokker_lt at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨lams, hlams, hmem⟩ := hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨apps, happs, hmem⟩ := hmem
    rw [List.mem_range] at hlams happs
    obtain ⟨hfv, hbb, habs, happ⟩ :=
      gen_terms_bvar_sound (lams + apps) n lams apps rfl M hmem
    refine ⟨hfv, ?_, hbb⟩
    rw [fokker_size_eq_abs_count_add_app_count, habs, happ]
    omega
  · rintro ⟨hfv, hsz, hbb⟩
    have hsz' : M.abs_count + M.app_count < n := by
      rw [← fokker_size_eq_abs_count_add_app_count]; exact hsz
    unfold terms_fokker_lt
    rw [List.mem_flatMap]
    refine ⟨M.abs_count, List.mem_range.mpr (by omega), ?_⟩
    rw [List.mem_flatMap]
    exact ⟨M.app_count, List.mem_range.mpr (by omega), gen_terms_bvar_complete M n hfv hbb⟩

/-- Every closed locally closed term of Fokker size `< n` occurs in `terms_fokker_lt n`;
so this enumeration refines the one of `GenTerms.lean`. -/
theorem mem_terms_fokker_lt_of_closed_lc (n : Nat) (M : Term String)
    (hfv : M.fv = ∅) (hlc : M.LC) (hsz : M.fokker_size < n) :
    M ∈ terms_fokker_lt n := by
  refine (mem_terms_fokker_lt n M).mpr ⟨hfv, hsz, ?_⟩
  -- Under `LcAt d`, indices are below `d` plus the number of enclosing binders.
  have h : ∀ (N : Term String) (d : Nat),
      LcAt d N = true → N.bvar_bound ≤ d + N.abs_count := by
    intro N
    induction N with
    | bvar i => intro d h; simp only [LcAt, decide_eq_true_eq] at h; simp [abs_count]; omega
    | fvar _ => intro d _; simp
    | abs N ihN =>
      intro d h
      have hN := ihN (d + 1) h
      simp only [bvar_bound, abs_count]
      omega
    | app L R ihL ihR =>
      intro d h
      simp only [LcAt, Bool.and_eq_true] at h
      have h1 := ihL d h.1
      have h2 := ihR d h.2
      simp only [bvar_bound, abs_count, max_le_iff]
      omega
  have hM := h M 0 ((lcAt_iff_LC M).mpr hlc)
  have hsz' : M.abs_count + M.app_count < n := by
    rw [← fokker_size_eq_abs_count_add_app_count]; exact hsz
  omega

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
