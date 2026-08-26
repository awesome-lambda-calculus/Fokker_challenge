import FokkerChallenge.BLC.BLCTotal

/-!
# Enumerating the terms with a short binary code

Given `N : ℕ`, `Term.termsUpTo Var N` is the (finite) list of *all* terms of
`Term Var` that contain no free variable and whose binary lambda calculus code
`blcT` (see `RequestProject.BLCTotal`) is shorter than `N`:

```
t ∈ termsUpTo Var N  ↔  IsDB t ∧ t.blcT.length < N
```

Here `IsDB t` says that `t` is a pure de Bruijn term, i.e. contains no `fvar`;
for `DecidableEq Var` this is the same as `fv t = ∅` (see `mem_termsUpTo_fv`).

The list is built length by length: `termsOfLen Var n` enumerates the terms
whose code has length exactly `n`.  Since

```
|bvar n| = n + 2,   |λ M| = |M| + 2,   |M N| = |M| + |N| + 2,
```

a term with a code of length `n + 2` is either `bvar n`, or `λ M` with
`|M| = n`, or `M N` with `|M| + |N| = n`; all sub-terms occurring have a
strictly smaller code, so the recursion is well founded.  It is implemented with
a fuel argument, which keeps the definition structurally recursive and hence
reducible by the kernel, so that concrete enumerations can be checked by
`decide`.

Main results:

* `mem_termsOfLen`   — `t ∈ termsOfLen Var n ↔ IsDB t ∧ t.blcT.length = n`;
* `mem_termsUpTo`    — `t ∈ termsUpTo Var N ↔ IsDB t ∧ t.blcT.length < N`;
* `mem_termsUpTo_fv` — the same, phrased with `fv t = ∅`;
* `termsOfLen_nodup`, `termsUpTo_nodup` — the enumerations have no repetitions,
  so `termsUpTo Var N` lists each such term exactly once.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

/-! ## Code lengths of de Bruijn terms -/

/-- The code of a term without free variables has length at least `2`. -/
theorem two_le_blcT_length_of_isDB {t : Term Var} (h : IsDB t) : 2 ≤ t.blcT.length := by
  cases h with
  | bvar n => simp
  | abs h => simp
  | app h1 h2 => simp

/-! ## The enumeration -/

/-- Auxiliary fuelled version of `termsOfLen`: `termsOfLenF Var k n` lists the
terms with a code of length `n`, provided the fuel `k` is at least `n`. -/
def termsOfLenF (Var : Type u) : ℕ → ℕ → List (Term Var)
  | 0, _ => []
  | _ + 1, 0 => []
  | _ + 1, 1 => []
  | k + 1, m + 2 =>
      (bvar m : Term Var) ::
        ((termsOfLenF Var k m).map abs ++
          (List.range (m + 1)).flatMap fun a =>
            (termsOfLenF Var k a).flatMap fun t => (termsOfLenF Var k (m - a)).map (app t))

/-- Any two sufficiently large amounts of fuel give the same list. -/
theorem termsOfLenF_fuel {n : ℕ} : ∀ {k k' : ℕ}, n ≤ k → n ≤ k' →
    termsOfLenF Var k n = termsOfLenF Var k' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro k k' _ _; cases k <;> cases k' <;> rfl
    | 1 => intro k k' hk hk'; cases k <;> cases k' <;> simp_all [termsOfLenF]
    | (m + 2) =>
        intro k k' hk hk'
        match k, k' with
        | (j + 1), (j' + 1) =>
            have hm : termsOfLenF Var j m = termsOfLenF Var j' m :=
              ih m (by omega) (k := j) (k' := j') (by omega) (by omega)
            have hsplit : ∀ a ∈ List.range (m + 1),
                ((termsOfLenF Var j a).flatMap fun t =>
                    (termsOfLenF Var j (m - a)).map (app t)) =
                  (termsOfLenF Var j' a).flatMap fun t =>
                    (termsOfLenF Var j' (m - a)).map (app t) := by
              intro a ha
              have ha' : a ≤ m := by simpa [Nat.lt_succ_iff] using List.mem_range.mp ha
              rw [ih a (by omega) (k := j) (k' := j') (by omega) (by omega),
                ih (m - a) (by omega) (k := j) (k' := j') (by omega) (by omega)]
            simp only [termsOfLenF, hm, List.flatMap_congr hsplit]

/-- `termsOfLen Var n` is the list of all terms of `Term Var` without free
variables whose binary code `blcT` has length exactly `n`. -/
def termsOfLen (Var : Type u) (n : ℕ) : List (Term Var) := termsOfLenF Var n n

@[simp] theorem termsOfLen_zero : termsOfLen Var 0 = [] := rfl

@[simp] theorem termsOfLen_one : termsOfLen Var 1 = [] := rfl

theorem termsOfLen_add_two (m : ℕ) :
    termsOfLen Var (m + 2) =
      (bvar m : Term Var) ::
        ((termsOfLen Var m).map abs ++
          (List.range (m + 1)).flatMap fun a =>
            (termsOfLen Var a).flatMap fun t => (termsOfLen Var (m - a)).map (app t)) := by
  have hm : termsOfLenF Var (m + 1) m = termsOfLen Var m :=
    termsOfLenF_fuel (by omega) (by omega)
  have hsplit : ∀ a ∈ List.range (m + 1),
      ((termsOfLenF Var (m + 1) a).flatMap fun t =>
          (termsOfLenF Var (m + 1) (m - a)).map (app t)) =
        (termsOfLen Var a).flatMap fun t => (termsOfLen Var (m - a)).map (app t) := by
    intro a ha
    have ha' : a ≤ m := by simpa [Nat.lt_succ_iff] using List.mem_range.mp ha
    rw [termsOfLenF_fuel (Var := Var) (n := a) (k := m + 1) (k' := a) (by omega) (by omega),
      termsOfLenF_fuel (Var := Var) (n := m - a) (k := m + 1) (k' := m - a) (by omega) (by omega)]
    rfl
  show termsOfLenF Var (m + 2) (m + 2) = _
  simp only [termsOfLenF, hm, List.flatMap_congr hsplit]

/-- Membership in `termsOfLen Var (m + 2)`, unfolded. -/
theorem mem_termsOfLen_add_two {t : Term Var} {m : ℕ} :
    t ∈ termsOfLen Var (m + 2) ↔
      t = bvar m ∨ (∃ s ∈ termsOfLen Var m, t = abs s) ∨
        ∃ a ≤ m, ∃ u ∈ termsOfLen Var a, ∃ v ∈ termsOfLen Var (m - a), t = app u v := by
  rw [termsOfLen_add_two]
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro (rfl | ⟨s, hs, rfl⟩ | ⟨a, ha, u, hu, v, hv, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, ha, u, hu, v, hv, rfl⟩)
  · rintro (rfl | ⟨s, hs, rfl⟩ | ⟨a, ha, u, hu, v, hv, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, ha, u, hu, v, hv, rfl⟩)

/-- The enumeration is correct: `termsOfLen Var n` contains exactly the terms
without free variables whose code has length `n`. -/
theorem mem_termsOfLen {t : Term Var} {n : ℕ} :
    t ∈ termsOfLen Var n ↔ IsDB t ∧ t.blcT.length = n := by
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    match n with
    | 0 =>
        simp only [termsOfLen_zero, List.not_mem_nil, false_iff, not_and]
        intro h _
        have := two_le_blcT_length_of_isDB h
        omega
    | 1 =>
        simp only [termsOfLen_one, List.not_mem_nil, false_iff, not_and]
        intro h _
        have := two_le_blcT_length_of_isDB h
        omega
    | (m + 2) =>
        rw [mem_termsOfLen_add_two]
        constructor
        · rintro (rfl | ⟨s, hs, rfl⟩ | ⟨a, ha, u, hu, v, hv, rfl⟩)
          · exact ⟨.bvar m, by simp⟩
          · obtain ⟨hs1, hs2⟩ := (ih m (by omega) (t := s)).1 hs
            exact ⟨.abs hs1, by simp [hs2]⟩
          · obtain ⟨hu1, hu2⟩ := (ih a (by omega) (t := u)).1 hu
            obtain ⟨hv1, hv2⟩ := (ih (m - a) (by omega) (t := v)).1 hv
            refine ⟨.app hu1 hv1, ?_⟩
            simp only [blcT_length_app, hu2, hv2]
            omega
        · rintro ⟨hdb, hlen⟩
          cases hdb with
          | bvar k =>
              left
              simp only [blcT_length_bvar] at hlen
              exact congrArg _ (by omega)
          | @abs s hs =>
              right; left
              simp only [blcT_length_abs] at hlen
              exact ⟨s, (ih m (by omega) (t := s)).2 ⟨hs, by omega⟩, rfl⟩
          | @app u v hu hv =>
              right; right
              simp only [blcT_length_app] at hlen
              have hu2 := two_le_blcT_length_of_isDB hu
              have hv2 := two_le_blcT_length_of_isDB hv
              refine ⟨u.blcT.length, by omega, u,
                (ih _ (by omega) (t := u)).2 ⟨hu, rfl⟩, v, ?_, rfl⟩
              exact (ih _ (by omega) (t := v)).2 ⟨hv, by omega⟩

/-- **The answer to the question**: `termsUpTo Var N` is the list of all terms of
`Term Var` without free variables whose binary code `blcT` has length `< N`. -/
def termsUpTo (Var : Type u) (N : ℕ) : List (Term Var) :=
  (List.range N).flatMap (termsOfLen Var)

/-- Correctness of the enumeration: `termsUpTo Var N` contains exactly the terms
without free variables whose code is shorter than `N`. -/
theorem mem_termsUpTo {t : Term Var} {N : ℕ} :
    t ∈ termsUpTo Var N ↔ IsDB t ∧ t.blcT.length < N := by
  simp only [termsUpTo, List.mem_flatMap, List.mem_range, mem_termsOfLen]
  constructor
  · rintro ⟨n, hn, hdb, rfl⟩; exact ⟨hdb, hn⟩
  · rintro ⟨hdb, hlen⟩; exact ⟨t.blcT.length, hlen, hdb, rfl⟩

/-- Correctness of the enumeration, phrased with the set of free variables:
`termsUpTo Var N` contains exactly the terms `t` with `fv t = ∅` and
`t.blcT.length < N`. -/
theorem mem_termsUpTo_fv [DecidableEq Var] {t : Term Var} {N : ℕ} :
    t ∈ termsUpTo Var N ↔ fv t = ∅ ∧ t.blcT.length < N := by
  rw [mem_termsUpTo, fv_eq_empty_iff_isDB]

/-! ## The enumerations have no repetitions -/

theorem termsOfLen_nodup (n : ℕ) : (termsOfLen Var n).Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
        have happ : ∀ a ≤ m,
            (((termsOfLen Var a).flatMap fun t =>
              (termsOfLen Var (m - a)).map (app t))).Nodup := by
          intro a ha
          refine List.nodup_flatMap.2 ⟨fun u _ => ?_, ?_⟩
          · exact (ih (m - a) (by omega)).map (fun _ _ h => by injection h)
          · refine (ih a (by omega)).pairwise_of_forall_ne ?_
            intro u _ u' _ huu'
            refine List.disjoint_left.2 ?_
            rintro w hw hw'
            simp only [List.mem_map] at hw hw'
            obtain ⟨x, -, rfl⟩ := hw
            obtain ⟨y, -, hy⟩ := hw'
            injection hy with h1 _
            exact huu' h1.symm
        rw [termsOfLen_add_two]
        refine List.nodup_cons.2 ⟨?_, ?_⟩
        · intro hmem
          rcases List.mem_append.1 hmem with h | h
          · obtain ⟨s, -, hs⟩ := List.mem_map.1 h
            simp at hs
          · obtain ⟨a, -, h⟩ := List.mem_flatMap.1 h
            obtain ⟨u, -, h⟩ := List.mem_flatMap.1 h
            obtain ⟨v, -, hv⟩ := List.mem_map.1 h
            simp at hv
        · refine List.Nodup.append ((ih m (by omega)).map (fun _ _ h => by injection h)) ?_ ?_
          · refine List.nodup_flatMap.2 ⟨fun a ha => happ a ?_, ?_⟩
            · simpa [Nat.lt_succ_iff] using List.mem_range.mp ha
            · refine List.nodup_range.pairwise_of_forall_ne ?_
              rintro a - b - hab
              refine List.disjoint_left.2 ?_
              rintro w hw hw'
              simp only [List.mem_flatMap, List.mem_map] at hw hw'
              obtain ⟨u, hu, x, -, rfl⟩ := hw
              obtain ⟨u', hu', y, -, hy⟩ := hw'
              have h1 := (mem_termsOfLen (Var := Var)).1 hu
              have h2 := (mem_termsOfLen (Var := Var)).1 hu'
              injection hy with hy1 _
              subst hy1
              exact hab (by omega)
          · refine List.disjoint_left.2 ?_
            rintro w hw hw'
            simp only [List.mem_map] at hw
            obtain ⟨s, -, rfl⟩ := hw
            simp only [List.mem_flatMap, List.mem_map] at hw'
            obtain ⟨a, -, u, -, v, -, h⟩ := hw'
            simp at h

theorem termsUpTo_nodup (N : ℕ) : (termsUpTo Var N).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun n _ => termsOfLen_nodup n, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne ?_
  rintro m - n - hmn
  refine List.disjoint_left.2 ?_
  intro t ht ht'
  have h1 := (mem_termsOfLen (Var := Var)).1 ht
  have h2 := (mem_termsOfLen (Var := Var)).1 ht'
  exact hmn (h1.2 ▸ h2.2)

/-! ## Examples -/

/-- Rendering a pure de Bruijn term in de Bruijn notation, for display. -/
def dbToString : Term Var → String
  | bvar n => toString n
  | fvar _ => "?"
  | abs t => "λ" ++ dbToString t
  | app t u => "(" ++ dbToString t ++ " " ++ dbToString u ++ ")"

/-- The terms whose code has length exactly `6`. -/
example : (termsOfLen Unit 6).map dbToString = ["4", "λ2", "λλ0", "(0 0)"] := by decide

/-- The terms whose code has length `< 7`. -/
example :
    (termsUpTo Unit 7).map dbToString =
      ["0", "1", "2", "λ0", "3", "λ1", "4", "λ2", "λλ0", "(0 0)"] := by decide

/-- Every listed term really has a short code. -/
example : ((termsUpTo Unit 9).map fun t => t.blcT.length).all (· < 9) := by decide

/-- The number of terms with a code of length `< N`, for `N = 0, …, 10`. -/
example : ((List.range 11).map fun N => (termsUpTo Unit N).length) =
    [0, 0, 0, 1, 2, 4, 6, 10, 15, 25, 39] := by decide
