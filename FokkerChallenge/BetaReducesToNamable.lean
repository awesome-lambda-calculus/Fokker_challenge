import FokkerChallenge.BetaCheck

/-!
# Terms that β-reduce **to** a two-name-nameable term

`FokkerChallenge.BetaCheck` studies the class of terms that are β-*reducts* of
terms nameable with the two variable names `x`, `y` (`BetaReductOfNamable`).
This file treats the dual situation: a term `M` that itself β-reduces to a
nameable term `S`.

Such an `M` is not a one-point basis either.  The argument goes through the
βη-normal witness produced by `isNamedOfXY_not_basises_nf`: if `y` is a βη-normal
closed term that no applicative combination of `S` βη-reduces to, then no
applicative combination `t` of `M` βη-reduces to `y` either.  Indeed `t`
β-reduces to the corresponding combination `s` of `S`
(`genfinset_single_betaStar`), so confluence of βη gives a common reduct of `y`
and `s`, which is `y` itself because `y` is βη-normal; hence `s ↠βη y`, a
contradiction.

The file ends with a certificate format: a list `M = t₀, t₁, …, tₙ` of terms with
`tᵢ ⭢βᶠ tᵢ₊₁` and `namableXY tₙ = true`, checked by `betaCheck`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- If `M ↠βᶠ S`, then every applicative combination of `M` β-reduces to the
corresponding applicative combination of `S`. -/
theorem genfinset_single_betaStar {M S : Term String} (hstar : M ↠βᶠ S) (hM : M.LC) :
    ∀ {t}, GenFinset [M] t → ∃ s, GenFinset [S] s ∧ t ↠βᶠ s := by
  intro t ht
  induction ht with
  | @base a ha =>
      simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨S, ClosedUnderApp.base (by simp), hstar⟩
  | @app a b ha hb iha ihb =>
      obtain ⟨sa, hsa, ha'⟩ := iha
      obtain ⟨sb, hsb, hb'⟩ := ihb
      refine ⟨Term.app sa sb, ClosedUnderApp.app hsa hsb, ?_⟩
      have hlcb : b.LC := genfinset_lc hb (by grind)
      have hlcsa : sa.LC := by
        rcases FullBeta.steps_lc_or_rfl ha' with ⟨-, h⟩ | h
        · exact h
        · exact h ▸ genfinset_lc ha (by grind)
      exact (FullBeta.redex_app_l_cong ha' hlcb).trans (FullBeta.redex_app_r_cong hb' hlcsa)

/-- **A term that β-reduces to a term nameable with the two names `x`, `y` is
not a one-point basis.** -/
theorem not_basis_of_betaStar_namableXY {M S : Term String} (hstar : M ↠βᶠ S)
    (hS : namableXY S = true) : not_basis M := by
  have hlcM : M.LC := by
    rcases FullBeta.steps_lc_or_rfl hstar with ⟨h, -⟩ | h
    · exact h
    · exact h ▸ lc_of_namableXY hS
  obtain ⟨y, hylc, hyfv, hynf, hy⟩ :=
    isNamedOfXY_not_basis_nf (t := S) (by rw [isNamedOfXY_eq_namableXY]; exact hS)
  refine ⟨y, hylc, hyfv, ?_⟩
  intro t ht steps
  obtain ⟨s, hs, hts⟩ := genfinset_single_betaStar hstar hlcM ht
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (Relation.ReflTransGen.mono le_sup_left _ _ hts)
  have hZ := Relation.Normal.reflTransGen_eq hynf hz1
  subst hZ
  exact hy s hs hz2

/-! ## Certificates -/

/-- `reducesToNamableCheck M l` checks that `l` is a certificate for the fact
that `M` β-reduces to a term nameable with the two names `x`, `y`: it starts at
`M`, its consecutive elements are β-steps, and its last element is nameable. -/
def reducesToNamableCheck (M : Term String) (l : List (Term String)) : Bool :=
  (l.head? == some M) && betaChainCheck l &&
    (match l.getLast? with
     | some S => namableXY S
     | none => false)

theorem not_basis_of_reducesToNamableCheck {M : Term String} {l : List (Term String)}
    (h : reducesToNamableCheck M l = true) : not_basis M := by
  simp only [reducesToNamableCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hhead, hchain⟩, hlast⟩ := h
  match hl : l.getLast? with
  | none => rw [hl] at hlast; simp at hlast
  | some S =>
      rw [hl] at hlast
      exact not_basis_of_betaStar_namableXY (betaChainCheck_sound l M S hhead hl hchain) hlast

/-- A table of certificates, one for each term of a list. -/
def reducesToNamableEntriesOK (es : List (Term String × List (Term String))) : Bool :=
  es.all (fun p => reducesToNamableCheck p.1 p.2)

theorem not_basis_of_reducesToNamableEntriesOK {es : List (Term String × List (Term String))}
    (h : reducesToNamableEntriesOK es = true) : ∀ M ∈ es.map Prod.fst, not_basis M := by
  intro M hM
  simp only [List.mem_map] at hM
  obtain ⟨p, hp, rfl⟩ := hM
  simp only [reducesToNamableEntriesOK, List.all_eq_true] at h
  exact not_basis_of_reducesToNamableCheck (h p hp)

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
