import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.Fmt

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


@[simp, scoped grind =]
def lt7: Term String -> Bool
  | Term.bvar n => n < 7
  | Term.fvar _ => true
  | Term.abs t => lt7 t
  | Term.app t1 t2 => lt7 t1 && lt7 t2

@[simp, scoped grind =]
def encode: Term String → Option (List Char)
  | Term.bvar 0 => some (['0'])
  | Term.bvar 1 => some (['1'])
  | Term.bvar 2 => some (['2'])
  | Term.bvar 3 => some (['3'])
  | Term.bvar 4 => some (['4'])
  | Term.bvar 5 => some (['5'])
  | Term.bvar 6 => some (['6'])
  | Term.bvar _ => none
  | Term.fvar _ => none -- Return None immediately when an fvar is met
  | Term.abs t =>
    match encode t with
    | some bs => some ('L':: bs)
    | none => none
  | Term.app t₁ t₂ =>
    match encode t₁, encode t₂ with
    | some bs₁, some bs₂ => some ('A' :: bs₁ ++ bs₂)
    | _, _ => none

@[simp, scoped grind =]
def decodeFuel : Nat → List Char → Option (Term String × List Char)
  | 0,  _ => none
  | f + 1, 'L' :: bs =>
    match decodeFuel f bs with
    | some (t, rest) => some (Term.abs t, rest)
    | none => none
  | f + 1, 'A' :: bs =>
    match decodeFuel f bs with
    | some (t₁, rest₁) =>
      match decodeFuel f rest₁ with
      | some (t₂, rest₂) => some (Term.app t₁ t₂, rest₂)
      | none => none
    | none => none
  | _ + 1, '0' :: bs => some (Term.bvar 0, bs)
  | _ + 1, '1' :: bs => some (Term.bvar 1, bs)
  | _ + 1, '2' :: bs => some (Term.bvar 2, bs)
  | _ + 1, '3' :: bs => some (Term.bvar 3, bs)
  | _ + 1, '4' :: bs => some (Term.bvar 4, bs)
  | _ + 1, '5' :: bs => some (Term.bvar 5, bs)
  | _ + 1, '6' :: bs => some (Term.bvar 6, bs)
  | _, __=> none

@[simp, scoped grind =]
def decode (bs : List Char) : Option (Term String × List Char) :=
  decodeFuel bs.length bs

-- 4. Auxiliary Core Properties

theorem termNodes_lt_encode_length  (t : Term String) (bs : List Char)
    (henc : encode t = some bs) : fokker_size t < bs.length := by
  induction t generalizing bs with
  | bvar n => unfold encode at henc
              split at henc <;> grind
  | fvar x => simp [encode] at henc
  | abs body ih =>
    dsimp [encode] at henc
    cases h_enc : encode body with
    | none => simp [h_enc] at henc
    | some bs' =>
      simp [h_enc] at henc; subst bs
      dsimp [fokker_size]
      have ih' := ih  bs' h_enc
      omega
  | app t₁ t₂ ih₁ ih₂ =>
    dsimp [encode] at henc
    cases h1 : encode t₁ with
    | none => simp [h1] at henc
    | some bs₁ =>
      cases h2 : encode t₂ with
      | none => simp [h2] at henc
      | some bs₂ =>
        simp [h1, h2] at henc; subst bs
        dsimp [fokker_size]
        have ih1' := ih₁ bs₁ h1
        have ih2' := ih₂ bs₂ h2
        simp
        omega

-- 5. Correctness Proof: `decode (encode t) = t`

theorem decodeFuel_encode (t : Term String) (fuel : Nat) (bs rest : List Char)
    (henc : encode t = some bs) (hnodes : fokker_size t < fuel) :
    decodeFuel fuel (bs ++ rest) = some (t, rest) := by
  induction t generalizing fuel bs rest with
  | bvar n =>
    cases fuel with | zero => contradiction | succ f =>
    unfold encode at henc
    split at henc
    any_goals cases henc
    any_goals simp [decodeFuel]
    all_goals grind
  | fvar x => simp [encode] at henc
  | abs body ih =>
    cases fuel with | zero => contradiction | succ f =>
    dsimp [encode] at henc
    cases h_enc : encode  body with
    | none => simp [h_enc] at henc
    | some bs' =>
      simp [h_enc] at henc; subst bs
      simp [decodeFuel]
      have hf : fokker_size body < f := by simp [fokker_size] at hnodes; omega
      have h1 := ih f bs' rest h_enc hf
      rw [h1]
  | app t₁ t₂ ih₁ ih₂ =>
    cases fuel with | zero => contradiction | succ f =>
    dsimp [encode] at henc
    cases h1 : encode t₁ with
    | none => simp [h1] at henc
    | some bs₁ =>
      cases h2 : encode t₂ with
      | none => simp [h2] at henc
      | some bs₂ =>
        simp [h1, h2] at henc; subst bs
        simp [decodeFuel]
        have hf₁ : fokker_size t₁ < f := by simp [fokker_size] at hnodes; omega
        have h1' := ih₁ f bs₁ (bs₂ ++ rest) h1 hf₁
        rw [h1']
        have hf₂ : fokker_size t₂ < f := by simp [fokker_size] at hnodes; omega
        have h2' := ih₂ f bs₂ rest h2 hf₂
        simp
        rw [h2']

theorem decode_correct (t : Term String) (bs):
    encode t = some bs -> decode bs = some (t, []) := by
  intro hbs
  unfold decode
  have hlen := termNodes_lt_encode_length t bs hbs
  have h := decodeFuel_encode t bs.length bs [] hbs hlen
  simp at h
  exact h

theorem encode_wf_succeeds (t : Term String) (ht : t.fv = ∅) (h7: lt7 t):
 ∃ bs, encode t = some bs := by
  induction t with
  | bvar a => unfold encode
              split <;> grind
  | fvar _ => simp [fv] at ht
  | abs _ _ => grind [fv, encode]
  | app _ _ ih1 ih2 =>  unfold fv at ht
                        simp at ht
                        obtain ⟨h1, h2⟩ := ht
                        obtain ⟨_, h1⟩ := ih1 h1 (by grind)
                        obtain ⟨_, h2⟩ := ih2 h2 (by grind)
                        unfold encode
                        simp [h1, h2]

-- 6. Inverse Correctness Proof: `encode (decode bs) = bs`

theorem decodeFuel_sound (fuel):
     ∀ bs t rest,
    decodeFuel fuel bs = some (t, rest) →
    ∃ t_bs, encode t = some t_bs ∧ t_bs ++ rest = bs := by
  induction fuel with
  | zero => grind
  | succ n ih =>
  intros bs t rest h
  unfold decodeFuel at h
  split at h
  any_goals tauto
  any_goals split at h
  any_goals tauto
  any_goals split at h
  any_goals tauto
  any_goals cases h
  all_goals unfold encode
  all_goals grind

theorem encode_decode (bs : List Char) (t : Term String) (rest : List Char) :
    decode bs = some (t, rest) →
    ∃ t_bs, encode t = some t_bs ∧ t_bs ++ rest = bs := by
  intro h
  unfold decode at h
  exact decodeFuel_sound bs.length bs t rest h
