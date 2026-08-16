import Mathlib.Logic.Relation

namespace Relation
namespace ReflTransGen

theorem head_induction_on₂ {motive : ∀ a : α, ReflTransGen r a b → Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b .refl)
    (single : ∀ {a : α} (h' : r a b), motive a (ReflTransGen.single h'))
    (head₂ : ∀ {a c d : α} (h₁ : r a c) (h₂ : r c d) (h : ReflTransGen r d b),
      motive d h → motive a ((h.head h₂).head h₁)) :
    motive a h := by
  -- We strengthen the statement so that a single `head_induction_on` suffices: along with
  -- `motive a h` we also carry the value of the motive at any one-step extension of `h`.
  have key : ∀ (a : α) (h : ReflTransGen r a b),
      motive a h ∧ ∀ (z : α) (hz : r z a), motive z (h.head hz) := by
    intro a h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨refl, fun _ hz => single hz⟩
    | @head a c h' hcb ih => exact ⟨ih.2 a h', fun _ hz => head₂ hz h' hcb ih.1⟩
  exact (key a h).1
/-- The two-step analogue of `Relation.ReflTransGen.cases_head`: a chain either is empty,
consists of a single step, or starts with two steps. -/
theorem cases_head₂ {a : α} (h : ReflTransGen r a b) :
    a = b ∨ r a b ∨ ∃ c d, r a c ∧ r c d ∧ ReflTransGen r d b := by
  induction h using Relation.ReflTransGen.head_induction_on₂ with
  | refl => exact Or.inl rfl
  | single h' => exact Or.inr (Or.inl h')
  | head₂ h₁ h₂ h _ => exact Or.inr (Or.inr ⟨_, _, h₁, h₂, h⟩)
