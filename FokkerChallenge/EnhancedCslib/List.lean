import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem foldl_union_replicate_empty {fs : Finset String} (n : ℕ) :
    List.foldl (· ∪ ·) fs (List.replicate n ∅) = fs := by
  induction n generalizing fs with
  | zero => grind
  | succ n ih =>
    simp [List.replicate_succ]
    rw [ih]
    grind

lemma union_foldl {l : List _} {fs : Finset String}:
  fs ⊆ l.foldl Union.union fs := by
  induction l generalizing fs with grind

/-- Any member of `xs` is at most `xs.max?.getD d`, for any default `d`. -/
theorem List.mem_le_max?_getD {α : Type*} [Max α] [LE α]
    [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {xs : List α} {x d : α} (hx : x ∈ xs) : x ≤ xs.max?.getD d := by
  rcases hopt : xs.max? with _ | m
  · simp [List.max?_eq_none_iff.mp hopt] at hx
  · simpa [hopt] using (List.max?_eq_some_iff.mp hopt).2 x hx

/-- A member of the right list of a `Forall₂` is related to some member of the
left list. -/
theorem forall₂_exists_left {α : Type*} {R : α → α → Prop} {l1 l2 : List α}
    (h : List.Forall₂ R l1 l2) {b : α} (hb : b ∈ l2) : ∃ a ∈ l1, R a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact ⟨_, List.mem_cons_self .., hab⟩
      · obtain ⟨a, ha, hR⟩ := ih hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

theorem forall₂_exists_right {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : ∀ a ∈ as, ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp
  | @cons a b as bs hab _ ih =>
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨d, hd, hcd⟩ := ih c hc'
        exact ⟨d, by simp [hd], hcd⟩

theorem forall₂_snoc_right {α β : Type _} (R : α → β → Prop) (l₀ : List α) (l : List β) (b : β)
    (h : List.Forall₂ R l₀ (l ++ [b])) :
    ∃ l₀' a, l₀ = l₀' ++ [a] ∧ List.Forall₂ R l₀' l ∧ R a b := by
  induction l generalizing l₀ with
  | nil =>
      cases h with
      | cons hab hrest => cases hrest; exact ⟨[], _, rfl, List.Forall₂.nil, hab⟩
  | cons c l ih =>
      cases h with
      | cons hab hrest =>
          obtain ⟨l₀', a, rfl, h1, h2⟩ := ih _ hrest
          exact ⟨_ :: l₀', a, rfl, List.Forall₂.cons hab h1, h2⟩

theorem forall₂_refl {α : Type _} {R : α → α → Prop} (l : List α) :
    List.Forall₂ (Relation.ReflTransGen R) l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons Relation.ReflTransGen.refl ih

theorem forall₂_trans {α : Type _} {R : α → α → Prop} {l₁ l₂ l₃ : List α}
    (h₁ : List.Forall₂ (Relation.ReflTransGen R) l₁ l₂)
    (h₂ : List.Forall₂ (Relation.ReflTransGen R) l₂ l₃) :
          List.Forall₂ (Relation.ReflTransGen R) l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
      cases h₂ with
      | cons hbc hrest => exact List.Forall₂.cons (hab.trans hbc) (ih hrest)

theorem forall₂_sub {α : Type _} {R1 R2 : α → α → Prop} {l₁ l₂ : List α}
    (h : R1 ≤ R2)
    (h₁ : List.Forall₂ R1 l₁ l₂) :
          List.Forall₂ R2 l₁ l₂  := by
  induction h₁ with
  | nil => exact List.Forall₂.nil
  | cons g _ ih => exact List.Forall₂.cons (h _ _ g) ih


theorem forall₂_concat {α β : Type _} {R : α → β → Prop} {as : List α} {bs : List β} {a : α}
    {b : β} (h : List.Forall₂ R as bs) (hab : R a b) :
    List.Forall₂ R (as ++ [a]) (bs ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hh _ ih => exact List.Forall₂.cons hh ih
