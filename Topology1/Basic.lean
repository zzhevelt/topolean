import Mathlib.Init.Set
import Mathlib.Data.Set.Lattice

-- 0. SET THEORY
section s0
  /-
    #check Set
    #check Set.Subset
    #check Set.compl -- complement subset
    #check Set.image
    #check Set.preimage
    #check Set.iUnion -- indexed union
    #check Set.iInter -- indexed intersection
  -/

  variable (α β : Type)
  variable (X : Set α)
  variable (Y : Set β)
  variable (f : α → β)

  variable (σ : Type)
  variable (I : Set σ)
  variable (S : I → Set α)
  variable (T : I → Set β)

  example: Set.image f X = f '' X  := rfl -- notation
  example: Set.iUnion S = ⋃ i, S i := rfl -- notation

  -- Proposition 0.1
  -- images preserve unions but not in general intersections

  theorem image_union (f : α → β) (S : I → Set α):
    f '' (⋃ i, S i) = ⋃ i, f '' (S i) := Set.image_iUnion

  theorem image_inter_subset (f : α → β) (S : I → Set α):
    f '' (⋂ i, S i) ⊆ ⋂ i, f '' (S i) := Set.image_iInter_subset ..

  theorem image_inter (f : α → β) (S : I → Set α) (h : Set.InjOn f (⋃ i, S i)) (_ : Nonempty I):
    f '' (⋂ i, S i) = ⋂ i, f '' (S i) := Set.InjOn.image_iInter_eq h

  -- Proposition 0.2
  -- pre-images preserve unions and intersections

  theorem preimage_union (f : α → β) (T : I → Set β):
    f ⁻¹' (⋃ i, T i) = ⋃ i, f ⁻¹' (T i) := Set.preimage_iUnion

  theorem preimage_inter (f : α → β) (T : I → Set β):
    f ⁻¹' (⋂ i, T i) = ⋂ i, f ⁻¹' (T i) := Set.preimage_iInter

  -- Proposition 0.3
  -- de Morgan's law

  theorem compl_union {X : Set α} (S : I → Set α) (_: ∀ i, S i ⊆ X) (_: Nonempty I):
    X \ ⋃ i, S i = ⋂ i, X \ S i := Set.diff_iUnion ..

  theorem compl_inter {X : Set α} (S : I → Set α) (_: ∀ i, S i ⊆ X):
    X \ ⋂ i, S i = ⋃ i, X \ S i := Set.diff_iInter ..

  theorem subset_iff_compl_subset {X : Set α} (S₁ S₂ : Set α) (h₁: S₁ ⊆ X) (h₂: S₂ ⊆ X):
    S₁ ⊆ S₂ ↔ X \ S₂ ⊆ X \ S₁ :=
      ⟨ Set.diff_subset_diff_right,
      by
      intros h a ha
      have h': X \ (X \ S₁) ⊆ X \ (X \ S₂) := Set.diff_subset_diff_right h
      rw [Set.diff_diff_cancel_left h₁, Set.diff_diff_cancel_left h₂] at h'
      exact h' ha ⟩
end s0
