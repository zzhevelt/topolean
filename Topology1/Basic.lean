import Mathlib.Init.Set
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Module.Basic

/-
  Most examples are skipped, because they require
  importing many libraries and spending much time
  learning to handle imported objects
-/


-- 0. SET THEORY
namespace s0
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

-- 1. METRIC SPACES
namespace s1

  -- Definition 1.1
  -- metric space

  class MetricSpace (α : Type u) where
    d: α → α → ℝ
    d_nonneg: ∀ x y: α,        d x y ≥ 0
    d_symmetry: ∀ x y: α,      d x y = d y x
    d_triangle: ∀ x y z: α,    d x z ≤ d x y + d y z
    d_nondegeneracy: ∀ x y: α, d x y = 0 ↔ x = y

  -- Definition 1.2
  -- open balls

  -- note: no restriction on ε > 0
  def openBall   [ms: MetricSpace α] (x: α) (ε: ℝ):=
    { y : α | ms.d x y < ε }
  def closedBall [ms: MetricSpace α] (x: α) (ε: ℝ):=
    { y : α | ms.d x y ≤ ε }
  def sphere     [ms: MetricSpace α] (x: α) (ε: ℝ):=
    { y : α | ms.d x y = ε }

  lemma center_in_open_ball [MetricSpace α] (x: α) {ε: ℝ} (εpos: ε > 0): x ∈ openBall x ε :=
    by simp[openBall, show MetricSpace.d x x = 0 by simp[MetricSpace.d_nondegeneracy]]; linarith;

  -- Definition 1.3
  -- bounded subset

  def bounded [MetricSpace α] (S: Set α) := ∃ x: α, ∃ r: ℝ, S ⊆ openBall x r

  -- Definition 1.4
  -- normed vector space

  class NormedVectorSpace (V : Type u) extends AddCommGroup V, Module ℝ V where
    norm: V → ℝ
    norm_nonneg: ∀ v: V,            norm v ≥ 0
    norm_linearity: ∀ c: ℝ, ∀ v: V, norm (c • v) = (|c| * norm v)
    norm_triangle: ∀ v w: V,        norm (v + w) ≤ norm v + norm w
    norm_nondegeneracy: ∀ v: V,     norm v = 0 → v = 0

  -- Proposition 1.5
  -- normed vector space is metric space

  instance NormedVectorSpace.toMetricSpace [NVS: NormedVectorSpace V]: MetricSpace V where
      d := fun x y => NVS.norm (x - y)
      d_nonneg := fun x y => norm_nonneg (x - y)
      d_symmetry := by
        simp
        intros x y
        rw [show y-x = (-1: ℝ)•(x-y) by simp]
        rw [NVS.norm_linearity]
        simp
      d_triangle := by
        simp
        intros x y z
        rw [show x-z = (x-y) + (y-z) by simp]
        apply NVS.norm_triangle
      d_nondegeneracy := fun x y => ⟨ by
        simp
        intro h
        have h': x-y=0 := NVS.norm_nondegeneracy (x-y) h
        exact sub_eq_zero.mp h',
        by
        intro h
        simp [h]
        rw [show 0 = (0: ℝ) • x by simp, NVS.norm_linearity]
        simp ⟩

    -- Continuity
    variable (ε δ: ℝ)

    -- Definition 1.8
    -- epsilontic definition of continuity

    def continuous_at_point [X: MetricSpace α] [Y: MetricSpace β] (f: α → β) (x: α) :=
      ∀ ε > 0, ∃ δ > 0, ∀ x': α,
        X.d x x' < δ → Y.d (f x) (f x') < ε

    def continuous_eps [MetricSpace α] [MetricSpace β] (f: α → β) :=
      ∀ x: α, continuous_at_point f x

    -- Definition 1.11
    -- neighbourhood and open set

    def neighbourhood [MetricSpace α] (U: Set α) (x: α) :=
      ∃ ε > 0, openBall x ε ⊆ U

    def openSubset [MetricSpace α] (U: Set α) :=
      ∀ x ∈ U, ∃ ε > 0, openBall x ε ⊆ U

    def openNeighbourhood [MetricSpace α] (U: Set α) (x: α):=
      neighbourhood U x ∧ openSubset U

    theorem openNeighbourhood_eq [MetricSpace α] (U: Set α) (x: α):
      openNeighbourhood U x ↔ openSubset U ∧ x ∈ U :=
        ⟨ by
          intro ⟨⟨ε, εpos, h'⟩, hos⟩
          exact ⟨hos, Set.mem_of_subset_of_mem h' (center_in_open_ball x εpos)⟩,

          by intro ⟨h, h'⟩; exact ⟨h x h', h⟩⟩

    -- Example 1.12
    -- the empty subset is open

    theorem empty_open [MetricSpace α]:
      openSubset (∅: Set α) := by simp [openSubset]

    -- the entire set is open
    theorem univ_open [MetricSpace α]:
      openSubset (Set.univ: Set α) :=
        fun _ _ => ⟨_, ⟨Real.zero_lt_one, Set.subset_univ _⟩⟩

    lemma openBall_is_openSubset [MetricSpace α] (x: α) (ε: ℝ): openSubset (openBall x ε) := by
      rw [openBall, openSubset]
      intros a ha
      let d := ((MetricSpace.d x a): ℝ)
      have ha: d < ε := ha
      use (ε - d) / 2
      exact ⟨by linarith, by
        intros y hy;
        simp [openBall] at *;
        exact calc
          ((MetricSpace.d x y) : ℝ) ≤ (MetricSpace.d x a) + (MetricSpace.d a y) := MetricSpace.d_triangle ..
          _                         = d + (MetricSpace.d a y)                   := rfl
          _                         < d + (ε - d) / (2: ℝ)                      := (Real.add_lt_add_iff_left d).mpr hy
          _                         < ε                                         := by linarith ⟩

    -- Proposition 1.14
    -- continuity in terms of open sets

    def continuous [MetricSpace α] [MetricSpace β] (f: α → β) :=
      ∀ Oy: Set β, openSubset Oy → openSubset (f⁻¹' Oy)

    theorem continuous_eps_eq_continuous [MetricSpace α] [MetricSpace β] (f: α → β):
      continuous_eps f ↔ continuous f := by
        simp [continuous, continuous_eps]
        exact
          ⟨by intros hc Oy hOy
              rw [openSubset]
              intros x hx
              have hBfx := hOy (f x) hx
              cases hBfx with | intro ε h' =>
              cases h' with | intro εpos hBfx =>
              have hBx: ∃ δ > 0, f '' (openBall x δ) ⊆ openBall (f x) ε := by
                have hcx := hc x
                rw [continuous_at_point] at hcx
                have hcx := hcx ε εpos
                cases hcx with | intro δ hδ =>
                cases hδ with | intro hδ hcx =>
                use δ
                simp [openBall]
                exact ⟨hδ, hcx⟩
              cases hBx with | intro δ hBx =>
              cases hBx with | intro hδ hBx =>
              use δ
              exact ⟨hδ, Set.image_subset_iff.mp (Set.Subset.trans hBx hBfx)⟩ ,

          by  intros h x
              rw [continuous_at_point]
              intros ε hε
              let Bfxε := openBall (f x) ε
              have hh: openSubset Bfxε := openBall_is_openSubset _ _
              have h': openSubset (f ⁻¹' Bfxε) := by exact h Bfxε hh
              rw [openSubset] at h'
              have h'': x ∈ f ⁻¹' Bfxε := by simp; exact center_in_open_ball (f x) hε
              have h' := h' x h''
              cases h' with | intro δ h' =>
              cases h' with | intro hδ ho =>
              use δ
              exact ⟨hδ, fun _ a ↦ ho a⟩⟩

    -- Compactness

    -- Definition 1.16
    -- sequence

    def sequence (_: ℕ → α) := true
    def injective_on_nat (f: ℕ → ℕ) := ∀ a b, f a = f b → a = b
    def sub_sequence (x: ℕ → α) (y: ℕ → α) :=
      ∃ ι: ℕ → ℕ, injective_on_nat ι ∧ y = x ∘ ι  -- y is subsequence of x

    -- Definition 1.17
    -- convergence to limit of a sequence

    def converges_to [ms: MetricSpace α] (x: ℕ → α) (a: α) :=
      ∀ ε > 0, ∃ n: ℕ, ∀ i > n, ms.d (x i) a < ε
    def converges [MetricSpace α] (x: ℕ → α):=
      ∃ a: α, converges_to x a

    -- Definition 1.18
    -- Cauchy sequence

    def cauchy_sequence [ms: MetricSpace α] (x: ℕ → α) :=
      ∀ ε > 0, ∃ n: ℕ, ∀ i > n, ∀ j > n, ms.d (x i) (x j) < ε

    -- Definition 1.19
    -- complete metric space

    def complete_metric_space [MetricSpace α] :=
      ∀ x: ℕ → α, cauchy_sequence x → converges x

    class NormedVectorSpaceWithMetricSpace (V : Type u) extends NormedVectorSpace V where
      metric_space := toNormedVectorSpace.toMetricSpace

    class BanachSpace (V : Type u) extends NormedVectorSpaceWithMetricSpace V where
      completeness: ∀ x: ℕ → V, cauchy_sequence x → converges x

    -- Definition 1.20
    -- sequentially compact metric space

    def sequentially_compact [MetricSpace α] (_: MetricSpace α) :=
      ∀ x: ℕ → α, ∃ ι: ℕ → ℕ, injective_on_nat ι ∧ converges (x ∘ ι)

    -- Proposition 1.21
    -- sequentially compact metric spaces are equivalently compact metric spaces

    variable (σ : Type)
    theorem seq_compactness_eq_compactness [X: MetricSpace α]:
      sequentially_compact X ↔
      ∀ I: Set σ, ∀ U: σ → Set α, ((∀i ∈ I, openSubset (U i)) ∧ α = (⋃ (i ∈ I), U i)) →
        ∃ J ⊆ I, Finite J ∧ α = (⋃ (j ∈ J), U j) := sorry

end s1
