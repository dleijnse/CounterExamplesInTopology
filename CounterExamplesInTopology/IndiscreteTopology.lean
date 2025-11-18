import Mathlib

/-
  ## The indiscrete topology
  Mathlib implements the Indiscrete topology in the following way:
  The set of all topologies on X is a poset (ordered by reverse inclusion)
  and one then takes the top element, i.e. one defines the indiscrete topology
  as the coarsest topology on X.
-/

class IndiscreteTopology (X : Type) [t : TopologicalSpace X] : Prop where
  eq_top : t = ⊤

-- Throughout this file, X has the indiscrete topology
variable (X : Type) [t : TopologicalSpace X] [h : IndiscreteTopology X]

lemma topology_eq_top : t = ⊤ := by
  exact h.eq_top

lemma indiscrete_coarsest_topology [τ : TopologicalSpace X] : τ ≤ t := by
  rw [h.eq_top]
  exact OrderTop.le_top τ

-- We now construct the indiscrete topology explicitly, by constructing a topology where
-- only the empty set and the whole set are open
def IndiscreteTopology' : TopologicalSpace X where
  IsOpen (A : Set X) := A = ∅ ∨ A = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    intro A B hA hB
    rcases hA with (h | h) <;> rcases hB with (h'| h') <;> rw [h, h'] <;> try (left; tauto_set)
    tauto_set
  isOpen_sUnion := by
    intro s hs
    have h : Set.univ ∈ s ∨ ¬ Set.univ ∈ s := Classical.em (Set.univ ∈ s)
    rcases h with (hl | hr)
    · right
      refine Set.eq_univ_of_univ_subset ?_
      exact Set.subset_sUnion_of_subset s Set.univ (fun ⦃a⦄ a_1 ↦ a_1) hl
    · left
      have hEmpty (A : Set X) : A ∈ s → A = ∅ := by
        intro hA
        have hA' := hs A hA
        have hAnot_Univ : ¬ A = Set.univ := fun h' => hr (h' ▸ hA)
        tauto
      exact Set.sUnion_eq_empty.mpr hEmpty

lemma indiscr'_eq_top : IndiscreteTopology' = ⊤ := by
  sorry

lemma open_iff_empty_or_all (A : Set X) : IsOpen A ↔ A = ∅ ∨ A = ⊤ :=
  h.eq_top ▸ TopologicalSpace.isOpen_top_iff A

lemma compact_of_indiscrete (A : Set X) : IsCompact A := by
  apply isCompact_of_finite_subcover
  intro ι U hUOpen hi
  rcases em (∃ i : ι, U i = Set.univ) with (hU | hnU)
  · obtain ⟨j, hUj⟩ := hU
    use {j}
    simp [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, hUj]
  · rw [not_exists] at hnU
    have hE : ∀ i : ι, U i = ∅ := by
      intro j
      have hUj := (open_iff_empty_or_all X (U j)).mp (hUOpen j)
      tauto
    have hAEmpty : A = ∅ := by
      suffices hInc : A ⊆ ∅
      · exact Set.subset_eq_empty hInc rfl
      · calc A ⊆ ⋃ i, U i      := by exact hi
             _  ⊆ ⋃ i : ι, ∅   := by simp [hE]
             _  = ∅             := by exact Set.iUnion_empty
    use ∅
    tauto_set

lemma all_functions_to_indiscrete_continuous (Y : Type) [TopologicalSpace Y] (f : Y → X) :
    Continuous f := by
  sorry

lemma indiscrete_path_connected : PathConnectedSpace X := by
  sorry

lemma indiscrete_not_T0 : ¬ T0Space X := by
  sorry

lemma indiscrete_not_metrizable : ¬ TopologicalSpace.MetrizableSpace X := by
  sorry
