import Mathlib

variable (X : Type) [t : TopologicalSpace X]
variable (P : Partition (Set.univ : Set X))

def PartitionTopology : TopologicalSpace X := TopologicalSpace.generateFrom P.parts

class partitionTopology where
  hEq : t = PartitionTopology X P

variable [hp : partitionTopology X P]

lemma P_is_basis : TopologicalSpace.IsTopologicalBasis P.parts := {
  exists_subset_inter := by
    intro s hs t ht x hx
    use s
    refine ⟨hs, ?_, ?_⟩
    · tauto_set
    · have hst : s = t := by
        by_contra hc
        have := Set.disjoint_iff_inter_eq_empty.mp (P.pairwiseDisjoint hs ht hc)
        simp at this
        rw[this] at hx
        exact hx
      simp[hst]
  sUnion_eq := P.sSup_eq'
  eq_generateFrom := by
    rw [hp.hEq]
    rfl
}

lemma basic_open (A : Set X) (hA : A ∈ P.parts) : IsOpen A := by
  rw [hp.hEq]
  exact TopologicalSpace.isOpen_generateFrom_of_mem hA

lemma open_iff_union_of_P (A : Set X) : IsOpen A ↔ ∃ s : Set (Set X),
    s ⊆ P.parts ∧ A = Set.sUnion s := by
  constructor
  · intro hA
    have hRes := TopologicalSpace.IsTopologicalBasis.open_eq_sUnion (P_is_basis X P) hA
    obtain ⟨S, hSP, hSU⟩ := hRes
    use S
  · intro h
    obtain ⟨s, hs, hA⟩ := h
    subst hA
    apply isOpen_sUnion
    intro t ht
    exact basic_open X P t (hs ht)


-- An subset of X is open if and only if it is closed
include hp
lemma open_iff_closed (A : Set X) :
    IsOpen A ↔ IsClosed A := by
  have h := open_iff_union_of_P X P

  sorry


lemma not_T0_if_not_trivial (h_nontrivial : ∃ S : P.parts, Nontrivial S) :
    ¬ T0Space X := by
  sorry

lemma pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace X := by
  sorry

-- To make some concrete examples of spaces with the partition topology, we need to explicitly
-- construct some partitions.

def discretePartition (A : Set X) : Partition A := {
  parts : Set (Set X) := Set.iUnion fun a : A => {{(a : X)}}
  sSupIndep' := by simp [Set.iUnion_singleton_eq_range, sSupIndep_iff, iSupIndep_def]
  bot_notMem' := by simp
  sSup_eq' := by simp
}

omit t hp in
lemma partition_union {X : Type} (A : Set X) (P : Partition A) : ⋃ s : P, s = A := by
  rw [← Set.iSup_eq_iUnion]
  unfold iSup
  simp

/-- Given a function `f : X → Y`, a subset `A` of `X` and a partition `P` on `f '' A`, we can pull
`P` back along `f` by defining a partition on `A` whose parts are the inverse images of the parts of
the partition on `f '' A`. -/
def pullbackPartition {X Y : Type} (f : X → Y) (A : Set X) (P : Partition (f '' A)) :
    Partition A := {
  parts := Set.iUnion fun p : P.parts => {f⁻¹' p ∩ A}
  sSupIndep' := by
    simp [sSupIndep_iff, iSupIndep_def]
    intro a ha b hb hab
    apply Disjoint.inter_left
    apply Disjoint.inter_right
    apply Disjoint.preimage f
    by_cases h : a = b
    · tauto
    · exact P.disjoint ha hb h
  bot_notMem' := by
    simp only [Partition.coe_parts, SetLike.coe_sort_coe, Set.iUnion_singleton_eq_range,
      Set.bot_eq_empty, Set.mem_range, Subtype.exists, exists_prop, not_exists, not_and]
    intro x hx hfx
    have hNonEmpty : x ≠ ∅ := by
      intro h
      rw [h] at hx
      exact P.bot_notMem' hx
    have h2 : ∃ b : Y, b ∈ x := by
      symm at hNonEmpty
      rw [← Set.nonempty_iff_empty_ne] at hNonEmpty
      rw [Set.nonempty_def] at hNonEmpty
      assumption
    obtain ⟨b, hb⟩ := h2
    have h3 : x ⊆ f '' A := by
      -- use that the union over P.parts is exactly f '' A
      calc x ⊆ ⋃₀ P   := Set.subset_sUnion_of_subset (↑P) x (fun ⦃a⦄ a_1 ↦ a_1) hx
           _ = f '' A  := by sorry -- partition_union (f '' A) P
    have h4 : ∃ a : X, a ∈ A ∧ f a = b := by
      rw [← Set.mem_image]
      exact h3 hb
    obtain ⟨a, ha⟩ := h4
    have h5 : a ∈ f ⁻¹'x ∩ A := by
      refine ⟨?_, ha.1⟩
      rw [Set.mem_preimage, ha.2]
      exact hb
    simp_all
  sSup_eq' := by
    simp only [Partition.coe_parts, SetLike.coe_sort_coe, Set.iUnion_singleton_eq_range,
      Set.sSup_eq_sUnion, Set.sUnion_range]
    rw [← Set.iUnion_inter]
    rw [← Set.preimage_iUnion]
    have hUnion : ⋃ i : P, i = f '' A := by
      rw [← Set.iSup_eq_iUnion]
      unfold iSup
      simp
    rw [hUnion]
    tauto_set
}

-- I think the above can maybe be generalized to something in the following vein, however, we may
-- need some more assumptions.
def pullbackPartition' {α β : Type} [CompleteLattice α] [CompleteLattice β] (s : α)
    (f : α →o β) (P : Partition s) : Partition (f s) := {
    parts := Set.iUnion fun p : P.parts => {f p}
    sSupIndep' := by
      simp only [Partition.coe_parts, SetLike.coe_sort_coe, Set.iUnion_singleton_eq_range]
      intro a b
      simp_all only [Set.mem_range, Subtype.exists, exists_prop]
      obtain ⟨x, hx⟩ := b

      sorry
    bot_notMem' := by

      sorry
    sSup_eq' := by

      sorry
  }


/-
Below this, we define some specific interesting cases of the partition topologies
-/

-- Doubled real line ℝ ⨿ ℝ
def twoℝ := ℝ × Bool

-- the projection of the doubled real line to ℝ
def proj : twoℝ → ℝ := fun x ↦ x.1

#check discretePartition ℝ (Set.univ : Set ℝ)

def doubledPartition : Partition (Set.univ : Set twoℝ) :=
  pullbackPartition proj (Set.univ) (discretePartition ℝ (proj '' Set.univ))

variable [t : TopologicalSpace twoℝ]
variable [hp : partitionTopology twoℝ doubledPartition]

lemma notLindelof : ¬ LindelofSpace twoℝ := by

  sorry
