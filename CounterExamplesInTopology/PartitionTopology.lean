import Mathlib

variable (X : Type)
variable (P : Partition (Set.univ : Set X))

def partitionTopology : TopologicalSpace X where
  IsOpen (A : Set X) := ∃ S : Set P.parts, A = Set.sUnion S
  isOpen_univ := by
    have h := P.sSup_eq'
    rw [Set.sSup_eq_sUnion] at h
    use (Set.univ : Set P.parts)
    simp only [Partition.coe_parts, SetLike.coe_sort_coe, Set.image_univ,
      Subtype.range_coe_subtype, SetLike.setOf_mem_eq, ← h]
  isOpen_inter := sorry
  isOpen_sUnion := sorry

class PartitionTopology [t : TopologicalSpace X] : Prop where
  eq_partition_topology : t = partitionTopology X P


-- An subset of X is open if and only if it is closed
lemma open_iff_closed (A : Set X) [TopologicalSpace X] [PartitionTopology X P] :
    IsOpen A ↔ IsClosed A := by
  sorry

lemma not_T0_if_not_trivial (h_nontrivial : ∃ S : P.parts, Nontrivial S) [TopologicalSpace X]
    [PartitionTopology X P] :
    ¬ T0Space X := by
  sorry

lemma pseudoMetrizable [TopologicalSpace X] [PartitionTopology X P] :
    TopologicalSpace.PseudoMetrizableSpace X := by
  sorry
