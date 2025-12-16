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
lemma open_iff_closed (A : Set X) :
    IsOpen A ↔ IsClosed A := by
  sorry


lemma not_T0_if_not_trivial (h_nontrivial : ∃ S : P.parts, Nontrivial S) :
    ¬ T0Space X := by
  sorry

lemma pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace X := by
  sorry
