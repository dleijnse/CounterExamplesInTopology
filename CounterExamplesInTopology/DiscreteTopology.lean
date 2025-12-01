import Mathlib

variable (X : Type) [TopologicalSpace X] [DiscreteTopology X]
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

--#check Topology.IsOpen_of -- What does this do???


--It is the finest topology
theorem discr_top_finest (Top1 : TopologicalSpace X) [Top2 : TopologicalSpace X] [h : DiscreteTopology X] : ∀ (A : Set X), (Top1.IsOpen A) → IsOpen A  := by
    exact fun A h ↦ isOpen_discrete A

--Essentially same statement, but perhaps more inline with mathlib conventions.
--For some reason, it puts the discrete topology onto top2.
theorem discr_top_finest2 (Top1 Top2 : TopologicalSpace X) (h : DiscreteTopology X) : Top2 ≤  Top1 := by
    apply isOpen_implies_isOpen_iff.mp
    exact fun s g↦ isOpen_discrete s

--Alternatively, this one explicitly uses that the discrete topology is the smallest one.
theorem discr_top_finest3 (Top1 Top2 : TopologicalSpace X) (h : DiscreteTopology X) : Top2 ≤  Top1 := by
    rw[h.eq_bot]
    exact bot_le
    --exact fun U a ↦ trivial --Alternative method

--every point is isolated, isolated means, not in derived set, which is the collection of all limit points of a set. A limit point of a subset is, is a point such that all open sets of that point have another distinct point in the set as well.

--I think this should be interpreted as, the derived set of X is empty. (isolated point only mean something in relation to a subset)

theorem derived_set_empty : derivedSet (Set.univ : Set X) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x
    rw[ mem_derivedSet,accPt_iff_nhds] -- Alternatively use discreteTopology_iff_nhds_ne, which essentially already proves it
    intro h
    have h1 : {x} ∈  (nhds x)
    · apply mem_nhds_discrete.mpr (by rfl)
    apply h at h1
    rcases h1 with ⟨ y, h1⟩
    apply h1.2
    rw[h1.1.1]

-- x is not a limit point of the constant sequence x, considered as a set, but it is an adherent point

--with definition below, I am required to manually input X
--def limit_point (x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B ∩ A, y≠ x

def limit_point {X : Type} [TopologicalSpace X] (x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B ∩ A, y≠ x
def adherent_point {X : Type} [TopologicalSpace X] (x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B, y ∈ A

--after some searching these mathlib definitions are more suited for the above
theorem limit_point_is_accpt (x : X) (A : Set X) : limit_point x A ↔ AccPt x (Filter.principal A) := by
    rw[accPt_iff_nhds]
    constructor
    · intro h U h1
      rw[mem_nhds_iff] at h1
      rcases h1 with ⟨ V,⟨ h1,h2⟩ ⟩
      apply h V at h2
      rcases h2 with ⟨ y, ⟨ h2, h3⟩⟩
      have h4 : y ∈ U ∩ A := by tauto_set
      exact ⟨ y, h4,h3⟩
    · intro h U ⟨ h1,h2⟩
      rcases (h U (IsOpen.mem_nhds h1 h2)) with ⟨ y, h5⟩
      exact ⟨ y, h5⟩

theorem adherent_point_is_clusterpt (x : X) (A : Set X) : adherent_point x A ↔ ClusterPt x (Filter.principal A) := by
    rw[clusterPt_principal, ← limit_point_is_accpt]
    constructor
    · intro h
      by_cases h1: x ∈ A
      · left; exact h1
      · right
        rintro B h2
        rcases (h B h2) with ⟨ y,h5⟩
        use y
        refine ⟨h5, ?_⟩
        intro h7
        rw[← h7] at h1
        exact h1 h5.2
    · rintro (h1 | h2)
      · rintro B ⟨ h3,h4⟩
        exact ⟨ x, h4, h1⟩
      · rintro B h3
        apply h2 at h3
        rcases h3 with ⟨ y,h5⟩
        exact ⟨y, h5.1.1, h5.1.2⟩

theorem not_lim_point_mem (x : X) : ¬∃ p : X, limit_point p {x} := by
    apply not_exists.mpr
    intro p h
    rcases ((h {p}) ⟨ isOpen_discrete {p} , rfl⟩ ) with ⟨ y , ⟨ ⟨ h0,h1⟩ ,h2⟩ ⟩
    apply h2 h0

theorem adherent_point_mem (x p : X) : adherent_point p {x} → p = x := by
    intro h
    rcases ((h {p}) ⟨ isOpen_discrete {p} , rfl⟩ ) with ⟨ y, ⟨ h1, h2⟩⟩
    rw[← h1,h2]
