import Mathlib

variable (X : Type) [TopologicalSpace X] [DiscreteTopology X]

--#check Topology.IsOpen_of -- What does this do???


--It is the finest topology

--Why does this not work?
theorem discr_top_finest (Top1 : TopologicalSpace X) : ∀ (A : Set X), (Top1.IsOpen A) → IsOpen A  := by
    intro A h
    exact h

theorem discr_top_finest_correct (Top1 : TopologicalSpace X) [Top2 : TopologicalSpace X] [h : DiscreteTopology X] : ∀ (A : Set X), (Top1.IsOpen A) → IsOpen A  := by
    intro A h
    exact isOpen_discrete A --Can this be done in one line?

--every point is isolated, isolated means, not in derived set, which is the collection of all limit points of a set. A limit point of a subset is, is a point such that all open sets of that point have another distinct point in the set as well.

--I think this should be interpreted as, the derived set of X is empty. (isolated point only mean something in relation to a subset)

#check (Set.univ : Set X)

--I will clean this one up later. Definition was a lot more difficult to work with then expected.
theorem derived_set_empty : derivedSet (Set.univ : Set X) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x
    simp only [mem_derivedSet, Filter.principal_univ]
    unfold AccPt
    rw[Filter.neBot_iff]
    simp
    refine eq_bot_iff.mpr ?_
    refine Filter.le_def.mpr ?_
    intro x1 h

    unfold nhdsWithin
    refine Filter.mem_inf_iff_superset.mpr ?_
    use {x}
    simp
    -- constructor
    -- exact mem_nhds_discrete.mpr rfl
    use {x}ᶜ
    simp
    -- constructor
    -- exact fun ⦃a⦄ a_1 ↦ a_1
    -- simp

-- x is not a limit point of the constant sequence x, considered as a set, but it is an adherent point

--with definition below, I am required to manually input X
--def limit_point (x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B ∩ A, y≠ x
def limit_point {X: Type} [TopologicalSpace X](x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B ∩ A, y≠ x
def adherent_point {X: Type} [TopologicalSpace X](x : X) (A : Set X) := ∀ B : Set X, (IsOpen B ∧ x ∈ B) → ∃y ∈ B, y ∈ A


theorem not_lim_point_mem (x : X) : ¬∃ p : X, limit_point p {x} := by
    apply not_exists.mpr
    intro p h
    rcases ((h {p}) ⟨ isOpen_discrete {p} , rfl⟩ ) with ⟨ y , ⟨ ⟨ h0,h1⟩ ,h2⟩ ⟩
    apply h2 h0

theorem adherent_point_mem (x p : X) : adherent_point p {x} → p = x := by
    intro h
    rcases ((h {p}) ⟨ isOpen_discrete {p} , rfl⟩ ) with ⟨ y, ⟨ h1, h2⟩⟩
    rw[← h1,h2]
