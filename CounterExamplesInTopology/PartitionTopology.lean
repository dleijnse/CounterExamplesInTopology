import Mathlib

section General
variable (X : Type) [t : TopologicalSpace X]
variable (P : Partition (Set.univ : Set X))

def PartitionTopology : TopologicalSpace X := TopologicalSpace.generateFrom P.parts

class partitionTopology where
  hEq : t = PartitionTopology X P

variable [hp : partitionTopology X P]

-- some API lemmas about partition

lemma parts_eq {X : Type} {P : Partition Set.univ} {u s : Set X}
  (hs : s ∈ P.parts) (hu : u ∈ P.parts) (h : s ∩ u ≠ ∅) : s = u := by
   by_contra hc
   have := Set.disjoint_iff_inter_eq_empty.mp (P.pairwiseDisjoint hs hu hc)
   contradiction

-- for a given element, there exists one part which covers it
lemma exists_part_of_elt {X : Type} (P : Partition Set.univ) (x : X) : ∃ S ∈ P.parts, x ∈ S := by
  apply Set.mem_sUnion.mp
  rw[← Set.sSup_eq_sUnion]
  simp

--the complement of a union of sets in the partition equals the union of the complement
omit hp t in
lemma sUnion_compl_eq_compl_sUnion
  {S : Set (Set X)} (hs : S ⊆ P.parts) : (⋃₀ S)ᶜ = ⋃₀ (P.parts \ S) := by
  ext x
  constructor
  · intro h
    simp
    rcases exists_part_of_elt P x with ⟨t, ht_s, hx_t⟩
    use t
    refine ⟨⟨ht_s,?_⟩ , hx_t⟩
    by_contra hc
    have := Set.mem_sUnion.mpr ⟨t, hc, hx_t⟩
    contradiction
  · intro h
    by_contra hc
    simp at hc
    rcases hc with ⟨t2, ht21, ht22⟩
    rcases (Set.mem_sUnion.mp h) with ⟨t1, ht11, ht12⟩
    have ht : t1 = t2 := by
      apply parts_eq (Set.mem_of_mem_inter_left ht11) (hs ht21)
      apply Set.nonempty_iff_ne_empty.mp
      apply Set.inter_nonempty.mpr
      use x
    rw[ht] at ht11
    aesop

--back to the parition topology
lemma P_is_basis : TopologicalSpace.IsTopologicalBasis P.parts := {
  exists_subset_inter := by
    intro s hs u hu x hx
    use s
    refine ⟨hs, ?_, ?_⟩
    · tauto_set
    · have := parts_eq hs hu (Set.nonempty_iff_ne_empty.mp (Set.nonempty_of_mem hx))
      simp[this]
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
  constructor
  · intro ho
    rw[h] at ho
    rcases ho with ⟨s, hs⟩
    simp[hs.2]
    rw[← isOpen_compl_iff]
    rw[h (⋃₀ s)ᶜ]
    use P.parts \ s
    constructor
    · tauto_set
    · apply sUnion_compl_eq_compl_sUnion
      apply hs.1
  · intro hc
    rw[← isOpen_compl_iff] at hc
    rw[h] at hc
    rcases hc with ⟨s, hs⟩
    rw[h]
    use P.parts \ s
    constructor
    · tauto_set
    · apply compl_injective
      rw[hs.2]
      apply compl_injective
      rw[compl_compl]
      apply sUnion_compl_eq_compl_sUnion
      exact hs.1

lemma aux {S : P.parts} (x y : ↑↑S) (T : Set X) (hT : IsOpen T) : ↑x ∈ T → ↑y ∈ T := by
  intro hx
  rw[open_iff_union_of_P X P T] at hT
  rcases hT with ⟨U, hU⟩
  rw[hU.2] at hx
  rcases Set.mem_sUnion.mp hx with ⟨S0, hS0⟩
  have : S = S0 := by
    apply parts_eq
    · exact Subtype.coe_prop S
    · exact hU.1 hS0.1
    · apply Set.nonempty_iff_ne_empty'.mp
      apply nonempty_subtype.mpr
      use x
      simp[hS0.2]
  rw[← this] at hS0
  rw[hU.2]
  apply Set.mem_sUnion.mpr
  use S
  simp[hS0.1]

lemma not_T0_if_not_trivial (h_nontrivial : ∃ S : P.parts, Nontrivial S) :
    ¬ T0Space X := by
  rcases h_nontrivial with ⟨S , hS⟩
  rcases hS.exists_pair_ne with ⟨x, y, hxy⟩
  by_contra h
  have : Inseparable (x : X) (y : X) := by
    refine inseparable_iff_forall_isOpen.mpr ?_
    intro T hT
    constructor
    · exact aux X P x y T hT
    · exact aux X P y x T hT
  aesop

open Classical
lemma pseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace X := by
  let dist (x y : X) : ℝ := if (∃ S ∈ P.parts, x ∈ S ∧ y ∈ S) then (0 : ℝ) else (1 : ℝ)
  have h0 : ∀ x y : X, dist x y = 0 ∨ dist x y = 1 := by
        exact fun x y ↦ ite_eq_or_eq (∃ S ∈ P.parts, x ∈ S ∧ y ∈ S) 0 1
  letI m : PseudoMetricSpace X :=
  { dist := dist
    dist_self := by
      intro x
      unfold dist
      simp
      exact exists_part_of_elt P x
    dist_comm := by
      intro x y
      by_cases h : (∃ S ∈ P.parts, x ∈ S ∧ y ∈ S) <;>
      simp [dist, and_comm, and_left_comm, and_assoc]
    dist_triangle := by
      intro x y z
      by_cases h1 : dist x z = 0
      · by_cases h2 : dist x y = 0
        · by_cases h3 : dist y z = 0
          · simp[h1,h2,h3]
          · simp[h1,h2,Or.resolve_left (h0 y z) h3]
        · by_cases h3 : dist y z = 0
          · simp[h1, Or.resolve_left (h0 x y) h2, h3]
          · simp[h1, Or.resolve_left (h0 x y) h2, Or.resolve_left (h0 y z) h3]
      · by_cases h2 : dist x y = 0
        · by_cases h3 : dist y z = 0
          · simp[dist] at h1
            simp[dist] at h2
            simp[dist] at h3
            rcases h2 with ⟨S2, hS2⟩
            rcases h3 with ⟨S3, hS3⟩
            rw[← parts_eq hS2.1 hS3.1 (Set.nonempty_iff_ne_empty.mp ⟨y, hS2.2.2, hS3.2.1⟩)] at hS3
            have := h1 S2 hS2.1 hS2.2.1 hS3.2.2
            contradiction
          · simp[Or.resolve_left (h0 x z) h1, h2, Or.resolve_left (h0 y z) h3]
        · by_cases h3 : dist y z = 0
          · simp[Or.resolve_left (h0 x z) h1, Or.resolve_left (h0 x y) h2, h3]
          · simp [Or.resolve_left (h0 x z) h1, Or.resolve_left (h0 x y) h2,
            Or.resolve_left (h0 y z) h3]
        }
  constructor
  use m
  ext U
  rw[open_iff_union_of_P X P U]
  rw[Metric.isOpen_iff]
  constructor
  · intro h
    use {S ∈ P.parts | S ⊆ U}
    constructor
    · intro S hS
      exact hS.1
    · ext x
      constructor
      · intro hxU
        obtain ⟨ε, hε, hball⟩ := h x hxU
        simp
        rcases exists_part_of_elt P x with ⟨t, ht⟩
        use t
        constructor
        · constructor
          · exact ht.1
          · trans Metric.ball x ε
            · intro y hy
              simp[m]
              suffices : dist y x = 0
              · simp[this, hε]
              · simp[dist]
                use t
                exact ⟨ht.1, hy, ht.2⟩
            · exact hball
        · exact ht.2
      · intro hx
        rcases Set.mem_sUnion.mp hx with ⟨t, ht⟩
        simp at ht
        apply ht.1.2
        exact ht.2
  · rintro ⟨s, hs⟩ x hx
    rw[hs.2] at hx
    use 1
    constructor
    simp
    rcases Set.mem_sUnion.mp hx with ⟨T, hT⟩
    have : Metric.ball x 1 = T := by
      ext y
      constructor
      · intro hy
        simp[m] at hy
        have : dist y x = 0 := by
          by_contra hc
          rw[Or.resolve_left (h0 y x) hc] at hy
          norm_num at hy
        simp[dist] at this
        rcases this with ⟨T0, hT0⟩
        rw[← parts_eq hT0.1 (hs.1 hT.1) (Set.nonempty_iff_ne_empty.mp ⟨x, hT0.2.2, hT.2⟩)]
        exact hT0.2.1
      · intro hy
        have : dist y x = 0 := by
          unfold dist
          simp
          use T
          exact ⟨hs.1 hT.1, ⟨hy, hT.2⟩⟩
        simp[m, this]
    rw[this]
    intro y hy
    rw[hs.2]
    apply Set.mem_sUnion.mpr
    use T
    exact ⟨hT.1, hy⟩

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
           _ = f '' A  := by
            rw[← Set.sSup_eq_sUnion]
            simp
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


def subsetPartition {X : Type} (A : Set X) (P : Partition (Set.univ : Set X)) :
    Partition A := {
  parts := (Set.iUnion fun p : P.parts => {↑p ∩ A}) \ {∅}
  sSupIndep' := by
    simp[sSupIndep_iff, iSupIndep_def]
    intro a ha ha1 b hb hb1 hab
    apply Disjoint.inter_left
    apply Disjoint.inter_right
    by_cases h : a = b
    · tauto
    · exact P.disjoint ha hb h
  bot_notMem' := by
    simp
  sSup_eq' := by
    simp
    rw[← Set.iUnion_inter]
    rw[← Set.iSup_eq_iUnion]
    unfold iSup
    simp
}



-- for `f : X → Y` surjective, and a partition `P` on `Y`, then if we equip `X` and `Y` with
-- the partition topologies of `P` and the pullback of `P`, the map `f` is continuous with
-- respect to these two topologies.
omit X P hp in
lemma continuous_of_partition_topology {X Y : Type} (f : X → Y) (hf : f.Surjective)
    (P : Partition (Set.univ : Set Y)) :
    @Continuous X Y
    (PartitionTopology X (pullbackPartition f _
    (Partition.copy P (Set.image_univ_of_surjective hf).symm)))
    (PartitionTopology Y P) f := by
  set PX := (pullbackPartition f _ (Partition.copy P (Set.image_univ_of_surjective hf).symm))
  set tX := PartitionTopology X PX
  have hpx : partitionTopology X PX := {hEq := rfl }
  set tY := PartitionTopology Y P
  have hpy : partitionTopology Y P := {hEq := rfl}
  apply continuous_def.mpr
  intro s hs
  rw[open_iff_union_of_P X PX]
  rw[open_iff_union_of_P Y P] at hs
  rcases hs with ⟨p0, hp0⟩
  use Set.iUnion fun p : p0 => {f⁻¹' p}
  constructor
  · unfold PX pullbackPartition
    simp
    intro x hx
    rw[Set.mem_range] at hx
    rcases hx with ⟨y, hy⟩
    use Set.inclusion hp0.1 y
  · rw[hp0.2]
    simp

-- Discrete partition gives rise to discrete topology
lemma discrete_topology_of_discrete_partition' (h : P = discretePartition X Set.univ) : t = ⊥ := by
  refine eq_bot_of_singletons_open ?_
  intro x
  apply (open_iff_union_of_P X P {x}).mpr
  use {{x}}
  constructor
  · simp[h]
    unfold discretePartition
    use {{x}}
    simp
  · simp

omit t hp in
lemma discrete_topology_of_discrete_partition :
  PartitionTopology X (discretePartition X Set.univ) = ⊥ := by
  refine eq_bot_of_singletons_open ?_
  intro x
  set P := discretePartition X Set.univ with hP
  set t := PartitionTopology X P with ht
  have hp : partitionTopology X P := { hEq := ht }
  apply (open_iff_union_of_P X P {x}).mpr
  use {{x}}
  constructor
  · simp[hP]
    unfold discretePartition
    use {{x}}
    simp
  · simp

end General
section Example
/-
Below this, we define some specific interesting cases of the partition topologies
-/

-- Doubled real line ℝ ⨿ ℝ
def twoℝ := ℝ × Bool
def discreteℝ := ℝ

variable [hℝ : TopologicalSpace discreteℝ]
variable [htℝ : DiscreteTopology discreteℝ]

instance Uncountable_discreteℝ : Uncountable discreteℝ := by
  unfold discreteℝ
  infer_instance

-- the projection of the doubled real line to ℝ
def proj : twoℝ → discreteℝ := fun x ↦ x.1

omit htℝ hℝ in
lemma proj_surjective : proj.Surjective := fun y => ⟨⟨y, true⟩, rfl⟩

def doubledPartition : Partition (Set.univ : Set twoℝ) :=
  pullbackPartition proj (Set.univ) (discretePartition discreteℝ (proj '' Set.univ))

variable [t : TopologicalSpace twoℝ]
variable [hp : partitionTopology twoℝ doubledPartition]

lemma proj_continuous : Continuous proj := by
  convert
  continuous_of_partition_topology proj proj_surjective (discretePartition discreteℝ Set.univ)
  · rw[hp.hEq]
    unfold doubledPartition
    congr
    set h := Set.image_univ_of_surjective proj_surjective
    ext x
    rw[Partition.mem_copy_iff h.symm]
    rw[h]
  · rw[discrete_topology_of_discrete_partition discreteℝ]
    exact htℝ.eq_bot

lemma notLindelof : ¬ LindelofSpace twoℝ := by
  -- maybe use that ℝ with the discrete topology is not Lindelof by
  -- `countable_of_Lindelof_of_discrete`, and then use that `proj : twoℝ → ℝ`
  -- is continuous and surjective, then done by `LindelofSpace.of_continuous_surjective`
  intro hLindelof
  have hLindelofℝ := LindelofSpace.of_continuous_surjective proj_continuous proj_surjective
  have hCountable := countable_of_Lindelof_of_discrete (X := discreteℝ)
  have hUncountable := @not_countable _ Uncountable_discreteℝ
  exact hUncountable hCountable
