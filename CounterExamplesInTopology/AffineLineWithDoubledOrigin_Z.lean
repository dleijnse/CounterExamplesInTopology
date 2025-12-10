import Mathlib

open Polynomial
open AlgebraicGeometry
open Quiver
open CategoryTheory
open CategoryTheory.Limits
open Scheme
open LocallyRingedSpace.IsOpenImmersion

noncomputable section

lemma diag_eq_pullback_diagonal (Y : Scheme) :
diag Y ≫ (prodIsoPullback Y Y).hom = pullback.diagonal (terminal.from Y) := by
  apply pullback.hom_ext
  · simp_all only [Category.assoc, prodIsoPullback_hom_fst, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.mk_fst, pullback.diagonal_fst]
  · simp_all only [Category.assoc, prodIsoPullback_hom_snd, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.mk_snd, pullback.diagonal_snd]

lemma diag_is_closed_immersion (Y : Scheme) [IsSeparated (terminal.from Y)] :
  IsClosedImmersion (diag Y) := by
  have iso_closed : IsClosedImmersion (prodIsoPullback Y Y).hom := by
    infer_instance
  have diag_pullback := diag_eq_pullback_diagonal Y
  have rhs_closed : IsClosedImmersion (pullback.diagonal (terminal.from Y)) := by infer_instance
  have iso_sep : IsSeparated (prodIsoPullback Y Y).hom := by
    infer_instance
  have comp_closed : IsClosedImmersion (diag Y ≫ (prodIsoPullback Y Y).hom) := by
    rw [diag_pullback]
    infer_instance
  apply IsClosedImmersion.of_comp (diag Y) ((prodIsoPullback Y Y).hom)


instance isClosedImmersion_equalizer_ι {X Y : Scheme} [IsSeparated (terminal.from Y)]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g) := by
  refine MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip ?_
  have h : diag Y = prod.lift (𝟙 Y) (𝟙 Y) := by
    exact rfl
  rw [← h]
  exact diag_is_closed_immersion Y


-- Sanity check the terminal object in the category of schemes is Spec(ℤ)
example : (⊤_ Scheme) ≅ Spec (.of ℤ) :=
  terminalIsTerminal.uniqueUpToIso specZIsTerminal


def A1 : Scheme := Spec (.of ℤ [X])

def U : A1.Opens := PrimeSpectrum.basicOpen (X : ℤ [X])

abbrev i : U.toScheme ⟶ A1 := U.ι

lemma i_is_open_immersion : IsOpenImmersion i := by
  infer_instance

lemma U_is_nonempty : Nonempty (U.toScheme) := by
  use ⟨⊥, Ideal.bot_prime⟩
  exact Polynomial.X_ne_zero

lemma image_of_i_is_nonempty : Set.Nonempty (Set.range i.base) := by
  have h₁ := U_is_nonempty
  exact Set.range_nonempty ⇑(ConcreteCategory.hom i.base)

lemma X_is_prime : Ideal.IsPrime (Ideal.span {X} : Ideal ℤ[X]) := by
  rw [Ideal.span_singleton_prime Polynomial.X_ne_zero]
  exact Polynomial.prime_X

def originPt : A1 := ⟨(Ideal.span {X} : Ideal ℤ[X]), X_is_prime⟩

lemma originPt_not_in_image_i : originPt ∉ Set.range i.base := by
  intro h
  rw [Scheme.Opens.range_ι] at h
  change originPt ∈ PrimeSpectrum.basicOpen X at h
  rw [PrimeSpectrum.mem_basicOpen] at h
  apply h
  exact (Submodule.span_singleton_le_iff_mem X originPt.asIdeal).mp fun ⦃x⦄ a ↦ a

lemma originPt_in_complement_of_image_i :
  originPt ∈ Set.compl (Set.range i.base) := by
  exact originPt_not_in_image_i

def affineLineWithDoubledOrigin : Scheme := pushout i i

namespace AffineLineWithDoubledOrigin

def f : A1 ⟶ affineLineWithDoubledOrigin := pushout.inl i i
def g : A1 ⟶ affineLineWithDoubledOrigin := pushout.inr i i

def equalizer_fg := equalizer f g

lemma hcomm :  i ≫ f = i ≫ g := by
  simp only [f, g]
  exact pushout.condition

variable {Z : Scheme} (q : Z ⟶ A1)

lemma range_subset_of_equalizer_condition (h : q ≫ f = q ≫ g) :
    Set.range q.base ⊆ Set.range i.base := by sorry

instance A1_minus_zero_is_equalizer : IsLimit (Fork.ofι i hcomm) := by
  -- Fork.IsLimit.mk _ fun s => ...
  -- use range_subset_of_equalizer + universal property
  -- of open immersions for locally ringed spaces.
  sorry

def iso_U_to_equalizer :
  (U).toScheme ≅ equalizer (f) (g) :=
  IsLimit.conePointUniqueUpToIso
    A1_minus_zero_is_equalizer
    (limit.isLimit _)

lemma i_iso_equalizer_ι :
  i = iso_U_to_equalizer.hom ≫ equalizer.ι f g := by
  symm
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    A1_minus_zero_is_equalizer (limit.isLimit _) WalkingParallelPair.zero


lemma i_closed_immersion [IsSeparated (terminal.from affineLineWithDoubledOrigin)] :
IsClosedImmersion (i) := by
      rw [i_iso_equalizer_ι]
      -- Isomorphisms of schemes are closed immersions
      have h₁: IsClosedImmersion (iso_U_to_equalizer.hom) := by
        infer_instance
      -- This should follow from isClosedImmersion_equalizer_ι
      have h₂: IsClosedImmersion (equalizer.ι f g) := by
        infer_instance
      exact IsClosedImmersion.comp (iso_U_to_equalizer.hom) (equalizer.ι f g)


instance : IrreducibleSpace (A1) := by
  unfold A1
  infer_instance

lemma A1_not_irred [IsSeparated (terminal.from affineLineWithDoubledOrigin)] :
 ¬ (IrreducibleSpace A1) := by
  by_contra hcontra
  have h₁ : IsOpen (Set.range i.base) := by
    exact IsOpenImmersion.isOpen_range i
  have h₂ : IsClosed (Set.range i.base) := by
    exact i_closed_immersion.base_closed.isClosed_range
  -- Now we show the complement of the image of i is also closed and open
  have h₃ : IsOpen (Set.compl (Set.range i.base)) := by
    exact h₂.isOpen_compl
  have h₄ : IsClosed (Set.compl (Set.range i.base)) := by
    exact h₁.isClosed_compl
  -- The image of i and its complement are nonempty
  have h₅ : Set.Nonempty (Set.compl (Set.range i.base)) := by
    use originPt
    exact originPt_in_complement_of_image_i
  have h₆ : Set.Nonempty (Set.range i.base) := by
    exact image_of_i_is_nonempty
  have h₇ : Disjoint (Set.range i.base) (Set.compl (Set.range i.base)) := by
    exact Set.disjoint_left.mpr fun ⦃a⦄ a_1 a_2 ↦ a_2 a_1
  have h₈ : ¬ Disjoint (Set.range i.base) (Set.compl (Set.range i.base)) := by
    refine Set.not_disjoint_iff_nonempty_inter.mpr ?_
    exact nonempty_preirreducible_inter h₁ h₃ h₆ h₅
  contradiction

theorem not_isSeparated :
   ¬ (IsSeparated  (terminal.from affineLineWithDoubledOrigin) ) := by
  by_contra hcontra
  have : IrreducibleSpace A1 := by infer_instance
  have := A1_not_irred
  contradiction

end AffineLineWithDoubledOrigin
