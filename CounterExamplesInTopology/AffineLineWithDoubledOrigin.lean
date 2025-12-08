import Mathlib

variable (R : Type) [CommRing R]

open Polynomial
open AlgebraicGeometry
open Quiver
open CategoryTheory
open CategoryTheory.Limits
noncomputable section


-- 𝔸¹ over Spec(R)
def A1 := Spec (CommRingCat.of R[X])

-- 𝔸¹ \ 0
def U : (A1 R).Opens := PrimeSpectrum.basicOpen (X : R[X])

-- i is the canonical inclusion of 𝔸¹ \ 0 into 𝔸¹
abbrev i : (U R).toScheme ⟶ (A1 R) := (U R).ι


-- The identity map is a morphism of schemes (sanity check)
example (X : Scheme) : X ⟶ X := by exact CategoryTheory.CategoryStruct.id X

-- (sanity check)
example : (U R).toScheme ⟶ (U R).toScheme := by
  exact CategoryTheory.CategoryStruct.id ((U R).toScheme)

-- the inclusion i : 𝔸¹ \ 0 ⟶ 𝔸¹ is an open immersion (sanity check)
lemma immersion : IsOpenImmersion (i R) := by
  infer_instance

#synth IsOpenImmersion (i R)
-- Never use: Scheme.Opens.instIsOpenImmersionι ((A1 R).basicOpen ((f R) X))

-- The identity morphism is an open immersion. (sanity check)
example : IsOpenImmersion (CategoryTheory.CategoryStruct.id (A1 R) : (A1 R) ⟶ (A1 R)) :=
  IsOpenImmersion.of_isIso _



-- Two instances of Christian that should now be in the latest version of Mathlib.
-- (Remove these when the branch has been bumped)
instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (i : WalkingPair) : Mono ((span f g ⋙ Scheme.forget).map (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using f.isOpenEmbedding.injective
  · simpa using g.isOpenEmbedding.injective


instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    {i j : WalkingSpan} (t : i ⟶ j) : IsOpenImmersion ((span f g).map t) := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa


-- Definition of the affine line with doubled origin
def affineLineWithDoubledOrigin : Scheme := pushout (i R)  (i R)

namespace AffineLineWithDoubledOrigin

-- Constructing the map to the base scheme spec(R)
def toBase : affineLineWithDoubledOrigin R ⟶  Spec (.of R) :=
  pushout.desc (Spec.map <| CommRingCat.ofHom Polynomial.C)
    (Spec.map <| CommRingCat.ofHom Polynomial.C)


-- Main theorem we want to prove in this section. 
theorem not_isSeparated_toBase : ¬ (IsSeparated <| toBase  R) := by sorry


end AffineLineWithDoubledOrigin
