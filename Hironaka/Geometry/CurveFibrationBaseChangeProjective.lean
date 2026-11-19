import Hironaka.Geometry.CurveFibrationBaseChangeAlteration
import Hironaka.Geometry.ChowLemmaProduct
import Hironaka.Geometry.AlterationCommonRefinementProjective

/-!
# Actual absolute projectivity from the original relative closed presentation

The relative space is identified by its genuine coefficient Cartesian
square, then actual product projectivity and Segre give the original
coefficient projectivity of every actual closed source in it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow
open Hironaka.Geometry.BlowupProjectiveEmbedding

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X T S Y : Scheme.{u}}

/-- The actual coefficient Cartesian square gives the original native product isomorphism. -/
def relativeCoefficientProductIso (p : X ⟶ Spec (.of R)) (n : ℕ) :
    pullback p (projectiveSpaceStructure R n) ≅ relativeSpace X n := by
  have H : IsPullback
      (projectiveCoefficientMap (CommRingCat.isInitial.to (.of R)).hom n)
      (projectiveSpaceStructure R n) (projectiveSpaceStructure IntegerRing n)
      (integerStructure (Spec (.of R))) := by
    convert! ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap
      (CommRingCat.isInitial.to (.of R)).hom n using 1
    exact specULiftZIsTerminal.hom_ext _ _
  have H' : IsPullback (pullback.fst p (projectiveSpaceStructure R n))
      (pullback.snd p (projectiveSpaceStructure R n) ≫
        projectiveCoefficientMap (CommRingCat.isInitial.to (.of R)).hom n)
      (integerStructure X) (projectiveSpaceStructure IntegerRing n) := by
    rw [← integerStructure_naturality p]
    exact ((IsPullback.of_hasPullback p (projectiveSpaceStructure R n)).flip.paste_horiz H).flip
  exact H'.isoPullback

@[reassoc (attr := simp)]
theorem relativeCoefficientProductIso_hom_structure (p : X ⟶ Spec (.of R)) (n : ℕ) :
    (relativeCoefficientProductIso p n).hom ≫ relativeStructure X n =
      pullback.fst p (projectiveSpaceStructure R n) := by
  exact IsPullback.isoPullback_hom_fst _

/-- Actual relative projective space over an originally projective scheme is projective over R. -/
theorem relativeSpace_isProjective_over (p : X ⟶ Spec (.of R)) (hp : IsProjectiveOver p)
    (n : ℕ) : IsProjectiveOver (relativeStructure X n ≫ p) := by
  obtain ⟨m, e, he, hbase⟩ := ChowLemmaProduct.isProjectiveOver_product p
    (projectiveSpaceStructure R n) hp (isProjectiveOver_projectiveSpaceStructure R n)
  let := he
  refine ⟨m, (relativeCoefficientProductIso p n).inv ≫ e, inferInstance, ?_⟩
  have hi : (relativeCoefficientProductIso p n).inv ≫
      pullback.fst p (projectiveSpaceStructure R n) = relativeStructure X n := by
    rw [← relativeCoefficientProductIso_hom_structure p n, Iso.inv_hom_id_assoc]
  rw [Category.assoc, hbase, ← Category.assoc, hi]

/-- Compose genuine closed embeddings to obtain projectivity of the original actual closed source. -/
theorem closed_into_relativeSpace_isProjective (p : X ⟶ Spec (.of R))
    (hp : IsProjectiveOver p) {n : ℕ} (j : T ⟶ relativeSpace X n) [IsClosedImmersion j] :
    IsProjectiveOver (j ≫ relativeStructure X n ≫ p) := by
  obtain ⟨m, e, he, hbase⟩ := relativeSpace_isProjective_over p hp n
  let := he
  exact ⟨m, j ≫ e, inferInstance, by simp only [Category.assoc, hbase]⟩

/-- The SAME whole reduced pullback is projective over the original coefficient ring. -/
theorem reducedFirst_comp_isProjective (f : X ⟶ S) (g : Y ⟶ S)
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveOver p) {n : ℕ}
    (e : Y ⟶ relativeSpace S n) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S n = g) :
    IsProjectiveOver ((reductionι f g ≫ pullback.fst f g) ≫ p) := by
  have H := closed_into_relativeSpace_isProjective p hp (reductionProjectiveEmbedding f g e he)
  simpa only [← Category.assoc, reductionProjectiveEmbedding_structure] using H

/-- Actual absolute projectivity and properness produce a genuine relative closed presentation. -/
theorem exists_relativeEmbedding_of_isProjective (p : S ⟶ Spec (.of R))
    (f : X ⟶ S) [IsProper f] (hp : IsProjectiveOver (f ≫ p)) :
    ∃ (n : ℕ) (e : X ⟶ relativeSpace S n),
      IsClosedImmersion e ∧ e ≫ relativeStructure S n = f := by
  obtain ⟨n, a, ha, hbase⟩ :=
    AlterationCommonRefinement.exists_relative_projective_embedding p f hp.isQuasiProjective
  let := ha
  exact ⟨n, a ≫ (relativeCoefficientProductIso p n).hom, inferInstance, by simp [hbase]⟩

/-- The original fibration's actual relative embedding gives an embedding of the SAME reduced source. -/
def reducedSecondProjectiveEmbedding (f : X ⟶ S) (g : Y ⟶ S) {n : ℕ}
    (e : X ⟶ relativeSpace S n) (he : e ≫ relativeStructure S n = f) :
    reducedPullback f g ⟶ relativeSpace Y n :=
  reductionι f g ≫ (pullbackSymmetry f g).hom ≫
    AlterationDominatingBaseChange.baseChangeEmbedding g f e he

instance reducedSecondProjectiveEmbedding_isClosedImmersion (f : X ⟶ S) (g : Y ⟶ S) {n : ℕ}
    (e : X ⟶ relativeSpace S n) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S n = f) :
    IsClosedImmersion (reducedSecondProjectiveEmbedding f g e he) := by
  unfold reducedSecondProjectiveEmbedding
  infer_instance

@[reassoc (attr := simp)]
theorem reducedSecondProjectiveEmbedding_structure (f : X ⟶ S) (g : Y ⟶ S) {n : ℕ}
    (e : X ⟶ relativeSpace S n) (he : e ≫ relativeStructure S n = f) :
    reducedSecondProjectiveEmbedding f g e he ≫ relativeStructure Y n =
      reductionι f g ≫ pullback.snd f g := by
  simp [reducedSecondProjectiveEmbedding]

end Hironaka.Geometry.CurveFibrationBaseChange
