import Hironaka.Geometry.FiniteBirationalNormalExtension
import Hironaka.Geometry.FiniteBirationalNormalLift

/-!
# Internally constructed common normalization with genuine component sections

Starting from finite dominant generically-etale component maps, construct
the common finite Galois field, its actual projective normal alteration,
and closed-immersion sections of the actual component base changes.

The assertion that section images cover the whole boundary is not made here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S : Scheme.{u}} {ι : Type u} [Finite ι]

/-- A finite family of actual finite generically-etale component maps
internally produces one normal projective Galois alteration and actual
closed-immersion sections after base change. Neither the field nor its
embeddings, maps, sections or commutative triangles are supplied. -/
theorem exists_common_galois_normalization_sections
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (T : ι → Scheme.{u}) [∀ i, IsIntegral (T i)]
    (f : ∀ i, T i ⟶ S) [∀ i, IsDominant (f i)] [∀ i, IsFinite (f i)]
    (hf : ∀ i, IsGenericallyEtale (f i)) :
    ∃ L : IntermediateField S.functionField (SeparableClosure S.functionField),
      ∃ hfinite : FiniteDimensional S.functionField L,
        letI := hfinite
        IsGalois S.functionField L ∧
        IsVariety (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        IsNormalScheme (NormalizationInExtension.normalization S L) ∧
        IsFinite (NormalizationInExtension.normalizationStructure S L) ∧
        IsAlteration (NormalizationInExtension.normalizationStructure S L) ∧
        IsGenericallyEtale (NormalizationInExtension.normalizationStructure S L) ∧
        IsProjectiveOver (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        Nonempty (∀ i, {s : NormalizationInExtension.normalization S L ⟶
            pullback (f i) (NormalizationInExtension.normalizationStructure S L) //
          s ≫ pullback.snd (f i) (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ ∧
            IsClosedImmersion s}) := by
  obtain ⟨L, hfinite, h⟩ := exists_common_galois_normalization p hp T f hf
  let := hfinite
  obtain ⟨hg, he, hv, hn, hfin, ha, hge, hp', _⟩ := h
  let (i : ι) := functionFieldAlgebra (f i)
  obtain ⟨e⟩ := he
  refine ⟨L, hfinite, hg, hv, hn, hfin, ha, hge, hp', ⟨fun i => ?_⟩⟩
  exact ⟨normalizationSection (f i) L (e i),
    normalizationSection_snd (f i) L (e i), inferInstance⟩

end Hironaka.Geometry.FiniteBirationalNormal
