import Hironaka.Geometry.CurveFibrationNormalizedGenericPoints
import Hironaka.Geometry.CurveFibrationGenericMarksSpread
import Hironaka.Geometry.CurveFibrationGenericSmoothMarksFiber

/-! Actual original generic L-marks spread on the SAME canonical normalized base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationNormalizedGenericMarks

open NormalizationInExtension CurveFibrationNormalizedGenericPoints

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral S]
  (L : Type u) [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
  (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsSeparated f]

local notation "N" => normalization S L
local notation "π" => normalizationStructure S L
local notation "Y" => pullback f π
local notation "q" => pullback.snd f π

/-- Actual original generic L-points produce SAME-normalization dense-open closed disjoint
smooth sections, retaining BOTH entire native and original generic point-map triangles. -/
theorem exists_normalized_smooth_disjoint_spread {ι : Type u} [Finite ι]
    (φ : ι → (Spec (.of L) ⟶ X))
    (hφ : ∀ i, φ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
      S.fromSpecStalk (_root_.genericPoint S))
    (hdist : Function.Injective (fun i => φ i (IsLocalRing.closedPoint L)))
    (hsm : ∀ i, φ i (IsLocalRing.closedPoint L) ∈ f.smoothLocus) :
    ∃ (V : (N).Opens) (hη : _root_.genericPoint N ∈ V)
      (ρ : ι → (V.toScheme ⟶ (q ⁻¹ᵁ V).toScheme)),
      Dense (V : Set N) ∧
      (∀ i, ρ i ≫ (q ∣_ V) = 𝟙 V.toScheme ∧ IsClosedImmersion (ρ i)) ∧
      (∀ v : V, Function.Injective (fun i => ρ i v)) ∧
      (∀ i, Set.range (ρ i ≫ (q ⁻¹ᵁ V).ι) ⊆ (q).smoothLocus) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ρ i)) (Set.range (ρ j))) ∧
      (∀ i, V.fromSpecStalkOfMem (_root_.genericPoint N) hη ≫
        ρ i ≫ (q ⁻¹ᵁ V).ι = CurveFibrationNormalizedGenericPoints.genericPoint L f (φ i) (hφ i)) ∧
      ∀ i, V.fromSpecStalkOfMem (_root_.genericPoint N) hη ≫
        ρ i ≫ (q ⁻¹ᵁ V).ι ≫ pullback.fst f π = genericFieldMap L ≫ φ i := by
  let φ' : ι → (Spec (N).functionField ⟶ Y) :=
    fun i => CurveFibrationNormalizedGenericPoints.genericPoint L f (φ i) (hφ i)
  have hφ' (i : ι) : φ' i ≫ q = (N).fromSpecStalk (_root_.genericPoint N) :=
    genericPoint_snd L f (φ i) (hφ i)
  have hdist' : Function.Injective (fun i => φ' i (IsLocalRing.closedPoint (N).functionField)) :=
    genericPoints_injective L f φ hφ hdist
  have hsm' (i : ι) : φ' i (IsLocalRing.closedPoint (N).functionField) ∈ (q).smoothLocus :=
    genericPoint_mem_smoothLocus L f (φ i) (hφ i) (hsm i)
  obtain ⟨V, hη, ρ, hV, hsec, hinj, hsmooth, hdisj, hgeneric⟩ :=
    CurveFibrationGenericMarksSpread.exists_smooth_disjoint_spread q φ' hφ' hdist' hsm'
  refine ⟨V, hη, ρ, hV, hsec, hinj, hsmooth, hdisj, hgeneric, ?_⟩
  intro i
  calc
    _ = (V.fromSpecStalkOfMem (_root_.genericPoint N) hη ≫
        ρ i ≫ (q ⁻¹ᵁ V).ι) ≫ pullback.fst f π := by simp only [Category.assoc]
    _ = φ' i ≫ pullback.fst f π := by rw [hgeneric]
    _ = genericFieldMap L ≫ φ i := genericPoint_fst L f (φ i) (hφ i)

/-- The ORIGINAL proper smooth positive-dimensional generic fibre itself produces the actual
finite Galois field and three dense-open closed/disjoint/smooth normalized sections. -/
theorem exists_normalized_three_smooth_marks {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (g : A ⟶ B) [IsDominant g] [IsProper g]
    [LocallyOfFinitePresentation g]
    [Smooth (g.fiberToSpecResidueField (_root_.genericPoint B))]
    (hdim : 0 < topologicalKrullDim (g.fiber (_root_.genericPoint B))) :
    ∃ L : IntermediateField B.functionField (SeparableClosure B.functionField),
      ∃ hfinite : FiniteDimensional B.functionField L,
        letI := hfinite
        IsGalois B.functionField L ∧
        ∃ φ : Fin 3 → (Spec (.of L) ⟶ A),
          ∃ hφ : ∀ i, φ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B.functionField L)) ≫
            B.fromSpecStalk (_root_.genericPoint B),
          Function.Injective (fun i => φ i (IsLocalRing.closedPoint L)) ∧
          (∀ i, φ i (IsLocalRing.closedPoint L) ∈ g.smoothLocus) ∧
          let N' := normalization B L
          let π' := normalizationStructure B L
          let q' := pullback.snd g π'
          ∃ (V : N'.Opens) (hη : _root_.genericPoint N' ∈ V)
            (ρ : Fin 3 → (V.toScheme ⟶ (q' ⁻¹ᵁ V).toScheme)),
            Dense (V : Set N') ∧
            (∀ i, ρ i ≫ (q' ∣_ V) = 𝟙 V.toScheme ∧ IsClosedImmersion (ρ i)) ∧
            (∀ v : V, Function.Injective (fun i => ρ i v)) ∧
            (∀ i, Set.range (ρ i ≫ (q' ⁻¹ᵁ V).ι) ⊆ q'.smoothLocus) ∧
            (∀ i j, i ≠ j → Disjoint (Set.range (ρ i)) (Set.range (ρ j))) ∧
            (∀ i, V.fromSpecStalkOfMem (_root_.genericPoint N') hη ≫ ρ i ≫ (q' ⁻¹ᵁ V).ι =
              CurveFibrationNormalizedGenericPoints.genericPoint L g (φ i) (hφ i)) ∧
            ∀ i, V.fromSpecStalkOfMem (_root_.genericPoint N') hη ≫
              ρ i ≫ (q' ⁻¹ᵁ V).ι ≫ pullback.fst g π' = genericFieldMap L ≫ φ i := by
  obtain ⟨L, hfinite, hgal, φ, hφ, hdist, hsm⟩ :=
    CurveFibrationGenericSmoothMarks.exists_original_generic_smooth_marks g hdim
  let := hfinite
  have hclosed : IsLocalRing.closedPoint L = (⊥ : PrimeSpectrum L) := Subsingleton.elim _ _
  have hdist' : Function.Injective (fun i => φ i (IsLocalRing.closedPoint L)) := by
    simpa only [hclosed] using hdist
  have hsm' (i : Fin 3) : φ i (IsLocalRing.closedPoint L) ∈ g.smoothLocus := by
    simpa only [hclosed] using hsm i
  let ψ : ULift.{u} (Fin 3) → (Spec (.of L) ⟶ A) := fun i => φ i.down
  have hψ (i : ULift.{u} (Fin 3)) : ψ i ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField L)) ≫
        B.fromSpecStalk (_root_.genericPoint B) := hφ i.down
  have hψdist : Function.Injective (fun i => ψ i (IsLocalRing.closedPoint L)) := by
    intro i j hij
    apply ULift.ext
    exact hdist' hij
  obtain ⟨V, hη, ρ, hV, hsec, hinj, hsmooth, hdisj, hgeneric, horiginal⟩ :=
    exists_normalized_smooth_disjoint_spread L g ψ hψ hψdist (fun i => hsm' i.down)
  refine ⟨L, hfinite, hgal, φ, hφ, hdist', hsm', V, hη,
    (fun i => ρ ⟨i⟩), hV, (fun i => hsec ⟨i⟩), ?_, (fun i => hsmooth ⟨i⟩), ?_,
    (fun i => hgeneric ⟨i⟩), (fun i => horiginal ⟨i⟩)⟩
  · intro v i j hij
    exact congrArg ULift.down (hinj v hij)
  · intro i j hij
    exact hdisj ⟨i⟩ ⟨j⟩ (fun H => hij (congrArg ULift.down H))

end Hironaka.Geometry.CurveFibrationNormalizedGenericMarks
