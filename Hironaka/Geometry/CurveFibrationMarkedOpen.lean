import Hironaka.Geometry.CurveFibrationMarkedOpenSmooth
import Hironaka.Geometry.CurveFibrationMarkedOpenSections
import Hironaka.Geometry.CurveFibrationMarkedOpenFibers

/-!
# The actual smooth disjoint-marking base open of source4.17

Everything concerns literal restrictions of the ORIGINAL fibration,
ORIGINAL full ideal and ORIGINAL deduplicated sections. There is no
assumed marked-open, genus, stability, stable model or moduli certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Hironaka.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Source4.17 pre-moduli producer: the SAME original family and marks on an internally constructed dense BASE open. -/
theorem exists_actual_smooth_marked_base_open {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (D : X.IdealSheafData) {ι : Type u} [Finite ι] (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support) :
    ∃ (κ : Type u) (_ : Finite κ) (τ : κ → (S ⟶ X))
      (hτ : ∀ i, τ i ≫ f = 𝟙 S) (V : S.Opens),
      Nonempty V ∧ Dense (V : Set S) ∧ Function.Injective τ ∧ Set.range τ = Set.range σ ∧
      3 ≤ Nat.card κ ∧ f ⁻¹ᵁ V ≤ f.smoothLocus ∧
      let q := f ∣_ V
      let E := D.comap (f ⁻¹ᵁ V).ι
      let ρ : κ → (V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme) := fun i => restrictedSection f V (τ i) (hτ i)
      IsIntegral V.toScheme ∧ IsIntegral (f ⁻¹ᵁ V).toScheme ∧
      IsProper q ∧ Smooth q ∧ Flat q ∧ GeometricallyConnected q ∧
      (∀ i, ρ i ≫ q = 𝟙 V.toScheme ∧ IsClosedImmersion (ρ i)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ρ i)) (Set.range (ρ j))) ∧
      ⋃ i, Set.range (ρ i) = (E.support : Set (f ⁻¹ᵁ V).toScheme) ∧
      (∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ V.toScheme)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) → topologicalKrullDim C = 1) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ V.toScheme)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) →
        ∃ j : Fin 3 → κ, Function.Injective j ∧ ∀ i,
          fieldSectionPoint q (ρ (j i)) (restrictedSection_snd f V (τ (j i)) (hτ (j i))) a ∈ C ∧
          pullback.fst q a
            (fieldSectionPoint q (ρ (j i)) (restrictedSection_snd f V (τ (j i)) (hτ (j i))) a)
              ∈ q.smoothLocus) := by
  let (i : ι) : IsClosedImmersion (σ i) := by
    let : IsClosedImmersion (σ i ≫ f) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) f
  obtain ⟨κ, hκ, τ, hinj, hτ, hrange, hcoverτ⟩ := exists_deduplicated_closed_sections f σ hσ
  let := hκ
  let hτs : ∀ i, τ i ≫ f = 𝟙 S := fun i => (hτ i).1
  let (i : κ) : IsClosedImmersion (τ i) := (hτ i).2
  have hcover' : ⋃ i, Set.range (τ i) = (D.support : Set X) := hcoverτ.trans hcover
  have hcard := three_le_card_sections_of_geometric_three_points f D τ hτs hcover' hthree
  obtain ⟨Vs, hVs, _hdVs, hVsmooth, _hsVs⟩ := exists_nonempty_dense_smooth_base_open f
  obtain ⟨Vd, hVd, _hdVd, hVdistinct⟩ := exists_nonempty_dense_sections_distinct_open f τ hτs hinj
  let V := Vs ⊓ Vd
  have hηs : genericPoint S ∈ Vs :=
    (genericPoint_specializes (Classical.choice hVs).val).mem_open Vs.isOpen (Classical.choice hVs).property
  have hηd : genericPoint S ∈ Vd :=
    (genericPoint_specializes (Classical.choice hVd).val).mem_open Vd.isOpen (Classical.choice hVd).property
  have hη : genericPoint S ∈ V := ⟨hηs, hηd⟩
  let : Nonempty V := ⟨⟨genericPoint S, hη⟩⟩
  have hVsm : f ⁻¹ᵁ V ≤ f.smoothLocus := fun _ hx => hVsmooth hx.1
  have hVdist : ∀ s : V, Function.Injective (fun i => τ i s.val) :=
    fun s => hVdistinct ⟨s.val, s.property.2⟩
  let q := f ∣_ V
  let E := D.comap (f ⁻¹ᵁ V).ι
  let ρ : κ → (V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme) := fun i => restrictedSection f V (τ i) (hτs i)
  let : Smooth q := smooth_morphismRestrict_of_preimage_le_smoothLocus f V hVsm
  let : GeometricallyConnected q := restricted_geometricallyConnected f V
  let : Nonempty (f ⁻¹ᵁ V).toScheme := by
    obtain ⟨x, _⟩ := q.surjective (Classical.choice (show Nonempty V from inferInstance))
    exact ⟨x⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  have hρs : ∀ i, ρ i ≫ q = 𝟙 V.toScheme := fun i => restrictedSection_snd f V (τ i) (hτs i)
  have hρcover : ⋃ i, Set.range (ρ i) = (E.support : Set (f ⁻¹ᵁ V).toScheme) :=
    restrictedSections_cover_support f V D τ hτs hcover'
  have h3R := restricted_geometric_three_points f V D hthree
  refine ⟨κ, hκ, τ, hτs, V, inferInstance, V.isOpen.dense ⟨genericPoint S, hη⟩,
    hinj, hrange, hcard, hVsm, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, hρcover, ?_, ?_⟩
  · intro i
    exact ⟨hρs i, restrictedSection_isClosedImmersion f V (τ i) (hτs i)⟩
  · intro i j hij
    exact restrictedSections_disjoint_ranges f V τ hτs hVdist i j hij
  · intro K _ a C hC
    exact restricted_fieldFiber_components_dimension f V 1 hd a C hC
  · intro K _ _ a C hC
    exact three_section_indices_of_geometric_three_points q E ρ hρs hρcover h3R a C hC

end Hironaka.Geometry.CurveFibrationMarkedOpen
