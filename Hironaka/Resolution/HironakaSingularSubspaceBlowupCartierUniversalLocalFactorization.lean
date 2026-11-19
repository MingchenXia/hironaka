import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierCentreIdeal
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierDensity

/-!
# Local factorization of original intrinsic singular-source maps

This is the explicit regular-principal actual-stalk version. Its standard
invertible-module consumers derive those generators. The original intrinsic
map supplies its ambient representatives internally, and density derives
landing in the literal singular strict transform. Whole LRS squares survive.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-local-factorization.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalLocalFactorization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartier HironakaSingularSubspaceBlowupCartierCentreIdeal
  HironakaSingularSubspaceBlowupCartierDensity
  HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  BlowupFlatCoordinates

noncomputable section

section NativeLift

variable {n m : ℕ} {M Y N : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  {C : Set M} {π : Y → M} {G : N → M}

/-- A genuine flattening chart or the off-centre inverse is chosen internally
at the original point. No ambient pullback invertibility is assumed. -/
theorem exists_local_native_lift_of_actual_cartier
    (hπ : IsBlowupAlong n C π)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G)
    (S : Set N) (x : S)
    {alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier}
    (hreg : IsRegular alpha)
    (hCart : Ideal.map ((actualSubspaceInclusion (n := m) S).stalkMap x).hom
      (actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m := m) G (vanishingIdeal (n := n) C)) x.val) = Ideal.span {alpha}) :
    ∃ (U : Opens N) (_hxU : x.val ∈ U) (L : U → Y)
      (_hL : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ L),
      ∀ z : U, z.val ∈ S → π (L z) = G z.val := by
  by_cases hxC : G x.val ∈ C
  · obtain ⟨k, _, _, Φ, hΦsrc, _, hflat⟩ := hπ.1.2 (G x.val) hxC
    exact exists_local_holomorphic_blowup_lift_of_actual_cartier_ideal
      hπ hG hΦsrc hflat S x (mem_flatDomain_self Φ) hreg hCart
  · obtain ⟨s, hs, hπs, _⟩ := BlowupIsomorphismOff.exists_section_compl hπ
    let V : Opens M := ⟨Cᶜ, hπ.1.1.isOpen_compl⟩
    let U : Opens N := ⟨G ⁻¹' Cᶜ, hπ.1.1.isOpen_compl.preimage hG.continuous⟩
    let g : U → V := fun z => ⟨G z.val, z.property⟩
    have hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g :=
      (ContMDiff.subtypeVal_comp_iff V g).mp (hG.comp contMDiff_subtype_val)
    refine ⟨U, hxC, s ∘ g, hs.comp hg, ?_⟩
    intro z _
    exact congrFun hπs (g z)

end NativeLift

section IdealTransport

variable {n m l : ℕ} {M N Q : Type} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace Q] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  [ChartedSpace (ComplexModel l) Q] [IsComplexManifold l Q]
  {C W : Set M} {S : Set N} {R : Set Q} {G : Q → M}

/-- The original intrinsic Cartier ideal and full actual representative square
supply regular principal data for the SAME whole ambient pulled ideal at ALL
source-chart stalks. This is a transport lemma; its caller constructs G. -/
theorem cartier_on_actual_ambient_representative
    (hC : IsClosedSubmanifold n C)
    (F : actualSubspaceLocallyRingedSpace (n := m) S ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (j : actualSubspaceLocallyRingedSpace (n := l) R ⟶ actualSubspaceLocallyRingedSpace (n := m) S)
    [LocallyRingedSpace.IsOpenImmersion j]
    (hG : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hRW : ∀ z ∈ R, G z ∈ W) (hrep : actualSubspaceMap hG hRW = j ≫ F)
    (hCart : ∀ x : S,
      ∃ alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier,
        IsRegular alpha ∧
        Ideal.map (F.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base x).val)) =
          Ideal.span {alpha}) :
    ∀ z : R,
      ∃ alpha : ((actualSubspaceSheaf (n := l) R).presheaf.stalk z).carrier,
        IsRegular alpha ∧
        Ideal.map ((actualSubspaceInclusion (n := l) R).stalkMap z).hom
          (actualWholeSheafStalkIdeal
            (GermIdeal.pullback (m := l) G (vanishingIdeal (n := n) C)) z.val) =
          Ideal.span {alpha} := by
  intro z
  obtain ⟨alpha, hreg, hspan⟩ := hCart (j.base z)
  let I := Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base (j.base z))).hom
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base (j.base z)).val)
  obtain ⟨beta, hbeta, hbetaI⟩ := exists_regular_generator_on_open_chart_of_cartier j F z I hreg hspan
  have hideal := congrArg (fun H : actualSubspaceLocallyRingedSpace (n := l) R ⟶
      actualSubspaceLocallyRingedSpace (n := n) W =>
    Ideal.map (H.stalkMap z).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (H.base z)).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base z).val))) hrep
  have hdict := map_actualSubspace_stalk_ideal_pullback hG hRW
    (vanishingIdeal (n := n) C) (VanishingIdealCoherent.isCoherent_vanishingIdeal hC) z
  refine ⟨beta, hbeta, ?_⟩
  exact hdict.symm.trans (hideal.trans hbetaI)

end IdealTransport

section LocalFactorization

variable {n m : ℕ} {M Y N : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  {C W : Set M} {S : Set N} {π : Y → M}

/-- The original intrinsic map and SAME actual principal regular stalk ideals
internally produce a genuine source open and full factorization into the
LITERAL singular strict transform. Its source complement is also dense. -/
theorem exists_local_factorization_of_actual_cartier
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (F : actualSubspaceLocallyRingedSpace (n := m) S ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hF : F ≫ subspacePointMap (n := n) W = subspacePointMap (n := m) S)
    (hCart : ∀ x : S,
      ∃ alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier,
        IsRegular alpha ∧
        Ideal.map (F.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base x).val)) =
          Ideal.span {alpha}) (x : S) :
    ∃ (P : LocallyRingedSpace) (j : P ⟶ actualSubspaceLocallyRingedSpace (n := m) S)
      (K : P ⟶ actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
      K ≫ subspacePointMap (n := n) (strictTransform n π W) = j ≫ subspacePointMap (n := m) S ∧
      K ≫ strictTransformProjection hπ hW = j ≫ F ∧
      Dense {u : P | (F.base (j.base u)).val ∉ C} := by
  obtain ⟨T, hxT, O, hxO, G, hG, hSW, hrep⟩ := exists_local_ambient_representative F hF x
  let S₀ : Set O := (Subtype.val : O → T) ⁻¹' ((Subtype.val : T → N) ⁻¹' S)
  let j₀ : actualSubspaceLocallyRingedSpace (n := m) S₀ ⟶
      actualSubspaceLocallyRingedSpace (n := m) S :=
    actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫
      actualOpenSubspaceMap (n := m) S T
  let : LocallyRingedSpace.IsOpenImmersion j₀ := by
    dsimp only [j₀]
    infer_instance
  have hrep' : actualSubspaceMap hG hSW = j₀ ≫ F :=
    hrep.trans (Category.assoc _ _ _).symm
  have hCartG := cartier_on_actual_ambient_representative hπ.1 F j₀ hG hSW hrep' hCart
  let x₀ : S₀ := ⟨⟨⟨x.val, hxT⟩, hxO⟩, x.property⟩
  obtain ⟨alpha, hreg, hspan⟩ := hCartG x₀
  obtain ⟨U, hxU, L, hL, hfac⟩ := exists_local_native_lift_of_actual_cartier hπ hG S₀ x₀ hreg hspan
  let R : Set U := (Subtype.val : U → O) ⁻¹' S₀
  let j₁ : actualSubspaceLocallyRingedSpace (n := m) R ⟶
      actualSubspaceLocallyRingedSpace (n := m) S₀ := actualOpenSubspaceMap (n := m) S₀ U
  have hdense₀ := dense_compl_centre_of_actual_cartier hG.continuous hCartG
  have hdense : Dense {z : R | G z.val.val ∉ C} :=
    hdense₀.preimage (actualOpenSubspaceMap_base_isOpenEmbedding (n := m) S₀ U).isOpenMap
  have hclosed : IsClosed {z : R | L z.val ∈ BlowupStrictSubmanifold.geoStrictTransform π C W} :=
    isClosed_closure.preimage (hL.continuous.comp continuous_subtype_val)
  have hsub : {z : R | G z.val.val ∉ C} ⊆
      {z : R | L z.val ∈ BlowupStrictSubmanifold.geoStrictTransform π C W} := by
    intro z hz
    apply subset_closure
    change π (L z.val) ∈ W ∧ π (L z.val) ∉ C
    rw [hfac z.val z.property]
    exact ⟨hSW z.val.val z.property, hz⟩
  have hall : Set.univ ⊆ {z : R | L z.val ∈ BlowupStrictSubmanifold.geoStrictTransform π C W} := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  have hland : ∀ z ∈ R, L z ∈ strictTransform n π W := fun z hz =>
    BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W (hall (mem_univ (⟨z, hz⟩ : R)))
  let K := actualSubspaceMap hL hland
  let j := j₁ ≫ j₀
  have hpointT : actualOpenSubspaceMap (n := m) S T ≫ subspacePointMap (n := m) S =
      subspacePointMap (n := m) ((Subtype.val : T → N) ⁻¹' S) := actualSubspaceMap_point _ _
  have hpointO : actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫
      subspacePointMap (n := m) ((Subtype.val : T → N) ⁻¹' S) =
      subspacePointMap (n := m) S₀ := actualSubspaceMap_point _ _
  have hpoint₀ : j₀ ≫ subspacePointMap (n := m) S = subspacePointMap (n := m) S₀ := by
    calc
      _ = actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫
          (actualOpenSubspaceMap (n := m) S T ≫ subspacePointMap (n := m) S) := Category.assoc _ _ _
      _ = _ := (congrArg (fun H => actualOpenSubspaceMap (n := m)
        ((Subtype.val : T → N) ⁻¹' S) O ≫ H) hpointT).trans hpointO
  have hpoint₁ : j₁ ≫ subspacePointMap (n := m) S₀ = subspacePointMap (n := m) R :=
    actualSubspaceMap_point _ _
  have hjpoint : j ≫ subspacePointMap (n := m) S = subspacePointMap (n := m) R := by
    change (j₁ ≫ j₀) ≫ _ = _
    rw [Category.assoc, hpoint₀, hpoint₁]
  have hKpoint : K ≫ subspacePointMap (n := n) (strictTransform n π W) =
      subspacePointMap (n := m) R := actualSubspaceMap_point _ _
  have hGpoint : ∀ z : R, G z.val.val = (F.base (j.base z)).val := by
    intro z
    exact congrArg (fun H : actualSubspaceLocallyRingedSpace (n := m) S₀ ⟶
      actualSubspaceLocallyRingedSpace (n := n) W => (H.base (j₁.base z)).val) hrep'
  refine ⟨actualSubspaceLocallyRingedSpace (n := m) R, j, K, ?_, ?_,
    hKpoint.trans hjpoint.symm, ?_, ?_⟩
  · dsimp only [j, j₁]
    infer_instance
  · refine ⟨⟨⟨x₀.val, hxU⟩, x₀.property⟩, ?_⟩
    apply Subtype.ext
    rfl
  · apply actualSubspaceMap_eq_of_base_eq
    · rw [Category.assoc, strictTransformProjection_point, hKpoint]
    · rw [Category.assoc, hF, hjpoint]
    · ext z
      apply Subtype.ext
      change π (L z.val) = (F.base (j.base z)).val
      exact (hfac z.val z.property).trans (hGpoint z)
  · apply hdense.mono
    intro z hz
    change (F.base (j.base z)).val ∉ C
    rwa [← hGpoint z]

end LocalFactorization

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalLocalFactorization
