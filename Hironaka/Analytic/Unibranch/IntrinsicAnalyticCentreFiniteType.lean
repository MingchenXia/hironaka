import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets
import Hironaka.Coherence.CartanCoherenceInterface
import Hironaka.Resolution.HironakaLegacyCoherentIdealFiniteType
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback

/-!
# Native finite type of intrinsic analytic-centre ideals on original complex spaces

An ordinary analytic subset of any ORIGINAL reduced complex space has a
finite-type intrinsic ideal. Actual ambient Cartan sections pass through the
genuine quotient IMAGE ideal, then lift along actual open immersions to the
original space. Entire all-point ideal spans derive native finite-free epis.
No global embedding, compactness, purity, density or finite-type packet is used.

Blueprint: `intrinsic-analytic-centre-finite-type.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.IntrinsicAnalyticCentreFiniteType

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaLegacyCoherentIdealSheaf HironakaLegacyCoherentIdealFiniteType
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenSections HironakaIntrinsicReducedCentreOpenPullback
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaChowNativeFinitePresentationSpreading

noncomputable section

private theorem model_local_whole_span
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {W C₀ : Set M} (hC₀ : IsComplexAnalyticSubset (n := n) C₀)
    (hCW : C₀ ⊆ W) (w : W) :
    ∃ (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat)
      (_hw : w ∈ U) (r : ℕ)
      (s : Fin r → intrinsicReducedCentreSectionIdeal
        (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C₀) U),
      ∀ (y : W) (hy : y ∈ U),
        intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C₀) y =
          Ideal.span (range fun i => (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.germ
            U y hy (s i).val) := by
  have hI : (vanishingIdeal (n := n) C₀).IsCoherent :=
    CartanCoherenceInterface.cartanCoherence C₀ hC₀
  obtain ⟨V, hw, r, a, _hp, ha⟩ :=
    exists_local_finite_generators (vanishingIdeal (n := n) C₀) hI w.val
  let j := actualSubspaceInclusion (n := n) W
  let U := (Opens.map j.base).obj V
  let s (i : Fin r) := intrinsicReducedCentreModelSection W C₀ V (a i)
  refine ⟨U, hw, r, s, ?_⟩
  intro y hy
  calc
    _ = Ideal.map (j.stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C₀) y.val) :=
      intrinsicReducedCentreStalkInclusion_range_model hCW y
    _ = Ideal.map (j.stalkMap y).hom
        (LinearMap.range (stalkInclusionLinearMap (actualComplexStructureSheaf (n := n) M)
          (actualIdealModuleSheaf (vanishingIdeal (n := n) C₀))
          (actualIdealModuleInclusion (vanishingIdeal (n := n) C₀)) y.val)) :=
      congrArg (Ideal.map (j.stalkMap y).hom)
        (actualIdealModule_stalkRange (vanishingIdeal (n := n) C₀) hI y.val).symm
    _ = Ideal.map (j.stalkMap y).hom
        (Ideal.span (range fun i => (actualComplexStructureSheaf (n := n) M).presheaf.germ
          V y.val hy ((actualIdealModuleInclusion (vanishingIdeal (n := n) C₀)).val.app
            (op V) (a i)))) := congrArg (Ideal.map (j.stalkMap y).hom) (ha y.val hy)
    _ = Ideal.span (range fun i => j.stalkMap y
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ V y.val hy
          ((actualIdealModuleInclusion (vanishingIdeal (n := n) C₀)).val.app (op V) (a i)))) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = _ := congrArg Ideal.span (congrArg range
      (funext fun i => (intrinsicReducedCentreModelSection_germ W C₀ V (a i) y hy).symm))

private theorem openImmersion_lift_whole_span
    {Y X : LocallyRingedSpace} (j : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion j]
    (C : Set X) (V : Opens Y.toTopCat) {r : ℕ}
    (s : Fin r → intrinsicReducedCentreSectionIdeal Y (j.base ⁻¹' C) V)
    (hs : ∀ (y : Y) (hy : y ∈ V), intrinsicCentreStalkRange Y (j.base ⁻¹' C) y =
      Ideal.span (range fun i => Y.presheaf.germ V y hy (s i).val))
    (z : X) (hz : z ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) :
    intrinsicCentreStalkRange X C z =
      Ideal.span (range fun i => X.presheaf.germ
        ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) z hz
        (openImmersionIntrinsicSectionLift j C V (s i)).val) := by
  obtain ⟨y, hy, rfl⟩ := hz
  change intrinsicCentreStalkRange X C (j.base y) =
    Ideal.span (range fun i => X.presheaf.germ
      ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) (j.base y)
      (show j.base y ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V from
        ⟨y, hy, rfl⟩) (openImmersionIntrinsicSectionLift j C V (s i)).val)
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have hmap :
      Ideal.map (j.stalkMap y).hom (intrinsicCentreStalkRange X C (j.base y)) =
        Ideal.map (j.stalkMap y).hom
          (Ideal.span (range fun i => X.presheaf.germ
            ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) (j.base y)
            (show j.base y ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V from
              ⟨y, hy, rfl⟩) (openImmersionIntrinsicSectionLift j C V (s i)).val)) := by
    calc
      _ = intrinsicCentreStalkRange Y (j.base ⁻¹' C) y :=
        openImmersion_pulled_stalkIdeal_eq j C y
      _ = _ := hs y hy
      _ = _ := by
        rw [Ideal.map_span, ← Set.range_comp]
        exact congrArg Ideal.span (congrArg range
          (funext fun i => (openImmersionIntrinsicSectionLift_germ j C V (s i) y hy).symm))
  have hc := congrArg (Ideal.comap (j.stalkMap y).hom) hmap
  simpa only [Ideal.comap_map_of_bijective _ hbij] using hc

private theorem exists_original_local_generators
    (X : SourceReducedComplexSpace) (C : Set X.obj.left) (hC : X.IsAnalyticSubset C)
    (x : X.obj.left) :
    ∃ (U : Opens X.obj.left.toTopCat) (_hx : x ∈ U) (r : ℕ)
      (s : Fin r → (intrinsicReducedCentreIdealModule X.obj.left C).val.obj (op U)),
      Epi (freeOverMap X.obj.left.toSheafedSpace.sheaf U s) := by
  classical
  obtain ⟨e, ⟨w, hw⟩, A, hA, hpre⟩ := hC x
  let C₀ : Set e.ambient := e.carrier ∩ A
  have hC₀ : IsComplexAnalyticSubset (n := e.dim) C₀ := e.analytic.inter hA
  have hCW : C₀ ⊆ e.carrier := inter_subset_left
  let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
  let : LocallyRingedSpace.IsOpenImmersion j := e.isOpenImmersion
  have htrace : j.base ⁻¹' C = (Subtype.val : e.carrier → e.ambient) ⁻¹' C₀ := by
    change e.toPoint ⁻¹' C = _
    rw [hpre]
    ext y
    exact ⟨fun hy => ⟨y.property, hy⟩, fun hy => hy.2⟩
  obtain ⟨V, hwV, r, a, ha⟩ := model_local_whole_span hC₀ hCW w
  let s (i : Fin r) : intrinsicReducedCentreSectionIdeal
      (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier) (j.base ⁻¹' C) V :=
    ⟨(a i).val, by
      change (a i).val ∈ intrinsicReducedCentreSectionIdeal
        (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier) (j.base ⁻¹' C) V
      rw [htrace]
      exact (a i).property⟩
  have hs (y : e.carrier) (hy : y ∈ V) :
      intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier)
        (j.base ⁻¹' C) y =
        Ideal.span (range fun i =>
          (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier).presheaf.germ V y hy
            (s i).val) := by
    simpa only [s, htrace] using ha y hy
  let U := (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V
  let t (i : Fin r) := openImmersionIntrinsicSectionLift j C V (s i)
  have hxU : x ∈ U := hw ▸ (show j.base w ∈ U from ⟨w, hwV, rfl⟩)
  refine ⟨U, hxU, r, t, ?_⟩
  exact finite_free_epi_of_whole_image_span X.obj.left.toSheafedSpace.sheaf
    (intrinsicReducedCentreIdealInclusion X.obj.left C) (fun _ => Subtype.val_injective)
    U t (openImmersion_lift_whole_span j C V s hs)

/-- Every ordinary analytic subset of an arbitrary ORIGINAL reduced complex
space has a native finite-type intrinsic ideal, including the zero/unit cases. -/
theorem intrinsicReducedCentreIdealModule_isFiniteType
    (X : SourceReducedComplexSpace) (C : Set X.obj.left) (hC : X.IsAnalyticSubset C) :
    (intrinsicReducedCentreIdealModule X.obj.left C).IsFiniteType := by
  classical
  let R := X.obj.left.toSheafedSpace.sheaf
  let B := intrinsicReducedCentreIdealModule X.obj.left C
  choose U hx r s hp using exists_original_local_generators X C hC
  let gs (x : X.obj.left) : (B.over (U x)).GeneratingSections := by
    letI : Epi (freeOverMap R (U x) (s x)) := hp x
    exact (SheafOfModules.free.generatingSections (Fin (r x))).ofEpi
      ((freeOverIso R (U x) (Fin (r x))).hom ≫ freeOverMap R (U x) (s x))
  have hgs (x : X.obj.left) : (gs x).IsFiniteType :=
    ⟨inferInstanceAs (Finite (Fin (r x)))⟩
  let q : B.LocalGeneratorsData.{0} :=
    { I := X.obj.left
      X := U
      coversTop := by
        intro V
        apply (Opens.mem_grothendieckTopology X.obj.left.toTopCat).mpr
        intro x hxV
        refine ⟨V ⊓ U x, homOfLE inf_le_left, ?_, ⟨hxV, hx x⟩⟩
        exact (Sieve.mem_ofObjects_iff U _).mpr ⟨x, ⟨homOfLE inf_le_right⟩⟩
      generators := gs }
  exact ⟨⟨q, ⟨hgs⟩⟩⟩

end

end Hironaka.Analytic.Unibranch.IntrinsicAnalyticCentreFiniteType
