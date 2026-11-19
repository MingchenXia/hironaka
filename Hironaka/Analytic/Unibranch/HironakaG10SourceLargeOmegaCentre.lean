import Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
import Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundarySumCentre
import Hironaka.Analytic.Unibranch.HironakaG10SumCentreFlat
import Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation

/-! # Source large-exponent ideals produce compatible admissible sum centres -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaCentre
open Hironaka HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaExact
  Hironaka.Analytic.Unibranch.HironakaG10FiniteIdealSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdentifiedSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10SumCentreFlat
  Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdealSeparation
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- The large-ω source boundary ideals yield admissible centre-flat sum
  centres, whose whole stalk ideals have the original tracked-boundary
  formula near every tracked point in the chosen compact set. -/
theorem exists_source_large_omega_sumCentre {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    {q : ℕ} (Z : Fin q → LocalFlattener f) (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (hSaux : IsLocallyAnalyticOn X Zaux.V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) (i + 1)).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ i + 1)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support)
    (hdense : Dense (nonflatImage f)ᶜ)
    (K : Set X.obj.left) (hK : IsCompact K)
    (hKtracked : ∀ x ∈ K, ∃ p, x ∈ stratumBoundary f B (Z p).V (Z p).support i) :
    let C := Cset f B (fun p => (Z p).support) (i + 1)
    let Q := C ∩ stratumBoundary f B Zaux.V Zaux.support i
    ∃ (W : Set X.obj.left) (ω₀ : ℕ), IsOpen W ∧ K ⊆ W ∧ W ⊆ Zaux.V ∧
      ∀ ω ≥ ω₀, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = Q ∧
        (∀ x ∈ Zaux.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) x ⊔ Zaux.H x)) ∧
        ∃ α : ℕ, ∀ β : ℕ, α ≤ β → ∃ c : AdmissibleCentre f,
          nonunitLocus c.B c.b = Q ∧ IsSumCentreFor c.B c.b f β ∧
          (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt f x
            (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b x))) ∧
          (β ≠ 0 → letI : c.B.IsFiniteType := c.finiteType
            ∀ x' : (OriginalFiniteIdealBlowup.sourceObject c.B c.b c.dense).obj.left,
            (stepProj c.B c.b c.dense).hom.left.base x' ∈ Zaux.V →
            ¬ (OnStrictTransform (stepProj c.B c.b c.dense) x'
                (wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')) ∧
              OnStrictTransform (stepProj c.B c.b c.dense) x'
                (Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x'))
                ((wholeIdealFamily D d ((stepProj c.B c.b c.dense).hom.left.base x')) ^ β ⊔
                  Zaux.H ((stepProj c.B c.b c.dense).hom.left.base x')))) ∧
          ∀ p x, x ∈ K → x ∈ stratumBoundary f B (Z p).V (Z p).support i →
            ∀ᶠ y in 𝓝 x, LinearMap.range
              (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b y) =
                (intrinsicCentreStalkRange X.obj.left
                  (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y) ^ β ⊔
                    (Z p).H y := by
  let C := Cset f B (fun p => (Z p).support) (i + 1)
  let Q := C ∩ stratumBoundary f B Zaux.V Zaux.support i
  obtain ⟨hCa,hCc,_,hCnf⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support)
    (i + 1) hfinite hmax
  have hClocal : IsLocallyAnalyticOn X Zaux.V C := locallyAnalytic_of_analytic hCa Zaux.V
  have hCV : C ⊆ Zaux.V := fun x hx => (hC hx).1
  have hCdense : Dense Cᶜ := hdense.mono (Set.compl_subset_compl.mpr hCnf)
  have hQZ : Q ⊆ Zaux.support := fun _ hx => hx.2.2
  obtain ⟨hQcompact,hQnonflat⟩ := compact_global_cut_of_local_data f B C Zaux i
    hSaux hClocal hCc hCV
  have hQdense : Dense Qᶜ := hCdense.mono (Set.compl_subset_compl.mpr inter_subset_left)
  obtain ⟨W,ω₀,hW,hKW,hWV,hω⟩ := exists_source_large_omega_exact
    f B Z Zaux i hS hSaux N hN hcover hfinite hmax hC K hK hKtracked
  refine ⟨W,ω₀,hW,hKW,hWV,fun ω hω₀ => ?_⟩
  obtain ⟨D,d,hDfin,hDQ,hDsource,_,hDtracked⟩ := hω ω hω₀
  let : D.IsFiniteType := hDfin
  let IS := wholeIdealFamily D d
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Zaux.V IS :=
    locallyFinite_wholeIdealFamily D d Zaux.V
  have hQIS : {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} = Q := by
    ext x
    constructor
    · intro hx
      have hxD : x ∈ nonunitLocus D d := hx.2
      rw [hDQ] at hxD
      exact hxD
    · intro hx
      have hxD : x ∈ nonunitLocus D d := by rw [hDQ]; exact hx
      exact ⟨hQZ hx,hxD⟩
  have hcompact : IsCompact {x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤} :=
    hQIS.symm ▸ hQcompact
  have hdense' : Dense {x : X.obj.left | ¬ (x ∈ Zaux.support ∧ IS x ≠ ⊤)} := by
    change Dense ({x : X.obj.left | x ∈ Zaux.support ∧ IS x ≠ ⊤}ᶜ)
    rw [hQIS]
    exact hQdense
  obtain ⟨α,hα⟩ := exists_sourceIdentified_sumCentre f Zaux IS hIS hcompact hdense'
  refine ⟨D,d,hDfin,hDQ,hDsource,α,fun β hαβ => ?_⟩
  obtain ⟨T,t,htfinite,htQ,htdense,htsum,htsource⟩ := hα β hαβ
  let c : AdmissibleCentre f := ⟨T,t,htfinite,htdense,by rw [htQ,hQIS]; exact hQnonflat⟩
  let : T.IsFiniteType := htfinite
  refine ⟨c,htQ.trans hQIS,htsum,flatOver_sumCentre f c.B c.b β htsum,?_,?_⟩
  · intro hβ x' hx'
    exact source_families_separated_unpowered f Zaux IS β hβ T t htdense htsource x' hx'
  intro p x hxK hxE
  have hxC := tracked_boundary_subset_cset f B Z i hS N hN hcover p hxE
  have hxAux : x ∈ Zaux.support := hC hxC
  have hH := Zaux.eventually_eq (Z p) hxAux hxE.2
  have hD := hDtracked p x hxK hxE
  filter_upwards [Zaux.isOpen.mem_nhds hxAux.1,hH,hD] with y hyV hyH hyD
  change LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf T t y) = _
  change IS y = _ at hyD
  rw [htsource y hyV,hyD,hyH]

end
end Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaCentre
