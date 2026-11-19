import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
import Hironaka.Analytic.Unibranch.HironakaG10OpenChartHelpers
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaG10LocSectionNoether
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
  Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
namespace Hironaka.Analytic.Unibranch.HironakaG10SchurSectionStalk
noncomputable section
variable {E₁ E₀ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- An actual scalar operator section has its literal translated scalar germ
under the genuine manifold stalk-chart equivalence. -/
theorem operatorScalarSection_stalk_germ (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U)
    (p : U) (v : E₁) (ell : E₀ →L[ℂ] ℂ) :
    let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U
    actualStalkChartEquiv (n := d) p
      (X.presheaf.germ ⊤ p trivial (operatorScalarSection d U S hS v ell)) =
      germAt p.val (operatorScalarFunction d S v ell) := by
  let sec := operatorScalarSection d U S hS v ell
  let f := sectionExtension (⊤ : Opens U) sec
  have hf : HolomorphicAt d f p := sectionExtension_holomorphicAt ⊤ sec p trivial
  have hS' : HolAt (operatorScalarFunction d S v ell) p.val := by
    filter_upwards [U.isOpen.mem_nhds p.property] with x hx
    exact (differentiableOn_operatorScalarFunction d U S hS v ell x hx).differentiableAt (U.isOpen.mem_nhds hx)
  dsimp only
  change actualStalkChartEquiv (n := d) p
    ((actualComplexStructureSheaf (n := d) U).presheaf.germ ⊤ p trivial sec) = _
  rw [actualStalkChartEquiv_germ]
  change chartTranslatedGerm p p (mem_chart_source _ p) f hf = _
  rw [chartTranslatedGerm_open_eq_germAt U p p f hf]
  apply (germAt_eq_germAt_iff ?_ hS').mpr
  · filter_upwards [U.isOpen.mem_nhds p.property] with z hz
    have hz' : z ∈ U := hz
    have he := open_chart_symm_val U p hz'
    change f ((chartAt (ComplexModel d) p).symm z) = operatorScalarFunction d S v ell z
    change sectionExtension (⊤ : Opens U) sec ((chartAt (ComplexModel d) p).symm z) = _
    rw [sectionExtension_apply ⊤ sec _ trivial]
    change ell (S (((chartAt (ComplexModel d) p).symm z).val) v) = ell (S z v)
    rw [he]
  · simpa only [open_chart_apply] using (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ p) hf)

/-- The complete family of actual section germs maps to the whole scalar
operator germ ideal, with no finite-generator choice. -/
theorem map_scalarOperatorSection_stalk_ideal (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U) (p : U) :
    let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U
    let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
      fun q => operatorScalarSection d U S hS q.1 q.2
    Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) =
      Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) => germAt p.val (operatorScalarFunction d S q.1 q.2)) := by
  dsimp only
  simp only [spanFamily, Set.image_univ, Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, (operatorScalarSection_stalk_germ d U S hS p q.1 q.2).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨_, ⟨q, rfl⟩, ?_⟩
    exact operatorScalarSection_stalk_germ d U S hS p q.1 q.2
/-- At the original parameter origin, the actual section-germ ideal is the
literal whole scalar HolGerm span used in the native quotient criterion. -/
theorem map_scalarOperatorSection_stalk_ideal_zero (d : ℕ) (U : Opens (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ U)
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U)
    (hT : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ S z) :
    let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) U
    let p : U := ⟨0,h0⟩
    let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
      fun q => operatorScalarSection d U S hS q.1 q.2
    Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) =
      Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) =>
        HolGerm.mk (operatorScalarFunction d S q.1 q.2)
          (hT.mono fun z hz => q.2.differentiableAt.comp z ((ContinuousLinearMap.apply ℂ E₀ q.1).differentiableAt.comp z hz))) := by
  dsimp only
  rw [map_scalarOperatorSection_stalk_ideal]
  congr 1
  ext g
  constructor
  · rintro ⟨q,rfl⟩
    refine ⟨q,?_⟩
    have h : HolAt (operatorScalarFunction d S q.1 q.2) (0 : ComplexModel d) :=
      hT.mono fun z hz => q.2.differentiableAt.comp z ((ContinuousLinearMap.apply ℂ E₀ q.1).differentiableAt.comp z hz)
    change HolGerm.mk (operatorScalarFunction d S q.1 q.2) _ =
      germAt (0 : ComplexModel d) (operatorScalarFunction d S q.1 q.2)
    rw [germAt_of_holAt h]
    simp only [zero_add, add_zero]
  · rintro ⟨q,rfl⟩
    refine ⟨q,?_⟩
    have h : HolAt (operatorScalarFunction d S q.1 q.2) (0 : ComplexModel d) :=
      hT.mono fun z hz => q.2.differentiableAt.comp z ((ContinuousLinearMap.apply ℂ E₀ q.1).differentiableAt.comp z hz)
    change germAt (0 : ComplexModel d) (operatorScalarFunction d S q.1 q.2) =
      HolGerm.mk (operatorScalarFunction d S q.1 q.2) _
    rw [germAt_of_holAt h]
    simp only [zero_add, add_zero]

end
end Hironaka.Analytic.Unibranch.HironakaG10SchurSectionStalk
