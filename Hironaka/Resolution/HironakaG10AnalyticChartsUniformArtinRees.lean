import Hironaka.Resolution.HironakaG10PNIdealNoetherModel
import Hironaka.Resolution.HironakaG10NativeFamilyUniformArtinRees
import Hironaka.Resolution.HironakaG10OpenImmersionUniformArtinRees

/-! # Uniform Artin--Rees on spaces with analytic model charts -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10AnalyticChartsUniformArtinRees

noncomputable section

open HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaG10PNIdealFamily HironakaG10PNIdealNoetherModel
  HironakaG10ChowUniformArtinRees HironakaG10GraphCentreUniformArtinRees
  HironakaG10NativeFamilyUniformArtinRees HironakaG10OpenImmersionUniformArtinRees

/-- Local uniform Artin--Rees for whole native ideals on a reduced embedded
analytic model, obtained from their full preimages in the actual ambient open. -/
theorem exists_model_uniform_artinRees {n : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (hC : IsComplexAnalyticSubset (n := n) C)
    (J K : ∀ y : actualSubspaceLocallyRingedSpace (n := n) C,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk y))
    (hJ : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) C) J)
    (hK : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) C) K)
    (x : actualSubspaceLocallyRingedSpace (n := n) C) :
    ∃ α : ℕ, ∃ O : Set (actualSubspaceLocallyRingedSpace (n := n) C),
      IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O, IsArtinReesNumber (J y) (K y) α := by
  let A := pushFamily C J
  let B := pushFamily C K
  have hA := pushFamily_isLocallyFinitelyGenerated hC J hJ
  have hB := pushFamily_isLocallyFinitelyGenerated hC K hK
  obtain ⟨α,O,hO,hxO,hAR⟩ := exists_native_locallyFG_uniform_artinRees U A B hA hB x.val
  refine ⟨α,Subtype.val ⁻¹' O,hO.preimage continuous_subtype_val,hxO,fun y hy => ?_⟩
  have hpre : A y.val = Ideal.comap ((actualSubspaceInclusion (n := n) C).stalkMap y).hom (J y) :=
    pushFamily_of_mem C J y
  have hh := hAR y.val hy
  rw [hpre] at hh
  have hdown := isArtinReesNumber_of_comap ((actualSubspaceInclusion (n := n) C).stalkMap y).hom
    (actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C y) (J y) (B y.val) α hh
  have hreturn := pull_pushFamily C K y
  change K y = Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap y).hom (B y.val) at hreturn
  rwa [← hreturn] at hdown

/-- Local uniform Artin--Rees on a native locally ringed space with the
actual embedded analytic charts. -/
theorem exists_charts_uniform_artinRees {X : LocallyRingedSpace.{0}}
    (hX : HasAnalyticModelCharts X)
    (I K : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hI : IsLocallyFinitelyGenerated X I) (hK : IsLocallyFinitelyGenerated X K) (x : X) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α := by
  obtain ⟨n,U,C,hC,i,hi,y,rfl⟩ := hX x
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  apply exists_uniform_artinRees_of_openImmersion i I K y
  exact exists_model_uniform_artinRees U C hC (pullFamily i I) (pullFamily i K)
    (isLocallyFinitelyGenerated_pull i hI) (isLocallyFinitelyGenerated_pull i hK) y

/-- One exponent works on a neighbourhood of any compact subset of an
analytic space, for the two whole locally finitely generated ideal families. -/
theorem exists_charts_compact_uniform_artinRees {X : LocallyRingedSpace.{0}}
    (hX : HasAnalyticModelCharts X)
    (I K : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hI : IsLocallyFinitelyGenerated X I) (hK : IsLocallyFinitelyGenerated X K)
    (Q : Set X) (hQ : IsCompact Q) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ Q ⊆ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α := by
  obtain ⟨O,α,hO,hQO,hAR⟩ := exists_artinReesOn_of_local I K Q hQ
    (fun y _ => by
      obtain ⟨a,U,hU,hyU,hlocal⟩ := exists_charts_uniform_artinRees hX I K hI hK y
      exact ⟨U,hU.mem_nhds hyU,a,hlocal⟩)
  exact ⟨α,O,hO,hQO,hAR⟩

end

end Hironaka.HironakaG10AnalyticChartsUniformArtinRees
