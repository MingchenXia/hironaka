import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierRatios
import Hironaka.Blowup.BlowupLocalSurjectivity

/-!
# Local singular-source lifts through the actual monomial blowup charts

A regular principal ideal in the actual singular stalk supplies the chart
ratios. The ambient source pulled ideal need not be invertible, and the
ambient extension need not satisfy the monomial identity away from the
singular carrier. The original manifold-source UP is applied only to the
standard monomial chart. The resulting local square is a WHOLE actual LRS
square, obtained by reduced-source faithfulness.

Blueprint: `hironaka-singular-subspace-blowup-cartier-chart-lift.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierChartLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces
  HironakaSingularSubspaceBlowupCartierRatios
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity

noncomputable section

variable {n m : ℕ} {M Y N : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  {C : Set M} {π : Y → M} {G : N → M} {y₀ : M} {k : ℕ}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}

/-- Actual singular Cartier normal coordinates produce a local holomorphic
lift into the SAME ambient blowup. There is no ambient source ideal
invertibility or incoming ambient factorization premise. -/
theorem exists_local_holomorphic_blowup_lift_of_actual_cartier_coordinates
    (hπ : IsBlowupAlong n C π)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (S : Set N) (x : S) (hxdom : G x.val ∈ flatDomain Φ)
    {alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier}
    (halpha : IsRegular alpha)
    (hspan : Ideal.span (Set.range fun i : {i : Fin n // k ≤ i.val} =>
      ((actualSubspaceInclusion (n := m) S).stalkMap x)
        (actualOriginalFunctionGerm x.val (flatCoord Φ i.val ∘ G)
          ((holomorphicAt_flatCoord Φ i.val hxdom).comp_contMDiff
            (Eventually.of_forall fun z => hG z)))) = Ideal.span {alpha}) :
    ∃ (U : Opens N) (_hxU : x.val ∈ U) (L : U → Y)
      (_hL : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ L),
      ∀ z : U, z.val ∈ S → π (L z) = G z.val := by
  classical
  let I := {i : Fin n // k ≤ i.val}
  let f := fun i : I => flatCoord Φ i.val ∘ G
  have hf : ∀ i : I, HolomorphicAt m (f i) x.val := fun i =>
    (holomorphicAt_flatCoord Φ i.val hxdom).comp_contMDiff
      (Eventually.of_forall fun z => hG z)
  obtain ⟨U₀, hxU₀, j, r, hr, hrj, heq⟩ :=
    exists_local_actual_cartier_ratios S x f hf halpha hspan
  let v : N → Fin n → ℂ := fun z i =>
    if hi : k ≤ i.val ∧ i ≠ j.val then r ⟨i, hi.1⟩ z else flatCoord Φ i (G z)
  let w : N → ComplexModel n := fun z => (EuclideanSpace.equiv (Fin n) ℂ).symm (v z)
  have hdom : G ⁻¹' flatDomain Φ ∈ 𝓝 x.val :=
    hG.continuous.continuousAt.preimage_mem_nhds ((isOpen_flatDomain Φ).mem_nhds hxdom)
  obtain ⟨D, hD, hDo, hxD⟩ := mem_nhds_iff.mp hdom
  let U₁ : Opens N := U₀ ⊓ ⟨D, hDo⟩
  have hxU₁ : x.val ∈ U₁ := ⟨hxU₀, hxD⟩
  have hv : ∀ z ∈ U₁, ∀ i, HolomorphicAt m (fun z' => v z' i) z := by
    intro z hz i
    dsimp only [v]
    split_ifs with hi
    · exact hr ⟨i, hi.1⟩ z hz.1
    · exact (holomorphicAt_flatCoord Φ i (hD hz.2)).comp_contMDiff
        (Eventually.of_forall fun z' => hG z')
  have hw : ∀ z ∈ U₁,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ w z := by
    intro z hz
    have hpi : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, Fin n → ℂ) ∞ v z :=
      contMDiffAt_pi_space.mpr fun i =>
        contMDiffAt_of_eventually_mdifferentiableAt (hv z hz i)
    exact (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.contMDiffAt.comp z hpi
  have hmono : ∀ z ∈ U₁, z ∈ S →
      monomial k j.val (w z) = Φ.toFun (chartAt (ComplexModel n) y₀ (G z)) := by
    intro z hz hzS
    ext i
    rw [monomial_apply]
    change (if k ≤ i.val ∧ i ≠ j.val then v z i * v z j.val else v z i) = _
    dsimp only [v]
    by_cases hi : k ≤ i.val ∧ i ≠ j.val
    · rw [if_pos hi, dif_pos hi, dif_neg (by simp)]
      exact (mul_comm _ _).trans (heq z hz.1 hzS ⟨i, hi.1⟩).symm
    · rw [if_neg hi, dif_neg hi]
      rfl
  have hxw : w x.val ∈ monomialDomain Φ k j.val := by
    change monomial k j.val (w x.val) ∈ Φ.target
    rw [hmono x.val hxU₁ x.property]
    exact Φ.mapsTo_toFun hxdom.2
  have hwmem : ∀ᶠ z in 𝓝 x.val, w z ∈ monomialDomain Φ k j.val :=
    (hw x.val hxU₁).continuousAt.eventually
      ((monomialDomain Φ k j.val).isOpen.mem_nhds hxw)
  obtain ⟨T, hT, hTo, hxT⟩ := mem_nhds_iff.mp hwmem
  let U : Opens N := U₁ ⊓ ⟨T, hTo⟩
  let W : U → LiftedOpen (monomialDomain Φ k j.val) :=
    fun z => LiftedOpen.mk _ (w z.val) (hT z.property.2)
  have hW : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ W := by
    intro z
    apply LiftedOpen.contMDiffAt_of_toModel
    change ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (fun z : U => w z.val) z
    exact contMDiffAt_subtype_iff.mpr (hw z.val z.property.1)
  obtain ⟨ell, ⟨hell, hpie⟩, _⟩ := existsUnique_monomialLift hπ hΦsrc hflat j.property
  refine ⟨U, ⟨hxU₁, hxT⟩, ell ∘ W, hell.comp hW, ?_⟩
  intro z hzS
  calc
    π (ell (W z)) = monomialChart Φ k j.val (W z) := congrFun hpie (W z)
    _ = G z.val := by
      change (chartAt (ComplexModel n) y₀).symm
        (Φ.invFun (monomial k j.val (w z.val))) = G z.val
      rw [hmono z.val z.property.1 hzS]
      exact flatInverse_flat Φ (hD z.property.1.2)

/-- The internally constructed singular-source chart lift retains the complete
actual quotient structure-sheaf square, by original scalar compatibility and
whole-map faithfulness rather than only equality of point maps. -/
theorem exists_local_actual_blowup_square_of_actual_cartier_coordinates
    (hπ : IsBlowupAlong n C π)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (S : Set N) (x : S) (hxdom : G x.val ∈ flatDomain Φ)
    {alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier}
    (halpha : IsRegular alpha)
    (hspan : Ideal.span (Set.range fun i : {i : Fin n // k ≤ i.val} =>
      ((actualSubspaceInclusion (n := m) S).stalkMap x)
        (actualOriginalFunctionGerm x.val (flatCoord Φ i.val ∘ G)
          ((holomorphicAt_flatCoord Φ i.val hxdom).comp_contMDiff
            (Eventually.of_forall fun z => hG z)))) = Ideal.span {alpha}) :
    ∃ (U : Opens N) (_hxU : x.val ∈ U) (L : U → Y)
      (hL : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ L),
      actualSubspaceMap hL
          (C := (Subtype.val : U → N) ⁻¹' S) (D := Set.univ) (fun _ _ => Set.mem_univ _) ≫
        actualSubspaceMap hπ.contMDiff
          (C := Set.univ) (D := Set.univ) (fun _ _ => Set.mem_univ _) =
      actualSubspaceMap (hG.comp contMDiff_subtype_val)
        (C := (Subtype.val : U → N) ⁻¹' S) (D := Set.univ) (fun _ _ => Set.mem_univ _) := by
  obtain ⟨U, hxU, L, hL, hfac⟩ :=
    exists_local_holomorphic_blowup_lift_of_actual_cartier_coordinates
      hπ hG hΦsrc hflat S x hxdom halpha hspan
  refine ⟨U, hxU, L, hL, ?_⟩
  apply actualSubspaceMap_eq_of_base_eq
  · rw [Category.assoc, actualSubspaceMap_point, actualSubspaceMap_point]
  · exact actualSubspaceMap_point _ _
  · ext z
    apply Subtype.ext
    exact hfac z.val z.property

end

end Hironaka.HironakaSingularSubspaceBlowupCartierChartLift
