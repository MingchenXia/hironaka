import Hironaka.Resolution.HironakaG4OptionalGammaProtectedBoundary
import Hironaka.Resolution.HironakaG4JointGammaLowerChart
import Hironaka.Resolution.HironakaG4WellFormedSubopen

/-! A prepared Gamma chart and the actual local lower trace protect the step. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4GammaLocalTraceProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34CoordinateScaling HironakaG34MaskFoldEquivariance HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalDivisorMasks HironakaG4GammaOptionalDictionary HironakaG4JointGammaLowerChart
  HironakaG4WellFormedSubopen HironakaG4OptionalGammaProtectedBoundary HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- A Gamma chart and a locally identified lower trace protect the actual
equivariant test centre, with the literal original-tail-plus-birth boundary. -/
theorem gamma_chart_and_local_lower_trace_protect_step_with_window
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (G : Set X) (F₀ : List (Set X))
    (hDE : D.E = G :: F₀) (hN : IsClosedSubmanifold n D.N) (hI : D.ideal.IsCoherent)
    (hDclosed : ∀ K ∈ D.E, IsClosed K) (hmark : D.d = 0)
    (U : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (S : Set X) (hSlice : (Subtype.val : U → X) ⁻¹' S =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ G))
    {W H : Set X} {E : List (Set X)} (j : Fin D.E.length)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) (hEq : IsEquivariant W E (.step T C π hπ))
    (x : Y) (hxC : x ∈ C) (hxW : T.proj x ∈ W)
    (hW : ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ D.N ∩ D.E.get j)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (T.proj x) (T.proj x)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (T.proj x)).target)
    (hΦU : flatDomain Φ ⊆ (U : Set X))
    (s t : Fin n) (c : Fin n → ℕ) (R₀ : Finset (Fin n)) (m : Fin D.E.length → Option (Fin n))
    (hs : s ∈ R₀) (hst : t ≠ s) (hcs : c s = 0) (hm : DivisorMasksValid R₀ m)
    (hNcoords : ∀ y ∈ flatDomain Φ, y ∈ D.N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hDcoords : ∀ i y, y ∈ flatDomain Φ → (y ∈ D.E.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ binomial s t c (flatMap Φ y) = 0)
    (hE : ∀ K ∈ E, K = H ∨ (K ∈ D.E ∨ (U : Set X) ⊆ K)) :
    let K : MarkedIdeal n X := {D with E := []}
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S)
      (F₀.map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  obtain ⟨Ψ,R,hsrc,hR,hcenter,hN',hD',hH',hW'⟩ :=
    exists_joint_gamma_lower_chart Φ D.N W H D.E j R₀ m s t c hxW hW hNcoords hDcoords hH
  have hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) (T.proj x)).target := hsrc.trans hΦsrc
  have hΨU : flatDomain Ψ ⊆ (U : Set X) := by
    intro y hy
    exact hΦU ⟨hy.1,hsrc hy.2⟩
  let V : Opens X := ⟨flatDomain Ψ, isOpen_flatDomain Ψ⟩
  have hVU : V ≤ U := hΨU
  have hDV := wellFormed_pullback_val_of_subopen D hN hI U V hVU hD
  have hSliceV : (Subtype.val : V → X) ⁻¹' S = (Subtype.val : V → X) ⁻¹' (D.N ∩ G) := by
    ext y
    exact Set.ext_iff.mp hSlice ⟨y.val,hVU y.property⟩
  have hWindow : ∀ y ∈ V, y ∈ flatDomain Ψ ∧ flatMap Ψ y ∈ Ψ.target := by
    intro y hy
    exact ⟨hy,Ψ.mapsTo_toFun hy.2⟩
  have hWcoords : ∀ y ∈ flatDomain Ψ, flatMap Ψ y ∈ Ψ.target →
      (y ∈ W ↔ flatMap Ψ y ∈ coordSubspace R) := fun y hy _ => hW' y hy
  let O : Opens (ComplexModel n) := ⟨Ψ.target, Ψ.isOpen_target⟩
  have hEcoords := optional_gamma_dictionary_of_masks_with_window Ψ O D.E E H m s t c hD' hH' U hΨU hE
  exact optional_gamma_chart_protects_equivariant_centre_with_actual_boundary P D hPN G F₀ hDE
    hN.1 hDclosed V hDV hmark S hSliceV Ψ hΨsrc O (Subset.rfl) hWindow
    s t c R R₀ m hs hst hcs hN' hD' hm hWcoords hEcoords T C π hπ hTest hEq
    x hxC (mem_flatDomain_self Ψ)

/-- Protect the step using the whole actual boundary as the equivariance data. -/
theorem gamma_chart_and_local_lower_trace_protect_step
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (G : Set X) (F₀ : List (Set X))
    (hDE : D.E = G :: F₀) (hN : IsClosedSubmanifold n D.N) (hI : D.ideal.IsCoherent)
    (hDclosed : ∀ K ∈ D.E, IsClosed K) (hmark : D.d = 0)
    (U : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (S : Set X) (hSlice : (Subtype.val : U → X) ⁻¹' S =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ G))
    {W H : Set X} {E : List (Set X)} (j : Fin D.E.length)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) (hEq : IsEquivariant W E (.step T C π hπ))
    (x : Y) (hxC : x ∈ C) (hxW : T.proj x ∈ W)
    (hW : ∀ᶠ y in 𝓝 (T.proj x), y ∈ W ↔ y ∈ D.N ∩ D.E.get j)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (T.proj x) (T.proj x)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (T.proj x)).target)
    (hΦU : flatDomain Φ ⊆ (U : Set X))
    (s t : Fin n) (c : Fin n → ℕ) (R₀ : Finset (Fin n)) (m : Fin D.E.length → Option (Fin n))
    (hs : s ∈ R₀) (hst : t ≠ s) (hcs : c s = 0) (hm : DivisorMasksValid R₀ m)
    (hNcoords : ∀ y ∈ flatDomain Φ, y ∈ D.N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hDcoords : ∀ i y, y ∈ flatDomain Φ → (y ∈ D.E.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ binomial s t c (flatMap Φ y) = 0)
    (hE : ∀ K ∈ E, K = H ∨ K ∈ D.E) :
    let K : MarkedIdeal n X := {D with E := []}
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S)
      (F₀.map (strictAlong T) ++ (geoTransformAlong K T).E) C x :=
  gamma_chart_and_local_lower_trace_protect_step_with_window
    P D hPN G F₀ hDE hN hI hDclosed hmark U hD S hSlice j T C π hπ hTest hEq
    x hxC hxW hW Φ hΦsrc hΦU s t c R₀ m hs hst hcs hm hNcoords hDcoords hH
    (fun K hK => (hE K hK).imp id Or.inl)

end
end Hironaka.HironakaG4GammaLocalTraceProtection
