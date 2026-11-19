import Hironaka.Resolution.HironakaG3UniverseNormalCrossings
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Resolution.HironakaG3UniverseConjugateGeometry
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! The full stage conditions of one physical embedded-resolution history
are preserved by universe lifting and by rebasing along a biholomorphism. -/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG8UniverseBMTransport

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG3UniverseChartTransport HironakaG3UniverseCoordinateTransport
  HironakaG3UniverseCarrierGeometry HironakaG3UniverseNormalCrossings HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  HironakaG3UniverseDiffeoDerivative HironakaG3UniverseLiftedMarkedHistory
  HironakaSmoothSubmersionCoefficientIdeals HironakaCoherentTransformExtension
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  MarkedIdealTowerTransport HomogenizedGlueingTower GermIdealOrder RestrictEmptyTower

/-- The two centre positions, with normal crossings with the full boundary. -/
def BMPosition {n : ℕ} {X : CMfd.{u} n} (A : Set X) (E : List (Set X)) (C : Set X) : Prop :=
  (C ⊆ singularSet (n := n) A ∨
    (IsClosedSubmanifold n A ∧ C ⊆ A ∩ ⋃ H ∈ E, H)) ∧
    HasNormalCrossings n C E

/-- The full boundary at each literal prefix of an original ambient tower. -/
def BMStages {n : ℕ} {X Y : CMfd.{u} n} (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) : Prop :=
  StageCentres (fun P C => BMPosition (strictTransform n P.proj W)
    (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E C) T

section TransportedCoordinates

variable {n : ℕ} {X : CMfd.{u} n} {Y : Type v} [TopologicalSpace Y]
  (e : X ≃ₜ Y)

/-- The singular locus follows the transported complex atlas. -/
theorem transported_singular_set (A : Set X) :
    let : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    let : IsComplexManifold n Y := transported_complex_manifold e
    singularSet (n := n) (e.symm ⁻¹' A) = e.symm ⁻¹' singularSet (n := n) A := by
  let : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  let : IsComplexManifold n Y := transported_complex_manifold e
  ext y
  rw [mem_preimage, mem_singularSet_iff, mem_singularSet_iff]
  exact and_congr_right fun _ => forall_congr' fun d => not_congr (transported_regularAtDim_iff e A y d)

end TransportedCoordinates

theorem bm_stage_test {n : ℕ} {X : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), BMStages W E T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hStage => by
    let G := geometricTemplate (univ : Set X) E
    have hT := bm_stage_test W E T hStage.1
    have hCos : (geoTransformAlong G T).cosupp = univ := by
      rw [template_current, strict_univ]
      exact cosupport_zero (fun _ _ hg => hg)
    exact ⟨hT, hπ.1, hCos.symm ▸ subset_univ C, hStage.2.2⟩

theorem bm_position_of_preimage {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    {A C : Set X} {E : List (Set X)} (f : Y → X) (h : BMPosition A E C)
    (hSing : singularSet (n := n) (f ⁻¹' A) = f ⁻¹' singularSet (n := n) A)
    (hSmooth : IsClosedSubmanifold n A → IsClosedSubmanifold n (f ⁻¹' A))
    (hNC : HasNormalCrossings n (f ⁻¹' C) (E.map (f ⁻¹' ·))) :
    BMPosition (f ⁻¹' A) (E.map (f ⁻¹' ·)) (f ⁻¹' C) := by
  refine ⟨?_, hNC⟩
  rcases h.1 with hS | ⟨hA, hC⟩
  · left
    rw [hSing]
    exact preimage_mono hS
  · right
    refine ⟨hSmooth hA, ?_⟩
    rw [← HironakaEmbeddedBoundary.preimage_biUnion_list]
    exact preimage_mono hC


/-- The full stage predicate uses the same boundary as the original mark-one record. -/
theorem bm_stages_iff_markOne {n : ℕ} {X Y : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) :
    BMStages W E T ↔
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform n P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := n) (strictTransform n P.proj W) x k} ∨
        (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
          C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈
            (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) P).E, H)) ∧
          HasNormalCrossings n C
            (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) P).E) T := by
  induction T with
  | refl => rfl
  | @step A B T C π hπ ih =>
    change (BMStages W E T ∧ _) ↔ (StageCentres _ T ∧ _)
    apply and_congr ih
    dsimp only
    rw [geoTransformAlong_E_eq_of_E_eq (𝔪 := (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
      (𝔍 := geometricTemplate (univ : Set X) E) rfl T]
    unfold BMPosition
    have hS : singularSet (n := n) (strictTransform n T.proj W) =
        {x | x ∈ strictTransform n T.proj W ∧
          ∀ k, ¬ RegularAtDim (n := n) (strictTransform n T.proj W) x k} :=
      Set.ext (fun _ => mem_singularSet_iff)
    rw [hS]

/-- The accumulated boundary of a lifted physical history pulls back
entry by entry along its actual lifted endpoint. -/
theorem lift_bm_boundary_eq {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hStage : BMStages W E T) :
    let G := geometricTemplate (univ : Set X) E
    let eX := (liftDiffeomorph.{u} X).symm
    let G' := geometricTemplate (univ : Set (liftCMfd.{u} X)) (E.map (eX ⁻¹' ·))
    (geoTransformAlong G' (liftTower.{u} T)).E =
      (geoTransformAlong G T).E.map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·) := by
  let G := geometricTemplate (univ : Set X) E
  let eX := (liftDiffeomorph.{u} X).symm
  let G' := geometricTemplate (univ : Set (liftCMfd.{u} X)) (E.map (eX ⁻¹' ·))
  have hG : G.IsWellFormed := ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal,
    hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hT := bm_stage_test W E T hStage
  change (geoTransformAlong G' (liftTower.{u} T)).E =
    (geoTransformAlong G T).E.map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·)
  rw [geoTransformAlong_E_eq_of_E_eq
    (𝔪 := markedPullback (m := n) eX G) (show G'.E = _ from rfl),
    liftTower_geoTransformAlong G hG T hT]
  rfl

/-- Geometry of the literal boundary along the rebased physical history. -/
theorem rebase_bm_boundary_eq {n : ℕ} {X X' Y : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hStage : BMStages W E T) :
    let F := transport e T
    let G := geometricTemplate (univ : Set X) E
    let G' := geometricTemplate (univ : Set X') (E.map (e ⁻¹' ·))
    (geoTransformAlong G' F.tower).E =
      (geoTransformAlong G T).E.map (F.back ⁻¹' ·) := by
  let F := transport e T
  let G := geometricTemplate (univ : Set X) E
  let G' := geometricTemplate (univ : Set X') (E.map (e ⁻¹' ·))
  have hG : G.IsWellFormed := ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal,
    hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hT := bm_stage_test W E T hStage
  change (geoTransformAlong G' F.tower).E = (geoTransformAlong G T).E.map (F.back ⁻¹' ·)
  rw [geoTransformAlong_E_eq_of_E_eq
    (𝔪 := MarkedIdealBiholomorphism.MarkedIdeal.pullback e G) (show G'.E = _ from rfl),
    IsTowerIso.geoTransformAlong_eq e hG.isClosedSubmanifold_N hG.isCoherent
      (transport_isTowerIso e T) hT]
  rfl

/-- Literal rebasing keeps all actual centres over the pulled-back footprint. -/
theorem centresOver_rebase {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T →
      CentresOver (e ⁻¹' F) (transport e T).tower
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    refine ⟨centresOver_rebase e F T h.1, ?_⟩
    intro z hz
    change e ((transport e T).tower.proj z) ∈ F
    rw [proj_transport e T z]
    exact h.2 hz
/-- Every actual BM centre has the same position and full boundary after
lifting the tower to a larger universe. -/
theorem lift_bm_stages {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), BMStages W E T →
      BMStages ((liftDiffeomorph.{u} X).symm ⁻¹' W)
        (E.map ((liftDiffeomorph.{u} X).symm ⁻¹' ·)) (liftTower.{u} T)
  | _, .refl, _ => trivial
  | _, @BlowupTower.step _ _ Y Z T C π _, h => by
    let eX := (liftDiffeomorph.{u} X).symm
    let eY := (liftDiffeomorph.{u} Y).symm
    let E' := E.map (eX ⁻¹' ·)
    let G' := geometricTemplate (univ : Set (liftCMfd.{u} X)) E'
    have hBoundary := lift_bm_boundary_eq.{u} W E hE T h.1
    have hStrict : strictTransform n (liftTower.{u} T).proj (eX ⁻¹' W) =
        eY ⁻¹' strictTransform n T.proj W := by
      rw [liftTower_proj]
      exact conjugate_strictTransform (liftDiffeomorph.{u} _) (liftDiffeomorph.{u} X)
        T.proj T.contMDiff_proj W
    refine ⟨lift_bm_stages W E hE T h.1, ?_⟩
    change BMPosition (strictTransform n (liftTower.{u} T).proj (eX ⁻¹' W))
      (geoTransformAlong G' (liftTower.{u} T)).E (eY ⁻¹' C)
    rw [hStrict, hBoundary]
    apply bm_position_of_preimage eY h.2
    · exact transported_singular_set Homeomorph.ulift.symm _
    · intro hSmooth
      exact transported_closedSubmanifold (Homeomorph.ulift.symm) _ hSmooth
    · exact transported_list_normalCrossings Y Homeomorph.ulift.symm C _ h.2.2

/-- A literal rebasing along a base biholomorphism preserves every BM
centre position and its normal crossings with the same full boundary. -/
theorem rebase_bm_stages {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), BMStages W E T →
      BMStages (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    let F := transport e T
    let G' := geometricTemplate (univ : Set X') (E.map (e ⁻¹' ·))
    have hBoundary := rebase_bm_boundary_eq e W E hE T h.1
    have hProj : F.tower.proj = e.symm ∘ T.proj ∘ F.back := by
      funext z
      have hz := congrArg (fun x => e.symm x) (proj_transport e T z)
      simpa only [Function.comp_apply, e.symm_apply_apply] using hz
    have hStrict : strictTransform n F.tower.proj (e ⁻¹' W) = F.back ⁻¹' strictTransform n T.proj W := by
      rw [hProj]
      exact conjugate_strictTransform F.back.symm e.symm T.proj T.contMDiff_proj W
    refine ⟨rebase_bm_stages e W E hE T h.1, ?_⟩
    change BMPosition (strictTransform n F.tower.proj (e ⁻¹' W))
      (geoTransformAlong G' F.tower).E (F.back ⁻¹' C)
    rw [hStrict, hBoundary]
    apply bm_position_of_preimage F.back h.2
    · ext z
      rw [mem_preimage, mem_singularSet_iff, mem_singularSet_iff]
      exact and_congr_right fun _ => forall_congr' fun k =>
        not_congr (CodimOnePartCanonical.regularAtDim_preimage_iff F.back)
    · exact (isClosedSubmanifold_preimage_iff F.back).mpr
    · exact hasNormalCrossings_preimage (pullsBackCoordinates F.back) h.2.2

end
end Hironaka.HironakaG8UniverseBMTransport
