import Hironaka.Resolution.HironakaG4NativeProcessedMaskReindex
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4NativeFactorTauDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HomogenizedGlueingTower DivisorExponentAlong MonomialPartAlong GermIdealOrder
  RestrictedIdealExtension RelativePrincipalizationSpan
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskFiniteBlock HironakaActualProcessedMaskControlledSum
  HironakaG4ZeroMaskSameGammaHistory HironakaActualProcessedSharpCleanup
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Native old-row matrix entries and their count coincide with the original
factor matrix through the literal current old-row equivalence. -/
theorem native_factor_tau_dictionary {W : Set X} (E : List (Set X)) (T : BlowupTower X Y) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let L := A.E
    let e := oldEquiv E T
    let a : Y → Fin O.length → Fin L.length → ℕ := fun x i j =>
      divExpAlong n N (oldMonomialPart N O L i) (L.get j) x
    (∀ x i j,a x (e i) j=factorMatrix W E T x i j) ∧
    (∀ x,tauD (a x)=tauD (factorMatrix W E T x)) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let L := A.E
  let e := oldEquiv E T
  let D := oldMonomialPart N O L
  let a : Y → Fin O.length → Fin L.length → ℕ := fun x i j => divExpAlong n N (D i) (L.get j) x
  have hNid : A.N=N := N_geoTransformAlong _ _
  have hD (i : Fin E.length) : D (e i)=oldFactor W E T i := by
    change oldMonomialPart N O L (e i) = _
    rw [show oldFactor W E T i=monomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) L by
        change monomialPartAlong n A.N (restrictOn n A.N
          (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E = _
        rw [hNid]]
    exact monomial_oldEquiv N E L T i
  have hMatrix (x : Y) (i : Fin E.length) (j : Fin L.length) :
      a x (e i) j = factorMatrix W E T x i j := by
    dsimp only [a]
    rw [hD i]
    change divExpAlong n N (oldFactor W E T i) (L.get j) x =
      divExpAlong n A.N (oldFactor W E T i) (A.E.get j) x
    rw [hNid]
  refine ⟨hMatrix,?_⟩
  intro x
  have he := tauD_row_equiv e (a x)
  have hm : (fun i j => a x (e i) j)=factorMatrix W E T x := by
    funext i j
    exact hMatrix x i j
  rw [hm] at he
  exact he.symm
end
end Hironaka.HironakaG4NativeFactorTauDictionary
