import Hironaka.Resolution.HironakaG4OpenGammaChart
import Hironaka.Resolution.HironakaG4OpenClosedExtension

/-! The prepared local Gamma chart gives an ambient chart and optional masks. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4AmbientPreparedGammaChart
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates MonomialPartAlong RestrictedIdealExtension
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4PreparedGammaChart
  HironakaG4OpenGammaChart HironakaG4OpenClosedExtension AnalyticSubsetOpens
  DivisorExponentAlong HironakaG34CoordinateScaling

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual local residual factorization produces a Gamma chart on the
ambient manifold, using the closed ambient extension of the auxiliary slice. -/
theorem exists_ambient_prepared_gamma_chart (hn : 0 < n)
    (U : Opens X) (x : U) (N H : Set X) (F : List (Set X)) (Haux : Set U)
    (B L : List (Set U)) (J : GermIdeal n U)
    (hN : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' N))
    (hEF : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hBsub : B.Sublist (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hL : IsSNCDivisor n L) (hHL : (Subtype.val : U → X) ⁻¹' H ∈ L)
    (hxN : x ∈ (Subtype.val : U → X) ⁻¹' N) (hxHaux : x ∈ Haux)
    (hI : (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))).IsCoherent)
    (hnz : ∀ y ∈ (Subtype.val : U → X) ⁻¹' N, IsNonzeroAlongAt ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) y)
    (hfactor : restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H)) =
      restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        ((monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
          (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
            (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mul J))
    (hgamma : ¬ (monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mem x 1)
    (hJZ : ∀ g, J.mem x g ↔
      (vanishingIdeal (n := n) (((Subtype.val : U → X) ⁻¹' N) ∩ Haux)).mem x g) :
    let G : Set X := closure ((Subtype.val : U → X) '' Haux)
    let D := G :: F
    ∃ (S : Finset (Fin n)) (m : Fin D.length → Option (Fin n)) (s t : Fin n) (c : Fin n → ℕ)
      (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (x : X) x)),
      DivisorMasksValid S m ∧ s ∈ S ∧ t ∉ S ∧ t ≠ s ∧ c s = 0 ∧
      Ψ.source ⊆ (chartAt (ComplexModel n) (x : X)).target ∧
      Ψ.toFun (chartAt (ComplexModel n) (x : X) x) = 0 ∧
      flatDomain Ψ ⊆ (U : Set X) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ D.get i ↔
        flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (flatMap Ψ y) = 0 := by
  let G : Set X := closure ((Subtype.val : U → X) '' Haux)
  let D : List (Set X) := G :: F
  let DU : List (Set U) := Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hG : (Subtype.val : U → X) ⁻¹' G = Haux :=
    preimage_closure_image_eq U (hEF.1 Haux (by simp))
  let e : Fin D.length ≃ Fin DU.length := finCongr (by simp [D,DU])
  have hget (i : Fin D.length) : (Subtype.val : U → X) ⁻¹' D.get i = DU.get (e i) := by
    simp only [D, DU, List.get_eq_getElem, e, finCongr_apply]
    cases i using Fin.cases with
    | zero => simpa using hG
    | succ j => simp
  obtain ⟨S,m,s,t,c,Φ,hm,hm0,hs,ht,hst,hcs,hsrc,hzero,hNcoords,hDcoords,hHcoords⟩ :=
    exists_prepared_gamma_chart (X := CMfd.of (n := n) U) hn hN hEF hTF hBsub hL hHL hxN hxHaux hI hnz hfactor hgamma hJZ
  let mA : Fin D.length → Option (Fin n) := m ∘ e
  have hmA : DivisorMasksValid S mA := by
    constructor
    · intro i k hik hk
      exact hm.1 (e i) k hik hk
    · intro i j k hi hj
      exact e.injective (hm.2 (e i) (e j) k hi hj)
  have hD' : ∀ i y, y ∈ flatDomain Φ → (y ∈ (Subtype.val : U → X) ⁻¹' D.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((mA i).map (fun k => {k}))) := by
    intro i y hy
    rw [hget]
    exact hDcoords (e i) y hy
  refine ⟨S,mA,s,t,c,Φ,hmA,hs,ht,hst,hcs,hsrc.trans (chartAt_opens_target_subset x),hzero,?_,?_,?_,?_⟩
  · intro y hy
    exact mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
  · intro y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hNcoords ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
  · intro i y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hD' i ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
  · intro y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hHcoords ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩

end
end Hironaka.HironakaG4AmbientPreparedGammaChart
