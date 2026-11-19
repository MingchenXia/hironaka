import Hironaka.Resolution.HironakaG1RatioBlockNativeStates

/-! Actual native ratio-graph records from an intrinsic isomorphism preserving the ordered traces. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1IntrinsicRatioNativeComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec HironakaG11PresLineState
  HironakaReducedComplexAnalyticSpaces HironakaG1SNCReaderNormalization HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaG1RelativeReaderWindow HironakaG1ReaderProductSubmersions
  HironakaG1RatioGraphProductEquations HironakaG1RatioBlockGraphAdapters
  HironakaG1RatioBlockNativeStates AnalyticDimensionBasics HironakaG1RelativeBoundaryProjections

set_option maxHeartbeats 1000000 in
/-- The intrinsic isomorphism and ordered stalk traces produce exact padded
records on a common ratio open. Every inherited slot and each original mark
is retained. The common analytic carrier projects bijectively to the two
actual cut windows. -/
theorem exists_intrinsic_ratio_native_comparison
    {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {C : Set M} {D : Set N}
    (P : MarkedIdeal n M) (Q : MarkedIdeal m N) (H : ℕ → ℕ)
    (hP : NativeHSState P C H) (hPD : IsInvDomain n P)
    (hQ : NativeHSState Q D H) (hQD : IsInvDomain m Q)
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C) (p : C)
    (τ : Fin P.E.length ≃ Fin Q.E.length) (hτ : ∀ i, (τ i).val = i.val)
    (hTrace : ∀ i : Fin P.E.length, Ideal.map (e.hom.stalkMap p).hom
      (actualLabelledBoundaryTraceIdeal D Q.E (τ i) (e.hom.base p)) =
        actualLabelledBoundaryTraceIdeal C P.E i p) :
    ∃ (R : RelativeReaders p.val (e.hom.base p).val P.E Q.E τ)
      (U : Opens M) (V : Opens N) (G : Set (readerUnitWindow R))
      (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
      (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel R.b) ∞ forward U ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel R.a) ∞ backward V ∧
      (∀ x ∈ U, ∀ j, HolomorphicAt n (a j) x ∧ a j x ≠ 0) ∧
      (∀ y ∈ V, ∀ j, HolomorphicAt m (b j) y ∧ b j y ≠ 0) ∧
      BijOn (firstReaderMap R) G (C ∩ (U : Set M)) ∧
      BijOn (secondReaderMap R) G (D ∩ (V : Set N)) ∧
      (∀ z : readerUnitWindow R, z ∈ G ↔ firstReaderMap R z ∈ C ∩ (U : Set M) ∧
        (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (firstReaderMap R z)) ∧
      (∀ z : readerUnitWindow R, z ∈ G ↔ secondReaderMap R z ∈ D ∩ (V : Set N) ∧
        (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
          rightGraphValue R b backward (secondReaderMap R z)) ∧
      let d := (R.r+R.a)+(R.r+R.b)
      let X := CMfd.of (n := d) (Common R U V)
      let L := leftRatioMarked R U V a forward P
      let T := rightRatioMarked R U V b backward Q
      let K := graphEquationWindowToRatio R U V ⁻¹' G
      IsComplexAnalyticSubset (n := d) K ∧
      IsInvDomain d L ∧ IsInvDomain d T ∧
      NativeHSState (X := X) L K H ∧ NativeHSState (X := X) T K H ∧
      L.d = P.d ∧ T.d = Q.d ∧ T.E = L.E ∧
      (0 < m → ∀ x ∈ L.cosupp, ∃ k, k + 2 ≤ d ∧ LocDimLE (n := d) K x k) := by
  obtain ⟨R⟩ := exists_relative_readers C D e p hPD.isWellFormed.isSNCDivisor
    hQD.isWellFormed.isSNCDivisor τ hTrace
  obtain ⟨U,V,G,a,b,forward,backward,hp,hq,_,_,hf,hg,ha,hb,hBijL,hBijR,hL,hR,hK⟩ :=
    exists_actual_paired_ratio_graph_equations e p R he hTrace hP.2.1
  obtain ⟨hLD,hRD,hLS,hRS,hDim⟩ :=
    ratioMarked_nativeStates R U V P Q H hP hPD hQ hQD a b forward backward
      (fun x hx j => (ha x hx j).1) (fun y hy j => (hb y hy j).1) hf hg hL hR
  exact ⟨R,U,V,G,a,b,forward,backward,hp,hq,hf,hg,ha,hb,hBijL,hBijR,hL,hR,hK,
    hLD,hRD,hLS,hRS,rfl,rfl,(ratioMarked_ordered_boundary_eq R U V a b forward backward P Q
      rfl rfl hτ).symm, fun hm => hDim (R.dimension₂ ▸ hm)⟩

end
end Hironaka.HironakaG1IntrinsicRatioNativeComparison
