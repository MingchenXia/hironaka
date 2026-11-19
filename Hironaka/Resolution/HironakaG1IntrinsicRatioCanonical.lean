import Hironaka.Resolution.HironakaG1IntrinsicRatioNativeComparison
import Hironaka.Resolution.HironakaG1CodimensionTwoChartTransport

/-! Original canonical values on the two actual padded records of a common ratio graph. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1IntrinsicRatioCanonical

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HironakaG11PresLineState HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaG1SNCReaderNormalization HironakaG1RelativeReaderWindow
  HironakaG1RatioGraphProductEquations HironakaG1RatioBlockGraphAdapters
  HironakaG1IntrinsicRatioNativeComparison
  HironakaG1CodimensionTwoChartTransport HironakaG1OriginalUnequalMarkCanonical
  HironakaG1OriginalTwoPairCanonicalCuts HironakaG1NativeChartValueOrder HironakaG8GuardedCanonicality

set_option maxHeartbeats 1800000 in
/-- The intrinsic labelled isomorphism produces the two actual common ratio
records, at their own marks, with equivalent original canonical histories.
Their attainable original value orders agree on the identical endpoint support. -/
theorem exists_intrinsic_ratio_canonical_comparison
    {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {C : Set M} {D : Set N}
    (hm : 0 < m) (P : MarkedIdeal n M) (Q : MarkedIdeal m N) (H : ℕ → ℕ)
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
      BijOn (firstReaderMap R) G (C ∩ (U : Set M)) ∧
      BijOn (secondReaderMap R) G (D ∩ (V : Set N)) ∧
      let d := (R.r+R.a)+(R.r+R.b)
      let X := CMfd.of (n := d) (Common R U V)
      let L := leftRatioMarked R U V a forward P
      let J := rightRatioMarked R U V b backward Q
      let K := graphEquationWindowToRatio R U V ⁻¹' G
      NativeHSState (X := X) L K H ∧ NativeHSState (X := X) J K H ∧
      L.d = P.d ∧ J.d = Q.d ∧ J.E = L.E ∧
      ∀ {Y : CMfd.{0} d} (T : BlowupTower X Y),
        let I := canonicalInvariant d
        (IsCanonical L (I.inv L) T ↔ IsCanonical J (I.inv J) T) ∧
        (IsCanonical L (I.inv L) T →
          (geoTransformAlong L T).cosupp = (geoTransformAlong J T).cosupp ∧
          maxLocus (I.inv L T) (geoTransformAlong L T).cosupp =
            maxLocus (I.inv J T) (geoTransformAlong J T).cosupp ∧
          let S := (geoTransformAlong L T).cosupp
          let f := fun z : S => I.inv L T z.val
          let g := fun z : S => I.inv J T z.val
          ∃ o : range f ≃o range g, ∀ z : S, (o ⟨f z, mem_range_self z⟩ : ValTy d) = g z) := by
  obtain ⟨R,U,V,G,a,b,forward,backward,hp,hq,_,_,_,_,hLeft,hRight,_,_,_,
    hLD,hJD,hLS,hJS,hdL,hdJ,hE,hCodim⟩ :=
    exists_intrinsic_ratio_native_comparison P Q H hP hPD hQ hQD e he p τ hτ hTrace
  let d := (R.r+R.a)+(R.r+R.b)
  let X := CMfd.of (n := d) (Common R U V)
  let L := leftRatioMarked R U V a forward P
  let J := rightRatioMarked R U V b backward Q
  let I := canonicalInvariant d
  obtain ⟨hClass, hDim, hExp⟩ := native_codimension_two_zero_normalized hLS hJS hLD hJD hE (hCodim hm)
  refine ⟨R,U,V,G,a,b,forward,backward,hp,hq,hLeft,hRight,hLS,hJS,hdL,hdJ,hE,?_⟩
  intro Y T
  have hCan := canonicalInvariant_isCanonical_iff_of_local L J hLD hJD hClass hDim hExp T
  refine ⟨hCan, fun hLC => ?_⟩
  have hJC := hCan.mp hLC
  have hT := I.isInvValue.isGeoTestTower_of_isCanonical hLD T hLC
  have hCos := (hClass.wEquiv.2 T).2 hT
  have hCuts : CanonicalTwoPairCuts d I.inv := canonicalTwoPairCuts_canonicalInvariant d
  have hMax := maxLocus_eq_of_guarded_pairCuts (fun {_} _ => True) I.inv hCuts L J hLD hJD
    trivial trivial hClass hDim hExp T hT hLC hJC
  refine ⟨hCos, hMax, ?_⟩
  let S := (geoTransformAlong L T).cosupp
  let f := fun z : S => I.inv L T z.val
  let g := fun z : S => I.inv J T z.val
  have hLt (z w : S) : f z < f w ↔ g z < g w :=
    hCuts L J L J hLD hJD hLD hJD hClass hDim hExp hClass hDim hExp rfl rfl
      trivial trivial trivial trivial T T hLC hJC hLC hJC z.val z.property w.val w.property
  exact ⟨attainedValueOrderIso f g hLt, attainedValueOrderIso_apply f g hLt⟩

#print axioms exists_intrinsic_ratio_canonical_comparison

end Hironaka.HironakaG1IntrinsicRatioCanonical
