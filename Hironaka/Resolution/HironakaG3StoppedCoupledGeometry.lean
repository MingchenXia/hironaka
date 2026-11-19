import Hironaka.Resolution.HironakaG3CoupledNativeGeometry
import Hironaka.Resolution.HironakaG3LocalStoppedCoupledProducer
import Hironaka.Resolution.HironakaG8P1ArcTangentTrace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedCoupledGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance
  HironakaG3RBoundaryEmbedded HironakaG3RStoppedOverlap CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaDisjointFiniteControlledHistory HironakaG3CoupledNativeGeometry
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow GermIdealPullbackCalculus
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaActualNativeInvariantDomain BlowupTowerIsoTail

/-- The actual centre-relative iterated strict transform of a stopped native
history has the smooth, pure-dimensional, normal-crossings geometry of the
conventional strict transform. -/
theorem stopped_strictAlong_geometry {n : ℕ} {X : CMfd.{0} n}
    {V : Set X} (hVa : IsComplexAnalyticSubset (n := n) V) {r : ℕ} (hr : r < n)
    (hpure : V ⊆ closure (regularLocus (n := n) V r))
    {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hAvoid : V ⊆ closure (V \ ⋃ H ∈ E, H)) (U : Opens X)
    {Q : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) U) Q)
    (hS : bdryClass V r E U Q S) :
    let VU := (Subtype.val : U → X) ⁻¹' V
    let MU := MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ,E,vanishingIdeal (n := n) V,1⟩ : MarkedIdeal n X)
    IsClosedSubmanifold n (strictAlong S VU) ∧
      (∀ q ∈ strictAlong S VU, RegularAtDim (n := n) (strictAlong S VU) q r) ∧
      HasNormalCrossings n (strictAlong S VU) (geoTransformAlong MU S).E := by
  have hgeo := bdry_stopped_geometry hVa hr hpure hE hAvoid U S hS
  let VU : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' V
  let OU := nestedOpens U (bdryOpen V r E)
  have hdense : V ⊆ closure (V ∩ bdryOpen V r E) :=
    subset_closure_inter_bdryOpen hVa.isClosed hpure hE.1 hAvoid
  have hdenseU : VU ⊆ closure (VU ∩ (OU : Set (CMfd.of (n := n) U))) := by
    intro x hx
    have h := (Set.ext_iff.mp (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (V ∩ (bdryOpen V r E : Set X))) x).mp (hdense hx)
    exact h
  have havoidU : CentresAvoid OU S := hS.2.1
  have heq := HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
    VU (hVa.isClosed.preimage continuous_subtype_val) OU hdenseU S havoidU
  dsimp only
  rw [heq]
  exact ⟨hgeo.2.2.2.2.2.2.1,hgeo.2.2.2.2.2.2.2.1,hgeo.2.2.2.2.2.2.2.2⟩

/-- An actual coupled ambient history whose native tower is physically
isomorphic to a stopped boundary history carries its stopped strict-transform
geometry into the ambient endpoint. -/
theorem coupled_geometry_of_stopped_iso {d t : ℕ} (hn : 0 < d+t)
    {X : CMfd.{0} d} {P : CMfd.{0} d} {Q R : CMfd.{0} d}
    {Z Y : CMfd.{0} (d+t)} {V : Set X}
    (hVa : IsComplexAnalyticSubset (n := d) V) {r : ℕ} (hr : r < d)
    (hpure : V ⊆ closure (regularLocus (n := d) V r))
    {E : List (Set X)} (hE : IsSNCDivisor d E)
    (hAvoid : V ⊆ closure (V \ ⋃ H ∈ E, H)) (U : Opens X)
    (S : BlowupTower (CMfd.of (n := d) U) Q) (hS : bdryClass V r E U Q S)
    (e : P ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ CMfd.of (n := d) U)
    (T : BlowupTower P R) (β : R ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q)
    (hi : IsTowerIso e T S β)
    {N : Set Z} {B : List (Set Z)} {J : GermIdeal (d+t) Z} {ι : P → Z}
    (A : BlowupTower Z Y) (η : R → Y)
    (h : CoupledHistory N B J ι
      (MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : U → X)
        (⟨univ,E,vanishingIdeal (n := d) V,1⟩ : MarkedIdeal d X))) T A η) :
    let VU := (Subtype.val : U → X) ⁻¹' V
    IsClosedSubmanifold (d+t) (strictAlong A (ι '' (e ⁻¹' VU))) ∧
      (∀ y ∈ strictAlong A (ι '' (e ⁻¹' VU)),
        RegularAtDim (n := d+t) (strictAlong A (ι '' (e ⁻¹' VU))) y r) ∧
      HasNormalCrossings (d+t) (strictAlong A (ι '' (e ⁻¹' VU)))
        (geoTransformAlong (fullMarked B J) A).E := by
  let MU := MarkedIdeal.pullback (Subtype.val : U → X)
        (⟨univ,E,vanishingIdeal (n := d) V,1⟩ : MarkedIdeal d X)
  let VU := (Subtype.val : U → X) ⁻¹' V
  have hg := stopped_strictAlong_geometry hVa hr hpure hE hAvoid U S hS
  have hdom := InvDomainTowerAlong.isInvDomain_pullback_val U (isInvDomain_bdry hVa hr hpure hE)
  have htest := (canonicalInvariant d).isInvValue.isGeoTestTower_of_isCanonical hdom S hS.1
  have htrans := hi.geoTransformAlong_eq e hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent htest
  have hs : strictAlong T (e ⁻¹' VU) = β ⁻¹' strictAlong S VU := hi.strictAlong_eq VU
  have hsmooth : IsClosedSubmanifold d (strictAlong T (e ⁻¹' VU)) := by
    rw [hs]
    exact (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff β).mpr hg.1
  have hdim : ∀ q ∈ strictAlong T (e ⁻¹' VU),
      RegularAtDim (n := d) (strictAlong T (e ⁻¹' VU)) q r := by
    intro q hq
    rw [hs] at hq ⊢
    exact RegularAtDimTransport.regularAtDim_of_preimage β.contMDiff
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse β.contMDiff β.symm.contMDiff
        β.apply_symm_apply β.symm_apply_apply q) isOpen_univ (mem_univ _) (fun _ _ => Iff.rfl) (hg.2.1 (β q) hq)
  have hnc : HasNormalCrossings d (strictAlong T (e ⁻¹' VU))
      (geoTransformAlong (MarkedIdeal.pullback e MU) T).E := by
    rw [hs,htrans]
    exact hasNormalCrossings_preimage (MarkedIdealTowerTransport.pullsBackCoordinates β) hg.2.2
  have hgeom := coupled_strictAlong_geometry hn h (e ⁻¹' VU) hsmooth hnc
  have hdim' := coupled_strictAlong_regularAtDim h (e ⁻¹' VU) r hdim
  exact ⟨hgeom.1,hdim',hgeom.2⟩

/-- The stopped native roundtrip retained by the actual coupled-cover
producer gives the ambient iterated strict-transform geometry on its chart. -/
theorem actual_stopped_coupled_geometry
    {d t : ℕ} (_hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hVa : IsComplexAnalyticSubset (n := d) V)
      (_hTrace : GermIdeal.pullback (m := d) (Subtype.val : N → X) J = vanishingIdeal (n := d) V)
      {r : ℕ} (_hr : r < d) (_hpure : V ⊆ closure (regularLocus (n := d) V r))
      (_hAvoid : V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H))
      (U : Opens X),
      letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      ∀ {R : CMfd.{0} d} (T : BlowupTower
        (nativeManifold (Nat.le_add_right d t) (openSection N U) (openSection_regular hN U)) R)
        {Y : CMfd.{0} (d+t)} (A : BlowupTower (CMfd.of (n := d+t) U) Y) (η : R → Y),
        let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
        let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
        let M_U := fullMarked (B_U.map ((Subtype.val : openSection N U → U) ⁻¹' ·))
          (GermIdeal.pullback (m := d) (Subtype.val : openSection N U → U) J_U)
        CoupledHistory (openSection N U) B_U J_U (Subtype.val : openSection N U → U) M_U T A η →
        stoppedClass (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
          MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN))
          (bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·)))
          (nativeWindow (Nat.le_add_right d t) N hN U) _
          (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U).symm T).tower →
        let W_U := (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V)
        IsClosedSubmanifold (d+t) (strictAlong A W_U) ∧
          (∀ y ∈ strictAlong A W_U, RegularAtDim (n := d+t) (strictAlong A W_U) y r) ∧
          HasNormalCrossings (d+t) (strictAlong A W_U) (geoTransformAlong (fullMarked B_U J_U) A).E := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hVa hTrace r hr hpure hAvoid U
  let N_U := openSection N U
  let hNU := openSection_regular hN U
  let := chartedSpace (Nat.le_add_right d t) hNU
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hNU
  intro R T Y A η
  dsimp only
  intro hC hStop
  let E := B.map ((Subtype.val : N → X) ⁻¹' ·)
  let A0 := nativeWindow (Nat.le_add_right d t) N hN U
  let e := windowEquiv (Nat.le_add_right d t) N hN hNc U
  let K : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN) :=
    ⟨univ,E,vanishingIdeal (n := d) V,1⟩
  let K_A := MarkedIdeal.pullback (Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) K
  let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
  let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
  let M_U := fullMarked (B_U.map ((Subtype.val : N_U → U) ⁻¹' ·))
    (GermIdeal.pullback (m := d) (Subtype.val : N_U → U) J_U)
  have hE : IsSNCDivisor d E := isSNCDivisor_native_preimage (by omega) (Nat.le_add_right d t) hN hB hTrans
  have hdom := isInvDomain_bdry hVa hr hpure hE
  have hHol : ∀ x g, J.mem x g → HolomorphicAt (d+t) g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have hHolV : ∀ x g, (vanishingIdeal (n := d) V).mem x g → HolomorphicAt d g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hMarked : MarkedIdeal.pullback e K_A = M_U := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · simp [MarkedIdeal.pullback,K_A,K,M_U,fullMarked]
    · simp only [MarkedIdeal.pullback,K_A,K,M_U,fullMarked,B_U,E,List.map_map,Function.comp_def]
      rfl
    · change GermIdeal.pullback (m := d) e
          (GermIdeal.pullback (m := d) (Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN)
            (vanishingIdeal (n := d) V)) =
        GermIdeal.pullback (m := d) (Subtype.val : N_U → U)
          (GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J)
      calc
        _ = GermIdeal.pullback (m := d)
            ((Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) ∘ e) (vanishingIdeal (n := d) V) :=
          (whole_pullback_comp contMDiff_subtype_val e.contMDiff (vanishingIdeal (n := d) V) hHolV).symm
        _ = GermIdeal.pullback (m := d)
            ((Subtype.val : N → X) ∘ ((Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) ∘ e)) J := by
          rw [← hTrace]
          exact (whole_pullback_comp (contMDiff_val (Nat.le_add_right d t) hN)
            (contMDiff_subtype_val.comp e.contMDiff) J hHol).symm
        _ = GermIdeal.pullback (m := d) ((Subtype.val : U → X) ∘ (Subtype.val : N_U → U)) J := by
          congr 1
        _ = _ := whole_pullback_comp contMDiff_subtype_val (contMDiff_val (Nat.le_add_right d t) hNU) J hHol
    · rfl
  have hC' : CoupledHistory N_U B_U J_U (Subtype.val : N_U → U) (MarkedIdeal.pullback e K_A) T A η := by
    rw [hMarked]
    exact hC
  let S := (transport e.symm T).tower
  have hi := (transport_isTowerIso e.symm T).symm
  have hg := coupled_geometry_of_stopped_iso (by omega : 0 < d+t) hVa hr hpure hE hAvoid A0 S hStop e T _ hi A η hC'
  have hImage : (Subtype.val : N_U → U) '' (e ⁻¹' ((Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) ⁻¹' V)) =
      (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V) := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨(e p).val,hp,rfl⟩
    · rintro ⟨p,hp,hpx⟩
      have hpU : p.val ∈ U := hpx ▸ x.property
      refine ⟨⟨⟨p.val,hpU⟩,p.property⟩,?_,?_⟩
      · exact hp
      · exact Subtype.ext hpx
  dsimp only at hg
  rw [hImage] at hg
  exact hg

end
end Hironaka.HironakaG3StoppedCoupledGeometry
