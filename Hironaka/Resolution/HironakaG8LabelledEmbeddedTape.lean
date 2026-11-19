import Hironaka.Resolution.HironakaG8LabelledNativeResolution
import Hironaka.Resolution.HironakaG8LabelledNativeOverlap
import Hironaka.Resolution.HironakaG8LocalMixedEmbeddedResolution

/-! Retain the actual singular prefix and the smooth suffix on one
complete embedded tower over a prescribed compact-enclosed open. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LabelledEmbeddedTape

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaEmbeddedBoundary NormalCrossings NormalCrossingsInvariance
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaActualOpenEmbeddingVanishingIdeal HironakaActualSmoothBoundaryCleanup HomogenizedGlueingTower
  HironakaG8LabelledNativeHistory HironakaG8LabelledNativeResolution HironakaG8LocalMixedPhaseAssembly
  HironakaG8LocalMixedEmbeddedResolution HironakaG8UniverseDenseBoundary HironakaG8LocalPureEmbeddedResolution
  HironakaG8DenseBoundaryRestriction HironakaG8LocalPureFinish HironakaG8LabelledNativeOverlap
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFilteredBoundary HironakaG8FilteredBoundaryTerminalOverlap
  HironakaG3BiholomorphicFirstMeeting HironakaOriginalTerminalOverlapComparison MaxLocusLocal StepOneTangentChange

variable {n : ℕ} {X X' Y : CMfd.{0} n} {C : SmoothTailCertificate n}
variable {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y}

local notation "ref" B => Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞
private abbrev record {A : CMfd.{0} n} (W : Set A) (E : List (Set A)) : MarkedIdeal n A :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩
local notation "M[" W ";" E "]" => record W E

/-- One complete embedded tower with its retained ordered singular and
smooth phases, up to an actual isomorphism of the same tower. -/
structure LabelledEmbeddedHistory (C : SmoothTailCertificate n) (W : Set X) (E : List (Set X))
    (K : Set X) (T : BlowupTower X Y) : Prop where
  geometry : DenseBoundaryResolution W E T
  phases : ∃ (A Z : CMfd.{0} n) (P : BlowupTower X A) (Q : BlowupTower A Z)
    (χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z) (L : List (ℕ → ℕ)),
    LabelledNativeTower n W E K P L ∧
      C.holds (strictTransform n P.proj W) (geoTransformAlong M[W;E] P).E Q ∧
      IsTowerIso (ref X) T (P.append Q) χ

/-- Restrict both actual parts of a complete labelled embedded history to
the literal open, including the full accumulated boundary of the suffix. -/
theorem LabelledEmbeddedHistory.restrictOpen (h : LabelledEmbeddedHistory C W E K T)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) (O : Opens X) :
    LabelledEmbeddedHistory C ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·))
      ((Subtype.val : O → X) ⁻¹' K) (restrict O T) := by
  obtain ⟨A,Z,P,Q,χ,L,hP,hQ,hFactor⟩ := h.phases
  let U := openPreimage P O
  let P₀ := restrict O P
  let Q₀ := restrict U Q
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  have hCarrier : strictTransform n P₀.proj W₀ = (Subtype.val : U → A) ⁻¹' strictTransform n P.proj W :=
    strictTransform_restricted_tower O P W
  have hList : (geoTransformAlong M[W₀;E₀] P₀).E =
      (geoTransformAlong M[W;E] P).E.map ((Subtype.val : U → A) ⁻¹' ·) := by
    have hMark : MarkedIdeal.pullback (Subtype.val : O → X) M[W;E] = record (A := CMfd.of (n := n) O) W₀ E₀ :=
      pullback_val_mk_vanishingIdeal O E W
    have hTest : IsGeoTestTower M[W;E] P := hP.test_and_singular.1
    have hGeo := MarkedIdealRestrictOpen.geoTransformAlong_restrict O isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) P hTest
    rw [hMark] at hGeo
    exact congrArg MarkedIdeal.E hGeo
  have hQ₀ : C.holds (strictTransform n P₀.proj W₀) (geoTransformAlong M[W₀;E₀] P₀).E Q₀ := by
    rw [hCarrier,hList]
    exact C.restrictOpen hQ U
  have hBase : ∀ x : X, x ∈ O ↔ (ref X) x ∈ O := fun _ => Iff.rfl
  have hIso := isTowerIso_restrictOpens hBase hFactor (isTowerIso_mem_openPreimage_iff hFactor hBase)
  have hIso' := BlowupTowerSplitIso.IsTowerIso.congr_base hIso
    (Φ' := ref (CMfd.of (n := n) O)) (fun z => Subtype.ext rfl)
  let η := (diffeoOpens χ (openPreimage T O) (openPreimage (P.append Q) O)
    (isTowerIso_mem_openPreimage_iff hFactor hBase)).trans (opensCongr (openPreimage_append P Q O).symm)
  have hFull := hIso'.trans (isTowerIso_restrict_append O P Q)
  refine ⟨dense_boundary_resolution_restrict hW E hE hDense T h.geometry O,
    ⟨CMfd.of (n := n) U,CMfd.of (n := n) (openPreimage Q U),P₀,Q₀,η,L,
      hP.restrictOpen O,hQ₀,?_⟩⟩
  simpa only [Diffeomorph.refl_trans] using hFull

/-- A physical change of base retains the literal two-part factorization
and all geometry of the same complete embedded history. -/
theorem LabelledEmbeddedHistory.rebase (h : LabelledEmbeddedHistory C W E K T)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    LabelledEmbeddedHistory C (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (φ ⁻¹' K) (transport φ T).tower := by
  obtain ⟨A,Z,P,Q,χ,L,hP,hQ,hFactor⟩ := h.phases
  let tr := transport φ T
  let p := transport φ P
  let q := transport p.back Q
  let W₀ := φ ⁻¹' W
  let E₀ := E.map (φ ⁻¹' ·)
  have hPiso := transport_isTowerIso φ P
  have hQiso := transport_isTowerIso p.back Q
  have hCarrier := strictTransform_preimage_of_square φ p.back p.tower.contMDiff_proj P.contMDiff_proj
    W hW.isClosed (fun z => (hPiso.proj_comm z).symm)
  have hList : (geoTransformAlong M[W₀;E₀] p.tower).E =
      (geoTransformAlong M[W;E] P).E.map (p.back ⁻¹' ·) := by
    have hMark : MarkedIdeal.pullback φ M[W;E] = M[W₀;E₀] := by
      change (MarkedIdeal.mk (φ ⁻¹' univ) E₀
        (GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) W)) 1 : MarkedIdeal n X') = _
      rw [preimage_univ,pullback_vanishingIdeal_of_biholomorphism]
    have hTest : IsGeoTestTower M[W;E] P := hP.test_and_singular.1
    have hGeo := IsTowerIso.geoTransformAlong_eq φ isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) hPiso hTest
    rw [hMark] at hGeo
    exact congrArg MarkedIdeal.E hGeo
  have hQ₀ : C.holds (strictTransform n p.tower.proj W₀) (geoTransformAlong M[W₀;E₀] p.tower).E q.tower := by
    rw [hCarrier,hList]
    exact C.ofTowerIso hQiso hQ
  have hFull := ((transport_isTowerIso φ T).trans hFactor).trans (hPiso.append hQiso).symm
  refine ⟨dense_boundary_resolution_rebase φ hW E hE hDense T h.geometry,
    ⟨p.target,q.target,p.tower,q.tower,(tr.back.trans χ).trans q.back.symm,L,
      hP.of_isTowerIso hPiso,hQ₀,?_⟩⟩
  exact BlowupTowerSplitIso.IsTowerIso.congr_base hFull (Φ' := ref X') (fun z => by
    change z = φ.symm (φ z)
    exact (φ.symm_apply_apply z).symm)

private theorem compact_in_open {K : Set X} (hK : IsCompact K) {U : Opens X} (hKU : K ⊆ U) :
    IsCompact ((Subtype.val : U → X) ⁻¹' K) := by
  rw [Subtype.isCompact_iff,image_preimage_eq_inter_range,Subtype.range_coe,inter_eq_left.mpr hKU]
  exact hK

/-- Every prescribed open enclosed by a compact subset carries the same
finite complete tower and its actual two-part comparison data. -/
theorem exists_labelled_embedded_history_on_compact_enclosed_open {m : ℕ} {X : CMfd.{0} (m + 1)}
    (C : SmoothTailCertificate (m + 1)) (hProduce : ProducesLocalSmoothCertificates C)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) U) Y),
      LabelledEmbeddedHistory C ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) univ T := by
  let n := m + 1
  obtain ⟨V,hKV,Y,P,L,hP,_⟩ := exists_labelled_native_resolution_near_compact (Nat.succ_pos m)
    hW E hE hDense K hK
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let KV := (Subtype.val : V → X) ⁻¹' K
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
  have hDenseV := dense_complement_restrict W E hDense V
  have hTest : IsGeoTestTower (actualSmoothBoundaryMarked (X := CMfd.of (n := n) V) WV EV) P :=
    hP.test_and_singular.1
  obtain ⟨O,hKO,Z,Q,hQ,hEnd⟩ := exists_local_mixed_finish_with_certificate (X := CMfd.of (n := n) V)
    C hProduce hWV EV hEV hDenseV P hTest hP.test_and_singular.2 hP.target_smooth KV (compact_in_open hK hKV)
  let P₀ := restrict O P
  let J := P₀.append Q
  let WO := (Subtype.val : O → V) ⁻¹' WV
  let EO := EV.map ((Subtype.val : O → V) ⁻¹' ·)
  let KO := (Subtype.val : O → V) ⁻¹' KV
  have hTape : LabelledEmbeddedHistory C WO EO KO J :=
    ⟨hEnd,⟨_,_,P₀,Q,_,L,hP.restrictOpen O,hQ,IsTowerIso.refl_self _⟩⟩
  let U₁ := nestedOpens V U
  have hUV : U ≤ V := hUK.trans hKV
  have hUO : U₁ ≤ O := fun _ hx => hKO (hUK hx)
  let U₂ := nestedOpens O U₁
  let e₁ := (nestedOpensDiffeo (n := n) hUV).symm
  let e₂ := (nestedOpensDiffeo (n := n) hUO).symm
  let e := e₁.trans e₂
  let J₀ := restrict U₂ J
  let tr := transport e J₀
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWV O
  have hEO := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hEV
  have hDenseO := dense_complement_restrict WV EV hDenseV O
  have hWO₂ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWO U₂
  have hEO₂ := isSNCDivisor_map_preimage (pullsBackCoordinates_val U₂) continuous_subtype_val hEO
  have hDenseO₂ := dense_complement_restrict WO EO hDenseO U₂
  have hRestricted := (hTape.restrictOpen hWO hEO hDenseO U₂).rebase hWO₂ hEO₂ hDenseO₂ e
  have hCarrier : e ⁻¹' ((Subtype.val : U₂ → O) ⁻¹' WO) = (Subtype.val : U → X) ⁻¹' W := rfl
  have hList : (EO.map ((Subtype.val : U₂ → O) ⁻¹' ·)).map (e ⁻¹' ·) =
      E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    dsimp only [EO,EV]
    rw [List.map_map,List.map_map,List.map_map]
    rfl
  have hTask : e ⁻¹' ((Subtype.val : U₂ → O) ⁻¹' KO) = univ := by
    apply eq_univ_of_forall
    intro x
    exact hUK x.property
  rw [hCarrier,hList,hTask] at hRestricted
  exact ⟨tr.target,tr.tower,hRestricted⟩

end
end Hironaka.HironakaG8LabelledEmbeddedTape
