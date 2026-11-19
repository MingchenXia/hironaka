import Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductEmbedding
import Hironaka.Analytic.Unibranch.HironakaG11VanishingWindows
import Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingIso
import Hironaka.Resolution.HironakaG11PresLineState
import Hironaka.Resolution.HironakaActualOpenEmbeddingCanonicalExtension

/-! The actual independently selected source record on the canonical chart
of the SAME whole product window. No overlap/record-comparison packet is an
input. Blueprint FIRST: original-native-product-independent-record.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductIndependentRecord
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaG11PresLineState HironakaBaseChange
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  InvDomainTowerAlong HironakaActualOpenEmbeddingCanonicalExtension
  SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothProductEmbedding
  HironakaG11VanishingWindows MaxLocusLocal
open scoped ProductComplexManifold

private theorem native_state_open {n : ℕ} {M N : BlowupTowers.CMfd.{0} n}
    (b : N → M) (hb : IsOpenHoloEmbedding n b) {Q : MarkedIdeal n M}
    {C : Set M} {H : ℕ → ℕ} (hState : NativeHSState Q C H) :
    NativeHSState (MarkedIdeal.pullback b Q) (b ⁻¹' C) H := by
  obtain ⟨O,Φ,hΦ⟩ := hb
  have h := NativeHSState.pullback Φ (hState.restrict O)
  have hComp : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : O → M) Q) =
      MarkedIdeal.pullback ((Subtype.val : O → M) ∘ Φ) Q := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
    · exact List.map_map
    · exact (HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp
        contMDiff_subtype_val Φ.contMDiff Q.ideal hState.2.2.2.1).symm
  have hbEq : b = (Subtype.val : O → M) ∘ Φ := funext hΦ
  rw [hComp,← hbEq] at h
  have hCarrier : Φ ⁻¹' ((Subtype.val : O → M) ⁻¹' C) = b ⁻¹' C := by
    rw [hbEq]
    rfl
  exact hCarrier ▸ h

private theorem inclusion_open {n : ℕ} (U V : Opens (ComplexModel n)) (hVU : V ≤ U) :
    IsOpenHoloEmbedding n (Opens.inclusion hVU : V → U) :=
  ⟨nestedOpens U V,(nestedOpensDiffeo (n := n) hVU).symm,fun _ => rfl⟩

variable {X Y : SourceReducedComplexSpace}

/-- OUTPUT of the real independent-embedding comparison. Its current
native/ambient equations are derived from ordinary embeddings and points. -/
structure ProductRecordModel (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (z : (windowSpace e r W).obj.left) (d : DimEmbedding X (e.dim+r)) (c : d.carrier) where
  sourceOpen : Opens (ComplexModel (e.dim+r))
  targetOpen : Opens (ComplexModel (e.dim+r))
  source_subset : sourceOpen ≤ coordinateWindow e r W
  target_subset : targetOpen ≤ d.ambient
  phi : sourceOpen ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+r)),𝓘(ℂ,ComplexModel (e.dim+r))⟯ targetOpen
  point_mem : ((coordinateIso e r W).inv.hom.left.base z).val.val ∈ sourceOpen
  point_eq : (phi ⟨((coordinateIso e r W).inv.hom.left.base z).val.val,point_mem⟩).val = c.val.val
  carrier_eq : ∀ a : sourceOpen,
    Opens.inclusion source_subset a ∈ coordinateCarrier e r W ↔
      Opens.inclusion target_subset (phi a) ∈ d.carrier
  original : ∀ (a : coordinateCarrier e r W) (ha : a.val.val ∈ sourceOpen),
    ∃ q : d.carrier, q.val.val = (phi ⟨a.val.val,ha⟩).val ∧
      d.toLocalEmbedding.toPoint q = (productEmbedding e r W i hi).toPoint a

namespace ProductRecordModel

variable {e : LocalEmbedding Y} {r : ℕ} {W : Opens (productAmbient e r)}
  {i : windowSpace e r W ⟶ X} {hi : LocallyRingedSpace.IsOpenImmersion i.hom.left}
  {z : (windowSpace e r W).obj.left} {d : DimEmbedding X (e.dim+r)} {c : d.carrier}

def sourceCarrier (M : ProductRecordModel e r W i hi z d c) : Set M.sourceOpen :=
  (Opens.inclusion M.source_subset) ⁻¹' coordinateCarrier e r W

def targetCarrier (M : ProductRecordModel e r W i hi z d c) : Set M.targetOpen :=
  (Opens.inclusion M.target_subset) ⁻¹' d.carrier

def nativeIso (M : ProductRecordModel e r W i hi z d c) :
    chartSpace ((productEmbedding e r W i hi).restrict M.sourceOpen M.source_subset) ≅
      chartSpace (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (actualSubspaceBiholomorphicIso M.phi M.sourceCarrier M.targetCarrier M.carrier_eq)
      (actualSubspaceMap_point M.phi.contMDiff (fun a ha => (M.carrier_eq a).mp ha)))

theorem native_square (M : ProductRecordModel e r W i hi z d c) :
    M.nativeIso.hom ≫ chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) =
      chartInclusion ((productEmbedding e r W i hi).restrict M.sourceOpen M.source_subset) := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro a
  let y : coordinateCarrier e r W := ⟨Opens.inclusion M.source_subset a.val,a.property⟩
  obtain ⟨q,hq,hqx⟩ := M.original y a.val.property
  have hqe : q = (⟨Opens.inclusion M.target_subset (M.phi a.val),
      (M.carrier_eq a.val).mp a.property⟩ : d.carrier) :=
    Subtype.ext (Subtype.ext hq)
  change d.toLocalEmbedding.toPoint
    (⟨Opens.inclusion M.target_subset (M.phi a.val),
      (M.carrier_eq a.val).mp a.property⟩ : d.carrier) =
    (productEmbedding e r W i hi).toPoint y
  exact (congrArg d.toLocalEmbedding.toPoint hqe).symm.trans hqx

def record (M : ProductRecordModel e r W i hi z d c)
    (Q : MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) d.ambient)) :
    MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) M.sourceOpen) :=
  MarkedIdeal.pullback M.phi (MarkedIdeal.pullback (Opens.inclusion M.target_subset) Q)

end ProductRecordModel

/-- Ordinary independent embeddings/points and the genuine selected record
derive the whole native overlap and its actual pulled-back native state. -/
theorem exists_independent_product_record (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) (i : windowSpace e r W ⟶ X)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (z : (windowSpace e r W).obj.left)
    (d : DimEmbedding X (e.dim+r)) (c : d.carrier)
    (hc : i.hom.left.base z = d.toLocalEmbedding.toPoint c)
    (Q : MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) d.ambient))
    {H : ℕ → ℕ} (hQ : IsInvDomain (e.dim+r) Q) (hE : Q.E = [])
    (hState : NativeHSState Q d.carrier H) :
    ∃ M : ProductRecordModel e r W i hi z d c,
      IsInvDomain (e.dim+r) (M.record Q) ∧ (M.record Q).E = [] ∧
        NativeHSState (M.record Q) M.sourceCarrier H := by
  let p : LocalEmbedding X :=
    ⟨e.dim+r,coordinateWindow e r W,coordinateCarrier e r W,coordinateCarrier_analytic e r W,
      (productEmbedding e r W i hi).map,(productEmbedding e r W i hi).isOpenImmersion,
      (productEmbedding e r W i hi).overPoint⟩
  let cp := (coordinateIso e r W).inv.hom.left.base z
  have hcp : p.toPoint cp = d.toLocalEmbedding.toPoint c :=
    (productEmbedding_point e r W i hi z).trans hc
  obtain ⟨A,B,hA,hB,Φ,hcpA,hΦ,hCar,hPoint⟩ :=
    HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism p d.toLocalEmbedding rfl cp c hcp
  have hCar' : ∀ a : A, Opens.inclusion hA a ∈ coordinateCarrier e r W ↔
      Opens.inclusion hB (Φ a) ∈ d.carrier := by
    intro a
    exact (HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff p.carrier
      (Opens.inclusion hA a)).symm.trans
      ((hCar a).trans (HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff d.carrier
        (Opens.inclusion hB (Φ a))))
  let M : ProductRecordModel e r W i hi z d c :=
    ⟨A,B,hA,hB,Φ,hcpA,hΦ,hCar',hPoint⟩
  have hQB := isInvDomain_pullback_of_isOpenHoloEmbedding
    (X := BlowupTowers.CMfd.of (n := e.dim+r) d.ambient)
    (Y := BlowupTowers.CMfd.of (n := e.dim+r) B)
    (Opens.inclusion hB) (inclusion_open d.ambient B hB) hQ
  have hStateB := native_state_open
    (M := BlowupTowers.CMfd.of (n := e.dim+r) d.ambient)
    (N := BlowupTowers.CMfd.of (n := e.dim+r) B) (Opens.inclusion hB)
    (inclusion_open d.ambient B hB) hState
  have hD : IsInvDomain (e.dim+r) (M.record Q) := isInvDomain_pullback Φ hQB
  have hEmpty : (M.record Q).E = [] := by
    simp only [ProductRecordModel.record,MarkedIdeal.pullback,hE,List.map_nil]
  have hStateA := NativeHSState.pullback
    (X := BlowupTowers.CMfd.of (n := e.dim+r) B)
    (X' := BlowupTowers.CMfd.of (n := e.dim+r) A) Φ hStateB
  have hCarrier : Φ ⁻¹' ((Opens.inclusion hB) ⁻¹' d.carrier) = M.sourceCarrier :=
    Set.ext (fun a => (hCar' a).symm)
  exact ⟨M,hD,hEmpty,hCarrier ▸ hStateA⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductIndependentRecord
