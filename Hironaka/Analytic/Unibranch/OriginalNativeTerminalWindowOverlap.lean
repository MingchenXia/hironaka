import Hironaka.Analytic.Unibranch.HironakaG1DistinctNativeTerminalComparison
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaOriginalTerminalOpenComparison
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-! Genuine cross-family terminal current-window comparisons from ordinary
initial overlap geometry and the SAME actual histories. Blueprint FIRST:
original-native-terminal-window-overlap.tex. No common clock or endpoint
square-to-physical-isomorphism inference. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeTerminalWindowOverlap
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualPowerBoundaryExponents HomogenizedGlueingTower HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaG1DistinctNativeTerminalNormalization
  HironakaOriginalTerminalOpenComparison CanonicalCentres
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

section WindowOpen
variable {X : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
  {w : ι → DimEmbedding X n} {T : Towers w} (xs : XStage w T) (i : ι) (U : Opens (w i).ambient)

private def openCarrier : Set (openPreimage (T i).2 U) :=
  (Subtype.val : openPreimage (T i).2 U → (T i).1) ⁻¹' xs.carrier i

private theorem openCarrier_analytic : IsComplexAnalyticSubset (n := n) (openCarrier xs i U) :=
  AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (xs.analytic i) (openPreimage (T i).2 U)

def windowOpenSpace : SourceReducedComplexSpace := ofClosedAnalytic (openCarrier xs i U) (openCarrier_analytic xs i U)

def windowOpenMap : windowOpenSpace xs i U ⟶ xs.Y :=
  (ObjectProperty.homMk (Over.homMk
    (actualOpenSubspaceMap (n := n) (xs.carrier i) (openPreimage (T i).2 U))
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx))) :
      windowOpenSpace xs i U ⟶ ofClosedAnalytic (xs.carrier i) (xs.analytic i)) ≫ xs.map i

theorem windowOpenMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (windowOpenMap xs i U).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    (actualOpenSubspaceMap (n := n) (xs.carrier i) (openPreimage (T i).2 U) ≫ (xs.map i).hom.left)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
    (actualOpenSubspaceMap_isOpenImmersion (xs.carrier i) (openPreimage (T i).2 U))
    _ (xs.isOpenImmersion i)

theorem windowOpenMap_point (c : (windowOpenSpace xs i U).obj.left) :
    (windowOpenMap xs i U).hom.left.base c = (xs.map i).hom.left.base ⟨c.val.val,c.property⟩ := rfl

theorem windowOpen_carrier : openCarrier xs i U =
    strictAlong (restrict U (T i).2) ((Subtype.val : U → (w i).ambient) ⁻¹' (w i).carrier) := by
  rw [HironakaG11StrictTransformTowers.strictAlong_restrict,← xs.carrier_eq i]
  rfl

end WindowOpen

section Independent
variable {X : SourceReducedComplexSpace} {n : ℕ} {ι κ : Type}
  (wT : ι → DimEmbedding X n) (wS : κ → DimEmbedding X n)
  (rawT : ∀i,MarkedIdeal n (Amb wT i)) (rawS : ∀j,MarkedIdeal n (Amb wS j))
  (H : ℕ → ℕ) (hrecT : ∀i,IsNativeWindowRecord (wT i) (rawT i) H)
  (hrecS : ∀j,IsNativeWindowRecord (wS j) (rawS j) H)
  (eT : ι → ℕ) (eS : κ → ℕ) (heT : ∀i,1≤eT i) (heS : ∀j,1≤eS j)
  (TT : Towers wT) (TS : Towers wS) (xt : XStage wT TT) (xs : XStage wS TS)
  (hcT : ∀i,IsCanonical (powerMarked (rawT i) (eT i))
    ((canonicalInvariant n).inv (powerMarked (rawT i) (eT i))) (TT i).2)
  (hcS : ∀j,IsCanonical (powerMarked (rawS j) (eS j))
    ((canonicalInvariant n).inv (powerMarked (rawS j) (eS j))) (TS j).2)
  (hrT : ∀i,IsGeoResolution (powerMarked (rawT i) (eT i)) (TT i).2)
  (hrS : ∀j,IsGeoResolution (powerMarked (rawS j) (eS j)) (TS j).2)

private def sumWindow : ι ⊕ κ → DimEmbedding X n := Sum.elim wT wS
private def sumRaw : ∀a,MarkedIdeal n (Amb (sumWindow wT wS) a)
  | .inl i => rawT i
  | .inr j => rawS j
include hrecT hrecS in
private theorem sum_native : ∀a,IsNativeWindowRecord (sumWindow wT wS a) (sumRaw wT wS rawT rawS a) H
  | .inl i => hrecT i
  | .inr j => hrecS j

include hrecT heT hcT hrT in
private theorem targetData (i : ι) (U : Opens (wT i).ambient) :
    IsInvDomain n (windowPower wT rawT i U (eT i)) ∧
    IsCanonical (windowPower wT rawT i U (eT i))
      ((canonicalInvariant n).inv (windowPower wT rawT i U (eT i)))
      (BlowupTowerTransforms.restrict U (TT i).2) ∧
    IsGeoResolution (windowPower wT rawT i U (eT i)) (BlowupTowerTransforms.restrict U (TT i).2) :=
  original_terminal_open_history_data (powerMarked (rawT i) (eT i))
    (powerMarked_isInvDomain (rawT i) (hrecT i).1 (heT i)) (TT i).2 (hcT i) (hrT i) U
include hrecS heS hcS hrS in
private theorem sourceData (j : κ) (U' : Opens (wS j).ambient) :
    IsInvDomain n (windowPower wS rawS j U' (eS j)) ∧
    IsCanonical (windowPower wS rawS j U' (eS j))
      ((canonicalInvariant n).inv (windowPower wS rawS j U' (eS j)))
      (BlowupTowerTransforms.restrict U' (TS j).2) ∧
    IsGeoResolution (windowPower wS rawS j U' (eS j)) (BlowupTowerTransforms.restrict U' (TS j).2) :=
  original_terminal_open_history_data (powerMarked (rawS j) (eS j))
    (powerMarked_isInvDomain (rawS j) (hrecS j).1 (heS j)) (TS j).2 (hcS j) (hrS j) U'

variable (i : ι) (j : κ) (U : Opens (wT i).ambient) (U' : Opens (wS j).ambient)
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
  (hadm : mapAdm (sumWindow wT wS) (.inl i) (.inr j) U U' Φ)

private def localEta :
    CMfd.of (n := n) (openPreimage (TS j).2 U') ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (TT i).2 U) :=
  HironakaG1DistinctNativeTerminalComparison.ambientComparison (sumWindow wT wS)
    (sumRaw wT wS rawT rawS) H (sum_native wT wS rawT rawS H hrecT hrecS)
    (.inl i) (.inr j) U U' Φ hadm (eT i) (eS j) (heT i) (heS j)
    (BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2)
    (BlowupTowerTransforms.restrict (X := Amb wT i) U (TT i).2)
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.1
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.1
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.2
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.2

local notation "η" => localEta wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS hcT hcS hrT hrS i j U U' Φ hadm

private theorem localEta_proj (y : openPreimage (TS j).2 U') :
    (BlowupTowerTransforms.restrict (X := Amb wT i) U (TT i).2).proj (η y)=
      Φ ((BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2).proj y) := by
  let h := common_record_terminal_inputs (sumWindow wT wS) (sumRaw wT wS rawT rawS) H
    (sum_native wT wS rawT rawS H hrecT hrecS) (.inl i) (.inr j) U U' Φ hadm
    (eT i) (eS j) (heT i) (heS j)
    (BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2)
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.1
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.2
  exact OriginalNativeTerminalPhaseComparison.ambientComparison_proj
    (windowPower (sumWindow wT wS) (sumRaw wT wS rawT rawS) (.inl i) U (eT i)) h.1 Φ
    (BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2)
    (BlowupTowerTransforms.restrict (X := Amb wT i) U (TT i).2) h.2.1
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.1 h.2.2
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.2 y

private theorem localCarrier : openCarrier xs j U' = η ⁻¹' openCarrier xt i U := by
  rw [windowOpen_carrier xs j U',windowOpen_carrier xt i U]
  exact HironakaG1DistinctNativeTerminalComparison.whole_iterated_carrier
    (sumWindow wT wS) (sumRaw wT wS rawT rawS) H (sum_native wT wS rawT rawS H hrecT hrecS)
    (.inl i) (.inr j) U U' Φ hadm (eT i) (eS j) (heT i) (heS j)
    (BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2)
    (BlowupTowerTransforms.restrict (X := Amb wT i) U (TT i).2)
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.1
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.1
    (sourceData wS rawS H hrecS eS heS TS hcS hrS j U').2.2
    (targetData wT rawT H hrecT eT heT TT hcT hrT i U).2.2

/-- The actual native inverse-open comparison; the ambient comparison and
ENTIRE carrier identity are internally derived from the two OWN histories. -/
def localComparison : windowOpenSpace xs j U' ≅ windowOpenSpace xt i U :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (actualSubspaceBiholomorphicIso η (openCarrier xs j U') (openCarrier xt i U)
      (fun y => Set.ext_iff.mp (localCarrier wT wS rawT rawS H hrecT hrecS eT eS heT heS
        TT TS xt xs hcT hcS hrT hrS i j U U' Φ hadm) y))
      (actualSubspaceMap_point (η).contMDiff (fun y hy =>
        (Set.ext_iff.mp (localCarrier wT wS rawT rawS H hrecT hrecS eT eS heT heS
          TT TS xt xs hcT hcS hrT hrS i j U U' Φ hadm) y).mp hy)))

local notation "E" => localComparison wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS xt xs hcT hcS hrT hrS i j U U' Φ hadm

theorem localComparison_projection :
    (E).hom ≫ windowOpenMap xt i U ≫ xt.q = windowOpenMap xs j U' ≫ xs.q := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro c
  have hcS' : (TS j).2.proj c.val.val ∈ (wS j).carrier := xs.proj_mem j ⟨c.val.val,c.property⟩
  have hcT' : (TT i).2.proj (η c.val).val ∈ (wT i).carrier :=
    xt.proj_mem i ⟨(η c.val).val,
      (Set.ext_iff.mp (localCarrier wT wS rawT rawS H hrecT hrecS eT eS heT heS
        TT TS xt xs hcT hcS hrT hrS i j U U' Φ hadm) c.val).mp c.property⟩
  change (xt.q).hom.left.base ((xt.map i).hom.left.base
    ⟨(η c.val).val,_⟩) = (xs.q).hom.left.base ((xs.map j).hom.left.base ⟨c.val.val,_⟩)
  rw [xt.square i _ hcT',xs.square j _ hcS']
  have hp := localEta_proj wT wS rawT rawS H hrecT hrecS eT eS heT heS TT TS hcT hcS hrT hrS i j U U' Φ hadm c.val
  have hpval := congrArg (fun a : U => (a : (wT i).ambient)) hp
  rw [proj_restrict] at hpval
  have hsc : ((BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2).proj c.val : (wS j).ambient) ∈
      (wS j).carrier := by rw [proj_restrict]; exact hcS'
  have htc : (Φ ((BlowupTowerTransforms.restrict (X := Amb wS j) U' (TS j).2).proj c.val) : (wT i).ambient) ∈
      (wT i).carrier := hpval ▸ hcT'
  have hAdm : (wT i).toLocalEmbedding.toPoint ⟨_,htc⟩ =
      (wS j).toLocalEmbedding.toPoint ⟨_,hsc⟩ := hadm.2 _ hsc htc
  exact (congrArg (wT i).toLocalEmbedding.toPoint (Subtype.ext hpval)).trans
    (hAdm.trans (congrArg (wS j).toLocalEmbedding.toPoint (Subtype.ext (proj_restrict U' (TS j).2 c.val))))

omit U U' Φ hadm in
include hrecT hrecS heT heS hcT hcS hrT hrS in
/-- Every SAME actual current source point and initial target-window lift
has a computed local native endpoint comparison. -/
theorem exists_local_comparison_at (c : xs.carrier j) (t : (wT i).carrier)
    (ht : (wT i).toLocalEmbedding.toPoint t =
      xs.q.hom.left.base ((xs.map j).hom.left.base c)) :
    ∃ (N : SourceReducedComplexSpace) (a : N ⟶ xs.Y) (b : N ⟶ xt.Y),
      LocallyRingedSpace.IsOpenImmersion a.hom.left ∧
      LocallyRingedSpace.IsOpenImmersion b.hom.left ∧
      (xs.map j).hom.left.base c ∈ range a.hom.left.base ∧
      b ≫ xt.q = a ≫ xs.q := by
  let c₀ : (wS j).carrier := ⟨(TS j).2.proj c.val,xs.proj_mem j c⟩
  have h₀ : (wS j).toLocalEmbedding.toPoint c₀ = (wT i).toLocalEmbedding.toPoint t :=
    (xs.square j c (xs.proj_mem j c)).symm.trans ht.symm
  obtain ⟨V,V',Ψ,hcV',htV,hΨ,ha⟩ :=
    adm_exists_map (sumWindow wT wS) (.inl i) (.inr j) t c₀ h₀
  let E' := localComparison wT wS rawT rawS H hrecT hrecS eT eS heT heS
    TT TS xt xs hcT hcS hrT hrS i j V V' Ψ ha
  let a := windowOpenMap xs j V'
  let b := E'.hom ≫ windowOpenMap xt i V
  refine ⟨windowOpenSpace xs j V',a,b,windowOpenMap_isOpenImmersion xs j V',?_,?_,?_⟩
  · have hE : LocallyRingedSpace.IsOpenImmersion E'.hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft E').hom
      infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hE _
      (windowOpenMap_isOpenImmersion xt i V)
  · exact ⟨⟨⟨c.val,hcV'⟩,c.property⟩,rfl⟩
  · exact localComparison_projection wT wS rawT rawS H hrecT hrecS eT eS heT heS
      TT TS xt xs hcT hcS hrT hrS i j V V' Ψ ha

end Independent
end
end Hironaka.Analytic.Unibranch.OriginalNativeTerminalWindowOverlap
