import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace
import Hironaka.Resolution.HironakaG34MaskFoldEquivariance

/-! Strict local equivariance of an actual retained defect trace. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaG4RetainedDefectTraceEquivariance

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerSplitIso MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  MarkedIdealTowerTransport MaxLocusLocal StepOneTangentChange
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualHistory
  HironakaG4RetainedDefectRelativeDecrease HironakaG4OrderedRetainedDefectTrace
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- View an open of an ambient open as an open of the original ambient. -/
private def imageOpen (W : Opens X) (U : Opens W) : Opens X :=
  ⟨(Subtype.val : W → X) '' (U : Set W), W.isOpen.isOpenMap_subtype_val _ U.isOpen⟩

private theorem imageOpen_le (W : Opens X) (U : Opens W) : imageOpen W U ≤ W := by
  rintro _ ⟨x,_,rfl⟩
  exact x.property

private theorem mem_imageOpen_iff (W : Opens X) (U : Opens W) (x : W) :
    x ∈ U ↔ x.val ∈ imageOpen W U :=
  ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,he⟩ => (Subtype.ext he : y = x) ▸ hy⟩

private theorem exists_iso_restrict_nested {W V : Opens X} {U : Opens W}
    (hUV : ∀ x : W, x ∈ U ↔ x.val ∈ V) (hVW : V ≤ W) (T : BlowupTower X Y) :
    ∃ χ : CMfd.of (n := n) (openPreimage (restrict W T) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T V),
      IsTowerIso (nestedDiffeo W U V hUV hVW) (restrict U (restrict W T)) (restrict V T) χ := by
  have hEq : U = nestedOpens W V := by
    ext x
    exact hUV x
  subst U
  exact ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (isTowerIso_restrict_nestedOpens hVW T) (fun x => Subtype.ext rfl)⟩

/-- Strict local equivariance survives literal open restriction, with
every original boundary position pulled back. -/
theorem isEquivariant_restrictOpen {N : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (hT : IsEquivariant N E T) (W : Opens X) :
    IsEquivariant ((Subtype.val : W → X) ⁻¹' N) (E.map ((Subtype.val : W → X) ⁻¹' ·))
      (restrict W T) := by
  intro U U' φ hN hE
  let V := imageOpen W U
  let V' := imageOpen W U'
  let l := nestedDiffeo (n := n) W U V (mem_imageOpen_iff W U) (imageOpen_le W U)
  let r := nestedDiffeo (n := n) W U' V' (mem_imageOpen_iff W U') (imageOpen_le W U')
  let ψ := l.symm.trans (φ.trans r)
  have hN' (x : V) : (ψ x).val ∈ N ↔ x.val ∈ N := hN (l.symm x)
  have hE' (D : Set X) (hD : D ∈ E) (x : V) : (ψ x).val ∈ D ↔ x.val ∈ D :=
    hE ((Subtype.val : W → X) ⁻¹' D) (List.mem_map.mpr ⟨D,hD,rfl⟩) (l.symm x)
  obtain ⟨χ,hχ⟩ := hT V V' ψ hN' hE'
  obtain ⟨a,ha⟩ := exists_iso_restrict_nested (mem_imageOpen_iff W U) (imageOpen_le W U) T
  obtain ⟨b,hb⟩ := exists_iso_restrict_nested (mem_imageOpen_iff W U') (imageOpen_le W U') T
  refine ⟨a.trans (χ.trans b.symm), BlowupTowerSplitIso.IsTowerIso.congr_base (ha.trans (hχ.trans hb.symm)) ?_⟩
  intro x
  change φ x = r.symm (r (φ (l.symm (l x))))
  rw [l.symm_apply_apply,r.symm_apply_apply]

/-- Strict local equivariance survives a physical tower isomorphism.
The carrier and full ordered boundary are pulled back by its actual base. -/
theorem isEquivariant_of_actualIso {N : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso e T' T η) (hT : IsEquivariant N E T) :
    IsEquivariant (e ⁻¹' N) (E.map (e ⁻¹' ·)) T' := by
  intro U U' φ hN hE
  let V : Opens X := ⟨e.symm ⁻¹' (U : Set X'), U.isOpen.preimage e.symm.continuous⟩
  let V' : Opens X := ⟨e.symm ⁻¹' (U' : Set X'), U'.isOpen.preimage e.symm.continuous⟩
  have hV (x : X') : x ∈ U ↔ e x ∈ V := by
    change x ∈ U ↔ e.symm (e x) ∈ U
    rw [e.symm_apply_apply]
  have hV' (x : X') : x ∈ U' ↔ e x ∈ V' := by
    change x ∈ U' ↔ e.symm (e x) ∈ U'
    rw [e.symm_apply_apply]
  let l := diffeoOpens e U V hV
  let r := diffeoOpens e U' V' hV'
  let ψ := l.symm.trans (φ.trans r)
  have hPreserves (D : Set X)
      (hD : ∀ x : U, e ((φ x).val) ∈ D ↔ e x.val ∈ D) (x : V) : (ψ x).val ∈ D ↔ x.val ∈ D := by
    have hPoint : e (l.symm x).val = x.val := congrArg Subtype.val (l.apply_symm_apply x)
    change e ((φ (l.symm x)).val) ∈ D ↔ x.val ∈ D
    rw [← hPoint]
    exact hD (l.symm x)
  obtain ⟨χ,hχ⟩ := hT V V' ψ (hPreserves N hN)
    (fun D hD => hPreserves D (hE (e ⁻¹' D) (List.mem_map.mpr ⟨D,hD,rfl⟩)))
  have ha := isTowerIso_restrictOpens hV hIso (isTowerIso_mem_openPreimage_iff hIso hV)
  have hb := isTowerIso_restrictOpens hV' hIso (isTowerIso_mem_openPreimage_iff hIso hV')
  have hLift := ha.trans (hχ.trans hb.symm)
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base hLift ?_⟩
  intro x
  change φ x = r.symm (r (φ (l.symm (l x))))
  rw [l.symm_apply_apply,r.symm_apply_apply]

/-- The individual actual crest supplies strict local equivariance on
its full native geometry. -/
def RetainedCrestEquivariance (hn : 0 < n) : Prop :=
  ∀ {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y},
    NativeRetainedGeometry N old born → RetainedDefectCrestPhase hn N old born T →
      IsEquivariant N (old ++ born) T

/-- A proof-relevant retained trace is strictly locally equivariant
when its individual actual crest phases are. The continuation sees the
actual transformed carrier and the full chronological boundary. -/
theorem orderedRetainedDefectTrace_isEquivariant {hn : 0 < n} (hCrest : RetainedCrestEquivariance.{u} hn)
    {N : Set X} {old born : List (Set X)} {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
    (trace : OrderedRetainedDefectTrace hn N old born μ T) (hGeometry : NativeRetainedGeometry N old born) :
    IsEquivariant N (old ++ born) T := by
  induction trace with
  | done _ => exact isEquivariant_refl _ _
  | phase T S crest _ hTest hFull tail ih =>
    have hRec := actual_retained_born_recorded_residual_dictionary hn hGeometry.carrier hGeometry.full
      hGeometry.born_transverse hGeometry.dense T hTest hFull
    exact IsEquivariant.append_of_current hGeometry.carrier T hTest hFull (hCrest hGeometry crest) S
      (ih ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩)
  | restrictOpen O geometry _ ih =>
    simpa only [List.map_append] using isEquivariant_restrictOpen (ih geometry) O
  | @rebase B B' Z N old born μ T e geometry _ ih =>
    simpa only [List.map_append] using isEquivariant_of_actualIso (transport_isTowerIso e T) (ih geometry)

end
end Hironaka.HironakaG4RetainedDefectTraceEquivariance
