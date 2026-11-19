import Hironaka.Resolution.HironakaG8OddCuspGlobalStrict
import Hironaka.Resolution.HironakaG8StrictTransformAtlasSquare
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ActualCuspExceptionalFibre

open Hironaka.BlowupSequences BlowupTowers BlowupRestrictOpen HironakaBaseChange
  HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGlobalStrict
  HironakaG8StrictTransformAtlasSquare HironakaNormalCrossingsSeparationChoiceComparison
  BlowupExistenceOriginModel BlowupExistenceOriginUniversal

private abbrev M := ComplexModel 3

/-- An arbitrary actual singleton blowup has exactly one strict cusp point in the
entire exceptional fibre over the centred source chart. -/
theorem existsUnique_actual_cusp_exceptional_fibre {X Y : CMfd.{0} 3}
    {π : Y → X} {x : X} (hπ : IsBlowupAlong 3 ({x} : Set X) π)
    (e : OpenPartialHomeomorph X M) (he : e ∈ atlas M X)
    (hx : x ∈ e.source) (h0 : e x = 0) (W : Set X) (p : ℕ) (hp : 2 < p)
    (hW : ∀ a ∈ e.source, a ∈ W ↔ e a ∈ embeddedCuspSet p) :
    ∃! z : Y, z ∈ strictTransform 3 π W ∧ π z = x := by
  let U : Opens X := ⟨e.source,e.open_source⟩
  obtain ⟨V,Φ,hΦ⟩ := atlas_open_holo_embedding e he
  let u : U := ⟨x,hx⟩
  have hu : (Φ u).val = 0 := (hΦ u).symm.trans h0
  let O : Opens Y := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩
  let Q : Opens (OriginBlowup 3) := ⟨originProj ⁻¹' (V : Set M),
    V.isOpen.preimage (isBlowupAlong_originProj (by decide : 0 < 3)).contMDiff.continuous⟩
  let r (y : O) : U := ⟨π y.val,y.property⟩
  let s (a : Q) : V := ⟨originProj a.val,a.property⟩
  have hr := isBlowupAlong_restrict hπ U O.isOpen
  have hs := isBlowupAlong_restrict (isBlowupAlong_originProj (by decide : 0 < 3)) V Q.isOpen
  have hC : Φ ⁻¹' ((Subtype.val : V → M) ⁻¹' ({0} : Set M)) =
      (Subtype.val : U → X) ⁻¹' ({x} : Set X) := by
    ext a
    change (Φ a).val ∈ ({0} : Set M) ↔ a.val ∈ ({x} : Set X)
    simp only [mem_singleton_iff]
    constructor
    · intro ha
      exact congrArg Subtype.val (Φ.injective (Subtype.ext (ha.trans hu.symm)))
    · intro ha
      rw [show a = u from Subtype.ext ha,hu]
  obtain ⟨χ,hχ,_⟩ := exists_unique_lift (A' := CMfd.of U) (A := CMfd.of V) (B' := CMfd.of O) (B := CMfd.of Q) Φ hr hs hC
  change ∀ y : O, s (χ y) = Φ (r y) at hχ
  have hA : (Subtype.val : U → X) ⁻¹' W =
      (fun a : U => (Φ a).val) ⁻¹' embeddedCuspSet p := by
    ext a
    change a.val ∈ W ↔ (Φ a).val ∈ embeddedCuspSet p
    rw [← hΦ]
    exact hW a.val a.property
  have hΦemb : IsOpenHoloEmbedding 3 (fun a : U => (Φ a).val) := ⟨V,Φ,fun _ => rfl⟩
  have hχemb : IsOpenHoloEmbedding 3 (fun a : O => (χ a).val) := ⟨Q,χ,fun _ => rfl⟩
  have hR := strictTransform_preimage_eq hπ.contMDiff hr.contMDiff
    (isOpenHoloEmbedding_val U) (isOpenHoloEmbedding_val O) (fun _ => rfl) W
  have hRS := strictTransform_preimage_eq (isBlowupAlong_originProj (by decide : 0 < 3)).contMDiff
    hr.contMDiff hΦemb hχemb (fun y => congrArg Subtype.val (hχ y)) (embeddedCuspSet p)
  rw [hA,hRS] at hR
  have hread (y : O) : y.val ∈ strictTransform 3 π W ↔
      (χ y).val ∈ strictTransform 3 originProj (embeddedCuspSet p) :=
    (Set.ext_iff.mp hR y).symm
  have hproj (y : O) : π y.val = x ↔ originProj (χ y).val = 0 := by
    change (r y).val = x ↔ (s (χ y)).val = 0
    rw [hχ]
    constructor
    · intro h
      rw [show r y = u from Subtype.ext h,hu]
    · intro h
      exact congrArg Subtype.val (Φ.injective (Subtype.ext (h.trans hu.symm)))
  let a := originMk (0 : Fin 3) (0 : M)
  have ha : a ∈ strictTransform 3 originProj (embeddedCuspSet p) ∩
      originProj ⁻¹' ({0} : Set M) := by
    rw [strictTransform_cusp_exceptional_fibre p hp]
    exact mem_singleton _
  let q : Q := ⟨a, by
    change originProj a ∈ V
    rw [mem_singleton_iff.mp ha.2,← hu]
    exact (Φ u).property⟩
  let y := χ.symm q
  have hy : χ y = q := χ.apply_symm_apply _
  refine ⟨y.val, ⟨(hread y).mpr ?_,(hproj y).mpr ?_⟩, ?_⟩
  · rw [hy]
    exact ha.1
  · rw [hy]
    exact mem_singleton_iff.mp ha.2
  · intro z hz
    let v : O := ⟨z,by change π z ∈ U; rw [hz.2]; exact hx⟩
    have hv : (χ v).val ∈ strictTransform 3 originProj (embeddedCuspSet p) ∩
        originProj ⁻¹' ({0} : Set M) :=
      ⟨(hread v).mp hz.1,mem_singleton_iff.mpr ((hproj v).mp hz.2)⟩
    rw [strictTransform_cusp_exceptional_fibre p hp] at hv
    exact congrArg Subtype.val (χ.injective ((Subtype.ext (mem_singleton_iff.mp hv)).trans hy.symm))

#print axioms existsUnique_actual_cusp_exceptional_fibre

end Hironaka.HironakaG8ActualCuspExceptionalFibre
