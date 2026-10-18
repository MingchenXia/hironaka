/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformPrefixes
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
import Hironaka.Support.TowerIsoBaseCongruenceExact

/-! Genuine prefix/restriction flattening from actual append and split maps,
followed by the real restriction of an existing uniform-stage comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformPrefixRestriction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  BlowupTowerIsomorphism BlowupTowerIsoTail HironakaSharpActualCurveUniformPrefixes
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveComparisonRestriction
  HironakaSharpActualCurveFiniteRecipeComparison
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Real append/empty restriction and independent split-restriction maps
construct the unique isomorphism of the WHOLE uniform restricted prefix. -/
theorem exists_unique_uniformPrefix_open_restriction (T : BlowupTower X Y) (U : Opens X) (k : ℕ) :
    ∃! e : (uniformPrefix (restrict U T) k).1
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) e := by
  let A := openPreimage T U
  let R := restrict U T
  let F := T.append (identityEmptyTail Y k)
  have hRaw := (isTowerIso_restrict_append U T (identityEmptyTail Y k)).trans
    ((IsTowerIso.refl_self R).append (identityEmptyTail_open_restriction Y A k))
  have hFlat := BlowupTowerSplitIso.IsTowerIso.congr_base hRaw
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) (fun _ => rfl)
  obtain ⟨b,hb,_hbTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hFlat T.length
  obtain ⟨c,hc,_hcTail⟩ := exists_isTowerIso_split_restrict U F T.length
  have hHead := BlowupTowerSplitIso.IsTowerIso.congr_base (hb.symm.trans hc)
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) (fun _ => rfl)
  let P : (Σ V : CMfd.{u} n,BlowupTower (CMfd.of (n := n) U) V) → Prop := fun B =>
    ∃ e : B.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        B.2 (restrict U (uniformPrefix T k).2) e
  have hPacket : headPacket (R.append (identityEmptyTail (CMfd.of (n := n) A) k)) T.length=
      uniformPrefix R k :=
    congrArg (headPacket (R.append (identityEmptyTail (CMfd.of (n := n) A) k)))
      (length_restrict U T).symm
  have hh : P (headPacket (R.append (identityEmptyTail (CMfd.of (n := n) A) k)) T.length) :=
    ⟨b.symm.trans c,hHead⟩
  obtain ⟨e,he⟩ := (congrArg P hPacket).mp hh
  exact ⟨e,he,fun e' he' => actual_tower_comparison_unique he' he⟩

/-- The real stagewise comparison gives the full projection square on
EVERY endpoint point, including all actual exceptional/centre points. -/
theorem uniformPrefix_open_restriction_projection (T : BlowupTower X Y) (U : Opens X) (k : ℕ)
    (e : (uniformPrefix (restrict U T) k).1
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U))
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) e)
    (z : (uniformPrefix (restrict U T) k).1) :
    (uniformPrefix T k).2.proj (e z).val=((uniformPrefix (restrict U T) k).2.proj z).val := by
  have hh := congrArg Subtype.val (he.proj_comm z)
  change (((uniformPrefix (restrict U T) k).2.proj z : U) : X)=
    (((restrict U (uniformPrefix T k).2).proj (e z) : U) : X) at hh
  rw [proj_restrict] at hh
  exact hh.symm

/-- The OLD genuine prefix map, restricted to actual matching opens and
conjugated by both independently constructed prefix flattenings. -/
theorem exists_unique_uniformPrefix_comparison_open_restriction
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y) (k : ℕ)
    (e : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1)
    (h : IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 e) (U : Opens X) :
    ∃! d : (uniformPrefix (restrict (preimageOpen Φ U) T') k).1
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix (restrict U T) k).1,
      IsTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
        (uniformPrefix (restrict (preimageOpen Φ U) T') k).2
        (uniformPrefix (restrict U T) k).2 d ∧
      ∃ fs : (uniformPrefix (restrict (preimageOpen Φ U) T') k).1
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (uniformPrefix T' k).2 (preimageOpen Φ U)),
      ∃ ft : (uniformPrefix (restrict U T) k).1
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U),
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (preimageOpen Φ U)) ∞)
          (uniformPrefix (restrict (preimageOpen Φ U) T') k).2
          (restrict (preimageOpen Φ U) (uniformPrefix T' k).2) fs ∧
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) ft ∧
        d=fs.trans ((openRestriction e
          (openPreimage (uniformPrefix T' k).2 (preimageOpen Φ U))
          (openPreimage (uniformPrefix T k).2 U) (openPreimage_eq_preimage h U)).trans ft.symm) := by
  obtain ⟨fs,hfs,_hfsUnique⟩ := exists_unique_uniformPrefix_open_restriction T' (preimageOpen Φ U) k
  obtain ⟨ft,hft,_hftUnique⟩ := exists_unique_uniformPrefix_open_restriction T U k
  let er := openRestriction e (openPreimage (uniformPrefix T' k).2 (preimageOpen Φ U))
    (openPreimage (uniformPrefix T k).2 U) (openPreimage_eq_preimage h U)
  let d := fs.trans (er.trans ft.symm)
  have hR := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction h U
  have hNew := BlowupTowerSplitIso.IsTowerIso.congr_base (hfs.trans (hR.trans hft.symm))
    (Φ' := openRestriction Φ (preimageOpen Φ U) U rfl) (fun _ => rfl)
  exact ⟨d,⟨hNew,fs,ft,hfs,hft,rfl⟩,
    fun d' hd' => actual_tower_comparison_unique hd'.1 hNew⟩

end
end Hironaka.HironakaSharpActualCurveUniformPrefixRestriction
