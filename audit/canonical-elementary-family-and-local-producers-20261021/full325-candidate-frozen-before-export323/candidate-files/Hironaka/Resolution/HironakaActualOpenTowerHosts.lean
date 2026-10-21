/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalCanonicalSumSeparation

/-!
# Genuine open hosts of actual local canonical tower stages

The actual universal Cartesian square constructs an inverse for the actual
upper map on the true projection preimage of the original base open. Properness
then gives a compact enclosure of its whole image for local recursion.
Blueprint: `hironaka-actual-open-tower-hosts-extension.tex`.
-/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOpenTowerHosts
noncomputable section
open BlowupTowers HironakaBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
variable {n : ℕ} {X Y D C : CMfd.{u} n}

/-- The genuine universal square makes its actual upper map an open holomorphic embedding. -/
theorem upper_isOpenHoloEmbedding {b : Y → X} {T : BlowupTower X D}
    {Q : BlowupTower Y C} {g : C → D}
    (h : IsActualTowerPullback b Q T g) (hb : IsOpenHoloEmbedding n b) :
    IsOpenHoloEmbedding n g := by
  obtain ⟨O,Φ,hΦ⟩ := hb
  let V : Opens D := ⟨T.proj ⁻¹' (O : Set X),O.isOpen.preimage T.contMDiff_proj.continuous⟩
  let u : V → Y := fun z => Φ.symm ⟨T.proj z,z.property⟩
  have hu : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ u :=
    Φ.symm.contMDiff.comp ((ContMDiff.subtypeVal_comp_iff O _).mp
      (T.contMDiff_proj.comp contMDiff_subtype_val))
  have hcone : ∀ z : V,b (u z)=T.proj z := by
    intro z
    exact (hΦ (u z)).trans (congrArg Subtype.val (Φ.apply_symm_apply ⟨T.proj z,z.property⟩))
  obtain ⟨w,hw,_⟩ := h.universal n (CMfd.of (n := n) V) u Subtype.val
    hu contMDiff_subtype_val hcone
  let e : C → V := fun c => ⟨g c,by
    change T.proj (g c) ∈ O
    rw [h.proj_comm c,hΦ (Q.proj c)]
    exact (Φ (Q.proj c)).property⟩
  have he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e :=
    (ContMDiff.subtypeVal_comp_iff V e).mp h.isSubmersion.contMDiff
  have hue : ∀ c,u (e c)=Q.proj c := by
    intro c
    have hh : (⟨T.proj (g c),(e c).property⟩ : O)=Φ (Q.proj c) := by
      apply Subtype.ext
      exact (h.proj_comm c).trans (hΦ (Q.proj c))
    change Φ.symm ⟨T.proj (g c),(e c).property⟩=Q.proj c
    rw [hh,Φ.symm_apply_apply]
  have hwe : w ∘ e=id :=
    (h.universal n C Q.proj g Q.contMDiff_proj h.isSubmersion.contMDiff
      (fun c => (h.proj_comm c).symm)).unique
      ⟨hw.1.comp he,fun c => (hw.2.1 (e c)).trans (hue c),fun c => hw.2.2 (e c)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  have hew : ∀ z,e (w z)=z := fun z => Subtype.ext (hw.2.2 z)
  let Ψ : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V :=
    { toEquiv := ⟨e,w,fun c => congrFun hwe c,hew⟩
      contMDiff_toFun := he
      contMDiff_invFun := hw.1 }
  exact ⟨V,Ψ,fun _ => rfl⟩

/-- The whole actual image is exactly the inverse image of the original base image. -/
theorem upper_range_eq {b : Y → X} {T : BlowupTower X D}
    {Q : BlowupTower Y C} {g : C → D}
    (h : IsActualTowerPullback b Q T g) :
    range g=T.proj ⁻¹' range b := by
  apply subset_antisymm
  · rintro _ ⟨c,rfl⟩
    exact ⟨Q.proj c,(h.proj_comm c).symm⟩
  · intro d hd
    obtain ⟨y,hy⟩ := hd
    obtain ⟨w,hw,_⟩ := h.universal n Y (fun _ => y) (fun _ => d)
      contMDiff_const contMDiff_const (fun _ => hy)
    exact ⟨w y,hw.2.2 y⟩

/-- A true compact closure inside the host open gives a compact enclosure of the whole actual upper range. -/
theorem upper_range_subset_compact {B : CMfd.{u} n} {ι : B → X} (U : Opens X)
    (hιU : closure (range ι) ⊆ U) (hc : IsCompact (closure (range ι)))
    {T : BlowupTower (CMfd.of (n := n) U) D} {Q : BlowupTower B C}
    {g : C → D}
    (h : IsActualTowerPullback (fun z => (⟨ι z,hιU (subset_closure ⟨z,rfl⟩)⟩ : U)) Q T g) :
    ∃ K : Set D,IsCompact K ∧ range g ⊆ K := by
  refine ⟨T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' closure (range ι)),?_,?_⟩
  · refine (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage ?_
    rw [Subtype.isCompact_iff,image_preimage_eq_inter_range,Subtype.range_coe,inter_eq_left.mpr hιU]
    exact hc
  · rintro _ ⟨c,rfl⟩
    change ((T.proj (g c) : U) : X) ∈ closure (range ι)
    rw [h.proj_comm c]
    exact subset_closure ⟨Q.proj c,rfl⟩

end
end Hironaka.HironakaActualOpenTowerHosts
