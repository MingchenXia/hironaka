import Hironaka.Resolution.HironakaActualAnchoredMaskedHistories

/-! Refine the actual INITIAL comparison while keeping the SAME real
histories. Only the actual current windows are restricted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredInitialRefinement
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms HironakaActualGeneratedCurrentHistories
open HironakaActualAnchoredCurrentHistories HironakaActualAnchoredMaskedHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem current_window_trace {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X'))) :
 η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' ((U' ⊓ openPreimage T W' : Opens Y') : Set Y'))=
   (Subtype.val : U → Y) ⁻¹' ((U ⊓ openPreimage S W : Opens Y) : Set Y) := by
 have h := HironakaActualAnchoredMaskedHistories.Anchored.original_mask_traces H W W' hMask
 ext p
 change ((η p).val∈U' ∧ T.proj (η p).val∈W') ↔ (p.val∈U ∧ S.proj p.val∈W)
 exact ⟨fun hp => ⟨p.property,(Set.ext_iff.mp h p).mpr hp.2⟩,
   fun hp => ⟨(η p).property,(Set.ext_iff.mp h p).mp hp.2⟩⟩

def refinedComparison {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X'))) :
 CMfd.of (n := n) (U ⊓ openPreimage S W : Opens Y)
   ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (U' ⊓ openPreimage T W' : Opens Y') :=
 restrictComparison η (U ⊓ openPreimage S W) (U' ⊓ openPreimage T W')
   (fun _ h => h.1) (fun _ h => h.1) (current_window_trace H W W' hMask)

theorem refinedComparison_val {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η) (W : Opens X) (W' : Opens X')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X')))
 (p : (U ⊓ openPreimage S W : Opens Y)) :
 (refinedComparison H W W' hMask p).val=(η ⟨p.val,p.property.1⟩).val := rfl

/-- Initial refinement retains the complete actual source and target
histories; the current windows become their original inverse-image traces. -/
theorem Anchored.refine_initial {V₀ : Opens X} {V₀' : Opens X'} {φ}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S T U U' η)
 (W : Opens X) (W' : Opens X') (hW : (W : Set X)⊆V₀) (hW' : (W' : Set X')⊆V₀')
 (hMask : (Subtype.val : V₀ → X) ⁻¹' (W : Set X)=
   φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (W' : Set X'))) :
 Anchored W W' (restrictComparison φ W W' hW hW' hMask.symm)
   S T (U ⊓ openPreimage S W) (U' ⊓ openPreimage T W') (refinedComparison H W W' hMask) := by
 induction H with
 | initial =>
   let Us := V₀ ⊓ openPreimage (.refl : BlowupTower X X) W
   let Ut := V₀' ⊓ openPreimage (.refl : BlowupTower X' X') W'
   let φs := restrictComparison φ W W' hW hW' hMask.symm
   have hs : (Us : Set X)⊆W := fun _ h => h.2
   have ht : (Ut : Set X')⊆W' := fun _ h => h.2
   have htr : φs ⁻¹' ((Subtype.val : W' → X') ⁻¹' (Ut : Set X'))=
       (Subtype.val : W → X) ⁻¹' (Us : Set X) := by
     ext p
     exact ⟨fun _ => ⟨hW p.property,p.property⟩,
       fun _ => ⟨hW' (φs p).property,(φs p).property⟩⟩
   let ρ := restrictComparison φs Us Ut hs ht htr
   have Hρ := Anchored.shrink (Anchored.initial (V₀ := W) (V₀' := W') (φ := φs)) Us Ut hs ht htr
   have heq : ρ=refinedComparison (Anchored.initial (V₀ := V₀) (V₀' := V₀') (φ := φ)) W W' hMask := by
     apply Diffeomorph.ext
     intro p
     apply Subtype.ext
     rfl
   exact heq ▸ Hρ
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   let Us := U ⊓ openPreimage S W
   let Ut := U' ⊓ openPreimage T W'
   let Vs := V ⊓ openPreimage S W
   let Vt := V' ⊓ openPreimage T W'
   let ηs := refinedComparison H W W' hMask
   have hs : (Vs : Set Y)⊆Us := fun _ h => ⟨hV h.1,h.2⟩
   have ht : (Vt : Set Y')⊆Ut := fun _ h => ⟨hV' h.1,h.2⟩
   have htrace : ηs ⁻¹' ((Subtype.val : Ut → Y') ⁻¹' (Vt : Set Y'))=
       (Subtype.val : Us → Y) ⁻¹' (Vs : Set Y) := by
     ext p
     have h := Set.ext_iff.mp htr ⟨p.val,p.property.1⟩
     exact ⟨fun hp => ⟨h.mp hp.1,p.property.2⟩,
       fun hp => ⟨h.mpr hp.1,(ηs p).property.2⟩⟩
   let ρ := restrictComparison ηs Vs Vt hs ht htrace
   have Hρ := Anchored.shrink ih Vs Vt hs ht htrace
   have heq : ρ=refinedComparison (Anchored.shrink H V V' hV hV' htr) W W' hMask := by
     apply Diffeomorph.ext
     intro p
     apply Subtype.ext
     rfl
   exact heq ▸ Hρ
 | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
   let Us := U ⊓ openPreimage S W
   let Ut := U' ⊓ openPreimage T W'
   let ηs := refinedComparison H W W' hMask
   have hCs : ηs ⁻¹' ((Subtype.val : Ut → Y') ⁻¹' C')=(Subtype.val : Us → Y) ⁻¹' C := by
     ext p
     exact Set.ext_iff.mp hC ⟨p.val,p.property.1⟩
   have Hnext := Anchored.step ih hπ hπ' hCs
   let ψ := refinedComparison (Anchored.step H hπ hπ' hC) W W' hMask
   have hψ : ∀p,π' (ψ p).val=(ηs ⟨π p.val,p.property⟩).val := by
     intro p
     exact nextComparison_square hπ hπ' U U' η hC ⟨p.val,p.property.1⟩
   have heq : ψ=nextComparison hπ hπ' Us Ut ηs hCs :=
     (Classical.choose_spec
       (HironakaActualDifferentHistoryRecords.existsUnique_next_comparison hπ hπ' Us Ut ηs hCs)).2 ψ hψ
   rw [←heq] at Hnext
   exact Hnext

/-- Two arbitrary desired original neighborhoods of corresponding actual
points internally produce corresponding smaller initial opens. -/
theorem exists_initial_windows_inside
 (V₀ : Opens X) (V₀' : Opens X')
 (φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀')
 (W : Opens X) (W' : Opens X') (p : V₀) (hp : p.val∈W) (hp' : (φ p).val∈W') :
 ∃(V : Opens X)(V' : Opens X'),p.val∈V ∧ (φ p).val∈V' ∧
   (V : Set X)⊆V₀ ∧ (V' : Set X')⊆V₀' ∧ (V : Set X)⊆W ∧ (V' : Set X')⊆W' ∧
   (Subtype.val : V₀ → X) ⁻¹' (V : Set X)=
     φ ⁻¹' ((Subtype.val : V₀' → X') ⁻¹' (V' : Set X')) := by
 let O : Opens V₀ := ⟨{z | z.val∈W ∧ (φ z).val∈W'},
   (W.isOpen.preimage continuous_subtype_val).inter
     (W'.isOpen.preimage (continuous_subtype_val.comp φ.continuous))⟩
 let O' : Opens V₀' := ⟨φ '' (O : Set V₀),φ.toHomeomorph.isOpenMap _ O.isOpen⟩
 let V : Opens X := ⟨(Subtype.val : V₀ → X) '' (O : Set V₀),
   V₀.isOpen.isOpenMap_subtype_val _ O.isOpen⟩
 let V' : Opens X' := ⟨(Subtype.val : V₀' → X') '' (O' : Set V₀'),
   V₀'.isOpen.isOpenMap_subtype_val _ O'.isOpen⟩
 have hpO : p∈O := ⟨hp,hp'⟩
 refine ⟨V,V',⟨p,hpO,rfl⟩,⟨φ p,⟨p,hpO,rfl⟩,rfl⟩,?_,?_,?_,?_,?_⟩
 · rintro x ⟨z,_hz,rfl⟩
   exact z.property
 · rintro x ⟨z,_hz,rfl⟩
   exact z.property
 · rintro x ⟨z,hz,rfl⟩
   exact hz.1
 · rintro x ⟨z,⟨w,hw,rfl⟩,rfl⟩
   exact hw.2
 · ext z
   constructor
   · rintro ⟨w,hw,hEq⟩
     have hwz : w=z := Subtype.ext hEq
     exact ⟨φ w,⟨w,hw,rfl⟩,congrArg (fun q : V₀ => (φ q).val) hwz⟩
   · rintro ⟨w,⟨a,ha,haw⟩,hwz⟩
     have hφ : φ a=φ z := Subtype.ext ((congrArg (fun q : V₀' => q.val) haw).trans hwz)
     have haz : a=z := φ.injective hφ
     exact ⟨a,ha,congrArg (fun q : V₀ => q.val) haz⟩

end
end Hironaka.HironakaActualAnchoredInitialRefinement
