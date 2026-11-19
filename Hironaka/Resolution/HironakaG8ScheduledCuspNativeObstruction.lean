import Hironaka.Resolution.HironakaG8NativeFirstSlotSymmetry
import Hironaka.Resolution.HironakaG8CuspSheetFootprintTraces
import Hironaka.Resolution.HironakaG8FiniteCuspSheetSchedule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Filter Function
open scoped Manifold ContDiff Topology
namespace Hironaka.HironakaG8ScheduledCuspNativeObstruction

open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MaxLocusLocal HironakaEmbeddedAnalytic HironakaG8CountableCuspSheets
  HironakaG8CuspSheetFootprintTraces HironakaG8NativeFirstSlotSymmetry HironakaG8LabelledNativeHistory
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison HironakaG8OddCuspGeometricSource
  HironakaResolutionSpaceLocal StepOneTangentChange HironakaG8FiniteCuspSheetSchedule

noncomputable section
local notation "𝓘c" => 𝓘(ℂ,ComplexModel 3)

private theorem contMDiff_sheet_permute (σ : ℕ → ℕ) :
    ContMDiff 𝓘c 𝓘c ∞ (fun p : CuspSheets => (σ p.1,p.2)) := by
  intro p
  let f := (sheetChart (σ p.1)).symm ∘ sheetChart p.1
  have hFwd := (contMDiffOn_chart (I := 𝓘c) (n := ∞) (x := p)).contMDiffAt
    ((sheetOpen p.1).isOpen.mem_nhds (show p ∈ sheetOpen p.1 from ⟨rfl,mem_univ p.2⟩))
  have hInv := (contMDiffOn_chart_symm (I := 𝓘c) (n := ∞)
    (x := ((σ p.1,0) : CuspSheets))).contMDiffAt
    (show (sheetChart (σ p.1)).target ∈ 𝓝 p.2 from univ_mem)
  have hf : ContMDiffAt 𝓘c 𝓘c ∞ f p := hInv.comp p hFwd
  apply hf.congr_of_eventuallyEq
  filter_upwards [(sheetOpen p.1).isOpen.mem_nhds (show p ∈ sheetOpen p.1 from ⟨rfl,mem_univ p.2⟩)]
    with q hq
  change (σ q.1,q.2) = (σ p.1,q.2)
  rw [show q.1 = p.1 from mem_singleton_iff.mp hq.1]

private def sheetPermutation (σ : ℕ ≃ ℕ) : CuspSheets ≃ₘ⟮𝓘c,𝓘c⟯ CuspSheets where
  toEquiv := σ.prodCongr (Equiv.refl _)
  contMDiff_toFun := contMDiff_sheet_permute σ
  contMDiff_invFun := contMDiff_sheet_permute σ.symm

private theorem swap_mem_prefix (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    Equiv.swap 0 1 i ≤ m ↔ i ≤ m := by
  by_cases h0 : i = 0
  · subst i
    simp [hm]
  by_cases h1 : i = 1
  · subst i
    simp [hm]
  simp [Equiv.swap_apply_of_ne_of_ne h0 h1]

private def prefixSwap (m : ℕ) (hm : 1 ≤ m) :
    PrefixManifold m ≃ₘ⟮𝓘c,𝓘c⟯ PrefixManifold m :=
  diffeoOpens (X := sheetManifold) (X' := sheetManifold) (sheetPermutation (Equiv.swap 0 1)) (prefixOpen m) (prefixOpen m)
    (fun (p : CuspSheets) => (swap_mem_prefix m hm p.1).symm)

private theorem cuspPrefix_singular_anchor (m : ℕ) (hm : 1 ≤ m) :
    (⟨(1,0),hm⟩ : prefixOpen m) ∈ singularSet (n := 3) (cuspPrefix m) := by
  let x : prefixOpen m := ⟨(1,0),hm⟩
  let u : prefixSheetOpen m 1 := ⟨x,⟨rfl,mem_univ (0 : ComplexModel 3)⟩⟩
  have hs := embedded_odd_cusp_singular_at_zero 7 (by decide) (by decide)
  have hRead := sheetCusps_preimage_prefix_sheet (fun _ => 7) hm
  have hPull := congrArg (singularSet (n := 3)) hRead
  rw [singularSet_preimage_val,
    HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism
        (D := CMfd.of (n := 3) (prefixSheetOpen m 1)) (C := CMfd.of (n := 3) (ComplexModel 3))
        (prefixSheetBiholomorph hm))] at hPull
  exact (Set.ext_iff.mp hPull u).mpr hs

/-- The actual scheduled cutoff with at least two identical sheets has no
native epoch prefix with a smooth terminal carrier under any exact
tower factorization. In particular its staggered first slots do not
come from the ordered native chart class. -/
theorem scheduled_cusp_cutoff_not_native
    {m : ℕ} (hm : 1 ≤ m) {Y B D : CMfd.{0} 3}
    {T : BlowupTower (PrefixManifold m) Y} (hT : ScheduledSingletonTraces m T)
    {S : BlowupTower (PrefixManifold m) B} {Q : BlowupTower B D} {L : List (ℕ → ℕ)}
    (hS : LabelledNativeTower 3 (cuspPrefix m) [] univ S L)
    (χ : Y ≃ₘ⟮𝓘c,𝓘c⟯ D)
    (hIso : IsTowerIso (Diffeomorph.refl 𝓘c (PrefixManifold m) ∞) T (S.append Q) χ) : False := by
  let a : PrefixManifold m := ⟨(1,0),hm⟩
  let φ := prefixSwap m hm
  have hφW : φ ⁻¹' cuspPrefix m = cuspPrefix m := by
    ext u
    rfl
  have ha : a ∉ slotFootprint T 0 := by
    intro h
    obtain ⟨_,h₀ | h₁ | h₂⟩ := (scheduled_rawFootprint_mem hT 0 a).mp h
    · change 0 = 1 at h₀
      omega
    · change 0 = 2 at h₁
      omega
    · omega
  have hφa : φ a ∈ slotFootprint T 0 := by
    apply (scheduled_rawFootprint_mem hT 0 (φ a)).mpr
    refine ⟨rfl, Or.inl ?_⟩
    change 0 = Equiv.swap 0 1 1
    exact (Equiv.swap_apply_right 0 1).symm
  have hLen : 0 < S.length := by
    cases S with
    | refl =>
      exact False.elim (by
        have hSmooth := hS.target_smooth
        rw [BlowupTower.proj_refl,HironakaG11PresTowerState.strictTransform_id hS.source_analytic.isClosed] at hSmooth
        obtain ⟨d,hd⟩ := hSmooth.2 a (mem_singularSet_iff.mp (cuspPrefix_singular_anchor m hm)).1
        exact (mem_singularSet_iff.mp (cuspPrefix_singular_anchor m hm)).2 d hd)
    | step => simp
  have hFoot : slotFootprint T 0 = slotFootprint S 0 := by
    rw [slotFootprint_of_isTowerIso hIso,Diffeomorph.coe_refl,preimage_id,
      slotFootprint_append,if_pos hLen]
  exact ha (hFoot.symm ▸ labelled_native_first_slot_symmetry (by decide) φ hφW hS (hFoot ▸ hφa))

end
end Hironaka.HironakaG8ScheduledCuspNativeObstruction
