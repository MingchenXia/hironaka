import Hironaka.Resolution.HironakaActualGivenWholeLimitSerial

/-! Local finiteness across actual rounds and their individual centre occurrences. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ProjectedRoundGrouping

open Hironaka.BlowupSequences BlowupTowers
  HironakaActualGivenWholeLimitSerial

/-- Grouping by rounds cannot create local accumulation. Conversely,
locally finite grouped supports and locally finite families within each
round imply locally finite individual occurrences, even for infinite rounds. -/
theorem locallyFinite_sigma_iff_grouped {X ι : Type*} [TopologicalSpace X] {κ : ι → Type*}
    (F : ∀ i, κ i → Set X) :
    LocallyFinite (fun p : Σ i, κ i => F p.1 p.2) ↔
      LocallyFinite (fun i => ⋃ j, F i j) ∧ ∀ i, LocallyFinite (F i) := by
  classical
  constructor
  · intro h
    refine ⟨fun x => ?_,fun i x => ?_⟩
    · obtain ⟨U,hU,hFin⟩ := h x
      refine ⟨U,hU,(hFin.image Sigma.fst).subset ?_⟩
      rintro i ⟨z,hz,hzU⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact ⟨⟨i,j⟩,⟨z,hj,hzU⟩,rfl⟩
    · obtain ⟨U,hU,hFin⟩ := h x
      refine ⟨U,hU,(hFin.preimage (f := Sigma.mk i) (fun a _ b _ h => ?_)).subset ?_⟩
      · cases h
        rfl
      · exact fun _ hj => hj
  · rintro ⟨hGroup,hRows⟩ x
    obtain ⟨U₀,hU₀,hFin₀⟩ := hGroup x
    choose U hU hFin using fun i => hRows i x
    let I : Set ι := {i | ((⋃ j, F i j) ∩ U₀).Nonempty}
    have hI : I.Finite := hFin₀
    let V := U₀ ∩ ⋂ i ∈ I, U i
    have hV : V ∈ 𝓝 x := inter_mem hU₀ ((Filter.biInter_mem hI).mpr fun i _ => hU i)
    let S : Finset (Σ i, κ i) := hI.toFinset.sigma fun i => (hFin i).toFinset
    refine ⟨V,hV,S.finite_toSet.subset ?_⟩
    rintro ⟨i,j⟩ ⟨z,hz,hzV⟩
    have hi : i ∈ I := ⟨z,mem_iUnion.mpr ⟨j,hz⟩,hzV.1⟩
    have hj : (F i j ∩ U i).Nonempty := ⟨z,hz,mem_iInter₂.mp hzV.2 i hi⟩
    exact Finset.mem_sigma.mpr ⟨hI.mem_toFinset.mpr hi,(hFin i).mem_toFinset.mpr hj⟩

/-- Even when different rounds occur on different physical stages, projection
commutes with their unions. If the individual centres are locally finite
within each actual stage, the projected grouped rounds are locally finite
exactly when all projected individual occurrences are locally finite. -/
theorem locallyFinite_projectedRounds_iff {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    {Y : ι → CMfd.{0} n} {κ : ι → Type*}
    (P : ∀ i, BlowupTower X (Y i)) (C : ∀ i, κ i → Set (Y i))
    (hLocal : ∀ i, LocallyFinite (C i)) :
    LocallyFinite (fun i => (P i).proj '' ⋃ j, C i j) ↔
      LocallyFinite (fun p : Σ i, κ i => (P p.1).proj '' C p.1 p.2) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  have hRows i := locallyFinite_image_of_proper
    (HironakaLocalPrincipalization.isProperMap_proj (P i)) (C i) (hLocal i)
  rw [locallyFinite_sigma_iff_grouped (fun i j => (P i).proj '' C i j)]
  simp [hRows, image_iUnion]

end Hironaka.HironakaG8ProjectedRoundGrouping
