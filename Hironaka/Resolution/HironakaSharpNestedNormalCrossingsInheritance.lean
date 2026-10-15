/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalDistinctTraceUSC

/-! Genuine BM97 Lemma12.7 geometry from actual nested carriers and true
preferred-chart coordinate transitions. Target NC/transversality is NOT input.
Complete source-first blueprint precedes code; actual recursive history remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpNestedNormalCrossingsInheritance
noncomputable section
open Hironaka.BlowupSequences NormalCrossings SimultaneousNormalCrossings
  HironakaSharpNormalCrossingsOpenLocus RegularPatchPushforward
  RegularAtDimTransport BlowupSNCTransform
  BlowupTowers
variable {n : ℕ} {X : CMfd.{u} n}

/-- Genuine noncontainment makes the SAME actual smaller NC coordinates free for every incident member. -/
theorem exists_actual_free_family_of_germ_noncontainment {W : Set X} {E : List (Set X)} {x : X}
    (hx : x ∈ W) (hNC : normalCrossingsAt (n := n) W E x)
    (hnot : ∀ i : Fin E.length,x ∈ E.get i → ¬∀ᶠ y in 𝓝 x,y ∈ W → y ∈ E.get i) :
    ∃ (S₀ : Finset (Fin n)) (S : Fin E.length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim W (fun i => E.get i))
        (fun o => o.elim S₀ S) x ∧
      ∀ i : Fin E.length,x ∈ E.get i → (S i).card=1 ∧ Disjoint (S i) S₀ := by
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hfam⟩,hcard⟩ := hNC
  refine ⟨S₀,S,⟨Φ,hsrc,h0,hfam⟩,fun i hi => ⟨hcard i hi,?_⟩⟩
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i hi)
  rw [ha,Finset.disjoint_singleton_left]
  intro haS
  apply hnot i hi
  let e := (complexChartAt (n := n) x).val
  have hU : e.source ∩ e ⁻¹' Φ.source ∈ 𝓝 x :=
    (e.continuousOn.isOpen_inter_preimage e.open_source Φ.isOpen_source).mem_nhds
      ⟨mem_complexChartAt_source x,Φ.center_mem_source⟩
  filter_upwards [hU] with y hy hyW
  apply (hfam (some i) hi hy.1 hy.2).mpr
  change Φ.toFun (e y) ∈ coordSubspace (S i)
  rw [ha]
  intro j hj
  rw [Finset.mem_singleton.mp hj]
  exact ((hfam none hx hy.1 hy.2).mp hyW) a haS

/-- REAL nested smooth-carrier coordinate inheritance, without target NC or transversality. -/
theorem actual_normalCrossingsAt_of_nested_germ_noncontainment (hn : 0 < n)
    {W N : Set X} {E : List (Set X)} (hWN : W ⊆ N) (hN : IsClosedSubmanifold n N)
    {x : X} (hx : x ∈ W) (hNC : normalCrossingsAt (n := n) W E x)
    (hnot : ∀ i : Fin E.length,x ∈ E.get i → ¬∀ᶠ y in 𝓝 x,y ∈ W → y ∈ E.get i) :
    normalCrossingsAt (n := n) N E x := by
  obtain ⟨Y,S',⟨Θ,hΘt,hΘ0,hΘA⟩,hS'⟩ := exists_actual_free_family_of_germ_noncontainment hx hNC hnot
  obtain ⟨S₀,_S,⟨Ψ,hΨt,hΨ0,hΨA⟩,_hS⟩ := hasNormalCrossings_nil_of_isClosedSubmanifold hN x (hWN hx)
  let e := (complexChartAt (n := n) x).val
  let pick : Finset (Fin n) → Fin n := fun s => if h : s.Nonempty then s.min' h else ⟨0,hn⟩
  have hpick1 : ∀ s : Finset (Fin n),s.card=1 → s={pick s} := by
    intro s hs
    obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hs
    simp [pick]
  let p : Fin E.length → Fin n := fun i => pick (S' i)
  have hpY : ∀ i,x ∈ E.get i → p i ∉ Y := by
    intro i hi
    have hh := (hS' i hi).2
    rw [hpick1 _ (hS' i hi).1] at hh
    exact Finset.disjoint_singleton_left.mp hh
  have hHΘ : ∀ i,x ∈ E.get i → ∀ {y : X},y ∈ e.source → e y ∈ Θ.source →
      (y ∈ E.get i ↔ Θ.toFun (e y) (p i)=0) := by
    intro i hi y hy hyΘ
    have hh := hΘA (some i) hi hy hyΘ
    change (y ∈ E.get i ↔ Θ.toFun (e y) ∈ coordSubspace (S' i)) at hh
    rw [hpick1 _ (hS' i hi).1,mem_coordSubspace_singleton] at hh
    exact hh
  have hWΘ : ∀ {y : X},y ∈ e.source → e y ∈ Θ.source →
      (y ∈ W ↔ Θ.toFun (e y) ∈ coordSubspace Y) := fun hy hyΘ => hΘA none hx hy hyΘ
  have hNΨ : ∀ {y : X},y ∈ e.source → e y ∈ Ψ.source →
      (y ∈ N ↔ Ψ.toFun (e y) ∈ coordSubspace S₀) := fun hy hyΨ => hΨA none (hWN hx) hy hyΨ
  have h0Θ : (0 : ComplexModel n) ∈ Θ.target := hΘ0 ▸ Θ.mapsTo_toFun Θ.center_mem_source
  have hΘinv0 : Θ.invFun 0=e x := by
    rw [← hΘ0]
    exact Θ.left_inv _ Θ.center_mem_source
  let Ξ := LocalHolomorphicEquivAt.comp (symmAt Θ h0Θ) Ψ hΘinv0
  have hΞ0 : Ξ.toFun 0=0 := by
    change Ψ.toFun (Θ.invFun 0)=0
    rw [hΘinv0]
    exact hΨ0
  have hpt : ∀ u ∈ Ξ.source,e.symm (Θ.invFun u) ∈ e.source ∧
      e (e.symm (Θ.invFun u)) ∈ Θ.source ∧ e (e.symm (Θ.invFun u)) ∈ Ψ.source ∧
      Θ.toFun (e (e.symm (Θ.invFun u)))=u ∧ Ψ.toFun (e (e.symm (Θ.invFun u)))=Ξ.toFun u := by
    intro u hu
    have hwΘ := Θ.mapsTo_invFun hu.1
    have hwe := hΘt hwΘ
    rw [e.right_inv hwe]
    exact ⟨e.map_target hwe,hwΘ,hu.2,Θ.right_inv u hu.1,rfl⟩
  obtain ⟨Xs,σ,Φ',hXY,_hXp,hΦ's,hσ,hΦ'⟩ := exists_model_coords Ξ Y S₀
    (∅ : Set (Fin E.length)) p p (by simp) (by simp)
    (fun u hu huY => by
      obtain ⟨hy,hyΘ,hyΨ,hΘu,hΨu⟩ := hpt u hu
      have hmem := (hWΘ hy hyΘ).mpr (by rw [hΘu]; exact huY)
      rw [← hΨu]
      exact (hNΨ hy hyΨ).mp (hWN hmem))
  have hΦ'0 : Φ'.toFun 0=0 := by
    have hN0 : Φ'.toFun 0 ∈ complexCoordinatePlane n (n-S₀.card) :=
      (hΦ' 0 Φ'.center_mem_source).2.1.mp (by rw [hΞ0]; simp [coordSubspace])
    ext r
    obtain ⟨t,rfl⟩ := σ.surjective r
    by_cases ht : t ∈ Xs
    · exact hN0 (σ t) ((hσ t).mpr ht)
    · simpa using (hΦ' 0 Φ'.center_mem_source).2.2 t ht
  refine ⟨Finset.univ.filter (fun j : Fin n => n-S₀.card ≤ j.1),fun i => {σ (p i)},
    ⟨LocalHolomorphicEquivAt.comp Θ Φ' hΘ0,fun w hw => hΘt hw.1,?_,?_⟩,fun _ _ => Finset.card_singleton _⟩
  · change Φ'.toFun (Θ.toFun (e x))=0
    rw [hΘ0]
    exact hΦ'0
  · rintro (_ | i) hi y hy hyΦ
    · obtain ⟨hyΘ,huΦ⟩ := hyΦ
      let u := Θ.toFun (e y)
      have huΞ : u ∈ Ξ.source := hΦ's huΦ
      have hinv : Θ.invFun u=e y := Θ.left_inv _ hyΘ
      have hyΨ : e y ∈ Ψ.source := by rw [← hinv]; exact huΞ.2
      have hΞu : Ξ.toFun u=Ψ.toFun (e y) := by change Ψ.toFun (Θ.invFun u)=_; rw [hinv]
      change y ∈ N ↔ Φ'.toFun u ∈ coordSubspace (Finset.univ.filter fun j : Fin n => n-S₀.card ≤ j.1)
      rw [coordSubspace_eq_complexCoordinatePlane]
      exact (hNΨ hy hyΨ).trans (hΞu ▸ (hΦ' u huΦ).2.1)
    · obtain ⟨hyΘ,huΦ⟩ := hyΦ
      let u := Θ.toFun (e y)
      change y ∈ E.get i ↔ Φ'.toFun u ∈ coordSubspace {σ (p i)}
      rw [mem_coordSubspace_singleton,(hΦ' u huΦ).2.2 (p i) (fun h => hpY i hi (hXY h))]
      exact hHΘ i hi hy hyΘ

/-- ONLY genuine original smaller-carrier density supplies the actual noncontained-germ hypotheses internally. -/
theorem actual_normalCrossingsAt_of_nested_density (hn : 0 < n)
    {W N : Set X} {E : List (Set X)} (hWN : W ⊆ N) (hN : IsClosedSubmanifold n N)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W)
    (hNC : normalCrossingsAt (n := n) W E x) : normalCrossingsAt (n := n) N E x := by
  apply actual_normalCrossingsAt_of_nested_germ_noncontainment hn hWN hN hx hNC
  intro i _hi hcontains
  have hfreq : ∃ᶠ y in 𝓝 x,y ∈ W ∧ y ∉ ⋃ H ∈ E,H := mem_closure_iff_frequently.mp (hdense hx)
  obtain ⟨y,⟨hyW,hyE⟩,hyH⟩ := (hfreq.and_eventually hcontains).exists
  exact hyE (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hyH hyW⟩)

end
end Hironaka.HironakaSharpNestedNormalCrossingsInheritance
