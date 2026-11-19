import Hironaka.Resolution.HironakaDisjointBlowupCommutation
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupSourceBiholomorphism
import Hironaka.Analytic.RegularPointDimension

/-! # Simultaneous blowup of a locally finite family of pairwise disjoint smooth centres

Lane G3 (run 0080, round 1).  Blueprint: `hironaka-g3-r-simultaneous-blowup.tex`.
Notes: `work/hironaka-resume-20261111/G3/NONCOMPACT-SCHEDULE.md`.

The native blowup `IsBlowupAlong n C π` (universal property) allows a centre with several
components of different dimensions.  For a noncompact base, the global continuation of a
resolution blows up, at one step, a LOCALLY FINITE family of PAIRWISE DISJOINT closed smooth
centres.  This module shows that such a step is ONE native blowup, that it commutes with
restriction to open sets, and that it is the composite of the separate blowups.

* `isClosedSubmanifold_iUnion`, `interior_iUnion_eq_empty`: the union of a locally finite family
  of pairwise disjoint closed submanifolds (with empty interiors) is a closed submanifold (with
  empty interior) -- locally it is one member;
* `exists_isBlowupAlong_iUnion`: the simultaneous blowup exists (Demailly's blowup);
* `isBlowupAlong_restrict_iUnion`, `isBlowupAlong_restrict_iUnion_of_disjoint`: restricted to an
  open `V`, it is the simultaneous blowup of `V` along the traces, and only the members meeting
  `V` count (in particular the blowup of `V` along the one member it meets, or an isomorphism);
* `isInvertible_pullback_vanishingIdeal_union_iff`: for disjoint closed `C, D`,
  `g^* 𝓘_{C ∪ D}` is invertible iff `g^* 𝓘_C` and `g^* 𝓘_D` are;
* **`isBlowupAlong_union_comp`**: the blowup `ρ` along `C` followed by the blowup along
  `ρ⁻¹ D` (`D` disjoint from `C`) is THE blowup along `C ∪ D` -- so the simultaneous blowup of two
  disjoint centres is (up to unique isomorphism over the base) the composite in either order
  (`HironakaDisjointBlowupCommutation.disjoint_double_blowup_comparison`), and by restriction
  the simultaneous blowup of a locally finite family is, over every open set meeting only finitely
  many members, a finite composite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RSimultaneousBlowup

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers RelativePrincipalizationSpan

/-! ### The union of a locally finite family of pairwise disjoint closed submanifolds -/

section Union

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {ι : Type*} {C : ι → Set X}

/-- Near a point of one member, a locally finite pairwise disjoint family of closed sets is that
member: the union of the OTHER members is closed and misses the point. -/
theorem exists_open_iUnion_inter_eq (hlf : LocallyFinite C) (hcl : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (Disjoint on C)) {j : ι} {x : X} (hx : x ∈ C j) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (⋃ i, C i) ∩ O = C j ∩ O := by
  classical
  let F : {i // i ≠ j} → Set X := fun i => C i.1
  have hF : LocallyFinite F := hlf.comp_injective Subtype.val_injective
  have hFc : IsClosed (⋃ i, F i) := hF.isClosed_iUnion fun i => hcl i.1
  refine ⟨(⋃ i, F i)ᶜ, hFc.isOpen_compl, ?_, ?_⟩
  · simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro i hi
    exact disjoint_left.mp (hdisj i.2.symm) hx hi
  · ext y
    simp only [mem_inter_iff, mem_iUnion, mem_compl_iff, not_exists, F]
    constructor
    · rintro ⟨⟨i, hi⟩, hO⟩
      by_cases hij : i = j
      · subst hij; exact ⟨hi, hO⟩
      · exact absurd hi (hO ⟨i, hij⟩)
    · rintro ⟨hy, hO⟩
      exact ⟨⟨j, hy⟩, hO⟩

/-- **The union of a locally finite family of pairwise disjoint closed submanifolds is a closed
submanifold.** -/
theorem isClosedSubmanifold_iUnion (hlf : LocallyFinite C) (hdisj : Pairwise (Disjoint on C))
    (hC : ∀ i, IsClosedSubmanifold n (C i)) : IsClosedSubmanifold n (⋃ i, C i) := by
  refine ⟨hlf.isClosed_iUnion fun i => (hC i).1, fun x hx => ?_⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  obtain ⟨O, hO, hxO, hOeq⟩ := exists_open_iUnion_inter_eq hlf (fun i => (hC i).1) hdisj hxj
  obtain ⟨k, hk⟩ := (hC j).2 x hxj
  exact ⟨k, RegularPointDimension.regularAtDim_of_inter_eq hO hxO hOeq.symm hk⟩

/-- **The union of a locally finite family of pairwise disjoint closed nowhere dense sets is
nowhere dense** (here: has empty interior). -/
theorem interior_iUnion_eq_empty (hlf : LocallyFinite C) (hcl : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (Disjoint on C)) (hint : ∀ i, interior (C i) = ∅) :
    interior (⋃ i, C i) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (interior_subset hx)
  obtain ⟨O, hO, hxO, hOeq⟩ := exists_open_iUnion_inter_eq hlf hcl hdisj hxj
  have hsub : interior (⋃ i, C i) ∩ O ⊆ C j := by
    intro y hy
    have : y ∈ (⋃ i, C i) ∩ O := ⟨interior_subset hy.1, hy.2⟩
    rw [hOeq] at this
    exact this.1
  have hmem : x ∈ interior (C j) := interior_maximal hsub (isOpen_interior.inter hO) ⟨hx, hxO⟩
  rw [hint j] at hmem
  exact hmem

/-- **The simultaneous blowup exists.** -/
theorem exists_isBlowupAlong_iUnion (hlf : LocallyFinite C) (hdisj : Pairwise (Disjoint on C))
    (hC : ∀ i, IsClosedSubmanifold n (C i)) (hint : ∀ i, interior (C i) = ∅) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (π : Z → X), IsBlowupAlong n (⋃ i, C i) π :=
  BlowupExistence.exists_isBlowupAlong _ (isClosedSubmanifold_iUnion hlf hdisj hC)
    (interior_iUnion_eq_empty hlf (fun i => (hC i).1) hdisj hint)

end Union

/-! ### Restriction to open sets -/

section Restrict

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {ι : Type*} {C : ι → Set X} {π : Y → X}

/-- **The simultaneous blowup commutes with restriction to open sets**: over an open `V` it is the
simultaneous blowup of `V` along the traces of the members. -/
theorem isBlowupAlong_restrict_iUnion (hπ : IsBlowupAlong n (⋃ i, C i) π) (V : Opens X)
    (hV : IsOpen (π ⁻¹' (V : Set X))) :
    IsBlowupAlong n (⋃ i, ((↑) ⁻¹' C i : Set V))
      (fun p : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : V)) := by
  have h := BlowupRestrictOpen.isBlowupAlong_restrict hπ V hV
  rwa [preimage_iUnion] at h

/-- **Only the members meeting `V` count**: if every member outside `S` misses `V`, the restriction
to `V` is the blowup of `V` along the traces of the members in `S`. -/
theorem isBlowupAlong_restrict_iUnion_of_disjoint (hπ : IsBlowupAlong n (⋃ i, C i) π)
    (V : Opens X) (hV : IsOpen (π ⁻¹' (V : Set X))) (S : Set ι)
    (hS : ∀ i, i ∉ S → Disjoint (C i) (V : Set X)) :
    IsBlowupAlong n (⋃ i ∈ S, ((↑) ⁻¹' C i : Set V))
      (fun p : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : V)) := by
  have h := isBlowupAlong_restrict_iUnion hπ V hV
  have heq : (⋃ i, ((↑) ⁻¹' C i : Set V)) = ⋃ i ∈ S, ((↑) ⁻¹' C i : Set V) := by
    ext p
    simp only [mem_iUnion, mem_preimage, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hiS : i ∈ S
      · exact ⟨i, hiS, hi⟩
      · exact absurd p.2 (disjoint_left.mp (hS i hiS) hi)
    · rintro ⟨i, -, hi⟩
      exact ⟨i, hi⟩
  rwa [heq] at h

/-- Over an open set meeting exactly one member `C j`, the simultaneous blowup is the blowup along
the trace of `C j`. -/
theorem isBlowupAlong_restrict_iUnion_of_single (hπ : IsBlowupAlong n (⋃ i, C i) π)
    (V : Opens X) (hV : IsOpen (π ⁻¹' (V : Set X))) (j : ι)
    (hS : ∀ i, i ≠ j → Disjoint (C i) (V : Set X)) :
    IsBlowupAlong n ((↑) ⁻¹' C j : Set V)
      (fun p : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : V)) := by
  have h := isBlowupAlong_restrict_iUnion_of_disjoint hπ V hV {j} (fun i hi => hS i hi)
  simpa only [mem_singleton_iff, iUnion_iUnion_eq_left] using h

end Restrict

/-! ### Germs of the ideal of a disjoint union -/

section Germs

variable {n m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Type*} [TopologicalSpace W] [ChartedSpace (ComplexModel m) W]
  [IsManifold 𝓘(ℂ, ComplexModel m) ∞ W]

/-- Away from a closed set `D`, the ideal of `C ∪ D` is the ideal of `C`. -/
theorem vanishingIdeal_union_mem_eq_left {C D : Set X} (hD : IsClosed D) {x : X} (hx : x ∉ D) :
    (vanishingIdeal (n := n) (C ∪ D)).mem x = (vanishingIdeal (n := n) C).mem x := by
  funext g
  refine propext (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
  · filter_upwards [h] with y hy hyC
    exact hy (Or.inl hyC)
  · filter_upwards [h, hD.isOpen_compl.mem_nhds hx] with y hy hyD hyCD
    rcases hyCD with hyC | hyD'
    · exact hy hyC
    · exact absurd hyD' hyD

/-- Away from a closed set `C`, the ideal of `C ∪ D` is the ideal of `D`. -/
theorem vanishingIdeal_union_mem_eq_right {C D : Set X} (hC : IsClosed C) {x : X} (hx : x ∉ C) :
    (vanishingIdeal (n := n) (C ∪ D)).mem x = (vanishingIdeal (n := n) D).mem x := by
  rw [union_comm]
  exact vanishingIdeal_union_mem_eq_left hC hx

/-- The unit ideal sheaf (generated by `1`). -/
def unitIdeal (m : ℕ) (W : Type*) [TopologicalSpace W] [ChartedSpace (ComplexModel m) W] :
    GermIdeal m W where
  mem y g := IsInSpanAt (n := m) (· = fun _ => (1 : ℂ)) y g

/-- The unit ideal is invertible. -/
theorem isInvertible_unitIdeal : (unitIdeal m W).IsInvertible := by
  intro y
  refine ⟨univ, isOpen_univ, mem_univ y, fun _ => (1 : ℂ), ?_, ?_, fun _ _ _ => Iff.rfl⟩
  · exact mdifferentiableOn_const
  · rintro O - - ⟨w, hw⟩
    exact ⟨w, hw, (one_ne_zero : (1 : ℂ) ≠ 0)⟩

/-- Invertibility is local: an ideal which near every point agrees with SOME invertible ideal is
invertible. -/
theorem isInvertible_of_locally_eq (𝔞 : GermIdeal m W)
    (h : ∀ w : W, ∃ O : Set W, IsOpen O ∧ w ∈ O ∧ ∃ 𝔟 : GermIdeal m W, 𝔟.IsInvertible ∧
      ∀ y ∈ O, 𝔞.mem y = 𝔟.mem y) : 𝔞.IsInvertible := by
  intro w
  obtain ⟨O, hO, hwO, 𝔟, h𝔟, heq⟩ := h w
  obtain ⟨U, hU, hwU, f, hf, hnon, hgen⟩ := h𝔟 w
  refine ⟨U ∩ O, hU.inter hO, ⟨hwU, hwO⟩, f, hf.mono inter_subset_left,
    fun V hV hVsub hVne => hnon V hV (hVsub.trans inter_subset_left) hVne, fun y hy g => ?_⟩
  rw [heq y hy.2]
  exact hgen y hy.1 g

/-- Off a closed set `A`, the pullback of its ideal is the unit ideal. -/
theorem pullback_vanishingIdeal_mem_eq_unit {f : W → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) {A : Set X} (hA : IsClosed A)
    {y : W} (hy : f y ∉ A) :
    (GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) A)).mem y = (unitIdeal m W).mem y := by
  funext g
  refine propext ⟨fun hg => ?_, fun hg => ?_⟩
  · show IsInSpanAt (n := m) (· = fun _ => (1 : ℂ)) y g
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨a, ha, rfl⟩
    have hs : HolomorphicAt m (a ∘ f) y :=
      ha.1.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
    exact isInSpanAt_of_eq_mul rfl hs hs (Eventually.of_forall fun _ => (mul_one _).symm)
  · have hg' : IsInSpanAt (n := m) (· = fun _ => (1 : ℂ)) y g := hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg')
    rintro s rfl
    refine ⟨fun _ => (1 : ℂ), ⟨holomorphicAt_const 1, ?_⟩, rfl⟩
    filter_upwards [hA.isOpen_compl.mem_nhds hy] with x hx hxA
    exact absurd hxA hx

/-- The pullback of an ideal at `y` only depends on the ideal at `f y`. -/
theorem pullback_mem_eq_of_mem_eq {f : W → X} {𝔞 𝔟 : GermIdeal n X} {y : W}
    (h : 𝔞.mem (f y) = 𝔟.mem (f y)) :
    (GermIdeal.pullback (m := m) f 𝔞).mem y = (GermIdeal.pullback (m := m) f 𝔟).mem y := by
  show (fun g => IsInSpanAt (n := m) (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g) =
    fun g => IsInSpanAt (n := m) (fun s => ∃ a, 𝔟.mem (f y) a ∧ s = a ∘ f) y g
  rw [h]

/-- **The pullback of the ideal of a disjoint union of two closed sets is invertible iff both
pullbacks are.** -/
theorem isInvertible_pullback_vanishingIdeal_union_iff {f : W → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) {C D : Set X}
    (hC : IsClosed C) (hD : IsClosed D) (hCD : Disjoint C D) :
    (GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) (C ∪ D))).IsInvertible ↔
      (GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) C)).IsInvertible ∧
        (GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) D)).IsInvertible := by
  have hoC : IsOpen (f ⁻¹' Cᶜ) := hC.isOpen_compl.preimage hf.continuous
  have hoD : IsOpen (f ⁻¹' Dᶜ) := hD.isOpen_compl.preimage hf.continuous
  constructor
  · intro h
    refine ⟨isInvertible_of_locally_eq _ fun w => ?_, isInvertible_of_locally_eq _ fun w => ?_⟩
    · by_cases hwD : f w ∈ D
      · have hwC : f w ∉ C := fun hc => disjoint_left.mp hCD hc hwD
        exact ⟨_, hoC, hwC, unitIdeal m W, isInvertible_unitIdeal, fun y hy =>
          pullback_vanishingIdeal_mem_eq_unit hf hC hy⟩
      · exact ⟨_, hoD, hwD, _, h, fun y hy =>
          (pullback_mem_eq_of_mem_eq (vanishingIdeal_union_mem_eq_left hD hy)).symm⟩
    · by_cases hwC : f w ∈ C
      · have hwD : f w ∉ D := fun hd => disjoint_left.mp hCD hwC hd
        exact ⟨_, hoD, hwD, unitIdeal m W, isInvertible_unitIdeal, fun y hy =>
          pullback_vanishingIdeal_mem_eq_unit hf hD hy⟩
      · exact ⟨_, hoC, hwC, _, h, fun y hy =>
          (pullback_mem_eq_of_mem_eq (vanishingIdeal_union_mem_eq_right hC hy)).symm⟩
  · rintro ⟨h₁, h₂⟩
    refine isInvertible_of_locally_eq _ fun w => ?_
    by_cases hwD : f w ∈ D
    · have hwC : f w ∉ C := fun hc => disjoint_left.mp hCD hc hwD
      exact ⟨_, hoC, hwC, _, h₂, fun y hy =>
        pullback_mem_eq_of_mem_eq (vanishingIdeal_union_mem_eq_right hC hy)⟩
    · exact ⟨_, hoD, hwD, _, h₁, fun y hy =>
        pullback_mem_eq_of_mem_eq (vanishingIdeal_union_mem_eq_left hD hy)⟩

end Germs

/-! ### The simultaneous blowup of two disjoint centres is the composite -/

section Composite

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Two disjoint closed submanifolds with empty interiors: their union is one. -/
theorem union_geometry {C D : Set X} (hC : IsClosedSubmanifold n C) (hCint : interior C = ∅)
    (hD : IsClosedSubmanifold n D) (hDint : interior D = ∅) (hCD : Disjoint C D) :
    IsClosedSubmanifold n (C ∪ D) ∧ interior (C ∪ D) = ∅ := by
  let F : Bool → Set X := fun b => cond b C D
  have hU : (⋃ b, F b) = C ∪ D := by
    ext x; simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true, F, mem_union]
    exact or_comm
  have hlf : LocallyFinite F := locallyFinite_of_finite F
  have hdisj : Pairwise (Disjoint on F) := by
    intro a b hab
    cases a <;> cases b
    · exact absurd rfl hab
    · exact hCD.symm
    · exact hCD
    · exact absurd rfl hab
  have hF : ∀ b, IsClosedSubmanifold n (F b) := fun b => by cases b <;> assumption
  have hFi : ∀ b, interior (F b) = ∅ := fun b => by cases b <;> assumption
  rw [← hU]
  exact ⟨isClosedSubmanifold_iUnion hlf hdisj hF,
    interior_iUnion_eq_empty hlf (fun b => (hF b).1) hdisj hFi⟩

/-- **The blowup along `C` followed by the blowup along the preimage of a disjoint `D` is THE
blowup along `C ∪ D`.**  Hence (`BlowupUniqueness`) the simultaneous blowup of two disjoint
centres is, uniquely over the base, the composite of the two blowups, in either order. -/
theorem isBlowupAlong_union_comp {C D : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (hD : IsClosedSubmanifold n D) (hDint : interior D = ∅) (hCD : Disjoint C D)
    {q : Z → Y} (hq : IsBlowupAlong n (ρ ⁻¹' D) q) : IsBlowupAlong n (C ∪ D) (ρ ∘ q) := by
  obtain ⟨hU, hUint⟩ := union_geometry hρ.1 hρ.2.1 hD hDint hCD
  obtain ⟨B₀, tB, cB, mB, πB, hπB⟩ := BlowupExistence.exists_isBlowupAlong (C ∪ D) hU hUint
  let : TopologicalSpace B₀ := tB
  let : ChartedSpace (ComplexModel n) B₀ := cB
  let : IsComplexManifold n B₀ := mB
  let B : CMfd.{u} n := ⟨B₀⟩
  have hπB' : IsBlowupAlong n (C ∪ D) (πB : B → X) := hπB
  have hcohD : (vanishingIdeal (n := n) D).IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal hD
  have hρD : GermIdeal.pullback (m := n) ρ (vanishingIdeal (n := n) D) =
      vanishingIdeal (n := n) (ρ ⁻¹' D) :=
    FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hρ hD.1 hCD
  -- `πB` factors through `ρ` and then through `q`
  obtain ⟨hInvC, hInvD⟩ := (isInvertible_pullback_vanishingIdeal_union_iff hπB'.contMDiff hρ.1.1 hD.1
    hCD).mp hπB'.2.2.2.1
  obtain ⟨a, ⟨ha, hρa⟩, -⟩ := hρ.2.2.2.2 n B πB hπB'.contMDiff hInvC
  have hInvA : (GermIdeal.pullback (m := n) a (vanishingIdeal (n := n) (ρ ⁻¹' D))).IsInvertible := by
    rw [← hρD, ← GermIdealTotalTransform.pullback_comp hρ.contMDiff ha hcohD, hρa]
    exact hInvD
  obtain ⟨e, ⟨he, hqe⟩, -⟩ := hq.2.2.2.2 n B a ha hInvA
  -- `ρ ∘ q` factors through `πB`
  have hInvCq : (GermIdeal.pullback (m := n) (ρ ∘ q) (vanishingIdeal (n := n) C)).IsInvertible := by
    rw [GermIdealTotalTransform.pullback_comp hρ.contMDiff hq.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hρ)]
    exact GermIdealTotalTransform.isInvertible_pullback hq.contMDiff
      (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hq) hρ.2.2.2.1
  have hInvDq : (GermIdeal.pullback (m := n) (ρ ∘ q) (vanishingIdeal (n := n) D)).IsInvertible := by
    rw [GermIdealTotalTransform.pullback_comp hρ.contMDiff hq.contMDiff hcohD, hρD]
    exact hq.2.2.2.1
  have hρq : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (ρ ∘ q) :=
    hρ.contMDiff.comp hq.contMDiff
  obtain ⟨b, ⟨hb, hπb⟩, -⟩ := hπB'.2.2.2.2 n Z (ρ ∘ q) hρq
    ((isInvertible_pullback_vanishingIdeal_union_iff hρq hρ.1.1 hD.1 hCD).mpr ⟨hInvCq, hInvDq⟩)
  -- the two comparisons are inverse
  have hbe : b ∘ e = id := BlowupUniqueness.eq_id_of_comp_eq hπB' (hb.comp he) (by
    calc πB ∘ (b ∘ e) = (πB ∘ b) ∘ e := rfl
      _ = (ρ ∘ q) ∘ e := by rw [hπb]
      _ = ρ ∘ (q ∘ e) := rfl
      _ = ρ ∘ a := by rw [hqe]
      _ = πB := hρa)
  have heb : e ∘ b = id := by
    obtain ⟨_, _, huniq⟩ := hρ.2.2.2.2 n Z (ρ ∘ q) hρq hInvCq
    have h1 : q ∘ (e ∘ b) = q := by
      refine (huniq (q ∘ (e ∘ b)) ⟨hq.contMDiff.comp (he.comp hb), ?_⟩).trans
        (huniq q ⟨hq.contMDiff, rfl⟩).symm
      calc ρ ∘ (q ∘ (e ∘ b)) = (ρ ∘ (q ∘ e)) ∘ b := rfl
        _ = (ρ ∘ a) ∘ b := by rw [hqe]
        _ = πB ∘ b := by rw [hρa]
        _ = ρ ∘ q := hπb
    exact BlowupUniqueness.eq_id_of_comp_eq hq (he.comp hb) h1
  let χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B :=
    ⟨⟨b, e, congrFun heb, congrFun hbe⟩, hb, he⟩
  have hfin := HironakaSharpActualCurveSuccessorLocalBlowup.isBlowupAlong_comp_diffeomorph χ hπB'
  have hcomp : (πB : B → X) ∘ χ = ρ ∘ q := hπb
  rwa [hcomp] at hfin

end Composite

end

end Hironaka.HironakaG3RSimultaneousBlowup
