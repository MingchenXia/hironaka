/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restriction of a blowup to an open subset

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1, Remark after the definition of extensions ("the definition
of extension arises naturally when we pass to open subsets of the considered ambient variety"), and §2.4
(Proposition `pr:funct`: multiple test blow-ups pull back along smooth morphisms; an open embedding is the case used
in the analytic setting); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), the paragraph after Theorem
1.3 (trivial blowings-up inserted for open embeddings).

Let `π : Y → X` be the blowup of `X` along `C` (`IsBlowupAlong`, a universal property) and
`V ⊆ X` open.  Then the restriction `π⁻¹ V → V` of `π` is the blowup of `V` along `C ∩ V`:

* `isBlowupAlong_restrict` — for any proof `hV` that `π⁻¹ V` is open (the statement does not
  depend on it), `IsBlowupAlong n (C ∩ V) (π|_{π⁻¹V})`;

Ingredients, all about an open subset `V` of a complex manifold:

* `contMDiff_opens_mk` — a holomorphic map with values in `V` is holomorphic into the manifold
  `V`;
* `vanishingIdeal_opens_mem_iff` / `vanishingIdeal_opens_mem_comp_val` — the ideal of `A ∩ V`
  in `V` is the ideal of `A` read on `V` (extension by zero, `HolomorphicIdealSheaves.extendOpens`);
* `pullback_vanishingIdeal_opens` — for `g : Z → V`, `g^* 𝓘_{A ∩ V} = (ι ∘ g)^* 𝓘_A`.

The universal property of the restriction is that of `π`, applied to `ι ∘ g`: the lift lands in
`π⁻¹ V` because `π ∘ h = ι ∘ g` takes values in `V`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupRestrictOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences AnalyticSubsetOpens RelativePrincipalizationSpan

noncomputable section

/-! ### Maps into an open subset -/

section Maps

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- **A holomorphic map with values in an open subset `V` is holomorphic into the manifold
`V`.** -/
theorem contMDiff_opens_mk {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel m) Z] {V : Opens X} {f : Z → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) (hfV : ∀ z, f z ∈ V) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (fun z => (⟨f z, hfV z⟩ : V)) := by
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hfV).continuousAt, ?_⟩
  have h := (contMDiffAt_iff_target.mp (hf z)).2
  convert h using 1
  ext1 z'
  simp only [Function.comp_apply, extChartAt_coe, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

end Maps

/-! ### Vanishing ideals on an open subset -/

section Ideals

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (V : Opens X)

/-- **The ideal of `A ∩ V` in `V` is the ideal of `A`, read through extension by zero.** -/
theorem vanishingIdeal_opens_mem_iff {A : Set X} {x : V} {b : V → ℂ} :
    (vanishingIdeal (n := n) ((↑) ⁻¹' A : Set V)).mem x b ↔
      (vanishingIdeal (n := n) A).mem x.1 (extendOpens V b) := by
  refine and_congr (holomorphicAt_iff_extendOpens V) ?_
  rw [eventually_nhds_val_iff V (P := fun y => y ∈ A → extendOpens V b y = 0)]
  refine Filter.eventually_congr (Eventually.of_forall fun y => ?_)
  simp only [mem_preimage, extendOpens_val]

/-- An ambient germ of `𝓘_A` restricts to a germ of `𝓘_{A ∩ V}`. -/
theorem vanishingIdeal_opens_mem_comp_val {A : Set X} {x : V} {a : X → ℂ}
    (ha : (vanishingIdeal (n := n) A).mem x.1 a) :
    (vanishingIdeal (n := n) ((↑) ⁻¹' A : Set V)).mem x (a ∘ Subtype.val) := by
  refine ⟨(holomorphicAt_comp_val_iff V).mpr ha.1, ?_⟩
  exact (eventually_nhds_val_iff V (P := fun y => y ∈ A → a y = 0)).mp ha.2

/-- **`g^* 𝓘_{A ∩ V} = (ι ∘ g)^* 𝓘_A`** for a map `g` into the open subset `V`. -/
theorem pullback_vanishingIdeal_opens {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel m) Z] (g : Z → V) (A : Set X) :
    GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) ((↑) ⁻¹' A : Set V)) =
      GermIdeal.pullback (m := m) (Subtype.val ∘ g) (vanishingIdeal (n := n) A) := by
  refine GermIdeal.ext (funext fun z => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨b, hb, rfl⟩
    refine ⟨extendOpens V b, (vanishingIdeal_opens_mem_iff V).mp hb, ?_⟩
    funext z'
    simp only [Function.comp_apply, extendOpens_val]
  · refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a ∘ Subtype.val, vanishingIdeal_opens_mem_comp_val V ha, rfl⟩

end Ideals

/-! ### The restriction of a blowup -/

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- The trace of a closed submanifold on an open subset is a closed submanifold of it. -/
theorem isClosedSubmanifold_preimage_val {C : Set X} (hC : IsClosedSubmanifold n C)
    (V : Opens X) : IsClosedSubmanifold n ((↑) ⁻¹' C : Set V) :=
  ⟨hC.1.preimage continuous_subtype_val, fun x hx => by
    obtain ⟨k, hk⟩ := hC.2 x.1 hx
    exact ⟨k, regularAtDim_preimage_val_iff.mpr hk⟩⟩

/-- The trace of a nowhere dense set on an open subset is nowhere dense in it. -/
theorem interior_preimage_val_eq_empty {C : Set X} (hC : interior C = ∅) (V : Opens X) :
    interior ((↑) ⁻¹' C : Set V) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hopen : IsOpen ((↑) '' interior ((↑) ⁻¹' C : Set V) : Set X) :=
    V.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hsub : ((↑) '' interior ((↑) ⁻¹' C : Set V) : Set X) ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (s := ((↑) ⁻¹' C : Set V)) hy
  have hmem : x.1 ∈ interior C := interior_maximal hsub hopen ⟨x, hx, rfl⟩
  rw [hC] at hmem
  exact hmem

/-- **The restriction of a blowup to an open subset is the blowup of that subset along the
trace of the centre.**  Here `hV` is any proof that `π⁻¹ V` is open. -/
theorem isBlowupAlong_restrict (hπ : IsBlowupAlong n C π) (V : Opens X)
    (hV : IsOpen (π ⁻¹' (V : Set X))) :
    IsBlowupAlong n ((↑) ⁻¹' C : Set V)
      (fun p : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : V)) := by
  set W : Opens Y := ⟨π ⁻¹' (V : Set X), hV⟩ with hWdef
  set r : W → V := fun p => (⟨π p.1, p.2⟩ : V) with hrdef
  have hr : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ r :=
    contMDiff_opens_mk (hπ.contMDiff.comp contMDiff_subtype_val) fun p => p.2
  have hvalr : (Subtype.val ∘ r : W → X) = π ∘ Subtype.val := rfl
  refine ⟨isClosedSubmanifold_preimage_val hπ.1 V, interior_preimage_val_eq_empty hπ.2.1 V, hr,
    ?_, ?_⟩
  · rw [pullback_vanishingIdeal_opens V r C, hvalr]
    exact IsInvertible.pullback_comp_val W hπ.2.2.2.1
  · intro m Z _ _ _ g hg hginv
    have hg' : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ g) :=
      contMDiff_subtype_val.comp hg
    rw [pullback_vanishingIdeal_opens V g C] at hginv
    obtain ⟨h, ⟨hh, hπh⟩, huniq⟩ := hπ.2.2.2.2 m Z (Subtype.val ∘ g) hg' hginv
    have hhW : ∀ z, h z ∈ W := fun z => by
      show π (h z) ∈ (V : Set X)
      rw [show π (h z) = (g z).1 from congrFun hπh z]
      exact (g z).2
    refine ⟨fun z => ⟨h z, hhW z⟩, ⟨contMDiff_opens_mk hh hhW, ?_⟩, ?_⟩
    · funext z
      exact Subtype.ext (congrFun hπh z)
    · rintro k ⟨hk, hkr⟩
      have hk' : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ k) :=
        contMDiff_subtype_val.comp hk
      have hπk : π ∘ (Subtype.val ∘ k) = Subtype.val ∘ g := by
        funext z
        exact congrArg Subtype.val (congrFun hkr z)
      have := huniq (Subtype.val ∘ k) ⟨hk', hπk⟩
      funext z
      exact Subtype.ext (congrFun this z)

end Blowup

end

end Hironaka.BlowupRestrictOpen
