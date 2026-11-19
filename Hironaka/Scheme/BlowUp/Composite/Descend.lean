/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Glue.GlobalCharts
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The descended centre in chart coordinates

The pushforward criterion of `Hironaka.Scheme.BlowUp.Composite` (`mem_ideal_map_iff_of_le_iSup`) in
the coordinates of the charts of the blow-up: for an affine open `U` of `X`, generators `s` of
`I(U)` and an ideal sheaf `L` on the blow-up, a function `x ∈ Γ(X, U)` lies in the pushforward
`(L.map b)(U)` iff its image in every chart ring `Γ(X, U)[I(U)/c]`, `c ∈ s`, lies in the chart
ideal `L_c` (`mem_ideal_map_iff_chart`).  For `L = J' · E^m` this is the chart description of
Hironaka's `J(m)`: `x ∈ I^m` lies in `K_m` iff `x/c^m ∈ J'_c` on every chart.  The transport is
the identification of the pullback of `x` along `chart c ≫ b = Spec (algebraMap) ≫ fromSpec_U`
with `algebraMap x` on global sections (`appLE_chart_mem_ideal_iff`), through
`Scheme.Hom.appIso`, `appLE_comp_appLE`, `IsAffineOpen.SpecMap_appLE_fromSpec` and the
injectivity of `Spec.map`.  Used by `Hironaka.Scheme.BlowUp.Composite.Bound` and for the kernels of
chart maps in `Hironaka.Resolution.Algebraic.MaximalContact.AgreeOnBlowUpKernel`.
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

section Transport

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) {S : Type u} [CommRing S]

/-- The pullback of `x ∈ Γ(X, V)` along `Spec ψ ≫ fromSpec_V`, on global sections, is
`ΓSpecIso⁻¹ (ψ x)`: `Spec` of that pullback map composed with `fromSpec_V` is the morphism itself
(`IsAffineOpen.SpecMap_appLE_fromSpec`), and `Spec.map` is injective. -/
theorem appLE_specMap_fromSpec (ψ : Γ(X, V) →+* S)
    (e : (⊤ : (Spec (.of S)).Opens) ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ V)
    (x : Γ(X, V)) :
    (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).appLE V ⊤ e x =
      (Scheme.ΓSpecIso (.of S)).inv (ψ x) := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    hV (isAffineOpen_top (Spec (.of S))) e
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp] at h1
  have h2 : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).appLE V ⊤ e =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of S)).inv :=
    Spec.map_injective ((cancel_mono hV.fromSpec).mp h1)
  exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Spec (.of S), ⊤) => φ x) h2

/-- `appLE` of a morphism known to factor as `Spec ψ ≫ fromSpec_V`. -/
theorem appLE_eq_of_eq_specMap_fromSpec (g : Spec (.of S) ⟶ X) (ψ : Γ(X, V) →+* S)
    (hg : g = Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    (e : (⊤ : (Spec (.of S)).Opens) ≤ g ⁻¹ᵁ V) (x : Γ(X, V)) :
    g.appLE V ⊤ e x = (Scheme.ΓSpecIso (.of S)).inv (ψ x) := by
  subst hg
  exact appLE_specMap_fromSpec hV ψ e x

end Transport

section Chart

variable {X : Scheme.{u}} (I : X.IdealSheafData) (L : (blowUp I).IdealSheafData)
  (U : X.affineOpens) (c : I.ideal U)

/-- The image of the chart of `c` lies over `U`. -/
theorem chart_image_top_le : blowUp.chart I U c ''ᵁ ⊤ ≤ blowUpπ I ⁻¹ᵁ U.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  intro y hy
  exact blowUp.range_chart_subset I U c (Scheme.Hom.mem_opensRange.mp hy)

/-- The affine open `chart c ''ᵁ ⊤` of the blow-up. -/
noncomputable abbrev chartOpen : (blowUp I).affineOpens :=
  ⟨blowUp.chart I U c ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩

theorem chart_comp_π_eq :
    blowUp.chart I U c ≫ blowUpπ I =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c))) ≫
        U.2.fromSpec := by
  rw [blowUp.chart_π]
  rfl

theorem chart_comp_le : (⊤ : (Spec (.of (affineBlowUpAlgebra (I.ideal U) c))).Opens) ≤
    (blowUp.chart I U c ≫ blowUpπ I) ⁻¹ᵁ U.1 := fun z _ =>
  chart_image_top_le I U c (by rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨z, rfl⟩)

theorem appIso_hom_appLE_chart (x : Γ(X, U)) :
    ((blowUp.chart I U c).appIso ⊤).hom
        ((blowUpπ I).appLE U.1 (blowUp.chart I U c ''ᵁ ⊤) (chart_image_top_le I U c) x) =
      (blowUp.chart I U c ≫ blowUpπ I).appLE U.1 ⊤ (chart_comp_le I U c) x :=
  (congrArg (fun φ : Γ(blowUp I, blowUp.chart I U c ''ᵁ ⊤) ⟶
      Γ(Spec (.of (affineBlowUpAlgebra (I.ideal U) c)), ⊤) =>
        φ ((blowUpπ I).appLE U.1 (blowUp.chart I U c ''ᵁ ⊤) (chart_image_top_le I U c) x))
    (Scheme.Hom.appIso_hom' (blowUp.chart I U c) ⊤)).trans
  (congrArg (fun φ : Γ(X, U) ⟶ Γ(Spec (.of (affineBlowUpAlgebra (I.ideal U) c)), ⊤) => φ x)
    (Scheme.Hom.appLE_comp_appLE (blowUp.chart I U c) (blowUpπ I) U.1 _ ⊤
      (chart_image_top_le I U c) (Scheme.Hom.preimage_image_eq _ ⊤).ge))

theorem appLE_chart_comp_π (x : Γ(X, U)) :
    (blowUp.chart I U c ≫ blowUpπ I).appLE U.1 ⊤ (chart_comp_le I U c) x =
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra (I.ideal U) c))).inv
        (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) x) :=
  appLE_eq_of_eq_specMap_fromSpec U.2 _ _ (chart_comp_π_eq I U c) _ x

/-- The pullback of `x ∈ Γ(X, U)` to the chart of `c`, as a section over `chart c ''ᵁ ⊤`, is the
transport of `algebraMap x ∈ Γ(X, U)[I(U)/c]` along the chart's identification of sections. -/
theorem appLE_chart_eq (x : Γ(X, U)) :
    (blowUpπ I).appLE U.1 (blowUp.chart I U c ''ᵁ ⊤) (chart_image_top_le I U c) x =
      ((blowUp.chart I U c).appIso ⊤).inv
        ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra (I.ideal U) c))).inv
          (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) x)) :=
  (Iso.hom_inv_id_apply ((blowUp.chart I U c).appIso ⊤) _).symm.trans
    (congrArg ((blowUp.chart I U c).appIso ⊤).inv
      ((appIso_hom_appLE_chart I U c x).trans (appLE_chart_comp_π I U c x)))

/-- Membership in the chart ideal, read on the affine open `chart c ''ᵁ ⊤` of the blow-up. -/
theorem mem_chartIdeal_iff (z : affineBlowUpAlgebra (I.ideal U) c) :
    z ∈ chartIdeal I L U c ↔
      ((blowUp.chart I U c).appIso ⊤).inv
        ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra (I.ideal U) c))).inv z) ∈
          L.ideal (chartOpen I U c) :=
  SetLike.ext_iff.mp
    (ideal_comap_of_isOpenImmersion L (blowUp.chart I U c) ⟨⊤, isAffineOpen_top _⟩)
    ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra (I.ideal U) c))).inv z)

/-- The pullback of `x` to the chart of `c` lies in `L` iff `algebraMap x` lies in the chart
ideal `L_c`. -/
theorem appLE_chart_mem_ideal_iff (x : Γ(X, U)) :
    (blowUpπ I).appLE U.1 (chartOpen I U c).1 (chart_image_top_le I U c) x ∈
        L.ideal (chartOpen I U c) ↔
      algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) x ∈ chartIdeal I L U c :=
  (Eq.to_iff (congrArg (fun w => w ∈ L.ideal (chartOpen I U c)) (appLE_chart_eq I U c x))).trans
    (mem_chartIdeal_iff I L U c _).symm

/-- The pushforward criterion in chart coordinates: for generators `s` of `I(U)`, `x ∈ (L.map b)(U)`
iff `algebraMap x ∈ L_c` for every chart `c ∈ s`. -/
theorem mem_ideal_map_iff_chart [IsLocallyNoetherian X] (s : Set (I.ideal U))
    (hs : Ideal.span (Subtype.val '' s) = I.ideal U) (x : Γ(X, U)) :
    x ∈ (L.map (blowUpπ I)).ideal U ↔
      ∀ c ∈ s, algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) x ∈ chartIdeal I L U c := by
  have := blowUp.isProper_π I
  have hcov : blowUpπ I ⁻¹ᵁ U.1 ≤ ⨆ c : s, (chartOpen I U c.1).1 := by
    intro y hy
    have hy' : y ∈ ⋃ a ∈ s, Set.range (blowUp.chart I U a) := by
      rw [blowUp.iUnion_range_chart_of_span_eq I U s hs]
      exact hy
    obtain ⟨a, ha, z, rfl⟩ := Set.mem_iUnion₂.mp hy'
    refine Opens.mem_iSup.mpr ⟨⟨a, ha⟩, ?_⟩
    change blowUp.chart I U a z ∈ blowUp.chart I U a ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩
  refine (mem_ideal_map_iff_of_le_iSup (blowUpπ I) L U (fun c : s => chartOpen I U c.1)
    (fun c => chart_image_top_le I U c.1) hcov x).trans ⟨fun h c hc => ?_, fun h c => ?_⟩
  · exact (appLE_chart_mem_ideal_iff I L U c x).mp (h ⟨c, hc⟩)
  · exact (appLE_chart_mem_ideal_iff I L U c.1 x).mpr (h c.1 c.2)

end Chart

end AlgebraicGeometry
