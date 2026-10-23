import DeJongAlterations.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Composition of alterations

Quasi-finiteness at the generic point gives an actual finite target neighbourhood for a proper
morphism with integral source. This proves composition without a finiteness assumption on either
whole alteration.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations

universe u

variable {X Y Z : Scheme.{u}}

/-- A dominant morphism between integral schemes maps generic points to generic points. -/
theorem genericPoint_map_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness over a nonempty target open gives quasi-finiteness at the generic point. -/
theorem IsGenericallyFinite.quasiFiniteAt_genericPoint (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (hf : IsGenericallyFinite f) :
    f.QuasiFiniteAt (genericPoint X) := by
  obtain ⟨U, hU, hfin⟩ := hf
  let := hfin
  have hηY : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηX : genericPoint X ∈ f ⁻¹ᵁ U := by
    change f (genericPoint X) ∈ U
    rw [genericPoint_map_of_isDominant f]
    exact hηY
  have hq := (f ∣_ U).quasiFiniteAt ⟨genericPoint X, hηX⟩
  have hq' := (Scheme.Hom.quasiFiniteAt_comp_iff
    (f := f ∣_ U) (g := U.ι) (x := ⟨genericPoint X, hηX⟩)).mpr hq
  rw [morphismRestrict_ι] at hq'
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := (f ⁻¹ᵁ U).ι) (g := f) (x := ⟨genericPoint X, hηX⟩)).mp hq'

/-- For a proper morphism with integral source, quasi-finiteness at the generic point
produces a genuine finite target neighbourhood. -/
theorem isGenericallyFinite_of_quasiFiniteAt_genericPoint (f : X ⟶ Y)
    [IsIntegral X] [IsProper f] (hq : f.QuasiFiniteAt (genericPoint X)) :
    IsGenericallyFinite f := by
  have hc := hq.isClopen_singleton_asFiber.isClosed
  have heq (z : f.fiber (f (genericPoint X))) : z = f.asFiber (genericPoint X) := by
    have hs : f.asFiber (genericPoint X) ⤳ z := by
      apply (f.fiberι _).isEmbedding.isInducing.specializes_iff.mp
      rw [Scheme.Hom.fiberι_asFiber]
      exact genericPoint_specializes _
    exact Set.mem_singleton_iff.mp (hs.mem_closed hc (Set.mem_singleton _))
  let : Subsingleton (f.fiber (f (genericPoint X))) :=
    ⟨fun a b ↦ (heq a).trans (heq b).symm⟩
  have hfinite : (f ⁻¹' {f (genericPoint X)}).Finite :=
    (f.fiberHomeo _).finite_iff.mp inferInstance
  obtain ⟨U, hU, hfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f _ hfinite
  exact ⟨U, ⟨⟨f (genericPoint X), hU⟩⟩, hfin⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite of two alterations is an alteration. -/
theorem IsAlteration.comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : IsAlteration f] [hg : IsAlteration g] : IsAlteration (f ≫ g) := by
  let := hf.sourceIntegral
  let := hf.targetIntegral
  let := hg.targetIntegral
  have hqf := hf.genericallyFinite.quasiFiniteAt_genericPoint f
  have hqg : g.QuasiFiniteAt (f (genericPoint X)) := by
    rw [genericPoint_map_of_isDominant f]
    exact hg.genericallyFinite.quasiFiniteAt_genericPoint g
  have hqcomp : (f ≫ g).QuasiFiniteAt (genericPoint X) := by
    change ((f ≫ g).stalkMap (genericPoint X)).hom.QuasiFinite
    simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] using
      (show (f.stalkMap (genericPoint X)).hom.QuasiFinite from hqf).comp
        (show (g.stalkMap (f (genericPoint X))).hom.QuasiFinite from hqg)
  exact {
    sourceIntegral := hf.sourceIntegral
    targetIntegral := hg.targetIntegral
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint (f ≫ g) hqcomp }

end DeJongAlterations
