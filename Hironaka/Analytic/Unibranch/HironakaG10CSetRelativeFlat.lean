import Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

/-! # Relative flatness at the tracked part of Hironaka's C_i -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat

open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

noncomputable section

/-- If the support of a local flattener is relatively open in `C`, then its
  stalk ideal at a common point vanishes on the reduced germ of `C`. -/
theorem flattener_le_vanishing_of_relOpen {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (Z : LocalFlattener f) (C : Set X.obj.left)
    (hrel : IsRelOpen C Z.support) {x : X.obj.left} (hxC : x ∈ C) (hxZ : x ∈ Z.support) :
    Z.H x ≤ vanishingIdealAt X.obj.left C x := by
  obtain ⟨U,hU,hCU⟩ := hrel
  have hxU : x ∈ U := ((Set.ext_iff.mp hCU x).mp ⟨hxC,hxZ⟩).2
  obtain ⟨W,hxW,r,s,hs⟩ := Z.fg x hxZ.1
  let T : Opens X.obj.left.toTopCat := W ⊓ ⟨U,hU⟩ ⊓ ⟨Z.V,Z.isOpen⟩
  have hxT : x ∈ T := ⟨⟨hxW,hxU⟩,hxZ.1⟩
  have hTW : T ≤ W := inf_le_left.trans inf_le_left
  rw [hs x hxW hxZ.1, Ideal.span_le]
  rintro _ ⟨k,rfl⟩
  apply Ideal.subset_span
  refine ⟨T,hxT,X.obj.left.presheaf.map (homOfLE hTW).op (s k), ?_, ?_⟩
  · exact X.obj.left.presheaf.germ_res_apply (homOfLE hTW) x hxT (s k)
  · intro y hy hyC
    have hyZ : y ∈ Z.support := ((Set.ext_iff.mp hCU y).mpr ⟨hyC,hy.1.2⟩).2
    have hgen : X.obj.left.presheaf.germ W y (hTW hy) (s k) ∈ Z.H y := by
      rw [hs y (hTW hy) hy.2]
      exact Ideal.subset_span ⟨k,rfl⟩
    have hmax := IsLocalRing.le_maximalIdeal hyZ.2 hgen
    rw [X.obj.left.presheaf.germ_res_apply (homOfLE hTW) y hy (s k)]
    exact hmax

/-- Relative openness of a tracked flattener on `C` excludes relative
  non-flat points of `f/C` on its support. -/
theorem relNonflat_disjoint_support_of_relOpen {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (Z : LocalFlattener f) (C : Set X.obj.left)
    (hrel : IsRelOpen C Z.support) : relNonflat f C ∩ Z.support = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hxC, hxZ⟩
  have hle := flattener_le_vanishing_of_relOpen f Z C hrel hxC.1 hxZ
  exact hxC.2 ((Z.flattener x hxZ.1 hxZ.2 _).2 hle)

/-- Hironaka 4.5.1(2) for the actual selected higher-stratum set. -/
theorem cset_relNonflat_disjoint_tracked {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f) (i : ℕ)
    (hfinite : (selectedHigherComponents f B (fun p => (Z p).support) i).Finite)
    (hmax : ∀ jC ∈ badComponents f B (fun p => (Z p).support), jC.1 ≤ i) :
    ∀ p, relNonflat f (Cset f B (fun p => (Z p).support) i) ∩ (Z p).support = ∅ := by
  have hrel := (Cset_closed_relOpen_and_nonflat f B (fun p => (Z p).support) i hfinite hmax).2.2.1
  exact fun p => relNonflat_disjoint_support_of_relOpen f (Z p) _ (hrel p)

end
end Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat
