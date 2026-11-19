import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper shrinking of the base along a closed bad locus

For a closed (e.g. proper) map `f : X → Y` and ANY open "good" locus `W ⊆ X`
(for G10: the open flat locus, once its openness is proved), the set of base
points whose WHOLE fibre is good is open; it is the complement of the closed
image of the closed bad locus. Hence if the fibres over a set `K` are good, one
open neighbourhood of `K` has an entirely good preimage, and the good preimage
over it is the full restricted family. This is the purely topological core of
the proper-shrinking step; it does NOT prove openness of the flat locus.
BP FIRST: hironaka-g10-flat-proper-shrinking.tex. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG10FlatProperShrinking

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The base points with entirely good fibre are EXACTLY the complement of the
image of the bad locus. -/
theorem setOf_fibre_subset_eq_compl_image (W : Set X) :
    {y : Y | f ⁻¹' {y} ⊆ W} = (f '' Wᶜ)ᶜ := by
  ext y
  simp only [Set.mem_ofPred_eq, mem_compl_iff, mem_image, not_exists, not_and]
  constructor
  · intro h x hx hfx
    exact hx (h hfx)
  · intro h x hfx
    by_contra hx
    exact h x hx hfx

/-- Closed bad locus, closed map: the bad base locus `f(X \ W)` is closed. -/
theorem isClosed_image_compl (hf : IsClosedMap f) {W : Set X} (hW : IsOpen W) :
    IsClosed (f '' Wᶜ) :=
  hf _ hW.isClosed_compl

/-- For a closed map and an open good locus, the base points with entirely good
fibre form an OPEN set. -/
theorem isOpen_setOf_fibre_subset (hf : IsClosedMap f) {W : Set X} (hW : IsOpen W) :
    IsOpen {y : Y | f ⁻¹' {y} ⊆ W} := by
  rw [setOf_fibre_subset_eq_compl_image]
  exact (isClosed_image_compl hf hW).isOpen_compl

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The preimage of the good base set lies in the good locus. -/
theorem preimage_setOf_fibre_subset_subset (W : Set X) :
    f ⁻¹' {y : Y | f ⁻¹' {y} ⊆ W} ⊆ W :=
  fun _ hx => hx rfl

/-- Proper shrinking: if every fibre over `K` is good, ONE open neighbourhood `V`
of `K` has its WHOLE preimage in the good locus. -/
theorem exists_open_nhds_preimage_subset (hf : IsClosedMap f) {W : Set X} (hW : IsOpen W)
    {K : Set Y} (hK : f ⁻¹' K ⊆ W) :
    ∃ V : Set Y, IsOpen V ∧ K ⊆ V ∧ f ⁻¹' V ⊆ W :=
  ⟨{y : Y | f ⁻¹' {y} ⊆ W}, isOpen_setOf_fibre_subset hf hW,
    fun y hy x hx => hK (by simpa only [mem_preimage, mem_singleton_iff.mp hx] using hy),
    preimage_setOf_fibre_subset_subset W⟩

/-- The same for a proper map, phrased with an open good PROPERTY of source points
(e.g. relative flatness of the stalk): the set of base points over which the
property holds at EVERY source point is open. -/
theorem isOpen_setOf_forall_fibre_of_isProperMap (hf : IsProperMap f) {P : X → Prop}
    (hP : IsOpen {x : X | P x}) :
    IsOpen {y : Y | ∀ x : X, f x = y → P x} := by
  exact isOpen_setOf_fibre_subset hf.isClosedMap hP

/-- Pointwise proper shrinking for a proper map and an open good property: if the
property holds at every point of the fibre over `y`, it holds on the whole
preimage of one open neighbourhood of `y`. -/
theorem exists_open_nhds_forall_of_isProperMap (hf : IsProperMap f) {P : X → Prop}
    (hP : IsOpen {x : X | P x}) {y : Y} (hy : ∀ x : X, f x = y → P x) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ x : X, f x ∈ V → P x := by
  obtain ⟨V,hV,hyV,hVW⟩ := exists_open_nhds_preimage_subset hf.isClosedMap hP
    (K := {y}) (fun x hx => hy x hx)
  exact ⟨V,hV,hyV rfl,fun x hx => hVW hx⟩

end Hironaka.HironakaG10FlatProperShrinking
