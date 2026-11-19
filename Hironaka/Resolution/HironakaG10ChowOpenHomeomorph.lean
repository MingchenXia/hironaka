import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Open maps that are injective over a dense set

The topological step of the Chow-side lemma `chow:flat-bimeromorphic-iso`
(blueprint `hironaka-g10-chowside-flat-iso.tex`).  A flat morphism of complex
spaces is open; this file proves, with no analytic input, that an open map from a
Hausdorff space which is injective over a dense subset of the target is injective
everywhere, and that a continuous, open, closed map which is injective over a dense
set it covers is a homeomorphism.  This replaces the fibre-dimension argument of
the blueprint proof: no dimension theory is used.

Main declarations:

* `injective_of_isOpenMap_of_injOn_preimage_dense` — open + injective over a dense set
  ⇒ injective (Hausdorff source; continuity is not needed).
* `surjective_of_isClosedMap_of_dense_subset_range` — closed map whose range contains a
  dense set is surjective.
* `isHomeomorph_of_isOpenMap_of_isClosedMap`, `homeomorphOfOpenClosedInjOnDense` — the
  resulting homeomorphism.
* `isHomeomorph_of_isOpenMap_of_isProperMap` — the same for a proper map.
-/

set_option autoImplicit false

open Set Topology

namespace Hironaka.HironakaG10ChowOpenHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **An open map injective over a dense set is injective.**  If `p : Y → X` is open,
`Y` is Hausdorff, `V ⊆ X` is dense and `p` is injective on `p⁻¹ V`, then `p` is
injective: two distinct points of one fibre have disjoint open neighbourhoods whose
images are open neighbourhoods of the same point, hence meet in a point of `V`, which
then has a preimage in each neighbourhood. -/
theorem injective_of_isOpenMap_of_injOn_preimage_dense [T2Space Y] {p : Y → X}
    (hp : IsOpenMap p) {V : Set X} (hV : Dense V) (hinj : InjOn p (p ⁻¹' V)) :
    Function.Injective p := by
  intro a b hab
  by_contra hne
  obtain ⟨U, U', hU, hU', haU, hbU', hdisj⟩ := t2_separation hne
  have hopen : IsOpen (p '' U ∩ p '' U') := (hp U hU).inter (hp U' hU')
  have hmem : p a ∈ p '' U ∩ p '' U' := ⟨mem_image_of_mem p haU, hab ▸ mem_image_of_mem p hbU'⟩
  obtain ⟨v, ⟨⟨u, huU, rfl⟩, ⟨u', hu'U', hu'⟩⟩, hvV⟩ :=
    hV.inter_open_nonempty _ hopen ⟨p a, hmem⟩
  have huu' : u' = u := hinj (show p u' ∈ V from hu' ▸ hvV) (show p u ∈ V from hvV) hu'
  exact Set.disjoint_left.mp hdisj huU (huu' ▸ hu'U')

/-- A closed map whose range contains a dense set is surjective. -/
theorem surjective_of_isClosedMap_of_dense_subset_range {p : Y → X} (hp : IsClosedMap p)
    {V : Set X} (hV : Dense V) (hVr : V ⊆ range p) : Function.Surjective p := by
  have hclosed : IsClosed (range p) := by
    rw [← image_univ]
    exact hp _ isClosed_univ
  have huniv : range p = univ := by
    apply eq_univ_of_univ_subset
    rw [← hV.closure_eq]
    exact hclosed.closure_subset_iff.mpr hVr
  exact range_eq_univ.mp huniv

/-- A continuous, open and closed map from a Hausdorff space, injective over a dense set
`V` which lies in its range, is bijective. -/
theorem bijective_of_isOpenMap_of_isClosedMap [T2Space Y] {p : Y → X}
    (hpo : IsOpenMap p) (hpc : IsClosedMap p) {V : Set X} (hV : Dense V)
    (hinj : InjOn p (p ⁻¹' V)) (hVr : V ⊆ range p) : Function.Bijective p :=
  ⟨injective_of_isOpenMap_of_injOn_preimage_dense hpo hV hinj,
    surjective_of_isClosedMap_of_dense_subset_range hpc hV hVr⟩

/-- **The homeomorphism criterion.**  A continuous, open and closed map from a Hausdorff
space, injective over a dense set `V` which lies in its range, is a homeomorphism. -/
theorem isHomeomorph_of_isOpenMap_of_isClosedMap [T2Space Y] {p : Y → X}
    (hcont : Continuous p) (hpo : IsOpenMap p) (hpc : IsClosedMap p) {V : Set X}
    (hV : Dense V) (hinj : InjOn p (p ⁻¹' V)) (hVr : V ⊆ range p) : IsHomeomorph p :=
  ⟨hcont, hpo, bijective_of_isOpenMap_of_isClosedMap hpo hpc hV hinj hVr⟩

/-- The bundled homeomorphism of `isHomeomorph_of_isOpenMap_of_isClosedMap`. -/
noncomputable def homeomorphOfOpenClosedInjOnDense [T2Space Y] {p : Y → X}
    (hcont : Continuous p) (hpo : IsOpenMap p) (hpc : IsClosedMap p) {V : Set X}
    (hV : Dense V) (hinj : InjOn p (p ⁻¹' V)) (hVr : V ⊆ range p) : Y ≃ₜ X :=
  (isHomeomorph_of_isOpenMap_of_isClosedMap hcont hpo hpc hV hinj hVr).homeomorph p

@[simp]
theorem homeomorphOfOpenClosedInjOnDense_apply [T2Space Y] {p : Y → X}
    (hcont : Continuous p) (hpo : IsOpenMap p) (hpc : IsClosedMap p) {V : Set X}
    (hV : Dense V) (hinj : InjOn p (p ⁻¹' V)) (hVr : V ⊆ range p) (y : Y) :
    homeomorphOfOpenClosedInjOnDense hcont hpo hpc hV hinj hVr y = p y :=
  rfl

/-- **Proper form.**  An open proper map from a Hausdorff space which is injective over a
dense set `V` lying in its range is a homeomorphism. -/
theorem isHomeomorph_of_isOpenMap_of_isProperMap [T2Space Y] {p : Y → X}
    (hpo : IsOpenMap p) (hpp : IsProperMap p) {V : Set X} (hV : Dense V)
    (hinj : InjOn p (p ⁻¹' V)) (hVr : V ⊆ range p) : IsHomeomorph p :=
  isHomeomorph_of_isOpenMap_of_isClosedMap hpp.continuous hpo hpp.isClosedMap hV hinj hVr

end Hironaka.HironakaG10ChowOpenHomeomorph
