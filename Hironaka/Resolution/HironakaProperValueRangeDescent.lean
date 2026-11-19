import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

/-! Proper-map compact-fibre descent for actual finite value ranges.
Blueprint: `hironaka-proper-value-range-descent.tex`.
The analytic production of finite original HS ranges is a separate input. -/

open Set
open scoped Topology

namespace Hironaka.HironakaProperValueRangeDescent

noncomputable section

variable {X Y A B : Type*}

/-- A finite actual range remains finite under any function whose equality
is reflected by the original values on the supplied carrier. -/
theorem finite_image_of_eq_reflection {S : Set Y} {a : Y → A} {b : Y → B}
    (ha : (a '' S).Finite)
    (hab : ∀ y ∈ S, ∀ z ∈ S, a y = a z → b y = b z) :
    (b '' S).Finite := by
  classical
  let : Finite (a '' S) := ha.to_subtype
  let v : (a '' S) → B := fun c => b (Classical.choose c.property)
  apply (Set.finite_range v).subset
  rintro _ ⟨y, hy, rfl⟩
  let c : (a '' S) := ⟨a y, y, hy, rfl⟩
  refine ⟨c, ?_⟩
  exact hab _ (Classical.choose_spec c.property).1 y hy
    (Classical.choose_spec c.property).2

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual properness, a closed source carrier and compact fibre covers
descend local finite composed value ranges to their genuine image. -/
theorem exists_isOpen_finite_image_of_isProperMap {π : Y → X}
    (hπ : IsProperMap π) {S : Set Y} (hS : IsClosed S) (g : X → A)
    (hlocal : ∀ y ∈ S, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ((g ∘ π) '' (S ∩ U)).Finite) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ (g '' ((π '' S) ∩ V)).Finite := by
  classical
  choose U hU hyU hfin using fun y : S => hlocal y y.property
  have hK : IsCompact (S ∩ π ⁻¹' {x}) :=
    (hπ.isCompact_preimage isCompact_singleton).inter_left hS
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU (by
    rintro y ⟨hyS, _hyx⟩
    exact mem_iUnion.mpr ⟨⟨y, hyS⟩, hyU ⟨y, hyS⟩⟩)
  let L : Set Y := ⋃ y ∈ t, U y
  have hL : IsOpen L := isOpen_iUnion fun y => isOpen_iUnion fun _ => hU y
  let V : Set X := (π '' (S \ L))ᶜ
  have hV : IsOpen V := (hπ.isClosedMap _ (hS.sdiff hL)).isOpen_compl
  have hxV : x ∈ V := by
    rintro ⟨y, ⟨hyS, hyL⟩, hyx⟩
    exact hyL (ht ⟨hyS, hyx⟩)
  have hF : (⋃ y ∈ t, (g ∘ π) '' (S ∩ U y)).Finite :=
    t.finite_toSet.biUnion fun y _ => hfin y
  refine ⟨V, hV, hxV, hF.subset ?_⟩
  rintro _ ⟨z, ⟨⟨y, hyS, rfl⟩, hyV⟩, rfl⟩
  have hyL : y ∈ L := by
    by_contra hyL
    exact hyV ⟨y, ⟨hyS, hyL⟩, rfl⟩
  obtain ⟨v, hvt, hyU⟩ := mem_iUnion₂.mp hyL
  exact mem_iUnion₂.mpr ⟨v, hvt, y, ⟨hyS, hyU⟩, rfl⟩

end

end Hironaka.HironakaProperValueRangeDescent
