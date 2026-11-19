import Hironaka.Resolution.HironakaG8GeneralCentreTransverseFrame

set_option autoImplicit false

/-!
# Transverse total exceptional traces from the source normal-crossings data

The normal-crossings definition provides a single coordinate for an incident
boundary member, disjoint from the equations of the centre. Its differential
on the corresponding centre coordinate vector is nonzero. Consequently the
native exceptional strict carrier has points arbitrarily close to an incident
point outside the strict boundary. This is a local total-trace statement and
makes no assertion about a fixed exceptional fibre or the residual successor.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11TransverseTrace

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates
  NormalCrossings HironakaG8GeneralCentreTransverseFrame

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- For a normal-crossings centre, a boundary member which does not contain
the centre as a germ has a defining equation nonconstant to first order on
the centre. -/
theorem local_equation_of_normalCrossings_not_containing {C : Set X}
    {E : List (Set X)} {x : X} (hcross : HasNormalCrossings n C E)
    (hxC : x ∈ C) (i : Fin E.length) (hxi : x ∈ E.get i)
    (hnot : ¬ ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ E.get i) :
    ∃ f : X → ℂ, HolomorphicAt n f x ∧
      (∀ᶠ y in 𝓝 x, y ∈ E.get i ↔ f y = 0) ∧
      ∃ ξ ∈ tangentSpace n C x, germDiff n f x ξ ≠ 0 := by
  obtain ⟨S₀, S, hcoord, hS⟩ := hcross x hxC
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp (hS i hxi)
  obtain ⟨Ω, hΩsrc, hΩ0, hΩ⟩ := hcoord
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ C ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S₀) := by
    intro y hy hyΩ
    exact hΩ none hxC hy hyΩ
  have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ E.get i ↔ flatCoord Ω h y = 0) := by
    intro y hy hyΩ
    have hcoord := hΩ (some i) hxi hy hyΩ
    change y ∈ E.get i ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈
      coordSubspace (S i) at hcoord
    simpa [hh, coordSubspace, flatCoord] using hcoord
  have hhnot : h ∉ S₀ := by
    intro hhS₀
    apply hnot
    filter_upwards [(isOpen_flatDomain Ω).mem_nhds (mem_flatDomain_self Ω)] with y hy hyC
    apply (hflatH hy.1 hy.2).mpr
    have hcoords := (hflatC hy.1 hy.2).mp hyC
    exact hcoords h hhS₀
  exact local_equation_transverse_of_coordinate_crossings Ω hΩsrc hΩ0 S₀ h hhnot hflatC hflatH

/-- A normal-crossings member not containing the centre as a germ misses
points arbitrarily near any incident point of the total exceptional strict
carrier trace. -/
theorem frequently_exceptional_strict_not_boundary_of_normalCrossings
    {C : Set X} [Fact (IsClosedSubmanifold n C)] {P : Set X}
    (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) (hpH : p.base ∈ E.get i)
    (hnot : ¬ ∀ᶠ y in 𝓝 p.base, y ∈ C → y ∈ E.get i) :
    ∃ᶠ q in 𝓝 p, q.base ∈ C ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C (E.get i) := by
  obtain ⟨f, hf, hH, hdiff⟩ :=
    local_equation_of_normalCrossings_not_containing hcross hpC i hpH hnot
  exact frequently_exceptional_strict_not_boundary_of_local_equation hP hCP
    (hE.1 (E.get i) (List.get_mem E i)) hp hpC hpH hf hH hdiff

/-- At an incident normal-crossings centre, either the centre is locally
contained in the member or the total exceptional strict carrier trace
locally escapes its strict transform. -/
theorem centre_germ_contained_or_frequently_strict_not_boundary
    {C : Set X} [Fact (IsClosedSubmanifold n C)] {P : Set X}
    (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) (hpH : p.base ∈ E.get i) :
    (∀ᶠ y in 𝓝 p.base, y ∈ C → y ∈ E.get i) ∨
      ∃ᶠ q in 𝓝 p, q.base ∈ C ∧
        q ∈ geoStrictTransform (blowupProj n C) C P ∧
        q ∉ geoStrictTransform (blowupProj n C) C (E.get i) := by
  by_cases h : ∀ᶠ y in 𝓝 p.base, y ∈ C → y ∈ E.get i
  · exact Or.inl h
  · exact Or.inr (frequently_exceptional_strict_not_boundary_of_normalCrossings
      hP hCP hE hcross i hp hpC hpH h)

/-- An incident member of a divisor transverse to the centre has an actual
local defining equation whose differential is nonzero on the centre. -/
theorem local_equation_of_transverse {C : Set X} {E : List (Set X)} {x : X}
    (htrans : IsTransverse n C E) (hxC : x ∈ C) (i : Fin E.length)
    (hxi : x ∈ E.get i) :
    ∃ f : X → ℂ, HolomorphicAt n f x ∧
      (∀ᶠ y in 𝓝 x, y ∈ E.get i ↔ f y = 0) ∧
      ∃ ξ ∈ tangentSpace n C x, germDiff n f x ξ ≠ 0 := by
  obtain ⟨S₀, S, hcoord, hS⟩ := htrans x hxC
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp (hS i hxi).1
  have hnot : h ∉ S₀ := by
    intro hmem
    exact Finset.disjoint_left.mp (hS i hxi).2 (hh ▸ Finset.mem_singleton_self h) hmem
  obtain ⟨Ω, hΩsrc, hΩ0, hΩ⟩ := hcoord
  apply local_equation_transverse_of_coordinate_crossings Ω hΩsrc hΩ0 S₀ h hnot
  · intro y hy hyΩ
    exact hΩ none hxC hy hyΩ
  · intro y hy hyΩ
    have hcoord := hΩ (some i) hxi hy hyΩ
    change y ∈ E.get i ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈
      NormalCrossings.coordSubspace (S i) at hcoord
    simpa [hh, NormalCrossings.coordSubspace, flatCoord] using hcoord

/-- Source normal crossings, without a chosen adapted chart, imply local
noncontainment of the whole exceptional strict trace in an incident
transverse boundary member. -/
theorem frequently_exceptional_strict_not_boundary_of_transverse
    {C : Set X} [Fact (IsClosedSubmanifold n C)] {P : Set X}
    (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (htrans : IsTransverse n C E)
    (i : Fin E.length) {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) (hpH : p.base ∈ E.get i) :
    ∃ᶠ q in 𝓝 p, q.base ∈ C ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C (E.get i) := by
  obtain ⟨f, hf, hH, hdiff⟩ := local_equation_of_transverse htrans hpC i hpH
  exact frequently_exceptional_strict_not_boundary_of_local_equation hP hCP
    (hE.1 (E.get i) (List.get_mem E i)) hp hpC hpH hf hH hdiff

end

end Hironaka.HironakaG11TransverseTrace
