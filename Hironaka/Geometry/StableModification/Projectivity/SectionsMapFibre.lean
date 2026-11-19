/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors (Claude team, lane OM3A)
-/
import Hironaka.Geometry.StableModification.Projectivity.SectionsMap
import Hironaka.Geometry.StableModification.Projectivity.LineBundleOps

/-!
# The line bundle is trivial where the map to `ℙᴺ` is constant

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-map-constant` (PLAN-OM3 M2). Let
`h : X ⟶ ℙᴺ_R` be the map given by generating sections `s 0, …, s N` of `𝓛^m`
(`LineBundleData.toProjectiveSpace`). If `j : V ⟶ X` is a morphism such that `h ∘ j` lands in
the coordinate chart `D₊(x_a)` — for instance if `h ∘ j` is constant — then `j^* s a` is a
nowhere vanishing section of `(j^* 𝓛)^m` (`nonvanishingLocus_pullback_eq_top`), so
`(j^* 𝓛)^m ≅ 𝒪_V` and `F ⊗ (j^* 𝓛)^{m k} ≅ F` for every module `F` on `V` and every `k`
(`twistIsoOfConstant`). Neither reducedness nor connectedness of `V` is needed (the planned
statement assumed both, PLAN-OM3 §5 M2).

This is the input of the finiteness step of the local-to-global theorem (PLAN-OM3 §3, step 4): on a
`β`-contracted curve `V` on which `h` is constant, `𝓛^m|_V` would be trivial, which contradicts
fibre-ampleness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Hironaka.StableModification.Projectivity

open Geometry.ProjectiveIdeal

universe u

variable {R : Type u} [CommRing R] {X V : Scheme.{u}}

namespace LineBundleData

variable {L : LineBundleData X} {m : ℤ} {N : ℕ} (p : X ⟶ Spec (.of R))
  {s : Fin (N + 1) → L.Sections m ⊤} (hs : Generates s)

/-- If `h ∘ j` lands in the coordinate chart `D₊(x_a)`, then `j^* (s a)` vanishes nowhere. -/
theorem nonvanishingLocus_pullback_eq_top (j : V ⟶ X) (a : Fin (N + 1))
    (hj : ∀ v, toProjectiveSpace p hs (j v) ∈ nativeCoordinateOpen a) :
    ((s a).pullback j).nonvanishingLocus = ⊤ := by
  rw [Sections.nonvanishingLocus_pullback, ← toProjectiveSpace_preimage_coordinate p hs a]
  exact eq_top_iff.mpr fun v _ => hj v

/-- A point of `ℙᴺ_R` lies in some coordinate chart. -/
lemma exists_mem_nativeCoordinateOpen (q : projectiveSpace R N) :
    ∃ a : Fin (N + 1), q ∈ nativeCoordinateOpen (R := R) a := by
  have hq : q ∈ ⨆ a : Fin (N + 1), nativeCoordinateOpen (R := R) a := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  exact Opens.mem_iSup.mp hq

/-- **The line bundle is trivial where the map is constant** (blueprint
`lem:sm-lbd-map-constant`): if `h ∘ j` is constant, then `(j^* 𝓛)^m` has a nowhere vanishing
section, namely `j^* (s a)` for any chart `D₊(x_a)` containing the value. -/
theorem exists_nonvanishing_of_constant (j : V ⟶ X) (q : projectiveSpace R N)
    (hq : ∀ v, toProjectiveSpace p hs (j v) = q) :
    ∃ a, ((s a).pullback j).nonvanishingLocus = ⊤ := by
  obtain ⟨a, ha⟩ := exists_mem_nativeCoordinateOpen q
  exact ⟨a, nonvanishingLocus_pullback_eq_top p hs j a fun v => (hq v).symm ▸ ha⟩

/-- `(j^* 𝓛)^m` is trivial where `h ∘ j` is constant. -/
theorem hasNonvanishingSection_pullback_of_constant (j : V ⟶ X) (q : projectiveSpace R N)
    (hq : ∀ v, toProjectiveSpace p hs (j v) = q) : (L.pullback j).HasNonvanishingSection m := by
  obtain ⟨a, ha⟩ := exists_nonvanishing_of_constant p hs j q hq
  exact ⟨(s a).pullback j, ha⟩

/-- Where `h ∘ j` is constant, `F ⊗ (j^* 𝓛)^{m k} ≅ F` for every module `F` on `V`. -/
def twistIsoOfConstant (j : V ⟶ X) (q : projectiveSpace R N)
    (hq : ∀ v, toProjectiveSpace p hs (j v) = q) (F : V.Modules) (k : ℕ) :
    (L.pullback j).twist F (m * k) ≅ F :=
  (L.pullback j).twistIsoOfNonvanishingMul F _
    (exists_nonvanishing_of_constant p hs j q hq).choose_spec k

end LineBundleData

end Hironaka.StableModification.Projectivity
