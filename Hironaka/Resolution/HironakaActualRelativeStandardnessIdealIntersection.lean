import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Strict coefficient-ideal intersections for entire original quotient ideals

Projectivity of the actual quotient supplies a section internally. The resulting
intersection identity lifts an original member into the same original ideal
intersected with a prescribed normal-power ideal.
-/

set_option autoImplicit false

namespace Hironaka.HironakaActualRelativeStandardnessIdealIntersection

noncomputable section

section Modules

variable {B E F : Type*} [CommRing B] [AddCommGroup E] [AddCommGroup F]
  [Module B E] [Module B F] [Module.Projective B F]

/-- An internally split quotient has strict intersection with every coefficient ideal. -/
theorem ker_inf_smul_top_of_projective (p : E →ₗ[B] F) (hp : Function.Surjective p)
    (J : Ideal B) :
    LinearMap.ker p ⊓ (J • (⊤ : Submodule B E)) = J • LinearMap.ker p := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : F →ₗ[B] F) hp
  have hsec (y : F) : p (s y) = y := LinearMap.congr_fun hs y
  let r : E →ₗ[B] E := LinearMap.id - s.comp p
  have hfix (x : E) (hx : x ∈ LinearMap.ker p) : r x = x := by
    change x - s (p x) = x
    rw [LinearMap.mem_ker.mp hx, map_zero, sub_zero]
  have hRange : LinearMap.range r = LinearMap.ker p := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      change p (y - s (p y)) = 0
      rw [map_sub, hsec, sub_self]
    · intro x hx
      exact ⟨x, hfix x hx⟩
  have hImage : (J • (⊤ : Submodule B E)).map r = J • LinearMap.ker p := by
    rw [Submodule.map_smul'', Submodule.map_top, hRange]
  apply le_antisymm
  · intro x hx
    have hm : r x ∈ (J • (⊤ : Submodule B E)).map r :=
      Submodule.mem_map_of_mem hx.2
    rwa [hImage, hfix x hx.1] at hm
  · apply le_inf Submodule.smul_le_right
    exact Submodule.smul_le.mpr fun b hb x _ =>
      Submodule.smul_mem_smul hb (show x ∈ (⊤ : Submodule B E) from trivial)

end Modules

section Algebras

variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- A projective entire quotient produces an original ideal correction in every coefficient ideal. -/
theorem exists_ideal_correction_of_projective (I N : Ideal R)
    [Module.Projective B (R ⧸ (I ⊔ N))] (J : Ideal B) (g : R) (hg : g ∈ I)
    (hgJ : g ∈ (J • (⊤ : Submodule B R)) ⊔ N.restrictScalars B) :
    ∃ h ∈ J • I.restrictScalars B, g - h ∈ I ⊓ N := by
  let q : R →ₗ[B] R ⧸ N := (Ideal.Quotient.mkₐ B N).toLinearMap
  let p : (R ⧸ N) →ₗ[B] R ⧸ (I ⊔ N) :=
    (Ideal.Quotient.factorₐ B (le_sup_right : N ≤ I ⊔ N)).toLinearMap
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk N r, rfl⟩
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hKernel : LinearMap.ker p = (I.restrictScalars B).map q := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      have hr : r ∈ I ⊔ N := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        exact LinearMap.mem_ker.mp hx
      obtain ⟨i, hi, n, hn, he⟩ := Submodule.mem_sup.mp hr
      refine Submodule.mem_map.mpr ⟨i, hi, ?_⟩
      change Ideal.Quotient.mk N i = Ideal.Quotient.mk N r
      rw [← he, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hn, add_zero]
    · intro hx
      obtain ⟨i, hi, he⟩ := Submodule.mem_map.mp hx
      apply LinearMap.mem_ker.mpr
      rw [← he]
      change Ideal.Quotient.mk (I ⊔ N) i = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hi)
  have hqKernel : q g ∈ LinearMap.ker p := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (I ⊔ N) g = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)
  have hqJ : q g ∈ J • (⊤ : Submodule B (R ⧸ N)) := by
    obtain ⟨a, ha, n, hn, he⟩ := Submodule.mem_sup.mp hgJ
    have hqa : q a ∈ (J • (⊤ : Submodule B R)).map q :=
      Submodule.mem_map_of_mem ha
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hq] at hqa
    have hn0 : q n = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    rw [← he, map_add, hn0, add_zero]
    exact hqa
  have hqg : q g ∈ J • LinearMap.ker p := by
    rw [← ker_inf_smul_top_of_projective p hp J]
    exact ⟨hqKernel, hqJ⟩
  rw [hKernel, ← Submodule.map_smul''] at hqg
  obtain ⟨h, hh, he⟩ := Submodule.mem_map.mp hqg
  have hhI : h ∈ I :=
    (Submodule.smul_le_right : J • I.restrictScalars B ≤ I.restrictScalars B) hh
  refine ⟨h, hh, I.sub_mem hg hhI, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (g - h) = 0
  rw [map_sub, he, sub_self]

end Algebras

end

end Hironaka.HironakaActualRelativeStandardnessIdealIntersection
