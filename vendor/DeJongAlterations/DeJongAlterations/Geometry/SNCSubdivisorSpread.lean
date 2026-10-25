import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actual affine neighborhoods of principal local equations

Finite generation clears all denominators simultaneously. The resulting
principal-open equation concerns the actual extended ideal.
-/

noncomputable section

namespace DeJongAlterations.Geometry.SNCSubdivisorSpread

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R]

/-- One actual denominator clears a localized inclusion of a finitely generated ideal. -/
theorem exists_multiplier_of_map_le
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (I J : Ideal R) (hI : I.FG)
    (hle : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ s ∈ M, ∀ x ∈ I, s * x ∈ J := by
  classical
  obtain ⟨F, hF⟩ := hI
  have hfinite : ∀ F : Finset R,
      (∀ x ∈ F, ∃ s ∈ M, s * x ∈ J) →
      ∃ s ∈ M, ∀ x ∈ F, s * x ∈ J := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨1, M.one_mem, by simp⟩
    | @insert a F ha ih =>
      intro h
      obtain ⟨s, hs, hsa⟩ := h a (Finset.mem_insert_self _ _)
      obtain ⟨t, ht, htF⟩ := ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
      refine ⟨s * t, M.mul_mem hs ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa only [mul_assoc, mul_comm, mul_left_comm] using J.mul_mem_left t hsa
      · simpa only [mul_assoc] using J.mul_mem_left s (htF x hx)
  obtain ⟨s, hs, hsF⟩ := hfinite F (by
    intro x hx
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J x).mp
    apply hle
    apply Ideal.mem_map_of_mem
    rw [← hF]
    exact Ideal.subset_span hx)
  refine ⟨s, hs, ?_⟩
  have hcolon : I ≤ J.colon {s} := by
    rw [← hF]
    apply Ideal.span_le.mpr
    intro x hx
    apply Submodule.mem_colon.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simpa only [smul_eq_mul, mul_comm] using hsF x hx
  intro x hx
  have h := hcolon hx
  simpa only [smul_eq_mul, mul_comm] using (Submodule.mem_colon.mp h s rfl)

/-- An actual ideal element generating at a prime generates on an actual basic neighborhood. -/
theorem exists_away_span_eq
    (I : Ideal R) (hI : I.FG) (p : Ideal R) [p.IsPrime]
    (a : R) (ha : a ∈ I)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R (Localization.AtPrime p) a}) :
    ∃ s ∉ p, I.map (algebraMap R (Localization.Away s)) =
      Ideal.span {algebraMap R (Localization.Away s) a} := by
  have hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      (Ideal.span {a}).map (algebraMap R (Localization.AtPrime p)) := by
    simpa only [Ideal.map_span, Set.image_singleton] using heq.le
  obtain ⟨s, hs, hmul⟩ :=
    exists_multiplier_of_map_le p.primeCompl (Localization.AtPrime p) I
      (Ideal.span {a}) hI hle
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap R (Localization.Away s) x ∈
      Ideal.span {algebraMap R (Localization.Away s) a}
    apply (Ideal.unit_mul_mem_iff_mem _
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)).mp
    have h := Ideal.mem_map_of_mem (algebraMap R (Localization.Away s)) (hmul x hx)
    simpa only [map_mul, Ideal.map_span, Set.image_singleton] using h
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mem_map_of_mem _ ha

/-- Killing the actual annihilator by one denominator makes the actual equation regular. -/
theorem isRegular_away_of_annihilator_killed (a v : R)
    (hkill : ∀ x : R, x * a = 0 → v * x = 0) :
    IsRegular (algebraMap R (Localization.Away v) a) := by
  let L := Localization.Away v
  have hzero : ∀ z : L, z * algebraMap R L a = 0 → z = 0 := by
    intro z hz
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers v) z
    have hba : IsLocalization.mk' L (b * a) t = 0 := by
      simpa only [← IsLocalization.mk'_one (M := Submonoid.powers v) L a,
        ← IsLocalization.mk'_mul, mul_one] using hz
    obtain ⟨w, hw⟩ :=
      (IsLocalization.mk'_eq_zero_iff (M := Submonoid.powers v) (S := L) (b * a) t).mp hba
    have hv : v * ((w : R) * b) = 0 :=
      hkill _ (by simpa only [mul_assoc] using hw)
    apply (IsLocalization.mk'_eq_zero_iff (M := Submonoid.powers v) (S := L) b t).mpr
    exact ⟨⟨v, Submonoid.mem_powers v⟩ * w,
      by simpa only [Submonoid.coe_mul, mul_assoc] using hv⟩
  refine ⟨?_, ?_⟩
  · intro x y hxy
    change algebraMap R L a * x = algebraMap R L a * y at hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [mul_comm, mul_sub, hxy, sub_self]
  · intro x y hxy
    change x * algebraMap R L a = y * algebraMap R L a at hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [sub_mul, hxy, sub_self]

/-- Regularity at a prime spreads to an actual principal affine neighborhood. -/
theorem exists_away_isRegular [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (a : R)
    (ha : IsRegular (algebraMap R (Localization.AtPrime p) a)) :
    ∃ v ∉ p, IsRegular (algebraMap R (Localization.Away v) a) := by
  let K : Ideal R := (⊥ : Ideal R).colon {a}
  have hle : K.map (algebraMap R (Localization.AtPrime p)) ≤
      (⊥ : Ideal R).map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.map_bot]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap R (Localization.AtPrime p) x = 0
    apply ha.right
    have hx' : x * a = 0 := by
      simpa only [K, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] using hx
    simp only [← map_mul, hx', map_zero, zero_mul]
  obtain ⟨v, hv, hkill⟩ :=
    exists_multiplier_of_map_le p.primeCompl (Localization.AtPrime p) K ⊥
      (IsNoetherian.noetherian K) hle
  refine ⟨v, hv, isRegular_away_of_annihilator_killed a v ?_⟩
  intro x hx
  apply hkill
  simpa only [K, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] using hx

/-- A principal regular localized ideal has a regular generator coming from an actual ideal element. -/
theorem exists_mem_regular_generator_atPrime
    (I : Ideal R) (p : Ideal R) [p.IsPrime]
    (b : Localization.AtPrime p) (hb : IsRegular b)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {b}) :
    ∃ a ∈ I, IsRegular (algebraMap R (Localization.AtPrime p) a) ∧
      I.map (algebraMap R (Localization.AtPrime p)) =
        Ideal.span {algebraMap R (Localization.AtPrime p) a} := by
  have hmem : b ∈ I.map (algebraMap R (Localization.AtPrime p)) := by
    rw [heq]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨⟨a, t⟩, ht⟩ :=
    (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).mp hmem
  refine ⟨a.val, a.property, ?_, ?_⟩
  · rw [← ht]
    exact hb.mul (IsLocalization.map_units (Localization.AtPrime p) t).isRegular
  · rw [← ht, Ideal.span_singleton_mul_right_unit
      (IsLocalization.map_units (Localization.AtPrime p) t), heq]

/-- A regular principal equation at a prime spreads to an actual affine basic neighborhood. -/
theorem exists_away_regular_span_eq [IsNoetherianRing R]
    (I : Ideal R) (p : Ideal R) [p.IsPrime]
    (b : Localization.AtPrime p) (hb : IsRegular b)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {b}) :
    ∃ s ∉ p, ∃ a ∈ I,
      IsRegular (algebraMap R (Localization.Away s) a) ∧
      I.map (algebraMap R (Localization.Away s)) =
        Ideal.span {algebraMap R (Localization.Away s) a} := by
  obtain ⟨a, ha, hreg, hspan⟩ :=
    exists_mem_regular_generator_atPrime I p b hb heq
  have hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      (Ideal.span {a}).map (algebraMap R (Localization.AtPrime p)) := by
    simpa only [Ideal.map_span, Set.image_singleton] using hspan.le
  obtain ⟨u, hu, hmul⟩ :=
    exists_multiplier_of_map_le p.primeCompl (Localization.AtPrime p) I (Ideal.span {a})
      (IsNoetherian.noetherian I) hle
  let K : Ideal R := (⊥ : Ideal R).colon {a}
  have hK : K.map (algebraMap R (Localization.AtPrime p)) ≤
      (⊥ : Ideal R).map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.map_bot]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap R (Localization.AtPrime p) x = 0
    apply hreg.right
    have hx' : x * a = 0 := by
      simpa only [K, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] using hx
    simp only [← map_mul, hx', map_zero, zero_mul]
  obtain ⟨v, hv, hkill⟩ :=
    exists_multiplier_of_map_le p.primeCompl (Localization.AtPrime p) K ⊥
      (IsNoetherian.noetherian K) hK
  refine ⟨u * v, p.primeCompl.mul_mem hu hv, a, ha, ?_, le_antisymm ?_ ?_⟩
  · apply isRegular_away_of_annihilator_killed
    intro x hx
    have hkx : v * x = 0 := hkill x (by
      simpa only [K, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] using hx)
    rw [mul_assoc, hkx, mul_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap R (Localization.Away (u * v)) x ∈
      Ideal.span {algebraMap R (Localization.Away (u * v)) a}
    apply (Ideal.unit_mul_mem_iff_mem _
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (u * v)) (u * v))).mp
    have hux : (u * v) * x ∈ Ideal.span {a} := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        (Ideal.span {a}).mul_mem_left v (hmul x hx)
    have h := Ideal.mem_map_of_mem (algebraMap R (Localization.Away (u * v))) hux
    simpa only [map_mul, Ideal.map_span, Set.image_singleton] using h
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mem_map_of_mem _ ha

end DeJongAlterations.Geometry.SNCSubdivisorSpread
