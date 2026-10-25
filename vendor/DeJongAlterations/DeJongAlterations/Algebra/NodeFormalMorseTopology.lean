import DeJongAlterations.Algebra.NodeFormalMorseDecomposition
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The full base-and-variable adic topology for an actual split-node automorphism

The ideal here is the actual extended coefficient ideal plus both variable
generators. It is not identified with the coefficientwise base ideal.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

universe u
variable {R : Type u} [CommRing R]

/-- The actual full base-and-variable ideal `I R[[u,v]] + (u,v)`. -/
def fullIdeal (I : Ideal R) : Ideal (Series R) :=
  I.map C ⊔ Ideal.span (Set.range (fun i : Fin 2 => (X i : Series R)))

/-- The enlarged actual ideal is detected by the original constant coefficient. -/
theorem fullIdeal_eq_comap (I : Ideal R) : fullIdeal I = I.comap constantCoeff := by
  apply le_antisymm
  · change I.map C ⊔ Ideal.span (Set.range (fun i : Fin 2 => (X i : Series R))) ≤ _
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change constantCoeff (C r : Series R) ∈ I
      simpa using hr
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change constantCoeff (X i : Series R) ∈ I
      simp
  · intro f hf
    change constantCoeff f ∈ I at hf
    have hc : (C (constantCoeff f) : Series R) ∈ fullIdeal I :=
      (show I.map C ≤ fullIdeal I from le_sup_left) (Ideal.mem_map_of_mem C hf)
    have hx (i : Fin 2) : (X i : Series R) ∈ fullIdeal I :=
      (show Ideal.span (Set.range (fun j : Fin 2 => (X j : Series R))) ≤ fullIdeal I
        from le_sup_right) (Ideal.subset_span ⟨i, rfl⟩)
    rw [decomposition f]
    exact (fullIdeal I).add_mem
      ((fullIdeal I).add_mem hc ((fullIdeal I).mul_mem_right _ (hx 0)))
      ((fullIdeal I).mul_mem_right _ (hx 1))

/-- Identity coefficient reduction implies actual preservation of the full ideal. -/
theorem fullIdeal_map_le (I : Ideal R) (e : Series R ≃ₐ[R] Series R)
    (he : ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f) : (fullIdeal I).map e.toRingHom ≤ fullIdeal I := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [fullIdeal_eq_comap] at hf ⊢
  change constantCoeff f ∈ I at hf
  change constantCoeff (e f) ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hc := congrArg constantCoeff (he f)
  simp only [constantCoeff_map] at hc
  rw [hc]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- The inverse reduction identity follows from the original map, not an extra premise. -/
theorem inverse_reduction_of_reduction (I : Ideal R) (e : Series R ≃ₐ[R] Series R)
    (he : ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f) :
    ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e.symm f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  intro f
  simpa only [AlgEquiv.apply_symm_apply] using (he (e.symm f)).symm

/-- Both actual directions give equality of the image of the defining full ideal. -/
theorem fullIdeal_map_eq (I : Ideal R) (e : Series R ≃ₐ[R] Series R)
    (he : ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f) : (fullIdeal I).map e.toRingHom = fullIdeal I := by
  apply le_antisymm (fullIdeal_map_le I e he)
  intro f hf
  have hi : e.symm f ∈ fullIdeal I := Ideal.map_le_iff_le_comap.mp
    (fullIdeal_map_le I e.symm (inverse_reduction_of_reduction I e he)) hf
  have hm := Ideal.mem_map_of_mem e.toRingHom hi
  change e (e.symm f) ∈ (fullIdeal I).map e.toRingHom at hm
  rwa [AlgEquiv.apply_symm_apply] at hm

/-- An actual full-ideal-preserving automorphism is continuous for its literal adic topology. -/
theorem continuous_fullIdeal (I : Ideal R) (e : Series R ≃ₐ[R] Series R)
    (he : ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f) :
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e := by
  let : WithIdeal (Series R) := ⟨fullIdeal I⟩
  exact (WithIdeal.uniformContinuous_of_map_le (f := e.toRingHom) (fullIdeal_map_le I e he)).continuous

/-- The actual inverse is continuous for the same full topology, with no separate inverse certificate. -/
theorem continuous_symm_fullIdeal (I : Ideal R) (e : Series R ≃ₐ[R] Series R)
    (he : ∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f) :
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e.symm :=
  continuous_fullIdeal I e.symm (inverse_reduction_of_reduction I e he)

end DeJongAlterations.Algebra.NodeFormalMorse
