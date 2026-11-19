import Hironaka.Resolution.HironakaG10HirFlatQuotient
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flatness over every test ideal through a surjective base presentation (G10-02-04, algebra)

Lane G10SB, run 0081, plan item G10-02-04 (algebraic core).  A ring map `φ : A →+* B` (the native
stalk map of a morphism at a point of a possibly singular base) is presented by a ring map
`ψ : R →+* S` through a SURJECTION `π : R →+* A` of the base (the ambient chart germ ring onto the
native base stalk; its kernel is the whole defining ideal) and an ISOMORPHISM `ε : S ≃+* B` of the
target: `φ ∘ π = ε ∘ ψ`.  Then for EVERY ideal `J` of `A` (no reducedness, zero divisors and
nilpotents allowed) the fibre map over `V(J)` is flat iff the fibre map of `ψ` over the lifted ideal
`π⁻¹ J` (which contains `ker π`) is flat.

* `quotMap_flat_iff_of_square` — the dictionary;
* `quotMap_flat_iff_comap_le` — the converse parametrization: lifted ideals are exactly the ideals of
  `R` containing `ker π`;
* `quotMap_algebraMap_flat_iff_tensor` — for an `R`-algebra `S`, flatness of the fibre map over
  `V(I)` is flatness of the base-changed module `(R ⧸ I) ⊗[R] S`.

Pure commutative algebra; no analytic input, no named input.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat

open Hironaka.HironakaG10HirFlatQuotient

noncomputable section

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

/-- The lifted ideal of a test ideal contains the kernel of the presentation. -/
theorem ker_le_comap (π : R →+* A) (J : Ideal A) : RingHom.ker π ≤ J.comap π := by
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker.mp hr]
  exact J.zero_mem

/-- Every ideal of `R` containing `ker π` is a lifted ideal. -/
theorem comap_map_of_ker_le (π : R →+* A) (hπ : Function.Surjective π) (I : Ideal R)
    (hI : RingHom.ker π ≤ I) : (I.map π).comap π = I := by
  rw [Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI]

/-- **Flatness dictionary through a presentation square.**  If `φ ∘ π = ε ∘ ψ` with `π` surjective
and `ε` a ring isomorphism, then for every ideal `J` of `A` the fibre map of `φ` over `V(J)` is flat
iff the fibre map of `ψ` over `V(π⁻¹ J)` is flat. -/
theorem quotMap_flat_iff_of_square (φ : A →+* B) (π : R →+* A) (hπ : Function.Surjective π)
    (ψ : R →+* S) (ε : S ≃+* B) (hsq : φ.comp π = ε.toRingHom.comp ψ) (J : Ideal A) :
    (quotMap φ J).Flat ↔ (quotMap ψ (J.comap π)).Flat := by
  set L := J.comap π with hL
  have hJ : L.map π = J := Ideal.map_comap_of_surjective π hπ J
  have hmap : (L.map ψ).map ε.toRingHom = J.map φ := by
    rw [Ideal.map_map, ← hsq, ← Ideal.map_map, hJ]
  let q : R ⧸ L →+* A ⧸ J := Ideal.quotientMap J π le_rfl
  have hq : Function.Bijective q :=
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hπ⟩
  let e₂ : (S ⧸ L.map ψ) ≃+* (B ⧸ J.map φ) := Ideal.quotientEquiv _ _ ε hmap.symm
  have hcomm : (quotMap φ J).comp q = e₂.toRingHom.comp (quotMap ψ L) := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext r
    change Ideal.Quotient.mk (J.map φ) (φ (π r)) = Ideal.Quotient.mk (J.map φ) (ε (ψ r))
    congr 1
    exact RingHom.congr_fun hsq r
  rw [← RingHom.Flat.comp_iff_of_bijective_right (g := q) hq, hcomm,
    RingHom.Flat.comp_iff_of_bijective_left (g := e₂.toRingHom) e₂.bijective]

/-- The same dictionary read on the ideals of `R` above `ker π`. -/
theorem quotMap_flat_iff_of_square' (φ : A →+* B) (π : R →+* A) (hπ : Function.Surjective π)
    (ψ : R →+* S) (ε : S ≃+* B) (hsq : φ.comp π = ε.toRingHom.comp ψ) (I : Ideal R)
    (hI : RingHom.ker π ≤ I) :
    (quotMap φ (I.map π)).Flat ↔ (quotMap ψ I).Flat := by
  rw [quotMap_flat_iff_of_square φ π hπ ψ ε hsq, comap_map_of_ker_le π hπ I hI]

/-- Containment of test ideals is read on the lifted ideals. -/
theorem map_le_iff_le_comap_of_surjective (π : R →+* A) (H : Ideal R) (J : Ideal A) :
    H.map π ≤ J ↔ H ≤ J.comap π :=
  Ideal.map_le_iff_le_comap

/-- **Module form.**  For an `R`-algebra `S`, flatness of the fibre map over `V(I)` is flatness of
the literal base-changed module `(R ⧸ I) ⊗[R] S` over `R ⧸ I`. -/
theorem quotMap_algebraMap_flat_iff_tensor [Algebra R S] (I : Ideal R) :
    (quotMap (algebraMap R S) I).Flat ↔ Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := by
  constructor
  · intro h
    have hm : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
      apply RingHom.flat_algebraMap_iff.mp
      exact h
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv
  · intro h
    have hm : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
    exact RingHom.flat_algebraMap_iff.mpr hm

end

end Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
