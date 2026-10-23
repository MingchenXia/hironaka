import DeJongAlterations.Geometry.NodeFamilyGeometricPurity
import DeJongAlterations.Geometry.NodeFamilySmooth
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Density of the actual smooth locus on every field node

The simultaneous coordinate-zero locus contains at most one actual prime.
The actual node has no open singleton, so the two genuine smooth coordinate opens are dense.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

namespace DeJongAlterations.Geometry.NodeFamilySmoothDensity

open Algebra.NodeBlowupChart NodeFamilyFlat NodeFamilySmooth NodeFamilyGeometricPurity

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A subset with at most one omitted point is dense when no singleton is open. -/
theorem dense_of_subsingleton_compl {T : Type u} [TopologicalSpace T]
    (hno : ∀ x : T, ¬ IsOpen ({x} : Set T)) (s : Set T) (hs : sᶜ.Subsingleton) : Dense s := by
  by_cases h : sᶜ.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply (dense_compl_singleton_iff_not_open.mpr (hno x)).mono
    intro y hy
    by_contra hys
    exact hy (Set.mem_singleton_iff.mpr (hs hys hx))
  · have hs' : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    rw [hs']
    exact dense_univ

variable (K : Type u) [Field K]

/-- The literal ideal of variables is the actual constant-coefficient kernel. -/
theorem idealOfVars_eq_ker_constantCoeff :
    MvPolynomial.idealOfVars (Fin 2) K = RingHom.ker (MvPolynomial.constantCoeff :
      MvPolynomial (Fin 2) K →+* K) := by
  apply Ideal.ext
  intro P
  have hmem := MvPolynomial.mem_pow_idealOfVars_iff' (σ := Fin 2) (R := K) 1 P
  rw [pow_one] at hmem
  rw [hmem]
  change (∀ d, d.degree < 1 → P.coeff d = 0) ↔ P.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
    simpa only [hd0] using h

/-- The actual variable ideal is maximal over every field. -/
theorem idealOfVars_isMaximal : (MvPolynomial.idealOfVars (Fin 2) K).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff K]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C _ a⟩)

/-- At most one actual field-node point has both coordinates zero. -/
theorem zeroCoordinate_subsingleton (t : K) :
    {p : PrimeSpectrum (Node K t) | ∀ i : Fin 2, coordinate t i ∈ p.asIdeal}.Subsingleton := by
  have hcomap (p : PrimeSpectrum (Node K t))
      (hp : ∀ i : Fin 2, coordinate t i ∈ p.asIdeal) :
      p.asIdeal.comap (Ideal.Quotient.mk (Algebra.NodeChart.uChartIdeal K t)) =
        MvPolynomial.idealOfVars (Fin 2) K := by
    apply ((idealOfVars_isMaximal K).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hp i
  intro p hp q hq
  apply PrimeSpectrum.ext
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  exact (hcomap p hp).trans (hcomap q hq).symm

/-- The two literal coordinate opens are dense on every actual field node. -/
theorem coordinateUnion_dense (t : K) :
    Dense ((coordinateOpen t 0 ⊔ coordinateOpen t 1 :
      (Spec (CommRingCat.of (Node K t))).Opens) : Set (Spec (CommRingCat.of (Node K t)))) := by
  apply dense_of_subsingleton_compl (node_not_isOpen_singleton K t)
  intro p hp q hq
  apply zeroCoordinate_subsingleton K t
  · change ¬ (coordinate t 0 ∉ p.asIdeal ∨ coordinate t 1 ∉ p.asIdeal) at hp
    simpa only [Set.mem_ofPred_eq, Fin.forall_fin_two, not_not] using not_or.mp hp
  · change ¬ (coordinate t 0 ∉ q.asIdeal ∨ coordinate t 1 ∉ q.asIdeal) at hq
    simpa only [Set.mem_ofPred_eq, Fin.forall_fin_two, not_not] using not_or.mp hq

local instance (t : K) : LocallyOfFinitePresentation (nodeMorphism t) :=
  nodeMorphism_locallyOfFinitePresentation t

/-- The actual native relative smooth locus of every field node is dense. -/
theorem nodeMorphism_smoothLocus_dense (t : K) :
    Dense ((nodeMorphism t).smoothLocus : Set (Spec (CommRingCat.of (Node K t)))) :=
  (coordinateUnion_dense K t).mono (coordinateUnion_le_smoothLocus t)

end DeJongAlterations.Geometry.NodeFamilySmoothDensity
