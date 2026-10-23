import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral

/-!
# Dimension from an actual fraction field

The two integral-extension dimension comparisons are pure proof extractions
from EnvelopeProperty/AlgGeom/KrullDim.lean (SHA256
804535bd109a31ba7f281774b390f82f0c49a064e2be34f090ebb7cdfd71c815)
and EnvelopeProperty/AlgGeom/ProjectionNoether.lean (SHA256
a748c3343f786907107270e576d701395f66020e14595a41095def07b7b0ada4).
Only Mathlib is imported. Actual Noether normalization then identifies the
original finite-type domain's dimension with the transcendence degree of
its actual fraction field.
-/

noncomputable section

namespace DeJongAlterations.Algebra.FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ringKrullDim_le_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  let := f.toAlgebra
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun P Q hPQ => ?_
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (show P.asIdeal < Q.asIdeal from hPQ)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ.le ⟨hxQ, hxP⟩ (hf x)

theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  algebraize [f]
  have : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hPp, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (by
      rw [Ideal.comap_bot_of_injective (algebraMap R S) hinj]
      exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- Integral algebraic extensions preserve actual transcendence degree in a faithful tower. -/
theorem trdeg_eq_of_isAlgebraic (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [CommRing K] [NoZeroDivisors K] [Algebra k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] :
    Algebra.trdeg k A = Algebra.trdeg k K := by
  have h := trdeg_add_eq k A (A := K)
  rwa [trdeg_eq_zero (R := A) (A := K), add_zero] at h

/-- Noether normalization computes both actual affine dimension and fraction-field degree. -/
theorem exists_dimension_and_trdeg (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra.FiniteType k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] :
    ∃ d : ℕ, ringKrullDim A = d ∧ Algebra.trdeg k K = d := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := f.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  have : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hf
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hP : ringKrullDim P = n := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hd : ringKrullDim A = n := by
    apply le_antisymm
    · exact (ringKrullDim_le_of_isIntegral f.toRingHom
        (algebraMap_isIntegral_iff.mpr inferInstance)).trans_eq hP
    · exact hP ▸ ringKrullDim_le_of_isIntegral_of_injective f.toRingHom
        (algebraMap_isIntegral_iff.mpr inferInstance) hf
  have htrA : Algebra.trdeg k A = n := by
    rw [← trdeg_eq_of_isAlgebraic k P A]
    simp [P]
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact ⟨n, hd, (trdeg_eq_of_isAlgebraic k A K).symm.trans htrA⟩

/-- The dimension is derived from finite type and the actual fraction field. -/
theorem ringKrullDim_eq_of_trdeg_eq_nat (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra.FiniteType k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] (d : ℕ) (htr : Algebra.trdeg k K = d) :
    ringKrullDim A = d := by
  obtain ⟨n, hd, hn⟩ := exists_dimension_and_trdeg k A K
  have hnd : n = d := by exact_mod_cast hn.symm.trans htr
  simpa [hnd] using hd

end DeJongAlterations.Algebra.FunctionFieldDimension
