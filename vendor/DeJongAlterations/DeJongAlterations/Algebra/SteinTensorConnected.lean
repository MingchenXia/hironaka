import DeJongAlterations.Algebra.SteinTensor
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Connected.Clopen

/-!
# Connected tensor spectra from actual relatively closed constants

An actual finite coefficient specialization preserves both selected
nonzero coefficients of a purported nontrivial idempotent.  The
residue field is algebraic by Zariski's lemma, where irreducibility
has already been proved without any connectedness certificate.
-/

noncomputable section

open TensorProduct TopologicalSpace

namespace DeJongAlterations.Algebra.SteinTensorConnected

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native idempotent/clopen correspondence reflects connectedness. -/
theorem idempotent_trivial_of_preconnected (A : Type u) [CommRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (a : A) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩
  rcases preconnectedSpace_iff_clopen.mp inferInstance _ hc with hc | hc
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ha IsIdempotentElem.zero
    exact Opens.ext (by simpa using hc)
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ha IsIdempotentElem.one
    exact Opens.ext (by simpa using hc)

/-- Trivial actual idempotents give a preconnected native prime spectrum. -/
theorem preconnected_of_idempotent_trivial (A : Type u) [CommRing A]
    (h : ∀ a : A, IsIdempotentElem a → a = 0 ∨ a = 1) :
    PreconnectedSpace (PrimeSpectrum A) := by
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  obtain ⟨a, ha, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h a ha with rfl | rfl <;> simp

variable {K F E : Type u} [Field K] [Field F] [Algebra K F]
  [Field E] [Algebra K E]

/-- Coefficients in a fixed basis commute with the actual coefficient-ring map. -/
theorem coefficient_map {ι : Type u} [DecidableEq ι] (b : Module.Basis ι K F) (i : ι)
    {B C : Type u} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    (φ : B →ₐ[K] C) (x : B ⊗[K] F) :
    TensorProduct.equivFinsuppOfBasisRight b
        (Algebra.TensorProduct.map φ (AlgHom.id K F) x) i =
      φ (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  classical
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y => simp

/-- An algebraic scalar extension has no nontrivial actual tensor idempotents. -/
theorem idempotent_trivial_of_isAlgebraic [Algebra.IsAlgebraic K E]
    (h : integralClosure K F = ⊥) (a : E ⊗[K] F) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  let := SteinTensor.irreducibleSpace_tensorSpectrum_of_isAlgebraic (E := E) h
  exact idempotent_trivial_of_preconnected _ a ha

/-- Every actual tensor idempotent is trivial, with no restriction on the scalar field. -/
theorem idempotent_trivial (h : integralClosure K F = ⊥)
    (a : E ⊗[K] F) (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  classical
  by_contra! hbad
  let b := Module.Free.chooseBasis K F
  let c := TensorProduct.equivFinsuppOfBasisRight b a
  let d := TensorProduct.equivFinsuppOfBasisRight b (1 - a)
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! hc
    apply hbad.1
    apply (TensorProduct.equivFinsuppOfBasisRight b).injective
    ext i
    exact hc i
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra! hd
    have H : (1 : E ⊗[K] F) - a = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisRight b).injective
      ext j
      exact hd j
    exact hbad.2 (sub_eq_zero.mp H).symm
  let s := c.support.image c ∪ {(c i)⁻¹, (d j)⁻¹}
  let B := Algebra.adjoin K (s : Set E)
  have hcB (l) : c l ∈ B := by
    by_cases hl : l ∈ c.support
    · exact Algebra.subset_adjoin (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hl))
    · rw [Finsupp.notMem_support_iff.mp hl]; exact B.zero_mem
  have hiB : (c i)⁻¹ ∈ B := Algebra.subset_adjoin (by simp [s])
  have hjB : (d j)⁻¹ ∈ B := Algebra.subset_adjoin (by simp [s])
  let aB : B ⊗[K] F :=
    ∑ l ∈ c.support.attach, (⟨c l.1, hcB l.1⟩ : B) ⊗ₜ[K] b l.1
  let m := Algebra.TensorProduct.map B.val (AlgHom.id K F)
  have hm : Function.Injective m :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := F) B.val.toLinearMap
      Subtype.val_injective
  have hmB : m aB = a := by
    simp only [aB, m, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (∑ l ∈ c.support.attach, c l.1 ⊗ₜ[K] b l.1) = a
    rw [Finset.sum_attach c.support (fun l => c l ⊗ₜ[K] b l)]
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply a
  have haB : IsIdempotentElem aB := by
    apply hm
    simpa only [map_mul, hmB] using ha.eq
  have hu (x : B ⊗[K] F) (l) (hn : TensorProduct.equivFinsuppOfBasisRight b (m x) l ≠ 0)
      (hinv : (TensorProduct.equivFinsuppOfBasisRight b (m x) l)⁻¹ ∈ B) :
      IsUnit (TensorProduct.equivFinsuppOfBasisRight b x l) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    change B.val _ * _ = 1
    rw [← coefficient_map b l B.val]
    exact mul_inv_cancel₀ hn
  have hui : IsUnit (TensorProduct.equivFinsuppOfBasisRight b aB i) :=
    hu aB i (by simpa only [hmB] using hi) (by simpa only [hmB] using hiB)
  have huj : IsUnit (TensorProduct.equivFinsuppOfBasisRight b (1 - aB) j) :=
    hu (1 - aB) j (by simpa only [map_sub, map_one, hmB, d] using hj)
      (by simpa only [map_sub, map_one, hmB, d] using hjB)
  obtain ⟨q, hq⟩ := Ideal.exists_maximal B
  let := hq
  let E₀ := B ⧸ q
  let : Field E₀ := Ideal.Quotient.field q
  let : Algebra.FiniteType K B := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  let : Module.Finite K E₀ := finite_of_finite_type_of_isJacobsonRing K E₀
  let φ : B →ₐ[K] E₀ := Ideal.Quotient.mkₐ K q
  let n := Algebra.TensorProduct.map φ (AlgHom.id K F)
  have hna : IsIdempotentElem (n aB) := by
    change n aB * n aB = n aB
    rw [← map_mul, haB.eq]
  have hn0 (x : B ⊗[K] F) (l)
      (hx : IsUnit (TensorProduct.equivFinsuppOfBasisRight b x l)) : n x ≠ 0 := by
    intro hz
    have H := coefficient_map b l φ x
    rw [show Algebra.TensorProduct.map φ (AlgHom.id K F) x = n x from rfl, hz] at H
    exact (hx.map φ).ne_zero (by simpa using H.symm)
  rcases idempotent_trivial_of_isAlgebraic h (n aB) hna with hz | hz
  · exact hn0 aB i hui hz
  · apply hn0 (1 - aB) j huj
    rw [map_sub, map_one, hz, sub_self]

/-- Every scalar change has a connected actual prime spectrum. -/
theorem connectedSpace_tensorSpectrum (h : integralClosure K F = ⊥) :
    ConnectedSpace (PrimeSpectrum (E ⊗[K] F)) := by
  let := preconnected_of_idempotent_trivial _ (idempotent_trivial (E := E) h)
  exact ⟨inferInstance⟩

end DeJongAlterations.Algebra.SteinTensorConnected
