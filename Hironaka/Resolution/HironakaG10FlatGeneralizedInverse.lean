import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Complex.Basic

/-! # Direct operators are the operators with a bounded generalized inverse

A bounded operator `T : E → F` between complex Banach spaces is **direct** (Douady 1966, §1;
Frisch 1968, §2: its kernel and its image are topologically complemented) if and only if it has a
bounded **generalized inverse** `R : F → E`, `T ∘ R ∘ T = T` (`direct_iff_exists_generalizedInverse`).

* `closedComplemented_ker_of_generalizedInverse`, `closedComplemented_range_of_generalizedInverse`:
  the projections `1 − R T` onto `ker T` and `T R` onto `im T` (pure algebra, no completeness).
* `exists_generalizedInverse`: conversely, with `S` the complement of `ker T` given by the
  projection, `T|_S : S → im T` is a bounded bijection between Banach spaces, hence an isomorphism
  (open mapping theorem); `R = T|_S⁻¹ ∘ (projection onto im T)`.

This is the form of privilege (directness of the `B(K)`-operators of a presentation) that composes
algebraically in Douady's Propositions 3 and 6 and in Frisch's Lemme 3.
BP: hironaka-g10-flat-generalized-inverse.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatGeneralizedInverse
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A generalized inverse makes the kernel complemented (projection `1 − R T`). -/
theorem closedComplemented_ker_of_generalizedInverse (T : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hR : ∀ x, T (R (T x)) = T x) : (LinearMap.ker (T : E →ₗ[ℂ] F)).ClosedComplemented := by
  refine ⟨(ContinuousLinearMap.id ℂ E - R.comp T).codRestrict _ fun x => ?_, fun x => ?_⟩
  · show T (x - R (T x)) = 0
    rw [map_sub, hR, sub_self]
  · apply Subtype.ext
    have hx : T x = 0 := x.2
    show (x : E) - R (T x) = x
    rw [hx, map_zero, sub_zero]

/-- A generalized inverse makes the image complemented (projection `T R`). -/
theorem closedComplemented_range_of_generalizedInverse (T : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hR : ∀ x, T (R (T x)) = T x) : (LinearMap.range (T : E →ₗ[ℂ] F)).ClosedComplemented := by
  refine ⟨(T.comp R).codRestrict _ fun y => ⟨R y, rfl⟩, fun y => ?_⟩
  apply Subtype.ext
  obtain ⟨x, hx⟩ := y.2
  show T (R y) = y
  have hx' : T x = y := hx
  rw [← hx', hR]

/-- **A direct operator between Banach spaces has a bounded generalized inverse.** -/
theorem exists_generalizedInverse [CompleteSpace E] [CompleteSpace F] (T : E →L[ℂ] F)
    (hker : (LinearMap.ker (T : E →ₗ[ℂ] F)).ClosedComplemented)
    (hran : (LinearMap.range (T : E →ₗ[ℂ] F)).ClosedComplemented) :
    ∃ R : F →L[ℂ] E, ∀ x, T (R (T x)) = T x := by
  obtain ⟨p, hp⟩ := hker
  obtain ⟨q, hq⟩ := hran
  -- the complement `S = ker (i ∘ p)` of `ker T`
  let ip : E →L[ℂ] E := (LinearMap.ker (T : E →ₗ[ℂ] F)).subtypeL.comp p
  have hip_K : ∀ x ∈ LinearMap.ker (T : E →ₗ[ℂ] F), ip x = x :=
    fun x hx => congrArg Subtype.val (hp ⟨x, hx⟩)
  have hipip : ∀ x, ip (ip x) = ip x := fun x => hip_K _ (p x).2
  let S : Submodule ℂ E := LinearMap.ker (ip : E →ₗ[ℂ] E)
  have hSc : IsClosed (S : Set E) := ip.isClosed_ker
  have : CompleteSpace S := hSc.completeSpace_coe
  have hRc : IsClosed (LinearMap.range (T : E →ₗ[ℂ] F) : Set F) :=
    Submodule.ClosedComplemented.isClosed ⟨q, hq⟩
  have : CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] F)) := hRc.completeSpace_coe
  -- `T|_S : S → im T`
  let TS : S →L[ℂ] (LinearMap.range (T : E →ₗ[ℂ] F)) :=
    (T.comp S.subtypeL).codRestrict (LinearMap.range (T : E →ₗ[ℂ] F)) fun s => ⟨s, rfl⟩
  have hTS_apply : ∀ s : S, (TS s : F) = T s := fun s => rfl
  have hinj : LinearMap.ker (TS : S →ₗ[ℂ] (LinearMap.range (T : E →ₗ[ℂ] F))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    have hTs : T s = 0 := by
      have := congrArg Subtype.val hs
      rwa [ContinuousLinearMap.coe_coe, hTS_apply] at this
    apply Subtype.ext
    have h1 : ip s = s := hip_K s hTs
    have h2 : ip s = 0 := s.2
    show (s : E) = 0
    rw [← h1, h2]
  have hsurj : LinearMap.range (TS : S →ₗ[ℂ] (LinearMap.range (T : E →ₗ[ℂ] F))) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨y, x, rfl⟩
    have hmem : x - ip x ∈ S := by
      show ip (x - ip x) = 0
      rw [map_sub, hipip, sub_self]
    refine ⟨⟨x - ip x, hmem⟩, Subtype.ext ?_⟩
    rw [ContinuousLinearMap.coe_coe, hTS_apply]
    show T (x - ip x) = T x
    have hK : T (ip x) = 0 := (p x).2
    rw [map_sub, hK, sub_zero]
  let e : S ≃L[ℂ] (LinearMap.range (T : E →ₗ[ℂ] F)) :=
    ContinuousLinearEquiv.ofBijective TS hinj hsurj
  refine ⟨S.subtypeL.comp ((e.symm : (LinearMap.range (T : E →ₗ[ℂ] F)) →L[ℂ] S).comp q),
    fun x => ?_⟩
  have hqT : q (T x) = ⟨T x, x, rfl⟩ := hq ⟨T x, x, rfl⟩
  show T ((e.symm (q (T x)) : S) : E) = T x
  rw [hqT, ← hTS_apply]
  have : TS (e.symm ⟨T x, x, rfl⟩) = ⟨T x, x, rfl⟩ := e.apply_symm_apply _
  rw [this]

/-- **Direct ⇔ bounded generalized inverse** (Banach spaces). -/
theorem direct_iff_exists_generalizedInverse [CompleteSpace E] [CompleteSpace F] (T : E →L[ℂ] F) :
    ((LinearMap.ker (T : E →ₗ[ℂ] F)).ClosedComplemented ∧
      (LinearMap.range (T : E →ₗ[ℂ] F)).ClosedComplemented) ↔
      ∃ R : F →L[ℂ] E, ∀ x, T (R (T x)) = T x :=
  ⟨fun h => exists_generalizedInverse T h.1 h.2, fun ⟨R, hR⟩ =>
    ⟨closedComplemented_ker_of_generalizedInverse T R hR,
      closedComplemented_range_of_generalizedInverse T R hR⟩⟩

end
end Hironaka.HironakaG10FlatGeneralizedInverse
