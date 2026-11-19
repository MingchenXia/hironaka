import Hironaka.Resolution.Algebraic.ActualGlobalPaddingPrincipalizationChoice

/-!
# Intrinsic integral dimensions are genuine smooth relative dimensions

Source-first proof: `actual-integral-intrinsic-smooth-dimension-20261102.tex`.
This is actual geometry for the required smooth component/J naturality frontier.
No component-transport or ideal-naturality output is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualIntegralIntrinsicSmoothDimension

noncomputable section
variable {X Y : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
  (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
theorem affineSections_dimension (U : X.affineOpens) [Nonempty U.1] :
    ringKrullDim Γ(X, U.1) = topologicalKrullDim X := by
  obtain ⟨n, hn, htr⟩ := Hironaka.Geometry.FunctionFieldDimension.exists_dimension_and_trdeg p
  exact (Hironaka.Geometry.FunctionFieldDimension.affineSections_dimension_eq p U n htr).trans hn.symm

private theorem smoothLocus_dimension_congr {A B : Scheme.{u}} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (n : ℕ) :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension n (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

theorem smoothLocus_dimension [CharZero k] (n : ℕ) (hdim : topologicalKrullDim X = n) :
    SmoothOfRelativeDimension n (p.smoothLocus.ι ≫ p) := by
  let : X.Over (Spec (.of k)) := ⟨p⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType p)
  obtain ⟨m, hm⟩ := (Hironaka.Resolution.isReducedEquidimensional_of_isIntegral (k := k) X).2
  have : SmoothOfRelativeDimension m (p.smoothLocus.ι ≫ p) := hm
  obtain ⟨U, hηU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem (genericPoint X)
  let : Nonempty U.1 := ⟨⟨genericPoint X, hηU⟩⟩
  let := (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p U.2).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_finiteType p U.2)
  have hR : ringKrullDim Γ(X, U) = n := (affineSections_dimension p U).trans hdim
  have hmin : ∀ q : minimalPrimes Γ(X, U), ringKrullDim (Γ(X, U) ⧸ q.val) = n := by
    intro q
    have hq : q.val = ⊥ := by
      simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using q.property
    rw [hq, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Γ(X, U))]
    exact hR
  let f := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  have hf : f = U.2.fromSpec ≫ p := Hironaka.Algebra.FiniteTypePoint.affineBaseMap_spec p U.2
  have : LocallyOfFiniteType f := by rw [hf]; infer_instance
  have hn : SmoothOfRelativeDimension n ((U.2.fromSpec ≫ p).smoothLocus.ι ≫ (U.2.fromSpec ≫ p)) :=
    (smoothLocus_dimension_congr f (U.2.fromSpec ≫ p) hf n).mp
      (ActualDimensionGroupEquidimensionalPieces.affine_smoothLocus_of_component_dimensions Γ(X, U) k n hmin)
  have hm' : SmoothOfRelativeDimension (0 + m)
      ((U.2.fromSpec ∣_ p.smoothLocus) ≫ (p.smoothLocus.ι ≫ p)) := inferInstance
  rw [Nat.zero_add, ← Category.assoc, morphismRestrict_ι, Category.assoc,
    U.2.fromSpec.preimage_smoothLocus_eq p] at hm'
  have : Nonempty (Spec Γ(X, U)) := inferInstance
  have : Nonempty (U.2.fromSpec ≫ p).smoothLocus :=
    ⟨⟨genericPoint (Spec Γ(X, U)), (U.2.fromSpec ≫ p).genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have heq : m = n := SmoothOfRelativeDimension.eq_of_nonempty
    ((U.2.fromSpec ≫ p).smoothLocus.ι ≫ (U.2.fromSpec ≫ p))
  exact heq ▸ hm

include p in
theorem dimension_add_of_smooth [CharZero k] [IsIntegral Y] (f : Y ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r f] :
    topologicalKrullDim Y = topologicalKrullDim X + r := by
  have : Smooth f := SmoothOfRelativeDimension.smooth r f
  obtain ⟨d, hd, -⟩ := Hironaka.Geometry.FunctionFieldDimension.exists_dimension_and_trdeg p
  obtain ⟨e, he, -⟩ := Hironaka.Geometry.FunctionFieldDimension.exists_dimension_and_trdeg (f ≫ p)
  have : SmoothOfRelativeDimension d (p.smoothLocus.ι ≫ p) := smoothLocus_dimension p d hd
  have : SmoothOfRelativeDimension e ((f ≫ p).smoothLocus.ι ≫ (f ≫ p)) := smoothLocus_dimension (f ≫ p) e he
  have hη : genericPoint Y ∈ (f ≫ p).smoothLocus := (f ≫ p).genericPoint_mem_smoothLocus_of_perfectField
  obtain ⟨_, ⟨y, hy, rfl⟩, hfy⟩ := p.dense_smoothLocus_of_perfectField.inter_open_nonempty
    (f '' ((f ≫ p).smoothLocus : Set Y)) (f.isOpenMap _ (f ≫ p).smoothLocus.isOpen)
    ⟨f (genericPoint Y), genericPoint Y, hη, rfl⟩
  let W : Y.Opens := (f ≫ p).smoothLocus ⊓ f ⁻¹ᵁ p.smoothLocus
  have : Nonempty W := ⟨⟨y, hy, hfy⟩⟩
  have hsource : SmoothOfRelativeDimension (0 + e)
      (Y.homOfLE (inf_le_left : W ≤ (f ≫ p).smoothLocus) ≫ ((f ≫ p).smoothLocus.ι ≫ (f ≫ p))) := inferInstance
  rw [Nat.zero_add, ← Category.assoc, Scheme.homOfLE_ι] at hsource
  have hr : SmoothOfRelativeDimension r (f.resLE p.smoothLocus W inf_le_right) := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension r) :=
      @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
    have : SmoothOfRelativeDimension r (f ∣_ p.smoothLocus) :=
      IsZariskiLocalAtTarget.restrict (inferInstance : SmoothOfRelativeDimension r f) p.smoothLocus
    have h : SmoothOfRelativeDimension (0 + r)
        (Y.homOfLE (inf_le_right : W ≤ f ⁻¹ᵁ p.smoothLocus) ≫ (f ∣_ p.smoothLocus)) := inferInstance
    rw [Nat.zero_add] at h
    exact h
  have htarget : SmoothOfRelativeDimension (r + d)
      (f.resLE p.smoothLocus W inf_le_right ≫ (p.smoothLocus.ι ≫ p)) := inferInstance
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc] at htarget
  have hdim : e = r + d := SmoothOfRelativeDimension.eq_of_nonempty (W.ι ≫ (f ≫ p))
  rw [he, hd, hdim]
  exact_mod_cast Nat.add_comm r d

end
end Hironaka.Resolution.Algebraic.ActualIntegralIntrinsicSmoothDimension
