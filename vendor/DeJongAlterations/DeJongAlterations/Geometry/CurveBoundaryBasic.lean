import DeJongAlterations.Geometry.NormalCurveModification
import DeJongAlterations.Geometry.BlowupModification
import DeJongAlterations.Geometry.BlowupCartier
import DeJongAlterations.Geometry.SNCIso
import Mathlib.AlgebraicGeometry.Artinian

/-!
# Closed supports and Cartier ideals on actual normal curves

The Cartier property is obtained from the genuine blowup and its actual
normal-curve isomorphism. No local principal or Cartier witness is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveBoundary

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- The coheight of every actual curve point is at most one. -/
theorem coheight_le_one (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    Order.coheight x ≤ (1 : ℕ∞) := by
  have ho : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  exact_mod_cast (Order.coheight_le_krullDim x).trans ho

/-- Every nongeneric actual curve point has coheight one. -/
theorem coheight_eq_one (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : Order.coheight x = 1 := by
  apply le_antisymm (coheight_le_one hdim x)
  have hlt : x < (⊤ : X) := by
    refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
    intro h
    apply hx
    exact ((show x ⤳ genericPoint X from h).antisymm (genericPoint_specializes x)).eq
  have H := Order.coheight_add_one_le hlt
  simpa using H

/-- A nongeneric point on an integral curve is closed. -/
theorem isClosed_singleton_of_ne_genericPoint (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hs : x ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hyx : y < x := by
    refine lt_iff_le_not_ge.mpr ⟨hs, ?_⟩
    intro h
    apply hne
    exact Set.mem_singleton_iff.mpr (((show y ⤳ x from h).antisymm hs).eq)
  have H := Order.coheight_add_one_le hyx
  rw [coheight_eq_one hdim x hx] at H
  have hbad : (2 : ℕ∞) ≤ 1 := H.trans (coheight_le_one hdim y)
  norm_num at hbad

/-- The actual ambient local ring has dimension one at each nongeneric curve point. -/
theorem ringKrullDim_stalk_eq_one (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_one hdim x hx]
  rfl

/-- A proper closed subset of an integral scheme excludes its generic point. -/
theorem genericPoint_not_mem (Z : Closeds X) (hZ : Z ≠ ⊤) : genericPoint X ∉ Z := by
  intro hx
  have H := (genericPoint_spec X).mem_closed_set_iff Z.isClosed |>.mp hx
  apply hZ
  exact SetLike.coe_injective (Set.eq_univ_of_univ_subset H)

/-- The full original ideal on a normal curve is Cartier whenever its support is proper. -/
theorem isEffectiveCartier_of_support_ne_top [IsLocallyNoetherian X]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : D.support ≠ ⊤) : IsEffectiveCartierDivisor D := by
  let π := BlowupGluing.blowupStructure D
  let : IsModification π := BlowupModification.blowupStructure_isModification D hD
  let : IsIso π := NormalCurveModification.isIso_of_isModification π hnormal hdim
  have H := SNCIso.isEffectiveCartierDivisor_comap (asIso π).symm
    (D.comap π) (BlowupCartier.blowup_pullback_isEffectiveCartier D)
  simpa only [Iso.symm_hom, asIso_inv, ← Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id] using H

/-- Every reduced scheme with the T1 topology has actual field local rings,
hence is regular. No domain assumption on the whole scheme is needed. -/
theorem isRegularScheme_of_isReduced_of_t1 (Y : Scheme.{u}) [IsReduced Y] [T1Space Y] :
    IsRegularScheme Y := by
  intro y
  have hm : IsMax y := by
    intro z hyz
    have hzy : z = y := (show z ⤳ y from hyz).eq
    exact hzy.le
  have hco : Order.coheight y = 0 := Order.coheight_eq_zero.mpr hm
  let : Ring.KrullDimLE 0 (Y.presheaf.stalk y) :=
    krullDimLE_of_coheight_le (hco.le)
  let : Field (Y.presheaf.stalk y) := Ring.KrullDimLE.isField_of_isReduced.toField
  infer_instance

/-- Every actual closed subscheme with proper support on an integral curve has T1 topology. -/
theorem t1_subscheme (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) (hD : D.support ≠ ⊤) : T1Space D.subscheme := by
  constructor
  intro x
  have hx : D.subschemeι x ≠ genericPoint X := by
    intro h
    have hm : D.subschemeι x ∈ D.support := x.property
    exact genericPoint_not_mem D.support hD (h ▸ hm)
  have hc := isClosed_singleton_of_ne_genericPoint hdim (D.subschemeι x) hx
  convert hc.preimage D.subschemeι.continuous using 1
  ext y
  exact Set.mem_singleton_iff.trans
    (D.subschemeι.isEmbedding.injective.eq_iff).symm

/-- The actual reduced closed subscheme of a proper support on a curve is regular. -/
theorem isRegular_vanishingIdeal (hdim : topologicalKrullDim X ≤ 1)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    IsRegularScheme (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let D := Scheme.IdealSheafData.vanishingIdeal Z
  let : IsReduced D.subscheme := ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme Z
  let : T1Space D.subscheme := t1_subscheme hdim D hZ
  exact isRegularScheme_of_isReduced_of_t1 _

/-- A T1 scheme has topological dimension at most zero, since all its
specializations are equalities. -/
theorem topologicalKrullDim_le_zero_of_t1 (Y : Scheme.{u}) [T1Space Y] :
    topologicalKrullDim Y ≤ 0 := by
  change Order.krullDim (IrreducibleCloseds Y) ≤ 0
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro x y hxy
  exact ((show y ⤳ x from hxy).eq).le

/-- The actual proper closed support of a Noetherian integral curve has
finitely many points. -/
theorem finite_support [AlgebraicGeometry.IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    (D.support : Set X).Finite := by
  let : T1Space D.subscheme := t1_subscheme hdim D hD
  let : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  let : IsLocallyArtinian D.subscheme :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero
      (topologicalKrullDim_le_zero_of_t1 D.subscheme)
  let : CompactSpace D.subscheme := isCompact_iff_compactSpace.mp D.support.isClosed.isCompact
  let : Finite D.subscheme := finite_of_compact_of_discrete
  have H := Set.finite_range D.subschemeι
  rwa [D.range_subschemeι] at H

end DeJongAlterations.Geometry.CurveBoundary
