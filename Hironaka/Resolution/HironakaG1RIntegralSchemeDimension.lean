import Hironaka.Resolution.HironakaG1RFunctionFieldDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-!
# The dimension of an integral scheme of finite type over a field

**Main result** (`topologicalKrullDim_eq_ringKrullDim`): let `X` be an integral scheme locally of
finite type over a field `k`.  For EVERY nonempty affine open `U ⊆ X`,

  `topologicalKrullDim X = ringKrullDim Γ(X, U)`.

Consequently (`topologicalKrullDim_eq_of_isOpenImmersion`) every nonempty open subscheme of `X` has
the dimension of `X`, and the dimension is a natural number (`exists_topologicalKrullDim_eq_nat`).

Proof.  All rings `Γ(X, U)` (`U` nonempty affine) are finite type `k`-domains with the same
fraction field, the function field of `X`, compatibly with `k` (the `k`-structures all come from
`Γ(X, ⊤)`), so they have the same Krull dimension
(`HironakaG1RFunctionFieldDimension.ringKrullDim_eq_of_isFractionRing`, i.e. the transcendence
degree of the function field).  The dimension of `X` is the supremum of the coheights of its points,
and a point of an affine open `U` has the same coheight in `U` (Mathlib's
`coheight_eq_of_isOpenImmersion`), which is at most `dim Γ(X, U)`; conversely `Spec Γ(X, U) ↪ X` is
an embedding.  The covering argument follows `Hironaka/Geometry/
RationalCoordinateMapGenericFiberDimension.lean` (`topologicalKrullDim_le_of_affine_sections`).

Only Mathlib and lane G1's ring-level modules are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (node `g1r:integral-scheme-dimension`).
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace Hironaka.HironakaG1RIntegralSchemeDimension

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The `k`-structure of `Γ(X, U)` induced by a morphism `X ⟶ Spec k`. -/
noncomputable def sectionsRingHom (f : X ⟶ Spec (.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- On an affine open, `Γ(X, U)` is of finite type over `k`. -/
theorem sectionsRingHom_finiteType (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens}
    (hU : IsAffineOpen U) : (sectionsRingHom f U).FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

/-- The `k`-structures are compatible with restriction. -/
theorem sectionsRingHom_res (f : X ⟶ Spec (.of k)) {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsRingHom f U) = sectionsRingHom f V := by
  have e := Scheme.Hom.appLE_map f (U := ⊤) (show U ≤ f ⁻¹ᵁ ⊤ from le_top) (homOfLE h).op
  rw [sectionsRingHom, sectionsRingHom, ← RingHom.comp_assoc, ← CommRingCat.hom_comp]
  exact congrArg (fun φ ↦ φ.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) e

/-- The `k`-structures of all nonempty opens induce the same `k`-structure on the function
field. -/
theorem germ_comp_sectionsRingHom [IsIntegral X] (f : X ⟶ Spec (.of k)) (U V : X.Opens)
    [Nonempty U] [Nonempty V] :
    (X.germToFunctionField U).hom.comp (sectionsRingHom f U) =
      (X.germToFunctionField V).hom.comp (sectionsRingHom f V) := by
  have hU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hW : genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
  have key : ∀ (T : X.Opens) (hT : genericPoint X ∈ T) (hle : U ⊓ V ≤ T),
      (X.presheaf.germ T (genericPoint X) hT).hom.comp (sectionsRingHom f T) =
        (X.presheaf.germ (U ⊓ V) (genericPoint X) hW).hom.comp (sectionsRingHom f (U ⊓ V)) := by
    intro T hT hle
    rw [← sectionsRingHom_res f hle, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
      X.presheaf.germ_res]
  exact (key U hU inf_le_left).trans (key V hV inf_le_right).symm

/-- **Nonempty affine opens of an integral scheme of finite type over a field have the same
dimension.** -/
theorem ringKrullDim_eq_of_isAffineOpen [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [Nonempty U] [Nonempty V] : ringKrullDim Γ(X, U) = ringKrullDim Γ(X, V) := by
  let := (sectionsRingHom f U).toAlgebra
  let := (sectionsRingHom f V).toAlgebra
  let : Algebra k X.functionField :=
    ((X.germToFunctionField U).hom.comp (sectionsRingHom f U)).toAlgebra
  have : IsScalarTower k Γ(X, U) X.functionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k Γ(X, V) X.functionField := IsScalarTower.of_algebraMap_eq fun a ↦
    RingHom.congr_fun (germ_comp_sectionsRingHom f U V) a
  have : Algebra.FiniteType k Γ(X, U) := sectionsRingHom_finiteType f hU
  have : Algebra.FiniteType k Γ(X, V) := sectionsRingHom_finiteType f hV
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  exact HironakaG1RFunctionFieldDimension.ringKrullDim_eq_of_isFractionRing k Γ(X, U) Γ(X, V)
    X.functionField

/-- An affine open bounds the dimension of the scheme from below. -/
theorem ringKrullDim_le_topologicalKrullDim {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) ≤ topologicalKrullDim X := by
  have hle := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ topologicalKrullDim X at hle
  rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hle

/-- Bounds on all nonempty affine opens bound the dimension of the scheme (coheights of points are
computed in affine opens). -/
theorem topologicalKrullDim_le_of_affineOpens (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ U : X.affineOpens, Nonempty U.1 → ringKrullDim Γ(X, U.1) ≤ d) :
    topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
      (⊤ : X.Opens).isOpen
  replace hU : IsAffineOpen U := hU
  obtain ⟨z, hz⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [← hz, coheight_eq_of_isOpenImmersion hU.fromSpec]
  have hdim : topologicalKrullDim (Spec Γ(X, U)) ≤ d := by
    change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ d
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact h ⟨U, hU⟩ ⟨⟨x, hx⟩⟩
  have ho : Order.krullDim (Spec Γ(X, U)) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(X, U)))]
    exact hdim
  exact (Order.coheight_le_krullDim z).trans ho

/-- **The dimension of an integral scheme of finite type over a field is the Krull dimension of
the ring of sections of ANY nonempty affine open.** -/
theorem topologicalKrullDim_eq_ringKrullDim [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  refine le_antisymm (topologicalKrullDim_le_of_affineOpens X _ fun V hV ↦ ?_)
    (ringKrullDim_le_topologicalKrullDim hU)
  exact (ringKrullDim_eq_of_isAffineOpen f V.2 hU).le

/-- The dimension of an integral scheme of finite type over a field is a natural number. -/
theorem exists_topologicalKrullDim_eq_nat [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : ∃ n : ℕ, topologicalKrullDim X = n := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show genericPoint X ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  change X.Opens at U
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  let := (sectionsRingHom f U).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := sectionsRingHom_finiteType f hU
  obtain ⟨n, hn, -⟩ := HironakaG1RFunctionFieldDimension.exists_ringKrullDim_eq_trdeg k Γ(X, U)
    (FractionRing Γ(X, U))
  exact ⟨n, (topologicalKrullDim_eq_ringKrullDim f hU).trans hn⟩

/-- **Dimension is constant on nonempty opens**: a nonempty open subscheme of an integral scheme of
finite type over a field has the same dimension. -/
theorem topologicalKrullDim_eq_of_isOpenImmersion [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] [Nonempty Y] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  have : IsIntegral Y := isIntegral_of_isOpenImmersion j
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show (Nonempty.some ‹Nonempty Y›) ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  change Y.Opens at V
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty (j ''ᵁ V) := ⟨⟨j (Nonempty.some ‹Nonempty Y›), ⟨_, hx, rfl⟩⟩⟩
  rw [topologicalKrullDim_eq_ringKrullDim (j ≫ f) hV,
    topologicalKrullDim_eq_ringKrullDim f (hV.image_of_isOpenImmersion j)]
  exact ringKrullDim_eq_of_ringEquiv (j.appIso V).commRingCatIsoToRingEquiv.symm

end Hironaka.HironakaG1RIntegralSchemeDimension
