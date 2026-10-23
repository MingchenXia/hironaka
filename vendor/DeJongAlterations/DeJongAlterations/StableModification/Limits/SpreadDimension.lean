import DeJongAlterations.StableModification.DeJong.FibrationGeneric
import DeJongAlterations.StableModification.DeJong.BaseStepFlatDimension
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.StableModification.Curves.SemistableOpen
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import DeJongAlterations.Geometry.FiberDimensionUpperSemicontinuityClosedCover
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Pure one-dimensionality and extension of the base field

Let `T` be a scheme locally of finite type over a field `F` and `Ω` any field extension of `F`
(given by a morphism `a : Spec Ω ⟶ Spec F`), with `T_Ω = T ×_F Ω` and projection
`p : T_Ω ⟶ T`. This file proves that every irreducible component of `T` has dimension one if
and only if every irreducible component of `T_Ω` has dimension one (for the "only if" direction
`T` is assumed quasi-compact):

* `topologicalKrullDim_preimage_fst_eq`: for an irreducible closed `Z ⊆ T`,
  `dim p⁻¹(Z) = dim Z` (the reduced structure on `Z` is an integral scheme of finite type over
  `F`, whose dimension is invariant under base field extension by Codex's
  `DeJong.topologicalKrullDim_pullback_field`);
* `pure_of_pullback` (descent): a component `Z` of `T` is the closure of the image of the generic
  point of a component `Z'` of `T_Ω` (`p` is flat and surjective), so `1 = dim Z' ≤ dim p⁻¹(Z) =
  dim Z ≤ dim T_Ω = 1`;
* `pure_pullback` (ascent): a component `Z'` of `T_Ω` lies in `p⁻¹(Z)` for the component `Z` of
  `T` spanned by the image of its generic point, so `dim Z' ≤ 1`; if `dim Z' = 0`, then `Z'` is a
  closed point which is open in the noetherian space `T_Ω`, its image is an open point of `T`
  (`Spec Ω ⟶ Spec F` is universally open, Stacks 0383), hence a closed point (`T` is a Jacobson
  space), and `Z` would be a point.

The fibre versions `pureOneDimensionalFibres_of_hasPureFiberDimension` (from the pure dimension
of all fibres, EGA IV 4.2, to the pure dimension of all geometric fibres, the form used in
`DeJong.IsNodalCurve` and in `Curves.SemistableOpen.PureOneDimensionalFibres`) and
`pure_fiber_of_pure_pullback` (from one geometric fibre over a point to the fibre at that point)
are what the spreading of semi-stability needs (blueprint `sm-spread.tex`,
`lem:sm-spread-field-extension`). They are used in M. Temkin, *Stable modification of relative
curves*, Rem. 3.1.1 (T:2283–2300), where property (a) "for any field extension `l/k`, `f`
satisfies `P` iff `f ⊗_k l` does" is assumed for the fibre property `P` being spread.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

open Geometry.FiberDimensionUpperSemicontinuityClosedCover
  (topologicalKrullDim_eq_iSup_componentDimension)

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Dimension is monotone along inclusions of subsets. -/
theorem topologicalKrullDim_mono {A B : Set X} (h : A ⊆ B) :
    topologicalKrullDim A ≤ topologicalKrullDim B :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- The irreducible components of the target of a homeomorphism all have dimension one if
those of the source do. -/
theorem pure_of_homeomorph (e : X ≃ₜ Y)
    (h : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = 1) :
    ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = 1 := by
  intro Z hZ
  have hZ' : e ⁻¹' Z ∈ irreducibleComponents X := by
    refine preimage_mem_irreducibleComponents hZ e.isOpenEmbedding ?_
    rw [e.range_coe, Set.inter_univ]
    exact hZ.1.nonempty
  have := h _ hZ'
  rw [← this]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    ((e.subtype (p := fun x ↦ x ∈ e ⁻¹' Z) (q := fun y ↦ y ∈ Z) (fun _ ↦ Iff.rfl)).isHomeomorph))
    |>.symm

end Topology

variable {F Ω : Type u} [Field F] [Field Ω] {T : Scheme.{u}} (q : T ⟶ Spec (.of F))
  (a : Spec (.of Ω) ⟶ Spec (.of F))

/-- Every morphism between spectra of fields is flat. -/
instance flat_of_field : Flat a := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective a
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  algebraize [φ.hom]
  change Module.Flat F Ω
  infer_instance

/-- Every morphism between spectra of fields is surjective. -/
instance surjective_of_field : Surjective a :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩

/-- **Dimension of preimages.** For an irreducible closed subset `Z` of a scheme locally of finite
type over `F`, the preimage of `Z` in `T ×_F Ω` has the dimension of `Z`. -/
theorem topologicalKrullDim_preimage_fst_eq [LocallyOfFiniteType q] {Z : Set T}
    (hZ : IsIrreducible Z) (hZc : IsClosed Z) :
    topologicalKrullDim ((pullback.fst q a) ⁻¹' Z) = topologicalKrullDim Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZc⟩ : Closeds T)
  let ι := I.subschemeι
  have hrange : Set.range ι = Z := by
    rw [I.range_subschemeι]
    simp [I]
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  have : IsReduced I.subscheme :=
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  let e : I.subscheme ≃ₜ Z := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : Nonempty I.subscheme := ⟨e.symm ⟨hZ.nonempty.some, hZ.nonempty.some_mem⟩⟩
  have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
  have : IrreducibleSpace I.subscheme := e.isOpenEmbedding.irreducibleSpace
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨d, hd, -⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg (ι ≫ q)
  have hP := DeJong.topologicalKrullDim_pullback_field (ι ≫ q) Ω a d hd
  -- the preimage of `Z` is the base change of the closed immersion `ι`
  let s := pullback.snd ι (pullback.fst q a)
  have hsrange : Set.range s = (pullback.fst q a) ⁻¹' Z := by
    rw [Scheme.Pullback.range_snd, hrange]
  have hsemb : IsEmbedding s := s.isClosedEmbedding.isEmbedding
  have h1 : topologicalKrullDim (pullback (C := Scheme.{u}) ι (pullback.fst q a)) =
      topologicalKrullDim ((pullback.fst q a) ⁻¹' Z) :=
    DeJong.FlatDimension.topologicalKrullDim_eq_of_isEmbedding hsemb hsrange
  have h2 : topologicalKrullDim (pullback (C := Scheme.{u}) ι (pullback.fst q a)) =
      topologicalKrullDim (pullback (C := Scheme.{u}) (ι ≫ q) a) :=
    (pullbackRightPullbackFstIso q a ι).schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq
  have h3 : topologicalKrullDim I.subscheme = topologicalKrullDim Z :=
    DeJong.FlatDimension.topologicalKrullDim_eq_of_isEmbedding hemb hrange
  rw [← h1, h2, hP, ← hd, h3]

/-- **Descent of pure one-dimensionality** along a base field extension: if every irreducible
component of `T ×_F Ω` has dimension one, so has every irreducible component of `T`. -/
theorem pure_of_pullback [LocallyOfFiniteType q]
    (h : ∀ Z' ∈ irreducibleComponents (pullback (C := Scheme.{u}) q a),
      topologicalKrullDim Z' = 1) :
    ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = 1 := by
  intro Z hZ
  set p := pullback.fst q a
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hζ : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc
  obtain ⟨ζ'', hζ''⟩ := p.surjective hZ.1.genericPoint
  obtain ⟨Z', hZ', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({ζ''} : Set (pullback (C := Scheme.{u}) q a)) isIrreducible_singleton
  have hZ'c := isClosed_of_mem_irreducibleComponents Z' hZ'
  have hζ' : IsGenericPoint hZ'.1.genericPoint Z' := hZ'.1.isGenericPoint_genericPoint hZ'c
  have hsp : hZ'.1.genericPoint ⤳ ζ'' := hζ'.specializes (hsub rfl)
  have hC := Curves.genericPoint_image_mem_irreducibleComponents p hZ'
  -- the image of the generic point of `Z'` is the generic point of `Z`
  have hmem : hZ.1.genericPoint ∈ closure {p hZ'.1.genericPoint} := by
    rw [← hζ'']
    exact (hsp.map p.continuous).mem_closure
  have hZsub : Z ⊆ closure {p hZ'.1.genericPoint} := by
    rw [← hζ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  have hZeq : closure {p hZ'.1.genericPoint} = Z := Set.Subset.antisymm (hZ.2 hC.1 hZsub) hZsub
  have hZ'sub : Z' ⊆ p ⁻¹' Z := by
    rw [← hζ'.def]
    refine closure_minimal ?_ (hZc.preimage p.continuous)
    rw [Set.singleton_subset_iff, Set.mem_preimage, ← hZeq]
    exact subset_closure rfl
  have hdim := topologicalKrullDim_preimage_fst_eq q a hZ.1 hZc
  apply le_antisymm
  · rw [← hdim]
    refine (topologicalKrullDim_subspace_le _ _).trans ?_
    rw [topologicalKrullDim_eq_iSup_componentDimension]
    exact iSup_le fun W ↦ (h W.1 W.2).le
  · rw [← h Z' hZ', ← hdim]
    exact topologicalKrullDim_mono hZ'sub

/-- **Ascent of pure one-dimensionality** along a base field extension: if `T` is quasi-compact
and every irreducible component of `T` has dimension one, so has every irreducible component of
`T ×_F Ω`. -/
theorem pure_pullback [LocallyOfFiniteType q] [QuasiCompact q]
    (h : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = 1) :
    ∀ Z' ∈ irreducibleComponents (pullback (C := Scheme.{u}) q a), topologicalKrullDim Z' = 1 := by
  intro Z' hZ'
  set p := pullback.fst q a
  have hZ'c := isClosed_of_mem_irreducibleComponents Z' hZ'
  set ζ' := hZ'.1.genericPoint
  have hζ' : IsGenericPoint ζ' Z' := hZ'.1.isGenericPoint_genericPoint hZ'c
  have hC := Curves.genericPoint_image_mem_irreducibleComponents p hZ'
  have h1 := h _ hC
  have hZ'sub : Z' ⊆ p ⁻¹' closure {p ζ'} := by
    rw [← hζ'.def]
    refine closure_minimal ?_ (isClosed_closure.preimage p.continuous)
    rw [Set.singleton_subset_iff, Set.mem_preimage]
    exact subset_closure rfl
  have hle : topologicalKrullDim Z' ≤ 1 := by
    rw [← h1, ← topologicalKrullDim_preimage_fst_eq q a hC.1 isClosed_closure]
    exact topologicalKrullDim_mono hZ'sub
  refine Curves.eq_one_of_le_one_of_not_le_zero hle fun h0 ↦ ?_
  have : QuasiSober Z' := hZ'c.isClosedEmbedding_subtypeVal.quasiSober
  have hZeq : Z' = {ζ'} := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_) (Set.singleton_subset_iff.mpr hζ'.mem)
    have hsp : (⟨ζ', hζ'.mem⟩ : Z') ⤳ ⟨z, hz⟩ :=
      (IsInducing.subtypeVal.specializes_iff).mp (hζ'.specializes hz)
    exact (congrArg Subtype.val
      (Curves.eq_of_specializes_of_topologicalKrullDim_le_zero h0 hsp)).symm
  -- `T_Ω` is a noetherian space, so its zero-dimensional component is an open point
  have : IsNoetherian (pullback (C := Scheme.{u}) q a) := ⟨⟩
  obtain ⟨o, ho, hne, hosub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z' hZ'
  have hoeq : o = {ζ'} := by
    rw [hZeq] at hosub
    exact Set.Subset.antisymm hosub (fun x hx ↦ by
      obtain ⟨y, hy⟩ := hne
      rw [Set.mem_singleton_iff.mp hx, ← Set.mem_singleton_iff.mp (hosub hy)]
      exact hy)
  have hopen : IsOpen ({p ζ'} : Set T) := by
    have := p.isOpenMap _ ho
    rwa [hoeq, Set.image_singleton] at this
  -- an open point of a scheme locally of finite type over a field is closed
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty (p ζ'))
    hopen.isLocallyClosed
  rw [Set.mem_singleton_iff.mp hz, mem_closedPoints_iff] at hzc
  rw [hzc.closure_eq] at h1
  have h0' := topologicalKrullDim_zero_of_discreteTopology ({p ζ'} : Set T)
  rw [h1] at h0'
  exact absurd h0' (by decide)

section Fibres

variable {Y S : Scheme.{u}} (g : Y ⟶ S)

/-- A geometric point `a : Spec K ⟶ S` factors through `Spec κ(s) ⟶ S` for its image `s`, and
the geometric fibre `Y ×_S Spec K` is the base change of the fibre `Y_s` along
`Spec K ⟶ Spec κ(s)`. -/
theorem exists_pullback_iso_fiber {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    ∃ (φ : S.residueField (a (IsLocalRing.closedPoint K)) ⟶ .of K),
      Nonempty (pullback (g.fiberToSpecResidueField (a (IsLocalRing.closedPoint K)))
        (Spec.map φ) ≅ pullback g a) := by
  set s := a (IsLocalRing.closedPoint K)
  let φ : S.residueField s ⟶ .of K := ((Scheme.SpecToEquivOfField K S) a).2
  have ha : Spec.map φ ≫ S.fromSpecResidueField s = a :=
    (Scheme.SpecToEquivOfField K S).left_inv a
  refine ⟨φ, ⟨?_⟩⟩
  refine pullbackLeftPullbackSndIso g (S.fromSpecResidueField s) (Spec.map φ) ≪≫ ?_
  exact pullback.congrHom rfl ha

variable [LocallyOfFiniteType g]

instance (s : S) : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance [QuasiCompact g] (s : S) : QuasiCompact (g.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- **From fibres to geometric fibres.** If every irreducible component of every fibre of a
quasi-compact morphism locally of finite type has dimension one, then so has every irreducible
component of every geometric fibre. -/
theorem pureOneDimensionalFibres_of_hasPureFiberDimension [QuasiCompact g]
    (h : DeJong.HasPureFiberDimension g 1) : Curves.SemistableOpen.PureOneDimensionalFibres g := by
  intro K _ _ a
  obtain ⟨φ, ⟨e⟩⟩ := exists_pullback_iso_fiber g a
  refine pure_of_homeomorph e.schemeIsoToHomeo ?_
  exact pure_pullback (g.fiberToSpecResidueField _) (Spec.map φ) (fun Z hZ ↦ by
    simpa using h _ Z hZ)

/-- **From a geometric fibre to the fibre.** If every irreducible component of the geometric
fibre of `g` at `a : Spec K ⟶ S` has dimension one, then so has every irreducible component of
the fibre of `g` at the image of `a`. -/
theorem pure_fiber_of_pure_pullback {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (h : ∀ Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) g a), topologicalKrullDim Z = 1) :
    ∀ Z ∈ irreducibleComponents (g.fiber (a (IsLocalRing.closedPoint K))),
      topologicalKrullDim Z = 1 := by
  obtain ⟨φ, ⟨e⟩⟩ := exists_pullback_iso_fiber g a
  exact pure_of_pullback (g.fiberToSpecResidueField _) (Spec.map φ)
    (pure_of_homeomorph e.symm.schemeIsoToHomeo h)

end Fibres

end DeJongAlterations.StableModification.Limits.Spread
