import Hironaka.Resolution.HironakaIntrinsicComplexAnalyticRegularLocus

/-!
# Intrinsic regularity is local for open immersions (G11 regular-locus transport)

For two locally ringed spaces over the complex point and an open immersion `k` between them
commuting with the structure maps, a point is an intrinsic regular point (of a given dimension)
of the source exactly when its image is one of the target. Consequently two open immersions out
of the same locally ringed space, compatible with the structure maps, see the same regular
points. This is the pointwise regularity transport used for isomorphisms over open subsets
(goal G11, leaf G11.REM.23); no resolution data, global embedding or compactness is used.

Blueprint: `hironaka-g11-resume-regular-open-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11IntrinsicRegularOpenImmersion

noncomputable section

open HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus

private theorem openImmersion_lift {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem native_inclusion_point {d : ℕ} (O : Opens (ComplexModel d)) :
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d))) ≫
      ambientPointMap d (ComplexModel d) = ambientPointMap d O :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (IP := 𝓘(ℂ, ComplexModel 0))
    contMDiff_subtype_val
    (show ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : ComplexModel d => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- A native manifold chart of the source of an open immersion over the complex point is a
native manifold chart of its target. -/
theorem intrinsicRegularAtDim_map {A B : Over complexPoint} (k : A.left ⟶ B.left)
    (hk : LocallyRingedSpace.IsOpenImmersion k) (hkp : k ≫ B.hom = A.hom) (a : A.left) (d : ℕ)
    (h : intrinsicRegularAtDim A a d) : intrinsicRegularAtDim B (k.base a) d := by
  obtain ⟨O, i, hi, hip, v, hv⟩ := h
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨O, i ≫ k, inferInstance, ?_, v, ?_⟩
  · rw [Category.assoc, hkp]
    exact hip
  · change k.base (i.base v) = k.base a
    rw [hv]

/-- Conversely, a native manifold chart of the target through the image of a point restricts,
over the open image of the open immersion, to a native manifold chart of the source. -/
theorem intrinsicRegularAtDim_of_map {A B : Over complexPoint} (k : A.left ⟶ B.left)
    (hk : LocallyRingedSpace.IsOpenImmersion k) (hkp : k ≫ B.hom = A.hom) (a : A.left) (d : ℕ)
    (h : intrinsicRegularAtDim B (k.base a) d) : intrinsicRegularAtDim A a d := by
  obtain ⟨O, i, hi, hip, v, hv⟩ := h
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  let P : Opens O := ⟨i.base ⁻¹' range k.base,
    hk.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  have hvP : v ∈ P := by
    change i.base v ∈ range k.base
    exact ⟨a, hv.symm⟩
  let V : Opens (ComplexModel d) :=
    ⟨(Subtype.val : O → ComplexModel d) '' (P : Set O),
      O.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  let α := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  let β := ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  have hab : range β.base ⊆ range α.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨u, _hu, huz⟩ := z.property
    exact ⟨u, huz⟩
  let m := LocallyRingedSpace.IsOpenImmersion.lift α β hab
  let : LocallyRingedSpace.IsOpenImmersion m := openImmersion_lift α β hab
  have hma : m ≫ α = β := LocallyRingedSpace.IsOpenImmersion.lift_fac α β hab
  have hmP (z : V) : m.base z ∈ P := by
    obtain ⟨u, hu, huz⟩ := z.property
    have hmz : (m.base z).val = z.val := congrArg (fun f => f.base z) hma
    have hmu : m.base z = u := Subtype.ext (hmz.trans huz.symm)
    exact hmu.symm ▸ hu
  have hmp : m ≫ ambientPointMap d O = ambientPointMap d V := by
    rw [← native_inclusion_point O, ← Category.assoc, hma]
    exact native_inclusion_point V
  let g := m ≫ i
  have hgp : g ≫ B.hom = ambientPointMap d V := by
    dsimp only [g]
    rw [Category.assoc, hip, hmp]
  have hge : range g.base ⊆ range k.base := by
    rintro _ ⟨z, rfl⟩
    exact hmP z
  let H := LocallyRingedSpace.IsOpenImmersion.lift k g hge
  let : LocallyRingedSpace.IsOpenImmersion H := openImmersion_lift k g hge
  have hHk : H ≫ k = g := LocallyRingedSpace.IsOpenImmersion.lift_fac k g hge
  have hHp : H ≫ A.hom = ambientPointMap d V := by
    rw [← hkp, ← Category.assoc, hHk, hgp]
  let z : V := ⟨v.val, ⟨v, hvP, rfl⟩⟩
  have hmv : m.base z = v := by
    apply Subtype.ext
    exact congrArg (fun f => f.base z) hma
  have hHa : H.base z = a := by
    apply hk.base_open.injective
    have hh := congrArg (fun f => f.base z) hHk
    change k.base (H.base z) = i.base (m.base z) at hh
    rw [hmv] at hh
    exact hh.trans hv
  exact ⟨V, H, inferInstance, hHp, z, hHa⟩

/-- Intrinsic regularity of a fixed dimension is reflected and preserved by open immersions
over the complex point. -/
theorem intrinsicRegularAtDim_map_iff {A B : Over complexPoint} (k : A.left ⟶ B.left)
    (hk : LocallyRingedSpace.IsOpenImmersion k) (hkp : k ≫ B.hom = A.hom) (a : A.left) (d : ℕ) :
    intrinsicRegularAtDim B (k.base a) d ↔ intrinsicRegularAtDim A a d :=
  ⟨intrinsicRegularAtDim_of_map k hk hkp a d, intrinsicRegularAtDim_map k hk hkp a d⟩

/-- The intrinsic regular locus of the source of an open immersion over the complex point is the
preimage of the intrinsic regular locus of the target. -/
theorem mem_intrinsicRegularLocus_map_iff {A B : Over complexPoint} (k : A.left ⟶ B.left)
    (hk : LocallyRingedSpace.IsOpenImmersion k) (hkp : k ≫ B.hom = A.hom) (a : A.left) :
    k.base a ∈ intrinsicRegularLocus B ↔ a ∈ intrinsicRegularLocus A := by
  change (∃ d : ℕ, intrinsicRegularAtDim B (k.base a) d) ↔ ∃ d : ℕ, intrinsicRegularAtDim A a d
  exact exists_congr fun d => intrinsicRegularAtDim_map_iff k hk hkp a d

theorem preimage_intrinsicRegularLocus {A B : Over complexPoint} (k : A.left ⟶ B.left)
    (hk : LocallyRingedSpace.IsOpenImmersion k) (hkp : k ≫ B.hom = A.hom) :
    k.base ⁻¹' intrinsicRegularLocus B = intrinsicRegularLocus A :=
  Set.ext fun a => mem_intrinsicRegularLocus_map_iff k hk hkp a

/-- Two open immersions out of the SAME locally ringed space, compatible with the structure maps
to the complex point, see the same intrinsic regular points (of every dimension). -/
theorem intrinsicRegularAtDim_iff_of_openImmersions {A B : Over complexPoint}
    {V : LocallyRingedSpace} (j : V ⟶ A.left) (j' : V ⟶ B.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j) (hj' : LocallyRingedSpace.IsOpenImmersion j')
    (h : j ≫ A.hom = j' ≫ B.hom) (v : V) (d : ℕ) :
    intrinsicRegularAtDim A (j.base v) d ↔ intrinsicRegularAtDim B (j'.base v) d := by
  let C : Over complexPoint := Over.mk (j ≫ A.hom)
  have h₁ : intrinsicRegularAtDim A (j.base v) d ↔ intrinsicRegularAtDim C v d :=
    intrinsicRegularAtDim_map_iff (A := C) (B := A) j hj rfl v d
  have h₂ : intrinsicRegularAtDim B (j'.base v) d ↔ intrinsicRegularAtDim C v d :=
    intrinsicRegularAtDim_map_iff (A := C) (B := B) j' hj' h.symm v d
  exact h₁.trans h₂.symm

theorem mem_intrinsicRegularLocus_iff_of_openImmersions {A B : Over complexPoint}
    {V : LocallyRingedSpace} (j : V ⟶ A.left) (j' : V ⟶ B.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j) (hj' : LocallyRingedSpace.IsOpenImmersion j')
    (h : j ≫ A.hom = j' ≫ B.hom) (v : V) :
    j.base v ∈ intrinsicRegularLocus A ↔ j'.base v ∈ intrinsicRegularLocus B := by
  change (∃ d : ℕ, intrinsicRegularAtDim A (j.base v) d) ↔
    ∃ d : ℕ, intrinsicRegularAtDim B (j'.base v) d
  exact exists_congr fun d => intrinsicRegularAtDim_iff_of_openImmersions j j' hj hj' h v d

theorem mem_intrinsicSingularLocus_iff_of_openImmersions {A B : Over complexPoint}
    {V : LocallyRingedSpace} (j : V ⟶ A.left) (j' : V ⟶ B.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j) (hj' : LocallyRingedSpace.IsOpenImmersion j')
    (h : j ≫ A.hom = j' ≫ B.hom) (v : V) :
    j.base v ∈ intrinsicSingularLocus A ↔ j'.base v ∈ intrinsicSingularLocus B := by
  change j.base v ∉ intrinsicRegularLocus A ↔ j'.base v ∉ intrinsicRegularLocus B
  exact not_congr (mem_intrinsicRegularLocus_iff_of_openImmersions j j' hj hj' h v)

end

end Hironaka.HironakaG11IntrinsicRegularOpenImmersion
