import Hironaka.Analytic.Unibranch.HironakaG10ChowSingularTowerDomination
import Hironaka.Resolution.HironakaG10ChowCompactBranch

/-!
# Calculus of strict transforms and flattening data (global flattening, route steps G1–G3)

The global half of Hironaka's flattening theorem (`HironakaFlattening`, Hironaka
`HironakaG10ChowFlatteningReduction`) is an iteration: each round blows up the base along a
tower and replaces the family by its strict transform; the algorithm stops when the strict
transform is flat (route: `work/hironaka-resume-20261111/G10C/GLOBAL-FLATTENING-ROUTE.md`;
sources Rydh, *Functorial flatification of proper morphisms*, proof of Theorem 1.1, and
McQuillan, *Flattening and algebrisation*, Fact 4.2). This module proves the formal part of
that iteration in the native category:

* `isOpenImmersion_of_comp`, `isOpenImmersionOn_id`, `IsOpenImmersionOn.isOpen`,
  `IsOpenImmersionOn.mono`, `IsOpenImmersionOn.comp`, `isOpenImmersionOn_of_isIsoOver` —
  open immersions on subsets restrict to open subsets and compose;
* `IsStrictTransform.refl`, **`IsStrictTransform.trans`** — the identity is a strict
  transform, and a strict transform of a strict transform is a strict transform of the
  original family relative to `E₂ ∪ σ₂⁻¹ E₁`;
* `IsFlatteningData` (tower, closed nowhere dense `E`, open immersion off `E`, strict transform:
  exactly the data of the conclusion of `HironakaFlattening` except flatness),
  `IsFlatteningData.refl`, **`IsFlatteningData.trans`**, `interior_union_preimage_eq_empty`;
* `FlatteningSequence` (a sequence of rounds), `FlatteningSequence.tower`, `.excep`, `.strict`,
  **`FlatteningSequence.isFlatteningData`** (the composite of the first `N` rounds);
* **`FlatteningSequence.exists_flat`** — termination over a compact base: if the images of the
  non-flat loci are closed, compatible under the round maps and admit no infinite compatible
  branch, some round is flat; **`FlatteningSequence.exists_flattening`** — then the original
  family has flattening data with a flat strict transform, i.e. the conclusion of
  `HironakaFlattening` for it.

No named input; nothing is assumed about the existence of rounds (that is the analytic content of
route steps G4–G7).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus

open Hironaka SourceReducedComplexSpace
  HironakaG10ChowFlatBimeromorphicIso HironakaG10ChowTowerDomination
  HironakaG10ChowFlatteningReduction HironakaG10ChowSingularTowerDomination
  HironakaG10ChowCompactBranch

noncomputable section

/-! ### Open immersions on subsets -/

section OpenImmersion

/-- A morphism of locally ringed spaces whose composite with an open immersion is an open
immersion is itself an open immersion. -/
theorem isOpenImmersion_of_comp {A B C : LocallyRingedSpace} (f : A ⟶ B) (g : B ⟶ C)
    [hg : LocallyRingedSpace.IsOpenImmersion g]
    [hfg : LocallyRingedSpace.IsOpenImmersion (f ≫ g)] :
    LocallyRingedSpace.IsOpenImmersion f := by
  have hstalk : ∀ a : A, IsIso (f.stalkMap a) := fun a => by
    have h₁ : IsIso ((f ≫ g).stalkMap a) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at h₁
    have h₂ : IsIso (g.stalkMap (f.base a)) := inferInstance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap (f.base a)) (f.stalkMap a) h₂ h₁
  have hemb : Topology.IsOpenEmbedding f.base :=
    Topology.IsOpenEmbedding.of_comp _ hg.base_open hfg.base_open
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f hemb

variable {X Y Z : SourceReducedComplexSpace}

/-- The identity is an open immersion on the whole space. -/
theorem isOpenImmersionOn_id (X : SourceReducedComplexSpace) : IsOpenImmersionOn (𝟙 X) univ := by
  refine ⟨X.obj.left, 𝟙 _, inferInstance, ?_, ?_⟩
  · exact range_id
  · change LocallyRingedSpace.IsOpenImmersion (𝟙 X.obj.left ≫ 𝟙 X.obj.left)
    infer_instance

/-- The set on which a morphism is an open immersion is open. -/
theorem IsOpenImmersionOn.isOpen {q : Y ⟶ X} {S : Set Y.obj.left} (h : IsOpenImmersionOn q S) :
    IsOpen S := by
  obtain ⟨V, j, hj, hr, -⟩ := h
  rw [← hr]
  exact hj.base_open.isOpen_range

/-- An open immersion on `S` is injective on `S`. -/
theorem IsOpenImmersionOn.injOn {q : Y ⟶ X} {S : Set Y.obj.left} (h : IsOpenImmersionOn q S) :
    InjOn q.hom.left.base S := by
  obtain ⟨V, j, hj, hr, hjq⟩ := h
  rintro a ha b hb hab
  rw [← hr] at ha hb
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  have huv : u = v := hjq.base_open.injective (by
    change q.hom.left.base (j.base u) = q.hom.left.base (j.base v)
    exact hab)
  rw [huv]

/-- Restriction of an open immersion on `S` to an open subset `T ⊆ S`. -/
theorem IsOpenImmersionOn.mono {q : Y ⟶ X} {S T : Set Y.obj.left} (h : IsOpenImmersionOn q S)
    (hT : IsOpen T) (hTS : T ⊆ S) : IsOpenImmersionOn q T := by
  obtain ⟨V, j, hj, hr, hjq⟩ := h
  have : LocallyRingedSpace.IsOpenImmersion j := hj
  have : LocallyRingedSpace.IsOpenImmersion (j ≫ q.hom.left) := hjq
  let O : Opens V := ⟨j.base ⁻¹' T, hT.preimage j.base.hom.continuous⟩
  let k := V.ofRestrict (Opens.isOpenEmbedding O)
  refine ⟨V.restrict (Opens.isOpenEmbedding O), k ≫ j, inferInstance, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hy
      have hyS : y ∈ range j.base := by
        rw [hr]
        exact hTS hy
      obtain ⟨v, hv⟩ := hyS
      refine ⟨⟨v, ?_⟩, hv⟩
      change j.base v ∈ T
      rw [hv]
      exact hy
  · change LocallyRingedSpace.IsOpenImmersion (k ≫ (j ≫ q.hom.left))
    infer_instance

/-- **Composition.**  If `q₂` is an open immersion on `S₂`, `q₁` one on `S₁`, and `q₂` maps
`S₂` into `S₁`, then `q₂ ≫ q₁` is an open immersion on `S₂`. -/
theorem IsOpenImmersionOn.comp {q₂ : Z ⟶ Y} {q₁ : Y ⟶ X} {S₂ : Set Z.obj.left}
    {S₁ : Set Y.obj.left} (h₂ : IsOpenImmersionOn q₂ S₂) (h₁ : IsOpenImmersionOn q₁ S₁)
    (hmap : MapsTo q₂.hom.left.base S₂ S₁) : IsOpenImmersionOn (q₂ ≫ q₁) S₂ := by
  obtain ⟨V₂, j₂, hj₂, hr₂, hjq₂⟩ := h₂
  obtain ⟨V₁, j₁, hj₁, hr₁, hjq₁⟩ := h₁
  have : LocallyRingedSpace.IsOpenImmersion j₁ := hj₁
  have : LocallyRingedSpace.IsOpenImmersion (j₁ ≫ q₁.hom.left) := hjq₁
  have : LocallyRingedSpace.IsOpenImmersion (j₂ ≫ q₂.hom.left) := hjq₂
  have hsub : range (j₂ ≫ q₂.hom.left).base ⊆ range j₁.base := by
    rintro _ ⟨v, rfl⟩
    rw [hr₁]
    apply hmap
    rw [← hr₂]
    exact ⟨v, rfl⟩
  let g := LocallyRingedSpace.IsOpenImmersion.lift j₁ (j₂ ≫ q₂.hom.left) hsub
  have hg : g ≫ j₁ = j₂ ≫ q₂.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j₁ (j₂ ≫ q₂.hom.left) hsub
  have : LocallyRingedSpace.IsOpenImmersion (g ≫ j₁) := by
    rw [hg]
    infer_instance
  have : LocallyRingedSpace.IsOpenImmersion g := isOpenImmersion_of_comp g j₁
  refine ⟨V₂, j₂, hj₂, hr₂, ?_⟩
  have heq : j₂ ≫ (q₂ ≫ q₁).hom.left = g ≫ (j₁ ≫ q₁.hom.left) := by
    change j₂ ≫ (q₂.hom.left ≫ q₁.hom.left) = g ≫ (j₁ ≫ q₁.hom.left)
    rw [← Category.assoc, ← Category.assoc, hg]
  rw [heq]
  infer_instance

/-- An isomorphism over `U` is an open immersion on the preimage of `U`. -/
theorem isOpenImmersionOn_of_isIsoOver {π : Y ⟶ X} {U : Set X.obj.left} (h : IsIsoOver π U) :
    IsOpenImmersionOn π (π.hom.left.base ⁻¹' U) := by
  obtain ⟨V, j, hj, hr, hjπ, -⟩ := h
  exact ⟨V, j, hj, hr, hjπ⟩

end OpenImmersion

/-! ### Strict transforms compose -/

section Strict

variable {X X₁ X₂ Y Y₁ Y₂ : SourceReducedComplexSpace}

/-- The identity tower: `(Y, f, 𝟙)` is a strict transform of a proper `f` relative to `∅`. -/
theorem IsStrictTransform.refl (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) :
    IsStrictTransform f (𝟙 X) ∅ f (𝟙 Y) where
  comm := by rw [Category.id_comp, Category.comp_id]
  proper := hf
  pair_injective a b _ hq := hq
  covers y x' _ hyx := ⟨y, hyx, rfl⟩
  dense := by
    rw [compl_empty, preimage_univ]
    exact dense_univ
  openImmersionOn := by
    rw [compl_empty, preimage_univ]
    exact isOpenImmersionOn_id Y

/-- Commutation of the strict-transform square on points. -/
theorem IsStrictTransform.comm_apply {f : Y ⟶ X} {σ : X₁ ⟶ X} {E : Set X₁.obj.left}
    {p : Y₁ ⟶ X₁} {q : Y₁ ⟶ Y} (h : IsStrictTransform f σ E p q) (y : Y₁.obj.left) :
    f.hom.left.base (q.hom.left.base y) = σ.hom.left.base (p.hom.left.base y) :=
  congrArg (fun H : Y₁ ⟶ X => H.hom.left.base y) h.comm

/-- **Strict transforms compose.**  If `(Y₁, p₁, q₁)` is a strict transform of `f` under
`σ₁` relative to `E₁` and `(Y₂, p₂, q₂)` a strict transform of `p₁` under `σ₂` relative to
`E₂` (both closed), then `(Y₂, p₂, q₂ ≫ q₁)` is a strict transform of `f` under `σ₂ ≫ σ₁`
relative to `E₂ ∪ σ₂⁻¹ E₁`. -/
theorem IsStrictTransform.trans {f : Y ⟶ X} {σ₁ : X₁ ⟶ X} {E₁ : Set X₁.obj.left}
    {p₁ : Y₁ ⟶ X₁} {q₁ : Y₁ ⟶ Y} (h₁ : IsStrictTransform f σ₁ E₁ p₁ q₁) (hE₁ : IsClosed E₁)
    {σ₂ : X₂ ⟶ X₁} {E₂ : Set X₂.obj.left} {p₂ : Y₂ ⟶ X₂} {q₂ : Y₂ ⟶ Y₁}
    (h₂ : IsStrictTransform p₁ σ₂ E₂ p₂ q₂) (hE₂ : IsClosed E₂) :
    IsStrictTransform f (σ₂ ≫ σ₁) (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁) p₂ (q₂ ≫ q₁) := by
  have hsq₂ := IsStrictTransform.comm_apply h₂
  have hD₂open : IsOpen (p₂.hom.left.base ⁻¹' E₂ᶜ) :=
    hE₂.isOpen_compl.preimage p₂.hom.left.base.hom.continuous
  have hEopen : IsOpen (p₂.hom.left.base ⁻¹' (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁)ᶜ) :=
    (hE₂.union (hE₁.preimage σ₂.hom.left.base.hom.continuous)).isOpen_compl.preimage
      p₂.hom.left.base.hom.continuous
  have hsub : p₂.hom.left.base ⁻¹' (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁)ᶜ ⊆
      p₂.hom.left.base ⁻¹' E₂ᶜ := fun y hy hyE => hy (Or.inl hyE)
  have hmaps : MapsTo q₂.hom.left.base (p₂.hom.left.base ⁻¹' (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁)ᶜ)
      (p₁.hom.left.base ⁻¹' E₁ᶜ) := by
    intro y hy hyE
    apply hy
    right
    change σ₂.hom.left.base (p₂.hom.left.base y) ∈ E₁
    rw [← hsq₂ y]
    exact hyE
  refine
    { comm := ?_
      proper := h₂.proper
      pair_injective := ?_
      covers := ?_
      dense := ?_
      openImmersionOn := ?_ }
  · rw [Category.assoc, h₁.comm, ← Category.assoc, h₂.comm, Category.assoc]
  · intro a b hp hq
    have hq' : q₁.hom.left.base (q₂.hom.left.base a) = q₁.hom.left.base (q₂.hom.left.base b) :=
      hq
    have hp₁ : p₁.hom.left.base (q₂.hom.left.base a) = p₁.hom.left.base (q₂.hom.left.base b) := by
      rw [hsq₂ a, hsq₂ b, hp]
    exact h₂.pair_injective a b hp (h₁.pair_injective _ _ hp₁ hq')
  · intro y x hx hyx
    have hx₂ : x ∉ E₂ := fun h => hx (Or.inl h)
    have hx₁ : σ₂.hom.left.base x ∉ E₁ := fun h => hx (Or.inr h)
    obtain ⟨y₁, hy₁p, hy₁q⟩ := h₁.covers y (σ₂.hom.left.base x) hx₁ hyx
    obtain ⟨y₂, hy₂p, hy₂q⟩ := h₂.covers y₁ x hx₂ hy₁p
    refine ⟨y₂, hy₂p, ?_⟩
    change q₁.hom.left.base (q₂.hom.left.base y₂) = y
    rw [hy₂q, hy₁q]
  · -- density: the dense open set `p₂⁻¹ E₂ᶜ` meets `q₂⁻¹ (p₁⁻¹ E₁ᶜ)` densely
    rw [dense_iff_inter_open]
    intro O hO hOne
    obtain ⟨y, hyO, hyD⟩ := h₂.dense.inter_open_nonempty O hO hOne
    have hopen : IsOpen (q₂.hom.left.base '' (O ∩ p₂.hom.left.base ⁻¹' E₂ᶜ)) :=
      isOpen_image_of_isOpenImmersionOn h₂.openImmersionOn _ (hO.inter hD₂open)
        inter_subset_right
    obtain ⟨_, ⟨⟨z, ⟨hzO, hzD⟩, rfl⟩, hzD₁⟩⟩ := h₁.dense.inter_open_nonempty _ hopen
      ⟨q₂.hom.left.base y, y, ⟨hyO, hyD⟩, rfl⟩
    refine ⟨z, hzO, ?_⟩
    rintro (hz | hz)
    · exact hzD hz
    · apply hzD₁
      change p₁.hom.left.base (q₂.hom.left.base z) ∈ E₁
      rw [hsq₂ z]
      exact hz
  · exact IsOpenImmersionOn.comp (IsOpenImmersionOn.mono h₂.openImmersionOn hEopen hsub)
      h₁.openImmersionOn hmaps

end Strict

/-! ### Flattening data -/

section Data

variable {X X₁ X₂ Y Y₁ Y₂ : SourceReducedComplexSpace}

/-- **Flattening data** of `f : Y ⟶ X`: a tower of native blowups `σ : X₁ ⟶ X`, a closed
nowhere dense `E ⊆ X₁` off which `σ` is an open immersion, and a strict transform
`(Y₁, p, q)` of `f` relative to `E`.  The conclusion of `HironakaFlattening` is exactly
flattening data with `p` flat. -/
structure IsFlatteningData (f : Y ⟶ X) (σ : X₁ ⟶ X) (E : Set X₁.obj.left) (p : Y₁ ⟶ X₁)
    (q : Y₁ ⟶ Y) : Prop where
  tower : IsNativeBlowupTower X X₁ σ
  closed : IsClosed E
  thin : interior E = ∅
  openImmersion : IsOpenImmersionOn σ Eᶜ
  strict : IsStrictTransform f σ E p q

/-- The trivial flattening data of a proper morphism. -/
theorem IsFlatteningData.refl (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) :
    IsFlatteningData f (𝟙 X) ∅ f (𝟙 Y) where
  tower := IsNativeBlowupTower.refl
  closed := isClosed_empty
  thin := interior_empty
  openImmersion := by
    rw [compl_empty]
    exact isOpenImmersionOn_id X
  strict := IsStrictTransform.refl f hf

/-- If `σ₂` is an open immersion off a closed nowhere dense `E₂` and `E₁` is nowhere dense,
then `E₂ ∪ σ₂⁻¹ E₁` is nowhere dense. -/
theorem interior_union_preimage_eq_empty {σ₂ : X₂ ⟶ X₁} {E₁ : Set X₁.obj.left}
    {E₂ : Set X₂.obj.left} (hE₁ : interior E₁ = ∅) (hE₂c : IsClosed E₂)
    (hE₂ : interior E₂ = ∅) (hσ₂ : IsOpenImmersionOn σ₂ E₂ᶜ) :
    interior (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro x hx
  set O := interior (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁)
  have hO : IsOpen O := isOpen_interior
  have himg : IsOpen (σ₂.hom.left.base '' (O ∩ E₂ᶜ)) :=
    isOpen_image_of_isOpenImmersionOn hσ₂ _ (hO.inter hE₂c.isOpen_compl) inter_subset_right
  have himgE : σ₂.hom.left.base '' (O ∩ E₂ᶜ) ⊆ E₁ := by
    rintro _ ⟨z, ⟨hzO, hzE₂⟩, rfl⟩
    rcases interior_subset hzO with h | h
    · exact absurd h hzE₂
    · exact h
  have hempty : σ₂.hom.left.base '' (O ∩ E₂ᶜ) = ∅ := by
    apply eq_empty_of_subset_empty
    rw [← hE₁]
    exact interior_maximal himgE himg
  have hOE₂ : O ⊆ E₂ := by
    intro z hz
    by_contra hzE₂
    have : σ₂.hom.left.base z ∈ σ₂.hom.left.base '' (O ∩ E₂ᶜ) := ⟨z, ⟨hz, hzE₂⟩, rfl⟩
    rw [hempty] at this
    exact this
  have : x ∈ interior E₂ := interior_maximal hOE₂ hO hx
  rw [hE₂] at this
  exact this

/-- **Flattening data compose**: flattening data `(σ₂, E₂, p₂, q₂)` of the strict transform
`p₁` of flattening data `(σ₁, E₁, p₁, q₁)` of `f` give flattening data
`(σ₂ ≫ σ₁, E₂ ∪ σ₂⁻¹ E₁, p₂, q₂ ≫ q₁)` of `f`. -/
theorem IsFlatteningData.trans {f : Y ⟶ X} {σ₁ : X₁ ⟶ X} {E₁ : Set X₁.obj.left}
    {p₁ : Y₁ ⟶ X₁} {q₁ : Y₁ ⟶ Y} (h₁ : IsFlatteningData f σ₁ E₁ p₁ q₁)
    {σ₂ : X₂ ⟶ X₁} {E₂ : Set X₂.obj.left} {p₂ : Y₂ ⟶ X₂} {q₂ : Y₂ ⟶ Y₁}
    (h₂ : IsFlatteningData p₁ σ₂ E₂ p₂ q₂) :
    IsFlatteningData f (σ₂ ≫ σ₁) (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁) p₂ (q₂ ≫ q₁) where
  tower := HironakaG10ChowSingularTowerDomination.IsNativeBlowupTower.comp h₂.tower h₁.tower
  closed := h₂.closed.union (h₁.closed.preimage σ₂.hom.left.base.hom.continuous)
  thin := interior_union_preimage_eq_empty h₁.thin h₂.closed h₂.thin h₂.openImmersion
  openImmersion := by
    have hopen : IsOpen (E₂ ∪ σ₂.hom.left.base ⁻¹' E₁)ᶜ :=
      (h₂.closed.union (h₁.closed.preimage σ₂.hom.left.base.hom.continuous)).isOpen_compl
    refine IsOpenImmersionOn.comp
      (IsOpenImmersionOn.mono h₂.openImmersion hopen fun x hx hxE => hx (Or.inl hxE))
      h₁.openImmersion ?_
    intro x hx hxE
    exact hx (Or.inr hxE)
  strict := IsStrictTransform.trans h₁.strict h₁.closed h₂.strict h₂.closed

end Data

/-! ### Sequences of rounds and termination over a compact base -/

/-- A **flattening sequence**: spaces `X n`, `Y n`, families `f n : Y n ⟶ X n`, and for every
`n` flattening data `(σ n, E n, f (n+1), q n)` of `f n`. -/
structure FlatteningSequence where
  X : ℕ → SourceReducedComplexSpace
  Y : ℕ → SourceReducedComplexSpace
  f : ∀ n, Y n ⟶ X n
  σ : ∀ n, X (n + 1) ⟶ X n
  E : ∀ n, Set (X (n + 1)).obj.left
  q : ∀ n, Y (n + 1) ⟶ Y n
  data : ∀ n, IsFlatteningData (f n) (σ n) (E n) (f (n + 1)) (q n)

namespace FlatteningSequence

variable (F : FlatteningSequence)

/-- The composite tower of the first `N` rounds. -/
def tower : ∀ N : ℕ, F.X N ⟶ F.X 0
  | 0 => 𝟙 _
  | N + 1 => F.σ N ≫ tower N

/-- The exceptional set of the first `N` rounds. -/
def excep : ∀ N : ℕ, Set (F.X N).obj.left
  | 0 => ∅
  | N + 1 => F.E N ∪ (F.σ N).hom.left.base ⁻¹' excep N

/-- The composite of the maps of the strict transforms of the first `N` rounds. -/
def strict : ∀ N : ℕ, F.Y N ⟶ F.Y 0
  | 0 => 𝟙 _
  | N + 1 => F.q N ≫ strict N

/-- **The first `N` rounds compose** to flattening data of `f 0`. -/
theorem isFlatteningData (hf : IsProperMap (F.f 0).hom.left.base) :
    ∀ N, IsFlatteningData (F.f 0) (F.tower N) (F.excep N) (F.f N) (F.strict N)
  | 0 => IsFlatteningData.refl (F.f 0) hf
  | N + 1 => IsFlatteningData.trans (isFlatteningData hf N) (F.data N)

/-- The image in `X n` of the non-flat locus of `f n`. -/
def nonflatImage (n : ℕ) : Set (F.X n).obj.left :=
  (F.f n).hom.left.base '' {y | ¬ ((F.f n).hom.left.stalkMap y).hom.Flat}

theorem isFlatMorphism_of_nonflatImage_eq_empty {n : ℕ} (h : F.nonflatImage n = ∅) :
    IsFlatMorphism (F.f n) := by
  intro y
  by_contra hy
  have : (F.f n).hom.left.base y ∈ F.nonflatImage n := ⟨y, hy, rfl⟩
  rw [h] at this
  exact this

/-- Over a compact base every stage is compact. -/
theorem compactSpace (hX : CompactSpace (F.X 0).obj.left) (n : ℕ)
    (hf : IsProperMap (F.f 0).hom.left.base) : CompactSpace (F.X n).obj.left := by
  have hp : IsProperMap (F.tower n).hom.left.base :=
    HironakaG10ChowSingularTowerDomination.IsNativeBlowupTower.isProperMap
      (F.isFlatteningData hf n).tower
  have hc := hp.isCompact_preimage (isCompact_univ (X := (F.X 0).obj.left))
  rw [preimage_univ] at hc
  exact ⟨hc⟩

/-- **Termination over a compact base.**  Let `X 0` be compact and `f 0` proper.  If the images
of the non-flat loci are closed, mapped into each other by the round maps, and admit no infinite
compatible branch, then some `f N` is flat. -/
theorem exists_flat (hX : CompactSpace (F.X 0).obj.left)
    (hf : IsProperMap (F.f 0).hom.left.base) (hclosed : ∀ n, IsClosed (F.nonflatImage n))
    (hmaps : ∀ n, MapsTo (F.σ n).hom.left.base (F.nonflatImage (n + 1)) (F.nonflatImage n))
    (hno : ∀ s : ∀ n, (F.X n).obj.left,
      ¬ IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage s) :
    ∃ N, IsFlatMorphism (F.f N) := by
  have : ∀ n, CompactSpace (F.X n).obj.left := fun n => F.compactSpace hX n hf
  have : ∀ n, T2Space (F.X n).obj.left := fun n => (F.X n).property.1
  obtain ⟨N, hN⟩ := exists_eq_empty_of_forall_not_isBranch (S := fun n => (F.X n).obj.left)
    (fun n => (F.σ n).hom.left.base) (fun n => (F.σ n).hom.left.base.hom.continuous)
    F.nonflatImage hclosed hmaps hno
  exact ⟨N, F.isFlatMorphism_of_nonflatImage_eq_empty hN⟩

/-- **Flattening from a terminating sequence of rounds**: under the hypotheses of `exists_flat`,
`f 0` has flattening data with a flat strict transform — the conclusion of
`HironakaFlattening` for `f 0`. -/
theorem exists_flattening (hX : CompactSpace (F.X 0).obj.left)
    (hf : IsProperMap (F.f 0).hom.left.base) (hclosed : ∀ n, IsClosed (F.nonflatImage n))
    (hmaps : ∀ n, MapsTo (F.σ n).hom.left.base (F.nonflatImage (n + 1)) (F.nonflatImage n))
    (hno : ∀ s : ∀ n, (F.X n).obj.left,
      ¬ IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage s) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ F.X 0) (E : Set X'.obj.left),
      IsNativeBlowupTower (F.X 0) X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ F.Y 0),
        IsStrictTransform (F.f 0) σ E p q ∧ IsFlatMorphism p := by
  obtain ⟨N, hN⟩ := F.exists_flat hX hf hclosed hmaps hno
  have hd := F.isFlatteningData hf N
  exact ⟨F.X N, F.tower N, F.excep N, hd.tower, hd.closed, hd.thin, hd.openImmersion,
    F.Y N, F.f N, F.strict N, hd.strict, hN⟩

end FlatteningSequence

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus
