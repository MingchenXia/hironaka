import Hironaka.Resolution.HironakaG10PNKernelFamily
import Hironaka.Resolution.HironakaG10PNIdealNoetherModel

/-! Kernel families across squares of embeddings, and pointwise local finite generation (lane
G10P, run 0080 r5).  Blueprint: `hironaka-g10-pn-step-kernel.tex`.

* `IsLocallyFinitelyGeneratedAt X J x` — the pointwise form of `IsLocallyFinitelyGenerated`; it is
  pulled back along any morphism and ascends along open immersions.
* `kerFamily_apply_of_injective` — along a morphism injective on points the kernel family at an
  image point is the preimage of the family under the stalk map; hence
  `pullFamily_kerFamily_of_surjective` (the pull of the kernel family is the family when moreover
  the stalk maps are surjective: closed embeddings, open immersions).
* **`pullFamily_kerFamily_of_openSquare`** — for a square `k ≫ q = Q ≫ J` of open immersions `J, k`
  whose source chart contains every point over the target chart where the family is not the unit
  ideal, the kernel family of `q` restricted to the chart of `J` is the kernel family of `Q` of the
  restricted family (charts of glued blowups).
* **`pullFamily_kerFamily_of_closedSquare`** — for a square `ι_S ≫ Π = Q ≫ ι_W` with `ι_W` injective
  with surjective stalk maps, the kernel family of `Q` is the restriction of the kernel family of `Π`
  of the push `kerFamily ι_S K` (embedded models in ambient manifolds);
  `kerFamily_actualSubspaceInclusion` identifies that push with `pushFamily`. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.HironakaG10PNKernelSquare

open HironakaG10PNIdealFamily HironakaG10PNPointIdeal HironakaG10PNKernelFamily

noncomputable section

universe u

section At

variable {X Y : LocallyRingedSpace.{u}}

/-- **Pointwise local finite generation**: near `x` the germs of the same finitely many sections
span the family at every nearby point. -/
def IsLocallyFinitelyGeneratedAt (X : LocallyRingedSpace.{u})
    (J : ∀ x : X, Ideal (X.presheaf.stalk x)) (x : X) : Prop :=
  ∃ (W : Opens X) (_hxW : x ∈ W) (r : ℕ) (s : Fin r → X.presheaf.obj (op W)),
    ∀ (y : X) (hy : y ∈ W), J y = Ideal.span (Set.range fun i => X.presheaf.germ W y hy (s i))

theorem isLocallyFinitelyGenerated_iff {J : ∀ x : X, Ideal (X.presheaf.stalk x)} :
    IsLocallyFinitelyGenerated X J ↔ ∀ x, IsLocallyFinitelyGeneratedAt X J x := Iff.rfl

theorem IsLocallyFinitelyGeneratedAt.congr {J J' : ∀ x : X, Ideal (X.presheaf.stalk x)} {x : X}
    (h : IsLocallyFinitelyGeneratedAt X J x) (O : Opens X) (hxO : x ∈ O)
    (hJ : ∀ y, y ∈ O → J y = J' y) : IsLocallyFinitelyGeneratedAt X J' x := by
  obtain ⟨W, hxW, r, s, hs⟩ := h
  refine ⟨W ⊓ O, ⟨hxW, hxO⟩, r, fun i => X.presheaf.map (homOfLE inf_le_left).op (s i),
    fun y hy => ?_⟩
  rw [← hJ y hy.2, hs y hy.1]
  congr 1
  refine congrArg Set.range (funext fun i => ?_)
  exact (TopCat.Presheaf.germ_res_apply X.presheaf _ y hy (s i)).symm

/-- A family which is the unit ideal near `x` is locally finitely generated at `x`. -/
theorem isLocallyFinitelyGeneratedAt_of_eq_top {J : ∀ x : X, Ideal (X.presheaf.stalk x)} {x : X}
    (O : Opens X) (hxO : x ∈ O) (hJ : ∀ y, y ∈ O → J y = ⊤) :
    IsLocallyFinitelyGeneratedAt X J x := by
  refine ⟨O, hxO, 1, fun _ => 1, fun y hy => ?_⟩
  rw [hJ y hy, eq_comm, Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, map_one _⟩

/-- Pointwise local finite generation is pulled back along any morphism. -/
theorem IsLocallyFinitelyGeneratedAt.pull (f : Y ⟶ X) {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    {y : Y} (h : IsLocallyFinitelyGeneratedAt X J (f.base y)) :
    IsLocallyFinitelyGeneratedAt Y (pullFamily f J) y := by
  obtain ⟨W, hyW, r, s, hs⟩ := h
  refine ⟨(Opens.map f.base).obj W, hyW, r, fun i => f.c.app (op W) (s i), ?_⟩
  intro y' hy'
  rw [pullFamily, hs (f.base y') hy', Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i => LocallyRingedSpace.stalkMap_germ_apply f W y' hy' (s i)))

/-- **Pointwise local finite generation ascends along an open immersion.** -/
theorem IsLocallyFinitelyGeneratedAt.of_openImmersion (f : Y ⟶ X)
    [H : LocallyRingedSpace.IsOpenImmersion f] {J : ∀ x : X, Ideal (X.presheaf.stalk x)} {y : Y}
    (h : IsLocallyFinitelyGeneratedAt Y (pullFamily f J) y) :
    IsLocallyFinitelyGeneratedAt X J (f.base y) := by
  obtain ⟨W, hyW, r, s, hs⟩ := h
  have key : ∀ (y' : Y) (hy' : y' ∈ W)
      (hx : f.base y' ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W),
      J (f.base y') = Ideal.span (range fun i =>
        X.presheaf.germ ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W) (f.base y') hx
          (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) := by
    intro y' hy' hx
    have hbij : Function.Bijective (f.stalkMap y').hom :=
      (asIso (f.stalkMap y')).commRingCatIsoToRingEquiv.bijective
    have hle : (Opens.map f.base).obj ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)
        ≤ W := by
      rintro z ⟨z', hz', e⟩
      exact H.base_open.injective e ▸ hz'
    have hgerm : ∀ i, Y.presheaf.germ W y' hy' (s i) = (f.stalkMap y').hom
        (X.presheaf.germ ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W) (f.base y')
          hx (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) := by
      intro i
      calc Y.presheaf.germ W y' hy' (s i)
          = Y.presheaf.germ ((Opens.map f.base).obj
              ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)) y' hx
              (Y.presheaf.map (homOfLE hle).op (s i)) :=
            (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y' hx (s i)).symm
        _ = Y.presheaf.germ ((Opens.map f.base).obj
              ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)) y' hx
              (f.c.app (op ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W))
                (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) :=
            congrArg _ (LocallyRingedSpace.IsOpenImmersion.invApp_app_apply f W (s i)).symm
        _ = _ := (LocallyRingedSpace.stalkMap_germ_apply f _ y' hx _).symm
    have h1 := hs y' hy'
    simp only [hgerm] at h1
    rw [Set.range_comp' (f.stalkMap y').hom, ← Ideal.map_span] at h1
    rw [← Ideal.comap_map_of_bijective _ hbij (I := J (f.base y'))]
    change Ideal.comap (f.stalkMap y').hom (pullFamily f J y') = _
    rw [h1, Ideal.comap_map_of_bijective _ hbij]
  refine ⟨(LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W, ⟨y, hyW, rfl⟩, r,
    fun i => LocallyRingedSpace.IsOpenImmersion.invApp f W (s i), ?_⟩
  rintro x ⟨y', hy', rfl⟩
  exact key y' hy' _

end At

section Square

variable {X Y : LocallyRingedSpace.{u}}

/-- Along a morphism injective on points, the kernel family at an image point is the preimage of
the family under the stalk map. -/
theorem kerFamily_apply_of_injective (Q : Y ⟶ X) (hQ : Function.Injective Q.base)
    (K : ∀ y : Y, Ideal (Y.presheaf.stalk y)) (y : Y) :
    kerFamily Q K (Q.base y) = Ideal.comap (Q.stalkMap y).hom (K y) := by
  ext g
  rw [Ideal.mem_comap]
  exact mem_kerFamily_of_unique (fun y' h _ => hQ h) g

/-- Off the image of a morphism the kernel family is the unit ideal. -/
theorem kerFamily_of_not_mem_range (Q : Y ⟶ X) (K : ∀ y : Y, Ideal (Y.presheaf.stalk y))
    {x : X} (hx : x ∉ Set.range Q.base) : kerFamily Q K x = ⊤ :=
  kerFamily_eq_top fun y hy => absurd ⟨y, hy⟩ hx

/-- For a morphism injective on points with surjective stalk maps (a closed embedding, an open
immersion), the pull of the kernel family is the family. -/
theorem pullFamily_kerFamily_of_surjective (Q : Y ⟶ X) (hQ : Function.Injective Q.base)
    (hs : ∀ y, Function.Surjective (Q.stalkMap y).hom) (K : ∀ y : Y, Ideal (Y.presheaf.stalk y)) :
    pullFamily Q (kerFamily Q K) = K := by
  funext y
  rw [pullFamily, kerFamily_apply_of_injective Q hQ]
  exact Ideal.map_comap_of_surjective _ (hs y) _

theorem stalkMap_bijective_of_openImmersion (f : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion f]
    (y : Y) : Function.Bijective (f.stalkMap y).hom :=
  (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.bijective

/-- The kernel family of the pulled family along an open immersion is the family on its range. -/
theorem kerFamily_pullFamily_openImmersion (k : Y ⟶ X) [hk : LocallyRingedSpace.IsOpenImmersion k]
    (K : ∀ x : X, Ideal (X.presheaf.stalk x)) (y : Y) :
    kerFamily k (pullFamily k K) (k.base y) = K (k.base y) := by
  rw [kerFamily_apply_of_injective k hk.base_open.injective, pullFamily]
  exact Ideal.comap_map_of_bijective _ (stalkMap_bijective_of_openImmersion k y)

/-- **Kernel families across a square of open immersions.**  If `k ≫ q = Q ≫ J` with `J, k` open
immersions and every point of `Y'` over the range of `J` where `K` is not the unit ideal lies in the
range of `k`, then the restriction of the kernel family of `K` along `q` to the chart `J` is the
kernel family along `Q` of the restriction of `K`. -/
theorem pullFamily_kerFamily_of_openSquare {X' Y' : LocallyRingedSpace.{u}} (q : Y' ⟶ Y)
    (J : X ⟶ Y) (k : X' ⟶ Y') (Q : X' ⟶ X) (hsq : k ≫ q = Q ≫ J)
    [hJ : LocallyRingedSpace.IsOpenImmersion J] [hk : LocallyRingedSpace.IsOpenImmersion k]
    (K : ∀ y : Y', Ideal (Y'.presheaf.stalk y))
    (hrange : ∀ y' : Y', K y' ≠ ⊤ → q.base y' ∈ Set.range J.base → y' ∈ Set.range k.base) :
    pullFamily J (kerFamily q K) = kerFamily Q (pullFamily k K) := by
  have h1 : kerFamily J (kerFamily Q (pullFamily k K)) = kerFamily q (kerFamily k (pullFamily k K)) := by
    rw [← kerFamily_comp, ← kerFamily_comp, hsq]
  have h2 : ∀ x : X, kerFamily q (kerFamily k (pullFamily k K)) (J.base x) =
      kerFamily q K (J.base x) := by
    intro x
    ext g
    rw [mem_kerFamily_iff, mem_kerFamily_iff]
    refine forall_congr' fun y' => forall_congr' fun hy' => ?_
    by_cases hK : K y' = ⊤
    · rw [hK]
      by_cases hr : y' ∈ Set.range k.base
      · obtain ⟨x', rfl⟩ := hr
        rw [kerFamily_pullFamily_openImmersion, hK]
      · rw [kerFamily_of_not_mem_range k _ hr]
    · obtain ⟨x', rfl⟩ := hrange y' hK ⟨x, hy'.symm⟩
      rw [kerFamily_pullFamily_openImmersion]
  funext x
  rw [← pullFamily_kerFamily_of_surjective J hJ.base_open.injective
    (fun x => (stalkMap_bijective_of_openImmersion J x).2) (kerFamily Q (pullFamily k K)), h1]
  simp only [pullFamily, h2]

/-- **Kernel families across a square of closed embeddings.**  If `ι_S ≫ Π = Q ≫ ι_W` with `ι_W`
injective on points with surjective stalk maps, the kernel family of `K` along `Q` is the
restriction along `ι_W` of the kernel family along `Π` of the push `kerFamily ι_S K`. -/
theorem pullFamily_kerFamily_of_closedSquare {Z M : LocallyRingedSpace.{u}} (ιS : Y ⟶ Z)
    (Pm : Z ⟶ M) (Q : Y ⟶ X) (ιW : X ⟶ M) (hsq : ιS ≫ Pm = Q ≫ ιW)
    (hinj : Function.Injective ιW.base) (hsurj : ∀ x, Function.Surjective (ιW.stalkMap x).hom)
    (K : ∀ y : Y, Ideal (Y.presheaf.stalk y)) :
    pullFamily ιW (kerFamily Pm (kerFamily ιS K)) = kerFamily Q K := by
  rw [← kerFamily_comp, hsq, kerFamily_comp]
  exact pullFamily_kerFamily_of_surjective ιW hinj hsurj _

end Square

section Model

open Hironaka.HolomorphicIdealSheaves HironakaActualAnalyticSubspace
  HironakaG10PNIdealNoetherModel
open scoped Manifold

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The push of an ideal family of an embedded model to the ambient manifold is the kernel family
along the inclusion. -/
theorem kerFamily_actualSubspaceInclusion (C : Set M)
    (J : ∀ c : actualSubspaceLocallyRingedSpace (n := n) C,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk c)) :
    kerFamily (actualSubspaceInclusion (n := n) C) J = pushFamily C J := by
  funext x
  by_cases hx : x ∈ C
  · have h := kerFamily_apply_of_injective (actualSubspaceInclusion (n := n) C)
      Subtype.val_injective J ⟨x, hx⟩
    exact h.trans (pushFamily_of_mem C J ⟨x, hx⟩).symm
  · rw [pushFamily_of_not_mem C J x hx]
    exact kerFamily_eq_top fun y hy => absurd (hy ▸ y.property) hx

end Model

end

end Hironaka.HironakaG10PNKernelSquare
