import DeJongAlterations.Divisor
import DeJongAlterations.Geometry.AlgebraicFieldFiniteModelRefinement
import DeJongAlterations.StableModification.Limits.SpreadModificationProjective

/-! Actual regular closed geometric boundary members acquire ONE shared smooth closed finite-field family. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryFamily

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteModelRefinement

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
  [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]

/-- Actual regularity and a genuine closed immersion INTERNALLY give a smooth regular closed
finite-field model inside the SAME ambient model, retaining the WHOLE original closed arrow. -/
theorem exists_regular_closed_model {Z : Scheme.{u}} (a : Z ⟶ Y) [IsClosedImmersion a]
    (hZ : IsRegularScheme Z) {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (n : Model (diagram k L) (scalarCone k L) (a ≫ p) j)
      (t : n.Y ⟶ (m.baseChange h).Y),
      n.IsFP ∧ Smooth n.fY ∧ IsRegularScheme n.Y ∧ IsClosedImmersion t ∧
      t ≫ (m.baseChange h).fY = n.fY ∧ n.g ≫ t = a ≫ (m.baseChange h).g ∧
      IsPullback n.g a t (m.baseChange h).g := by
  let : Smooth (a ≫ p) := RegularSmoothConverse.smooth_of_isRegularScheme (a ≫ p) hZ
  obtain ⟨j₀, h₀, r, t, hr, ht, htf, hgt⟩ :=
    exists_closedImmersion_model (isLimitScalarCone k L) m hm (a ≫ p) a rfl
  obtain ⟨j, h₁, hs, hreg⟩ := exists_smooth_refinement k L r hr
  let M := m.baseChange h₀
  let n := r.baseChange h₁
  let c := topBaseChange r M t htf (Over.mk h₁)
  let : IsClosedImmersion t := ht
  let : IsClosedImmersion c := MorphismProperty.of_isPullback
    (isPullback_topBaseChange r M t htf (Over.mk h₁)) inferInstance
  let e := m.baseChangeCompIso h₀ h₁
  let t' := c ≫ e.hom
  have htf' : t' ≫ (m.baseChange (h₁ ≫ h₀)).fY = n.fY := by
    rw [Category.assoc, Model.baseChangeCompIso_hom_fY]
    exact topBaseChange_snd _ _ _ _ _
  have hgt' : n.g ≫ t' = a ≫ (m.baseChange (h₁ ≫ h₀)).g := by
    have hc : n.g ≫ c = a ≫ (M.baseChange h₁).g :=
      π_topBaseChange r M t htf a hgt rfl _
    rw [← Category.assoc, hc, Category.assoc, Model.g_baseChangeCompIso_hom]
  refine ⟨j, h₁ ≫ h₀, n, t', hr.baseChange h₁, hs, hreg, inferInstance, htf', hgt', ?_⟩
  refine IsPullback.of_bot ?_ hgt' (m.baseChange (h₁ ≫ h₀)).isPullback
  simpa only [htf'] using n.isPullback

/-- EVERY actual finite family of regular closed scalar schemes INTERNALLY acquires ONE finite
field's smooth regular closed models inside the SAME ambient base change, with ALL original maps. -/
theorem exists_finite_regular_closed_family {T : Type u} [Finite T]
    (Z : T → Scheme.{u}) (a : ∀ t, Z t ⟶ Y) [∀ t, IsClosedImmersion (a t)]
    (hZ : ∀ t, IsRegularScheme (Z t)) {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (n : ∀ t, Model (diagram k L) (scalarCone k L) (a t ≫ p) j)
      (b : ∀ t, (n t).Y ⟶ (m.baseChange h).Y),
      ∀ t, (n t).IsFP ∧ Smooth (n t).fY ∧ IsRegularScheme (n t).Y ∧
        IsClosedImmersion (b t) ∧ b t ≫ (m.baseChange h).fY = (n t).fY ∧
        (n t).g ≫ b t = a t ≫ (m.baseChange h).g ∧
        IsPullback (n t).g (a t) (b t) (m.baseChange h).g := by
  classical
  choose j h r t hr hs hreg ht htf hgt Horig using
    fun q => exists_regular_closed_model k L p (a q) (hZ q) m hm
  let K (q : T) : Over i := Over.mk (h q)
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨J, hJ⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image K)
  let g (q : T) : J ⟶ K q :=
    (hJ (Finset.mem_image_of_mem K (Finset.mem_univ q))).some
  let M := m.baseChange J.hom
  let n (q : T) := (r q).baseChange (g q).left
  let H (q : T) := isPullback_baseChangeDiagram_map (diagram k L) m.fY (g q)
  let b (q : T) : (n q).Y ⟶ M.Y :=
    (H q).lift (pullback.fst (r q).fY ((diagram k L).map (g q).left) ≫ t q)
      (n q).fY (by
        change (pullback.fst (r q).fY ((diagram k L).map (g q).left) ≫ t q) ≫
          (m.baseChange (h q)).fY = (n q).fY ≫ (diagram k L).map (g q).left
        rw [Category.assoc, htf q]
        exact pullback.condition)
  refine ⟨J.left, J.hom, n, b, ?_⟩
  intro q
  have hbf : b q ≫ (baseChangeDiagram (diagram k L) m.fY).map (g q) =
      pullback.fst (r q).fY ((diagram k L).map (g q).left) ≫ t q :=
    (H q).lift_fst _ _ _
  have hbs : b q ≫ M.fY = (n q).fY := (H q).lift_snd _ _ _
  have Houter : IsPullback
      (pullback.fst (r q).fY ((diagram k L).map (g q).left))
      (b q ≫ M.fY) (t q ≫ (m.baseChange (h q)).fY) ((diagram k L).map (g q).left) := by
    rw [hbs, htf q]
    exact IsPullback.of_hasPullback _ _
  have Hclosed := IsPullback.of_bot Houter hbf.symm (H q)
  let : IsClosedImmersion (t q) := ht q
  let : IsClosedImmersion (b q) := MorphismProperty.of_isPullback Hclosed inferInstance
  have hgn : (n q).g ≫ pullback.fst (r q).fY ((diagram k L).map (g q).left) = (r q).g := by
    simp [n, Model.baseChange]
  have hgm : M.g ≫ (baseChangeDiagram (diagram k L) m.fY).map (g q) =
      (m.baseChange (h q)).g := (baseChangeCone (diagram k L) (scalarCone k L) m.isPullback).w (g q)
  have hwhole : (n q).g ≫ b q = a q ≫ M.g := by
    apply (H q).hom_ext
    · rw [Category.assoc, hbf, ← Category.assoc, hgn, hgt q, Category.assoc, hgm]
    · change ((n q).g ≫ b q) ≫ M.fY = (a q ≫ M.g) ≫ M.fY
      rw [Category.assoc, hbs, (n q).isPullback.w]
      simpa only [Category.assoc] using (congrArg (fun f => a q ≫ f) M.isPullback.w).symm
  let : Smooth (r q).fY := hs q
  let : Smooth (n q).fY := by
    change Smooth (pullback.snd (r q).fY ((diagram k L).map (g q).left))
    infer_instance
  refine ⟨(hr q).baseChange (g q).left, inferInstance,
    RegularSmooth.isRegularScheme_of_smooth (K := levelField k L J.left) (n q).fY,
    inferInstance, hbs, hwhole, ?_⟩
  refine IsPullback.of_bot ?_ hwhole M.isPullback
  simpa only [hbs] using (n q).isPullback

/-- ORIGINAL actual SNC geometry INTERNALLY produces smooth regular closed models of ALL
actual nonempty component-intersection schemes over ONE finite field and SAME ambient model. -/
theorem exists_snc_intersection_family (D : Y.IdealSheafData) (hD : IsStrictNormalCrossings D)
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (n : ∀ J : {J : Finset (DivisorComponent D) // J.Nonempty},
        Model (diagram k L) (scalarCone k L) ((componentIntersection D J.val).subschemeι ≫ p) j)
      (b : ∀ J, (n J).Y ⟶ (m.baseChange h).Y),
      ∀ J, (n J).IsFP ∧ Smooth (n J).fY ∧ IsRegularScheme (n J).Y ∧
        IsClosedImmersion (b J) ∧ b J ≫ (m.baseChange h).fY = (n J).fY ∧
        (n J).g ≫ b J = (componentIntersection D J.val).subschemeι ≫ (m.baseChange h).g ∧
        IsPullback (n J).g (componentIntersection D J.val).subschemeι (b J) (m.baseChange h).g := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  exact exists_finite_regular_closed_family k L p
    (fun J : {J : Finset (DivisorComponent D) // J.Nonempty} => (componentIntersection D J.val).subscheme)
    (fun J => (componentIntersection D J.val).subschemeι)
    (fun J => hD.intersectionsRegular J.val J.property) m hm

end DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryFamily
