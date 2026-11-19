import Hironaka.Analytic.Unibranch.HironakaG10RkFibreDim
import Hironaka.Analytic.AnalyticImageDimension

/-!
# Native Remmert, item 5.5: the dimension of an image (lane G10R3)

Setting of `HironakaG10MwRemmertRegular`: `Y` a second-countable native reduced complex space,
`φ : Y ⟶ ofClosedAnalytic C hC`, `g = pointMap φ : Y → M`.

* `add_le_of_regularAtDim_image` (**the image-dimension bound**, Demailly II.8.6): if `T ⊆ Y` is analytic with
  `NativeDimLE Y T a` and every fibre `T ∩ g⁻¹(g y)` (`y ∈ T`) has native local dimension `≥ b` at `y`, then every
  regular point of `g(T) ⊆ M` has a dimension `j` with `j + b ≤ a`; `dimLE_image`, `eq_empty_of_lt`.

Proof.  At a regular point `w` of `g(T)` of dimension `j`, a flattening of `g(T)` gives flat coordinates
`φ_w : N₀ → ℂ^j`, injective on `g(T) ∩ N₀`, with a continuous section `σ` on an open `O' ∋ 0` landing in
`g(T) ∩ N₀`.  Second countability covers `Y` by countably many compact neighbourhoods `Q_x`, each inside a chart
piece of a local embedding with an ambient lift `G_x` of `g`; by Baire one of the compact sets
`φ_w(g(T ∩ g⁻¹(σ K') ∩ Q_x))` (`K'` a closed ball in `O'`) contains a nonempty open set.  On the manifold
`W_x ∩ G_x⁻¹(N₀)` the manifold image bound (`ImageDimensionBound.add_le_of_isOpen_subset_image`) applies to the
trace of `T` and `φ_w ∘ G_x`, whose fibres are those of `g` by injectivity of `φ_w`.

Without second countability the statement is false (an uncountable discrete `Y` mapped bijectively onto `ℂ`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Set TopologicalSpace Topology Filter CategoryTheory AlgebraicGeometry Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10RkImageDim

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  AnalyticDimensionBasics HironakaG10MwRemmertRegular HironakaG10RkNativeRank HironakaG10RkFibreDim
  AnalyticImageDimension

noncomputable section

/-! ### Flat coordinates at a regular point -/

section Flat

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- **Flat coordinates** at a regular point `w` of dimension `j` of a set `S ⊆ M`: holomorphic coordinates
`φw` on an open `N₀ ∋ w`, injective on `S ∩ N₀`, with a continuous section `σ` on an open `O' ∋ 0` of `ℂ^j`
landing in `S ∩ N₀`. -/
theorem exists_flat_coords {S : Set M} {w : M} {j : ℕ} (hw : RegularAtDim (n := k) S w j) :
    ∃ (N₀ : Set M) (φw : M → ComplexModel j) (O' : Set (ComplexModel j)) (σ : ComplexModel j → M),
      IsOpen N₀ ∧ ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel j) ∞ φw N₀ ∧
      (∀ z ∈ N₀, z ∈ S → ∀ z' ∈ N₀, z' ∈ S → φw z = φw z' → z = z') ∧
      IsOpen O' ∧ (0 : ComplexModel j) ∈ O' ∧ ContinuousOn σ O' ∧
      ∀ u ∈ O', σ u ∈ N₀ ∧ σ u ∈ S ∧ φw (σ u) = u := by
  obtain ⟨hjk, -, Φ, hΦt, hΦ0, hΦA⟩ := hw
  set e := chartAt (ComplexModel k) w with he
  set N₀ : Set M := e.source ∩ e ⁻¹' Φ.source with hN₀
  have hN₀o : IsOpen N₀ := e.isOpen_inter_preimage Φ.isOpen_source
  set φw : M → ComplexModel j := fun z => headCLM hjk (Φ.toFun (e z)) with hφw
  have hφs : ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel j) ∞ φw N₀ := by
    intro z hz
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ Φ.toFun (e z) :=
      (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
        hz.2).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e z :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (e.open_source.mem_nhds hz.1)
    exact ((headCLM hjk).contDiff.contMDiff.contMDiffAt.comp z (h1.comp z h2)).contMDiffWithinAt
  have hplane : ∀ z ∈ N₀, z ∈ S → Φ.toFun (e z) ∈ complexCoordinatePlane k j :=
    fun z hz hzS => (hΦA hz.1 hz.2).mp hzS
  have hinj : ∀ z ∈ N₀, z ∈ S → ∀ z' ∈ N₀, z' ∈ S → φw z = φw z' → z = z' := by
    intro z hz hzS z' hz' hzS' hφzz
    have h1 : Φ.toFun (e z) = Φ.toFun (e z') := by
      rw [← inclCLM_headCLM hjk (hplane z hz hzS), ← inclCLM_headCLM hjk (hplane z' hz' hzS')]
      exact congrArg _ hφzz
    have h2 : e z = e z' := by
      rw [← Φ.left_inv _ hz.2, ← Φ.left_inv _ hz'.2, h1]
    exact e.injOn hz.1 hz'.1 h2
  set O' : Set (ComplexModel j) := inclCLM ⁻¹' Φ.target with hO'
  set σ : ComplexModel j → M := fun u => e.symm (Φ.invFun (inclCLM u)) with hσ
  have hO'o : IsOpen O' := Φ.isOpen_target.preimage inclCLM.continuous
  have h0 : (0 : ComplexModel j) ∈ O' := by
    rw [mem_preimage, map_zero, ← hΦ0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hσc : ContinuousOn σ O' := by
    have h1 : ContinuousOn (fun u : ComplexModel j => Φ.invFun (inclCLM u)) O' :=
      Φ.invFun_holomorphic.continuousOn.comp inclCLM.continuous.continuousOn (fun u hu => hu)
    exact e.continuousOn_symm.comp h1 (fun u hu => hΦt (Φ.mapsTo_invFun hu))
  refine ⟨N₀, φw, O', σ, hN₀o, hφs, hinj, hO'o, h0, hσc, ?_⟩
  intro u hu
  set v : ComplexModel k := inclCLM u with hv
  have hvs : Φ.invFun v ∈ Φ.source := Φ.mapsTo_invFun hu
  have hvt : Φ.invFun v ∈ e.target := hΦt hvs
  have hzs : σ u ∈ e.source := e.map_target hvt
  have hez : e (σ u) = Φ.invFun v := e.right_inv hvt
  have hzN : σ u ∈ N₀ := ⟨hzs, by rw [mem_preimage, hez]; exact hvs⟩
  have hΦz : Φ.toFun (e (σ u)) = v := by rw [hez]; exact Φ.right_inv _ hu
  have hzS : σ u ∈ S := (hΦA hzs hzN.2).mpr (by
    change Φ.toFun (e (σ u)) ∈ _
    rw [hΦz]
    exact inclCLM_mem_plane u)
  refine ⟨hzN, hzS, ?_⟩
  change headCLM hjk (Φ.toFun (e (σ u))) = u
  rw [hΦz, hv, headCLM_inclCLM]

end Flat

/-! ### Compact chart pieces -/

section Pieces

variable {Y : SourceReducedComplexSpace} {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {C : Set M}
  {hC : IsComplexAnalyticSubset (n := k) C}

/-- **Compact chart pieces with lifts**: every point has a compact neighbourhood which is the image of a compact
set of carrier points of a local embedding, lying in an open `W` of the ambient space on which `pointMap φ` has a
holomorphic lift. -/
theorem exists_compact_piece (φ : Y ⟶ ofClosedAnalytic C hC) (x : Y.obj.left) :
    ∃ (e : LocalEmbedding Y) (W : Opens e.ambient) (G : W → M) (K : Set e.carrier),
      ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel k) ∞ G ∧
      (∀ (c' : e.carrier) (h : c'.val ∈ W), G ⟨c'.val, h⟩ = pointMap φ (e.toPoint c')) ∧
      IsCompact K ∧ (∀ c' ∈ K, (c' : e.ambient) ∈ W) ∧ e.toPoint '' K ∈ 𝓝 x := by
  let e := LocalEmbedding.ofPoint Y x
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint Y x
  obtain ⟨W, hcW, G, hG, hGl⟩ := exists_lift φ e c
  have : LocallyCompactSpace e.ambient := e.ambient.isOpen.locallyCompactSpace
  have : LocallyCompactSpace e.carrier := e.analytic.isClosed.locallyCompactSpace
  have hWn : ((fun c' : e.carrier => c'.val) ⁻¹' (W : Set e.ambient)) ∈ 𝓝 c :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hcW)
  obtain ⟨K, hKn, hKW, hKc⟩ := local_compact_nhds hWn
  refine ⟨e, W, G, K, hG, hGl, hKc, fun c' hc' => hKW hc', ?_⟩
  have h := e.isOpenEmbedding_toPoint.isOpenMap.image_mem_nhds hKn
  rwa [show e.toPoint c = x from hc] at h

end Pieces

/-! ### The image-dimension bound -/

variable {Y : SourceReducedComplexSpace} {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {C : Set M}
  {hC : IsComplexAnalyticSubset (n := k) C}

/-- **The image-dimension bound** (item 5.5; Demailly II.8.6).  If `T ⊆ Y` is analytic with `dim T ≤ a`
natively and every fibre `T ∩ g⁻¹(g y)` (`y ∈ T`) has native local dimension `≥ b` at `y`, then every regular
point of `g(T)` has a dimension `j` with `j + b ≤ a`. -/
theorem add_le_of_regularAtDim_image [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) {T : Set Y.obj.left} {a b : ℕ} (hT : Y.IsAnalyticSubset T)
    (hdim : HironakaG10EpNativeDim.NativeDimLE Y T a)
    (hfib : ∀ y ∈ T, NativeLocDimGE Y (T ∩ pointMap φ ⁻¹' {pointMap φ y}) y b)
    {w : M} {j : ℕ} (hw : RegularAtDim (n := k) (pointMap φ '' T) w j) : j + b ≤ a := by
  classical
  set g := pointMap φ with hg
  have hgc : Continuous g := continuous_pointMap φ
  have : T2Space M := inferInstance
  obtain ⟨N₀, φw, O', σ, hN₀o, hφs, hinj, hO'o, h0, hσc, hσ⟩ := exists_flat_coords hw
  -- a closed ball in `O'` and its compact image under `σ`
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO'o 0 h0
  set K' : Set (ComplexModel j) := closedBall 0 (ρ / 2) with hK'
  have hK'O : K' ⊆ O' := (closedBall_subset_ball (by linarith)).trans hρO
  have hK'c : IsCompact K' := isCompact_closedBall 0 (ρ / 2)
  set Kt : Set M := σ '' K' with hKt
  have hKtc : IsCompact Kt := hK'c.image_of_continuousOn (hσc.mono hK'O)
  have hKtN : Kt ⊆ N₀ := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hσ u (hK'O hu)).1
  -- countably many compact chart pieces cover `Y`
  choose e W G K hG hGl hKc hKW hKn using exists_compact_piece (Y := Y) φ
  obtain ⟨s, hsc, hsU⟩ := TopologicalSpace.countable_cover_nhds hKn
  set F : Y.obj.left → Set Y.obj.left := fun x => T ∩ g ⁻¹' Kt ∩ (e x).toPoint '' K x with hF
  have hFc : ∀ x, IsCompact (F x) := by
    intro x
    have hQ : IsCompact ((e x).toPoint '' K x) :=
      (hKc x).image (e x).isOpenEmbedding_toPoint.continuous
    exact hQ.inter_left (hT.isClosed.inter (hKtc.isClosed.preimage hgc))
  have hgF : ∀ x, g '' F x ⊆ N₀ := by
    rintro x _ ⟨t, ht, rfl⟩
    exact hKtN ht.1.2
  set P : s → Set (ComplexModel j) := fun x => φw '' (g '' F x) with hP
  have hPc : ∀ x : s, IsClosed (P x) := fun x =>
    (((hFc x).image hgc).image_of_continuousOn (hφs.continuousOn.mono (hgF x))).isClosed
  have hK'P : K' ⊆ ⋃ x : s, P x := by
    intro u hu
    obtain ⟨hσN, ⟨t, htT, hgt⟩, hφσ⟩ := hσ u (hK'O hu)
    have htQ : t ∈ ⋃ x ∈ s, (e x).toPoint '' K x := hsU ▸ mem_univ t
    obtain ⟨x, hxs, htx⟩ := mem_iUnion₂.mp htQ
    refine mem_iUnion.mpr ⟨⟨x, hxs⟩, g t, ⟨t, ⟨⟨htT, ?_⟩, htx⟩, rfl⟩, ?_⟩
    · rw [mem_preimage, hgt]
      exact ⟨u, hu, rfl⟩
    · rw [hgt]
      exact hφσ
  -- Baire: one piece has nonempty interior in the open ball
  have : Countable s := hsc.to_subtype
  obtain ⟨t₀, -, -⟩ := hw.2.1
  obtain ⟨x₀, hx₀s, -⟩ := mem_iUnion₂.mp (hsU ▸ mem_univ t₀ : t₀ ∈ ⋃ x ∈ s, (e x).toPoint '' K x)
  set B : Set (ComplexModel j) := ball 0 (ρ / 2) with hB
  have hcover : ⋃ x : s, (P x ∪ Bᶜ) = univ := by
    apply eq_univ_of_forall
    intro u
    by_cases hu : u ∈ B
    · obtain ⟨x, hx⟩ := mem_iUnion.mp (hK'P (ball_subset_closedBall hu))
      exact mem_iUnion.mpr ⟨x, Or.inl hx⟩
    · exact mem_iUnion.mpr ⟨⟨x₀, hx₀s⟩, Or.inr hu⟩
  have hdense := dense_iUnion_interior_of_closed (fun x => (hPc x).union isOpen_ball.isClosed_compl)
    hcover
  obtain ⟨u₀, hu₀B, hu₀⟩ := hdense.inter_open_nonempty B isOpen_ball
    ⟨0, mem_ball_self (by linarith)⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp hu₀
  set O'' : Set (ComplexModel j) := interior (P x ∪ Bᶜ) ∩ B with hO''
  have hO''o : IsOpen O'' := isOpen_interior.inter isOpen_ball
  have hO''P : O'' ⊆ P x := by
    rintro u ⟨hu1, hu2⟩
    rcases interior_subset hu1 with h | h
    · exact h
    · exact absurd hu2 h
  -- the chart piece and the manifold image bound
  set ex := e x.val with hex
  set U : Opens (W x.val) := ⟨(G x.val) ⁻¹' N₀, (hG x.val).continuous.isOpen_preimage _ hN₀o⟩ with hU
  set g' : U → ComplexModel j := fun z => φw (G x.val z) with hg'
  have hg's : ContMDiff 𝓘(ℂ, ComplexModel ex.dim) 𝓘(ℂ, ComplexModel j) ∞ g' :=
    AnalyticSubsetOpens.contMDiff_restrict (U := U)
      (hφs.comp (hG x.val).contMDiffOn fun z hz => hz)
  set T' : Set U := (↑) ⁻¹' ((↑) ⁻¹' (HironakaG10EpNativeDim.trace ex T) : Set (W x.val)) with hT'
  have hT'a : IsComplexAnalyticSubset (n := ex.dim) T' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
        (HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hT ex) (W x.val)) U
  have hT'd : DimLE (n := ex.dim) T' a :=
    AnalyticSubsetOpens.dimLE_preimage_val
      (AnalyticSubsetOpens.dimLE_preimage_val (hdim ex) (W x.val)) U
  have hO''T' : O'' ⊆ g' '' T' := by
    intro u hu
    obtain ⟨_, ⟨t, ⟨⟨htT, htK⟩, c', hc'K, rfl⟩, rfl⟩, rfl⟩ := hO''P hu
    set z₀ : W x.val := ⟨c'.val, hKW x.val c' hc'K⟩ with hz₀
    have hGz₀ : G x.val z₀ = g (ex.toPoint c') := hGl x.val c' _
    have hz₀U : z₀ ∈ U := by
      change G x.val z₀ ∈ N₀
      rw [hGz₀]
      exact hKtN htK
    refine ⟨⟨z₀, hz₀U⟩, ?_, ?_⟩
    · change c'.val ∈ HironakaG10EpNativeDim.trace ex T
      exact (HironakaG10EpNativeDim.mem_trace ex T c').mpr htT
    · change φw (G x.val z₀) = _
      rw [hGz₀]
  have hfib' : ∀ z ∈ T', LocDimGE (n := ex.dim) (T' ∩ g' ⁻¹' {g' z}) z b := by
    intro z hz
    have hzC : ((z : W x.val) : ex.ambient) ∈ ex.carrier :=
      HironakaG10EpNativeDim.trace_subset_carrier ex T hz
    set cz : ex.carrier := ⟨((z : W x.val) : ex.ambient), hzC⟩ with hcz
    have htz : ex.toPoint cz ∈ T := (HironakaG10EpNativeDim.mem_trace ex T cz).mp hz
    have hl := hfib _ htz ex cz rfl
    have hGz : G x.val z = g (ex.toPoint cz) := hGl x.val cz z.val.property
    have hset : T' ∩ g' ⁻¹' {g' z} = ((↑) ⁻¹' ((↑) ⁻¹' (HironakaG10EpNativeDim.trace ex
        (T ∩ g ⁻¹' {g (ex.toPoint cz)})) : Set (W x.val)) : Set U) := by
      ext z'
      have hgz'U : G x.val z' ∈ N₀ := z'.property
      have hgzU : G x.val z ∈ N₀ := z.property
      constructor
      · rintro ⟨hz'T, hz'g⟩
        have hz'C : ((z' : W x.val) : ex.ambient) ∈ ex.carrier :=
          HironakaG10EpNativeDim.trace_subset_carrier ex T hz'T
        set cz' : ex.carrier := ⟨((z' : W x.val) : ex.ambient), hz'C⟩ with hcz'
        have ht' : ex.toPoint cz' ∈ T := (HironakaG10EpNativeDim.mem_trace ex T cz').mp hz'T
        have hGz' : G x.val z' = g (ex.toPoint cz') := hGl x.val cz' z'.val.property
        have hφ : φw (G x.val z') = φw (G x.val z) := hz'g
        rw [hGz', hGz] at hφ
        have heq : g (ex.toPoint cz') = g (ex.toPoint cz) :=
          hinj _ (hGz' ▸ hgz'U) ⟨_, ht', rfl⟩ _ (hGz ▸ hgzU) ⟨_, htz, rfl⟩ hφ
        exact (HironakaG10EpNativeDim.mem_trace ex _ cz').mpr ⟨ht', heq⟩
      · intro h
        have hz'C : ((z' : W x.val) : ex.ambient) ∈ ex.carrier :=
          HironakaG10EpNativeDim.trace_subset_carrier ex _ h
        set cz' : ex.carrier := ⟨((z' : W x.val) : ex.ambient), hz'C⟩ with hcz'
        obtain ⟨ht', heq⟩ := (HironakaG10EpNativeDim.mem_trace ex _ cz').mp h
        have hGz' : G x.val z' = g (ex.toPoint cz') := hGl x.val cz' z'.val.property
        refine ⟨(HironakaG10EpNativeDim.mem_trace ex T cz').mpr ht', ?_⟩
        change φw (G x.val z') = φw (G x.val z)
        rw [hGz', hGz]
        exact congrArg φw heq
    rw [hset]
    exact AnalyticSubsetOpens.locDimGE_preimage_val_iff.mpr
      (AnalyticSubsetOpens.locDimGE_preimage_val_iff.mpr hl)
  exact ImageDimensionBound.add_le_of_isOpen_subset_image j hT'a hT'd hg's
    ⟨O'', hO''o, ⟨u₀, hx, hu₀B⟩, hO''T'⟩ hfib'

/-- `dim g(T) ≤ a - b`. -/
theorem dimLE_image [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) {T : Set Y.obj.left} {a b : ℕ} (hT : Y.IsAnalyticSubset T)
    (hdim : HironakaG10EpNativeDim.NativeDimLE Y T a)
    (hfib : ∀ y ∈ T, NativeLocDimGE Y (T ∩ pointMap φ ⁻¹' {pointMap φ y}) y b) :
    DimLE (n := k) (pointMap φ '' T) (a - b) := fun w j hw => by
  have := add_le_of_regularAtDim_image φ hT hdim hfib hw
  omega

/-- If `g(T)` is analytic and the fibres have native local dimension `≥ b > a ≥ dim T`, then `T = ∅`. -/
theorem eq_empty_of_lt [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) {T : Set Y.obj.left} {a b : ℕ} (hT : Y.IsAnalyticSubset T)
    (hdim : HironakaG10EpNativeDim.NativeDimLE Y T a)
    (hfib : ∀ y ∈ T, NativeLocDimGE Y (T ∩ pointMap φ ⁻¹' {pointMap φ y}) y b)
    (hgT : IsComplexAnalyticSubset (n := k) (pointMap φ '' T)) (hab : a < b) : T = ∅ := by
  by_contra hne
  obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨w, -, j, hw⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds hgT ⟨t, ht, rfl⟩ univ_mem
  have := add_le_of_regularAtDim_image φ hT hdim hfib hw
  omega

end

end Hironaka.Analytic.Unibranch.HironakaG10RkImageDim
