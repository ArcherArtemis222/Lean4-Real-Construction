import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Lean4RealConstruction.LagrangeMultiplier.PairComponent
import Lean4RealConstruction.LagrangeMultiplier.PrefixSplit
import Lean4RealConstruction.LagrangeMultiplier.Implicit
import Lean4RealConstruction.LagrangeMultiplier.LinearAlgebra

noncomputable section

set_option linter.unusedSectionVars false

open scoped Topology Set Filter
open EuclideanSplit EuclideanPrefixSplit Submodule ImplicitFunctionTheorem
open RealInnerProductSpace Gradient LinearMap ContinuousLinearMap InnerProduct

section TangentSet

variable {Y : Type*}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Curve-defined tangent set to `S` at `p`. -/
def TangentSet (S : Set Y) (p : Y) : Set Y :=
  {v | ∃ γ : ℝ → Y,
      HasDerivAt γ v 0 ∧
      γ 0 = p ∧
      ∀ᶠ t in nhds 0, γ t ∈ S}

/-!
這個集合有些性質，對後續論證很重要。
首先是這個集合定義和包含關係不會被座標轉換改變。
-/

/--
ContinuousLinearEquiv does not effects the structure of the Tangent Set.
-/
theorem TangentSet_image_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F)
    {S : Set E} {a : E} :
    TangentSet (e '' S) (e a)
      =
    e '' TangentSet S a := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨γ, hγ, hγ0, hγmem⟩

    let η : ℝ → E := fun t => e.symm (γ t)

    have hη_deriv : HasDerivAt η (e.symm v) 0 := by
      -- derivative of `e.symm ∘ γ`
      simpa only [η] using ((e.symm : F →L[ℝ] E).hasFDerivAt.comp_hasDerivAt 0 hγ)

    have hη0 : η 0 = a := by
      simp only [hγ0, ContinuousLinearEquiv.symm_apply_apply, η]

    have hηmem : ∀ᶠ t in nhds 0, η t ∈ S := by
      filter_upwards [hγmem] with t ht
      rcases ht with ⟨s, hs, hγs⟩
      simpa only [η, ← hγs, ContinuousLinearEquiv.symm_apply_apply]

    refine ⟨e.symm v, ?_, ?_⟩
    · exact ⟨η, hη_deriv, hη0, hηmem⟩
    · rw [ContinuousLinearEquiv.apply_symm_apply]

  · intro hv
    rcases hv with ⟨u, hu, rfl⟩
    rcases hu with ⟨γ, hγ, hγ0, hγmem⟩

    let η : ℝ → F := fun t => e (γ t)

    have hη_deriv : HasDerivAt η (e u) 0 := by
      simpa only [η] using
        ((e : E →L[ℝ] F).hasFDerivAt.comp_hasDerivAt 0 hγ)

    have hη0 : η 0 = e a := by
      simp only [η, hγ0]

    have hηmem : ∀ᶠ t in nhds 0, η t ∈ e '' S := by
      filter_upwards [hγmem] with t ht
      exact ⟨γ t, ht, rfl⟩

    exact ⟨η, hη_deriv, hη0, hηmem⟩

theorem TangentSet_graphOverT_eq_image
    (hmn : m ≤ n)
    (h : Euc (n - m) → Euc m)
    (T : Set (Euc (n - m)))
    (t₀ : Euc (n - m)) :
    TangentSet
      (graphOverT hmn h T)
      (xtPair hmn (h t₀) t₀)
    =
    graphOverTEquiv hmn ''
      TangentSet
        (graphSet h T)
        (EuclideanSplit.pairE (n := n - m) (m := m) t₀ (h t₀)) := by
  rw [graphOverT_eq_image_graphSet]
  simpa using
    TangentSet_image_equiv
      (graphOverTEquiv hmn)
      (S := graphSet h T)
      (a := EuclideanSplit.pairE (n := n - m) (m := m) t₀ (h t₀))

/-!
再來是，我們看兩個集合在某一點的 TangentSet 時，只要看局部就好。
局部一樣，兩 TangentSet 就一樣。
-/

/--
If two sets are locally equal near a point, the tangent sets of two sets at this point are equal.
-/
lemma TangentSet_congr {S₁ S₂ : Set (Euc n)} {a : Euc n} (h : ∀ᶠ x in nhds a, x ∈ S₁ ↔ x ∈ S₂)
  : TangentSet S₁ a = TangentSet S₂ a :=
by
  ext v; constructor
  .
    intro ⟨r, diff_r, eq, r0S₁⟩
    subst eq
    use r, diff_r, rfl
    filter_upwards [r0S₁, diff_r.continuousAt.eventually h] with t ht_S₁ ht_iff
    exact ht_iff.mp ht_S₁
  .
    intro ⟨r, diff_r, eq, r0S₂⟩
    subst eq
    use r, diff_r, rfl
    filter_upwards [r0S₂, diff_r.continuousAt.eventually h] with t ht_S₂ ht_iff
    exact ht_iff.mpr ht_S₂

end TangentSet

section TangentSpace

open EuclideanSplit

variable {n m : ℕ}

/-- The model tangent space to the graph of `f` at `a`. -/
def graphTangentModel (f : Euc n → Euc m) (a : Euc n) : Set (Euc (n + m)) :=
  {ξ | ∃ u : Euc n,
      ξ = pairE (n := n) (m := m) u ((fderiv ℝ f a) u)}

/-!
我們基本上只在可局部表為該點可微函數的 graph 的集合上討論 TangentSet。
在單點可維的情形下，Tangent Set 其實就是導數的 graph，因此是向量空間。
-/

/--
If a tangent vector is represented by a curve lying eventually in the graph of `f`,
then it lies in the graph of `Df(a)`.

This is the formal version of:

`(v, w) ∈ T_(a, f(a)) graph(f) → w = Df(a) v`.
-/
theorem tangent_graph_subset_graphTangentModel
    {f : Euc n → Euc m} {a : Euc n} {S : Set (Euc n)}
    (hS : IsOpen S) (aS : a ∈ S) (hf : DifferentiableAt ℝ f a) :
    TangentSet
      (graphSet f S)
      (pairE (n := n) (m := m) a (f a))
      = graphTangentModel f a := by
  apply subset_antisymm
  .
    intro ξ hξ
    rcases hξ with ⟨γ, hγ, hγ0, hγmem⟩

    let x : ℝ → Euc n := front γ
    let y : ℝ → Euc m := back γ

    have hx : HasDerivAt x (fstE ξ) 0 := by
      simpa only using hγ.front

    have hy : HasDerivAt y (sndE ξ) 0 := by
      simpa only using hγ.back

    have hx0 : x 0 = a := by
      simpa only [fstE_pairE] using congrArg fstE hγ0

    have hyeq : y =ᶠ[nhds 0] f ∘ x := by
      filter_upwards [hγmem] with t ht
      exact ht.2

    have hchain :
      HasDerivAt (f ∘ x) ((fderiv ℝ f a) (fstE ξ)) 0
      := by
      have hf_at_x0 : HasFDerivAt f (fderiv ℝ f a) (x 0) := by
        simpa only [hx0] using hf.hasFDerivAt
      have eq := hf_at_x0.comp 0 hx
      rw [hasDerivAt_iff_hasFDerivAt]
      have : (fderiv ℝ f a).comp (ContinuousLinearMap.toSpanSingleton ℝ (fstE ξ)) = ContinuousLinearMap.toSpanSingleton ℝ ((fderiv ℝ f a) (fstE ξ))
      := by
        ext1; simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      rwa [← this]

    have hsnd :
        sndE ξ = (fderiv ℝ f a) (fstE ξ) := by
      have hchain_y :
          HasDerivAt y
            ((fderiv ℝ f a) (fstE (n := n) (m := m) ξ))
            0 := by
        exact HasDerivAt.congr_of_eventuallyEq hchain hyeq
      exact hy.unique hchain_y

    rw [← pairE_fstE_sndE ξ]
    use fstE ξ
    congr
  .
    intro xfx ⟨u, eq⟩; subst eq
    let γ : ℝ → Euc n := fun t => a + t • u
    have h1 : γ 0 = a := by simp only [zero_smul, add_zero, γ]
    -- γ 的可微性為顯然。
    have h11 : DifferentiableAt ℝ γ 0 := by fun_prop
    -- 又由連續性，有 $0$ 的 neighborhood $E$ 使得 $γ(E) ⊆ S$。
    have h12 : ∀ᶠ t in 𝓝 0, γ t ∈ S := by
      have h121 := hS.mem_nhds aS
      rw [← h1] at h121
      exact h11.continuousAt h121
    have h13 : u = deriv γ 0 := by
      unfold γ; rw [deriv_const_add', deriv_smul_const (by fun_prop), deriv_id'', one_smul];
    use joinMap γ (f ∘ γ), ?_, ?_
    -- 局部相同：依定義。
    filter_upwards [h12] with x γxS
    use ?_, ?_
    rwa [joinMap, fstE_pairE]
    change back _ x = f (front _ x)
    rw [back_joinMap, Function.comp_apply, front_joinMap]
    have h22 : DifferentiableAt ℝ (f ∘ γ) 0 := by
      exact DifferentiableAt.comp 0 (by rwa [h1]) h11
    -- 由 $γ(0) = a$ 和 $f$ 在 $a$ 可微，用 chain rule。
    have h2 : DifferentiableAt ℝ (joinMap γ (f ∘ γ)) 0 := by
      have h21 := HasFDerivAt.join h11.hasFDerivAt h22.hasFDerivAt
      exact h21.differentiableAt
    have h3 : pairE u ((fderiv ℝ f a) u) = deriv (joinMap γ (f ∘ γ)) 0 := by
      rw [deriv_join h11 h22, pairE]; congr!
      symm; apply HasDerivAt.deriv
      apply HasFDerivAt.comp_hasDerivAt
      simpa only [h1] using hf.hasFDerivAt
      simpa only [h13] using h11.hasDerivAt
    simpa only [h3] using DifferentiableAt.hasDerivAt h2

    -- $(γ, f ∘ γ)(0) = (a, f(a))$ 則是由 $γ(0) = a$ 得到。
    rw [joinMap, Function.comp, h1];


/--
正式定義單點可微函數的 Tangent Space。
-/
def TangentSpace_ofFun (f : Euc n → Euc m) (a : Euc n) :
    Submodule ℝ (Euc (n + m)) :=
  (EuclideanSplit.graphCLM (fderiv ℝ f a)).range

/--
單點可微函數的切空間等同 TangentSet。
-/
theorem TangentSpace_ofFun_def {f : Euc n → Euc m} {a : Euc n} {S : Set (Euc n)}
  (hS : IsOpen S) (aS : a ∈ S) (diff_f : DifferentiableAt ℝ f a)
  : TangentSpace_ofFun f a = TangentSet (graphSet f S) (pairE a (f a)) :=
by
  rw [tangent_graph_subset_graphTangentModel hS aS diff_f];
  apply subset_antisymm
  . intro v ⟨x, eq⟩;
    use x; rw [← eq, ← graphCLM_apply]; rfl
  . intro v ⟨x, eq⟩;
    use x; rw [eq, ← graphCLM_apply]; rfl

/--
單點可微函數的切空間的維度，為函數的定義域的維度。
-/
theorem TangentSpace_ofFun_finrank
    {f : Euc n → Euc m} {a : Euc n} :
    Module.finrank ℝ ↥(TangentSpace_ofFun f a) = n := by
  let L : Euc n →L[ℝ] Euc m := fderiv ℝ f a
  change Module.finrank ℝ ↥((EuclideanSplit.graphCLM L).range) = n
  have h := (graphCLMRangeEquiv L).symm.finrank_eq
  rwa [finrank_euclideanSpace, Fintype.card_fin] at h

end TangentSpace

section LevelSet

/-!
這裡省略隱函數定理的 statement，直接談 level set 的切空間。
我們想宣稱，level set 的 TangentSet 就是 $\ker(Dg)$，藉此定義其切空間。
首先左推右很簡單，若 $g$ 可微，對於任意局部落在 level set 上的路徑，由 level set 的定義，必定局部為常數。
那麼，微分為 0。用 chain rule 即可證得。
-/

lemma levelSet_subset_ker {a : Euc n} {S : Set (Euc n)} {g : Euc n → Euc m}
  (hg : DifferentiableAt ℝ g a) (aS : a ∈ S) {k : Euc m} (ha : g a = k) :
  TangentSet (levelSetIn S g k) a ⊆ (fderiv ℝ g a).ker
:= by
  intro γ' ⟨γ, diff_γ, eq, γLS⟩; subst eq
  rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  rw [← diff_γ.deriv, deriv]
  let φ := g ∘ γ
  have h1: DifferentiableAt ℝ φ 0 := by
    exact DifferentiableAt.comp _ hg diff_γ.differentiableAt
  have h2 := h1.hasDerivAt
  have : fderiv ℝ φ 0 = (fderiv ℝ g (γ 0)).comp (fderiv ℝ γ 0) := by
    exact fderiv_comp _ hg diff_γ.differentiableAt
  have h3 : φ =ᶠ[𝓝 0] fun _ => k := by
    filter_upwards [γLS] with a ⟨γaS, eq⟩; exact eq
  have h4 : DifferentiableAt ℝ (fun (_ : ℝ) => k) 0 := by
    simp only [differentiableAt_const]
  have h5 : fderiv ℝ (fun (_ : ℝ) => k) 0 = 0 := by
    rw [fderiv_fun_const, Pi.zero_apply]
  have h6 : fderiv ℝ φ 0 = fderiv ℝ (fun (_ : ℝ) => k) 0 := by
    exact h3.fderiv_eq
  rw [h5, this] at h6
  have :(fderiv ℝ g (γ 0)).comp (fderiv ℝ γ 0) 1 = 0 := by
    rw [h6]; rfl
  rw [← this]; rfl

theorem fderiv_range_eq_top_of_DxBlock_invertible
    {g : Euc n → Euc m} {a : Euc n}
    (hmn : m ≤ n)
    (hDx : IsInvertibleCLM (DxBlock hmn g a)) :
    (fderiv ℝ g a).range = ⊤ := by
  rw [DxBlock_eq_DxBlockCLM] at hDx
  exact surjective_of_DxBlockCLM_invertible hmn (fderiv ℝ g a) hDx

theorem finrank_ker_fderiv_eq
    {g : Euc n → Euc m} {a : Euc n}
    (hmn : m ≤ n)
    (hDx : IsInvertibleCLM (DxBlock hmn g a)) :
    Module.finrank ℝ ↥((fderiv ℝ g a).ker) = n - m := by
  have hrange : (fderiv ℝ g a).range = ⊤ :=
    fderiv_range_eq_top_of_DxBlock_invertible hmn hDx

  have hRN :=
    (fderiv ℝ g a).finrank_range_add_finrank_ker

  have hDg : Module.finrank ℝ (fderiv ℝ g a).range = Module.finrank ℝ (⊤ : Submodule ℝ (Euc m)) := by rw [hrange]

  rw [finrank_euclideanSpace, Fintype.card_fin] at hRN
  rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hDg
  simp only [← hRN, hDg]

  exact Nat.eq_sub_of_add_eq' rfl

/-!
要說明相等則稍顯困難。
如果 $g : \mathbb{R}^n\to\mathbb{R}^m$ 在某點的可微性足夠好，那麼隱函數定理能把前 $m$ 個分量，表為後 $(n - m)$ 個分量的函數。
這個函數可微，且其 graph 表示 level set 在該點的局部。
可微代表有切空間，局部相等代表其與 level set 在該點的 Tangent Set 相同。
於是 level set 在該點的 Tangent Set 為向量空間，維度為定義域的維度，(n - m)。
另一方面，由維度定理可得 $\dim(\ker(Dg)) = n-m$。
兩個集合都是向量空間，其中一個是另一個的子空間，且兩者維度一樣。
這代表兩個空間相等。

這種行為良好的 level set，我們稱為 regular level set。
而我們可以在上面，定義切空間。
-/

lemma levelSet_eq_ker {a : Euc n} {S : Set (Euc n)} {g : Euc n → Euc m} (hS : IsOpen S)
  (aS : a ∈ S) {k : Euc m} (ha : g a = k) (hmn : m ≤ n) (hg : HasStrictFDerivAt g (fderiv ℝ g a) a) (hgDx : IsInvertibleCLM (DxBlock hmn g a)) :
  TangentSet (levelSetIn S g k) a = (fderiv ℝ g a).ker
:= by
  rcases ImplicitFunctionTheorem_localGraph hS aS ha hmn hg hgDx
  with ⟨T₀, h, open_T₀, aₜT₀, haₜaₓ, diff_h, graph_eq⟩
  have h0 := TangentSet_congr graph_eq
  have h1 := TangentSet_graphOverT_eq_image hmn h T₀ (tPart hmn a)
  rw [haₜaₓ, xtPair_xPart_tPart] at h1
  have : (TangentSpace_ofFun h (tPart hmn a)).map (graphOverTEquiv hmn).toLinearMap = ⇑(graphOverTEquiv hmn) '' ↑(TangentSpace_ofFun h (tPart hmn a)) := by
    rw [map_coe, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  have : TangentSet (graphOverT hmn h T₀) a = (TangentSpace_ofFun h (tPart hmn a)).map ((graphOverTEquiv hmn).toLinearMap) := by
    rw [h1, ← haₜaₓ, ← TangentSpace_ofFun_def open_T₀ aₜT₀ diff_h, this]
  rw [h0, this, ← SetLike.ext'_iff]
  apply Submodule.eq_of_le_of_finrank_eq
  .
    rw [← SetLike.coe_subset_coe, ← this, ← h0]
    exact levelSet_subset_ker hg.differentiableAt aS ha
  .
    rw [finrank_ker_fderiv_eq hmn hgDx]
    rw [LinearEquiv.finrank_map_eq, TangentSpace_ofFun_finrank]

/-!
我們可以進一步推廣。不過這在 Lean 中稍顯複雜，各位可以這麼理解。
如果 $\nabla{g}_1, \cdots, \nabla{g}_m$ 為 independent，$\rank(Dg) = m$。
我們可以從 $Dg$ 的 column 中，選出 $m$ 個線性獨立的向量。
那麼經過座標轉換得到 $g_0$，有 $D_xg_0$ 可逆，滿足 regular level set 的條件。
此時，觀察座標轉換對於 level set 和 kernel 的影響，再加上 TangentSet 在座標轉換下不變，我們可以觀察到，兩座標下的 TangentSet 一樣。

其實我們也順便證明了，regular level set 的切空間，跟座標是無關的。
-/

lemma ker_comp_linearEquiv_as_set
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F)
    (P : E ≃L[ℝ] E) :
    ((A.comp P.toContinuousLinearMap).ker : Set E)
      =
    P.symm '' ((A.ker : Submodule ℝ E) : Set E) := by
  ext x
  constructor
  · intro hx
    change A (P x) = 0 at hx
    refine ⟨P x, ?_, ?_⟩
    · change A (P x) = 0
      exact hx
    · simp
  · intro hx
    rcases hx with ⟨y, hy, hyx⟩
    change A (P x) = 0
    have hxy : x = P.symm y := hyx.symm
    rw [hxy]
    simpa using hy

lemma image_eq_image_of_equiv_iff
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F)
    {A B : Set E} :
    e '' A = e '' B ↔ A = B := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      have hximg : e x ∈ e '' A := ⟨x, hx, rfl⟩
      rw [h] at hximg
      rcases hximg with ⟨y, hy, hyx⟩
      have hy_eq_x : y = x := by
        exact e.injective hyx
      simpa only [hy_eq_x] using hy
    · intro hx
      have hximg : e x ∈ e '' B := ⟨x, hx, rfl⟩
      rw [← h] at hximg
      rcases hximg with ⟨y, hy, hyx⟩
      have hy_eq_x : y = x := by
        exact e.injective hyx
      simpa only [hy_eq_x] using hy
  · intro h
    rw [h]

theorem levelSet_eq_ker_of_perm_invertible {a : Euc n} {S : Set (Euc n)} {g : Euc n → Euc m} (hS : IsOpen S)
  (aS : a ∈ S) {k : Euc m} (ha : g a = k) (hmn : m ≤ n) (hg : HasStrictFDerivAt g (fderiv ℝ g a) a)
  (P : Euc n ≃L[ℝ] Euc n) (hgDx : IsInvertibleCLM (DxBlock hmn (g ∘ P) (P.symm a))) :
  TangentSet (levelSetIn S g k) a = (fderiv ℝ g a).ker
:= by
  have h1 : HasStrictFDerivAt (fun x => g (P x)) (fderiv ℝ (g ∘ P) (P.symm a)) (P.symm a) := by
    rw [fderiv_comp_linearEquiv hg.differentiableAt]
    apply HasStrictFDerivAt.comp _ ?_ P.hasStrictFDerivAt
    rwa [ContinuousLinearEquiv.apply_symm_apply]

  have h2 : (g ∘ P) (P.symm a) = k := by
    rwa [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

  have h3 := P.symm.isOpenMap S hS

  have h4 : P.symm a ∈ P.symm '' S := by
    use a, aS

  have h5 := levelSet_eq_ker h3 h4 h2 hmn h1 hgDx

  rw [fderiv_comp_linearEquiv hg.differentiableAt] at h5
  have h6 : ((fderiv ℝ g a).comp P.toContinuousLinearMap).ker = P.symm '' (fderiv ℝ g a).ker := by
    exact ker_comp_linearEquiv_as_set _ _

  have h7 : (levelSetIn (P.symm '' S) (g ∘ P) k) = P.symm '' levelSetIn S g k := by
    ext x; constructor
    . intro ⟨⟨t, tS, t_eq⟩, rfl⟩
      use t, ⟨tS, ?_⟩, t_eq
      rw [← t_eq, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    . intro ⟨t, ⟨tS, gtk⟩, t_eq⟩
      use ⟨t, tS, t_eq⟩, ?_
      rw [← t_eq, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, gtk]

  rwa [← h5, h7, TangentSet_image_equiv, image_eq_image_of_equiv_iff] at h6

/--
If the gradients of $g$ is independent, then the Tangent Set of the level set of $g$ is exactly the orthogonal complement of the gradients of $g$.
-/
theorem levelSet_eq_ker_of_grad_independent {a : Euc n} {S : Set (Euc n)} {g : Euc n → Euc m} (hS : IsOpen S)
  (aS : a ∈ S) {k : Euc m} (ha : g a = k) (hg : HasStrictFDerivAt g (fderiv ℝ g a) a)
  (hDg : LinearIndependent ℝ (fun i : Fin m => componentGradient g a i)) :
  TangentSet (levelSetIn S g k) a = (fderiv ℝ g a).ker
:= by
  have h1 := fderiv_range_eq_top_of_gradient_independent hg.differentiableAt hDg
  rcases exists_perm_DxBlockCLM_invertible_of_surjective h1
  with ⟨P, hmn', hDPg⟩
  have h2 : DxBlockCLM hmn' ((fderiv ℝ g a).comp P.toContinuousLinearMap) = DxBlock hmn' (g ∘ ⇑P) (P.symm a) := by
    rw [DxBlockCLM, DxBlock, fderiv_comp_linearEquiv hg.differentiableAt]
  rw [h2] at hDPg
  exact levelSet_eq_ker_of_perm_invertible hS aS ha hmn' hg P hDPg

end LevelSet

section LagrangeMultiplier

/-!
那麼我們現在就能以大一微積分的敘事，重新描述拉格朗日乘子。
如果 $f$ 在 level set 上有局部極值，考慮在上面、於該點可微的路徑。
$f$ 有局部極值，自然有一個局部，和局部的最值。
由連續性，我們可以找到足夠小的，路徑的定義域中的局部，在這個局部中，路徑既落在 level set 上，也位於極值的局部中。
那麼由 Fermat's Theorem，這個路徑所對應的單變數函數，在該點的微分為 0。
由 chain rule 和定義可知 $\nabla{f}$ 垂直於該路徑。
-/

lemma Submodule.mem_span_orthogonal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set V) (v : V) :
  (∀ u ∈ S, ⟪u, v⟫ = 0) → v ∈ (span ℝ S)ᗮ
:= by
  intro vO u hu
  induction hu using Submodule.span_induction with
  | mem u uS => exact vO u uS
  | zero => exact inner_zero_left v
  | add u₁ u₂ hu₁ hu₂ iu₁ iu₂ =>
    rw [inner_add_left, iu₁, iu₂, zero_add]
  | smul c u hu iu =>
    rw [inner_smul_left, iu, mul_zero];

theorem derivative_zero_on_tangent_space_aux
    {f : Euc n → ℝ} {S C : Set (Euc n)} (hS : IsOpen S) {a : Euc n}
    (haS : a ∈ S)
    (diff_f : DifferentiableOn ℝ f S)
    (hextr : IsLocalExtrOn f C a)
    : ∇ f a ∈ (span ℝ (TangentSet C a))ᗮ := by
  apply mem_span_orthogonal (TangentSet C a)
  intro v ⟨r, diff_r, eq, hrC⟩;

  have hgrad : HasGradientAt f (∇ f a) a := by
    exact diff_f.hasGradientAt (hS.mem_nhds haS)

  have hfa : DifferentiableAt ℝ f a := hgrad.differentiableAt

  have hr' : HasDerivAt r (deriv r 0) 0 := by
    exact diff_r.differentiableAt.hasDerivAt

  have hcomp : HasDerivAt (fun t => f (r t)) ((fderiv ℝ f a) (deriv r 0)) 0 := by
    rw [← eq] at hgrad ⊢
    have := hgrad.hasFDerivAt
    rw [gradient, LinearIsometryEquiv.apply_symm_apply] at this
    exact this.comp_hasDerivAt 0 hr'

  have hchain :
      deriv (fun t => f (r t)) 0 = ⟪deriv r 0, ∇ f a⟫ := by
    calc
      deriv (fun t => f (r t)) 0 = (fderiv ℝ f a) (deriv r 0) := hcomp.deriv
      _ = ⟪deriv r 0, ∇ f a⟫ := by
        symm
        exact inner_gradient_right hfa

  have hrt : Filter.Tendsto r (nhds 0) (nhdsWithin a C) := by
    rw [nhdsWithin, ← Std.min_self (a := 𝓝 0)]
    refine Filter.Tendsto.inf ?_ ?_
    · simpa only [← eq] using diff_r.continuousAt.tendsto
    · exact Filter.tendsto_principal.2 hrC

  have hloc : IsLocalExtr (fun t => f (r t)) 0 := by
    change IsExtrFilter (fun t => f (r t)) (nhds 0) 0
    change IsExtrFilter f (nhdsWithin a C) a at hextr
    rw [← eq] at hextr hrt
    exact hextr.comp_tendsto hrt

  have hz : deriv (fun t => f (r t)) 0 = 0 := by
    exact hloc.deriv_eq_zero
  simpa only [hchain, diff_r.deriv] using hz

/-!
$f$ 在 level set 上的局部極值發生時，level set 的切空間會與 $f$ 的 gradient 垂直。
而因為 $g$ 的 gradient 為 independent，level set 為正規，因而有切空間，且為 $\ker(Dg)$。
而 $\ker(Dg)$ 又是 $\span\{\nabla{g}₁, \cdots, \nabla{g}_m\}^\perp$。
整理一下，由於在有限維，便知 $\nabla{f} \in \span\{\nabla{g}₁, \cdots, \nabla{g}_m\}^\perp$，證畢。
-/

/--
Coordinate-Dependent Lagrange Multiplier
-/
theorem My_LagrangeMultiplier {n m : ℕ} {S : Set (Euc n)} (hS : IsOpen S)
  {f : Euc n → ℝ} {g : Euc n → Euc m} {k : Euc m} {a : Euc n}
  (diff_f : DifferentiableOn ℝ f S) (ha : a ∈ levelSetIn S g k) (diff_g : HasStrictFDerivAt g (fderiv ℝ g a) a)
  (is_extr : IsLocalExtrOn f (levelSetIn S g k) a)
  (hDg : LinearIndependent ℝ (fun i : Fin m => componentGradient g a i))
  : ∇ f a ∈ gradientSpan g a :=
by
  have h1 := derivative_zero_on_tangent_space_aux hS ha.1 diff_f is_extr
  have h2 := levelSet_eq_ker_of_grad_independent hS ha.1 ha.2 diff_g hDg
  have h3 := normalSpace_eq_gradientSpan diff_g.differentiableAt
  rwa [h2, span_coe_eq_restrictScalars, Submodule.restrictScalars_self,
  ker_fderiv_eq_normalSpace_orthogonal, orthogonal_orthogonal, h3] at h1

end LagrangeMultiplier
