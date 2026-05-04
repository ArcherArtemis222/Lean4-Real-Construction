import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear
import Lean4RealConstruction.LagrangeMultiplier.PairComponent
import Lean4RealConstruction.LagrangeMultiplier.PrefixSplit
import Lean4RealConstruction.LagrangeMultiplier.LinearAlgebra

noncomputable section

namespace ImplicitFunctionTheorem

open scoped Topology Set Filter
open EuclideanSplit EuclideanPrefixSplit

@[simp] theorem xProjCLM_apply
    (hmn : m ≤ n) (z : Euc n) :
    xProjCLM hmn z = xPart hmn z := by
  rfl

@[simp] theorem tProjCLM_apply
    (hmn : m ≤ n) (z : Euc n) :
    tProjCLM hmn z = tPart hmn z := by
  rfl

@[simp] theorem xInclCLM_apply
    (hmn : m ≤ n) (x : Euc m) :
    xInclCLM hmn x = xtPair hmn x 0 := by
  simp [xInclCLM, xtPair]

@[simp] theorem tInclCLM_apply
    (hmn : m ≤ n) (t : Euc (n - m)) :
    tInclCLM hmn t = xtPair hmn 0 t := by
  simp [tInclCLM, xtPair]

@[simp] theorem xPart_xInclCLM
    (hmn : m ≤ n) (x : Euc m) :
    xPart hmn (xInclCLM hmn x) = x := by
  simp

@[simp] theorem tPart_xInclCLM
    (hmn : m ≤ n) (x : Euc m) :
    tPart hmn (xInclCLM hmn x) = 0 := by
  simp

@[simp] theorem xPart_tInclCLM
    (hmn : m ≤ n) (t : Euc (n - m)) :
    xPart hmn (tInclCLM hmn t) = 0 := by
  simp

@[simp] theorem tPart_tInclCLM
    (hmn : m ≤ n) (t : Euc (n - m)) :
    tPart hmn (tInclCLM hmn t) = t := by
  simp

theorem xInclCLM_add_tInclCLM
    (hmn : m ≤ n) (x : Euc m) (t : Euc (n - m)) :
    xInclCLM hmn x + tInclCLM hmn t = xtPair hmn x t := by
  apply (splitPrefixEquiv n m hmn).injective
  simp [xInclCLM, tInclCLM, xtPair]

theorem hasStrictFDerivAt_tPart
    (hmn : m ≤ n) (a : Euc n) :
    HasStrictFDerivAt (tPart hmn) (tProjCLM hmn) a := by
  simpa [tPart, tProjCLM] using (tProjCLM hmn).hasStrictFDerivAt

def levelSetIn
    (S : Set (Euc n)) (f : Euc n → Euc m) (v : Euc m) :
    Set (Euc n) :=
  {z | z ∈ S ∧ f z = v}

theorem ImplicitFunctionTheorem_localGraph
    {S : Set (Euc n)}
    (hS : IsOpen S)
    {f : Euc n → Euc m}
    {pt : Euc n}
    {v : Euc m}
    (hptS : pt ∈ S)
    (zero_pt : f pt = v)
    (hmn : m ≤ n)
    (hf_strict : HasStrictFDerivAt f (fderiv ℝ f pt) pt)
    (hDx : IsInvertibleCLM (DxBlock hmn f pt)) :
    ∃ T₀ : Set (Euc (n - m)),
    ∃ g : Euc (n - m) → Euc m,
      IsOpen T₀ ∧
      tPart hmn pt ∈ T₀ ∧
      g (tPart hmn pt) = xPart hmn pt ∧
      DifferentiableAt ℝ g (tPart hmn pt) ∧
      (∀ᶠ z in nhds pt,
        z ∈ levelSetIn S f v ↔ z ∈ graphOverT hmn g T₀) := by
  let A : Euc m ≃L[ℝ] Euc m := Classical.choose hDx
  have hA : ((A : Euc m →L[ℝ] Euc m) = DxBlock hmn f pt) := Classical.choose_spec hDx
  have hA' : DxBlock hmn f pt = (A : Euc m →L[ℝ] Euc m) := hA.symm
  let Φ : Euc n → Euc m × Euc (n - m) := fun z => (f z, tPart hmn z)
  let Φ' : Euc n →L[ℝ] Euc m × Euc (n - m) :=
    (fderiv ℝ f pt).prod (tProjCLM hmn)
  have hΦ : HasStrictFDerivAt Φ Φ' pt := by
    simpa [Φ, Φ'] using hf_strict.prodMk (hasStrictFDerivAt_tPart hmn pt)
  let Ψ : Euc m × Euc (n - m) →L[ℝ] Euc n :=
    (xInclCLM hmn).comp
        ((A.symm : Euc m →L[ℝ] Euc m).comp
          (ContinuousLinearMap.fst ℝ (Euc m) (Euc (n - m)) -
            (DtBlock hmn f pt).comp
              (ContinuousLinearMap.snd ℝ (Euc m) (Euc (n - m)))))
      + (tInclCLM hmn).comp
          (ContinuousLinearMap.snd ℝ (Euc m) (Euc (n - m)))
  have hΨ_apply :
      ∀ p : Euc m × Euc (n - m),
        Ψ p = xtPair hmn (A.symm (p.1 - DtBlock hmn f pt p.2)) p.2 := by
    intro p
    apply (splitPrefixEquiv n m hmn).injective
    simp [Ψ, xtPair]
  have hΦ'_xtPair :
      ∀ x : Euc m, ∀ t : Euc (n - m),
        Φ' (xtPair hmn x t) = (DxBlock hmn f pt x + DtBlock hmn f pt t, t) := by
    intro x t
    rw [← xInclCLM_add_tInclCLM (hmn := hmn) x t]
    ext <;> simp [Φ', DxBlock, DtBlock, map_add]
  have hleft : ∀ p : Euc m × Euc (n - m), Φ' (Ψ p) = p := by
    intro p
    rw [hΨ_apply, hΦ'_xtPair]
    ext <;> simp [hA']
  have hright : ∀ z : Euc n, Ψ (Φ' z) = z := by
    intro z
    have hz :
        Φ' z =
          (DxBlock hmn f pt (xPart hmn z) + DtBlock hmn f pt (tPart hmn z), tPart hmn z) := by
      simpa [xtPair_xPart_tPart (hmn := hmn) z] using
        hΦ'_xtPair (xPart hmn z) (tPart hmn z)
    rw [hz, hΨ_apply]
    simp [hA', xtPair_xPart_tPart (hmn := hmn) z]
  have hΦ'_ker : (Φ' : Euc n →ₗ[ℝ] Euc m × Euc (n - m)).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.2
    intro z w hzw
    simpa [hright z, hright w] using congrArg Ψ hzw
  have hΦ'_range : (Φ' : Euc n →ₗ[ℝ] Euc m × Euc (n - m)).range = ⊤ := by
    apply LinearMap.range_eq_top.2
    intro p
    refine ⟨Ψ p, hleft p⟩
  let Φe : Euc n ≃L[ℝ] Euc m × Euc (n - m) :=
    ContinuousLinearEquiv.ofBijective Φ' hΦ'_ker hΦ'_range
  have hΦe : HasStrictFDerivAt Φ (Φe : Euc n →L[ℝ] Euc m × Euc (n - m)) pt := by
    simpa [Φe] using hΦ
  let e := hΦe.toOpenPartialHomeomorph Φ
  let G : Euc m × Euc (n - m) → Euc n := e.symm
  let T₀ : Set (Euc (n - m)) := (fun t => (v, t)) ⁻¹' (e.target ∩ G ⁻¹' S)
  let g : Euc (n - m) → Euc m := fun t => xPart hmn (G (v, t))
  have htarget_pt : (v, tPart hmn pt) ∈ e.target := by
    simpa [e, Φ, zero_pt] using hΦe.image_mem_toOpenPartialHomeomorph_target (f := Φ)
  have hG_pt : G (v, tPart hmn pt) = pt := by
    simpa [G, e, Φ, zero_pt] using hΦe.localInverse_apply_image (f := Φ) (f' := Φe) (a := pt)
  have hT₀_open : IsOpen T₀ := by
    change IsOpen ((fun t : Euc (n - m) => (v, t)) ⁻¹' (e.target ∩ e.symm ⁻¹' S))
    exact (e.isOpen_inter_preimage_symm hS).preimage (continuous_const.prodMk continuous_id)
  have ht₀ : tPart hmn pt ∈ T₀ := by
    change (v, tPart hmn pt) ∈ e.target ∩ G ⁻¹' S
    refine ⟨htarget_pt, ?_⟩
    simpa [G, hG_pt] using hptS
  have hgpt : g (tPart hmn pt) = xPart hmn pt := by
    simp [g, hG_pt]
  have hG_strict :
      HasStrictFDerivAt G (Φe.symm : (Euc m × Euc (n - m)) →L[ℝ] Euc n)
        (v, tPart hmn pt) := by
    simpa [G, e, Φ, zero_pt] using hΦe.to_localInverse (f := Φ) (f' := Φe) (a := pt)
  have hprod :
      HasStrictFDerivAt
        (fun t : Euc (n - m) => (v, t))
        ((0 : Euc (n - m) →L[ℝ] Euc m).prod (ContinuousLinearMap.id ℝ (Euc (n - m))))
        (tPart hmn pt) := by
    simpa using
      (hasStrictFDerivAt_const v (tPart hmn pt)).prodMk (hasStrictFDerivAt_id (tPart hmn pt))
  have hgdiff : DifferentiableAt ℝ g (tPart hmn pt) := by
    have hGv :
        HasStrictFDerivAt
          (fun t : Euc (n - m) => G (v, t))
          ((Φe.symm : (Euc m × Euc (n - m)) →L[ℝ] Euc n).comp
            ((0 : Euc (n - m) →L[ℝ] Euc m).prod
              (ContinuousLinearMap.id ℝ (Euc (n - m)))))
          (tPart hmn pt) := by
      exact hG_strict.comp (tPart hmn pt) hprod
    have hx :
        HasStrictFDerivAt
          g
          ((xProjCLM hmn).comp
            ((Φe.symm : (Euc m × Euc (n - m)) →L[ℝ] Euc n).comp
              ((0 : Euc (n - m) →L[ℝ] Euc m).prod
                (ContinuousLinearMap.id ℝ (Euc (n - m))))))
          (tPart hmn pt) := by
      simpa [g, xPart, xProjCLM] using
        (xProjCLM hmn).hasStrictFDerivAt.comp (tPart hmn pt) hGv
    exact hx.hasFDerivAt.differentiableAt
  refine ⟨T₀, g, hT₀_open, ht₀, hgpt, hgdiff, ?_⟩
  have hsource_pt : pt ∈ e.source := by
    simpa [e] using hΦe.mem_toOpenPartialHomeomorph_source (f := Φ)
  have hsource_nhds : e.source ∈ nhds pt := e.open_source.mem_nhds hsource_pt
  have hS_nhds : S ∈ nhds pt := hS.mem_nhds hptS
  filter_upwards [hsource_nhds, hS_nhds] with z hz_source hzS
  constructor
  · intro hz_level
    have hz_target : (v, tPart hmn z) ∈ e.target := by
      have hz_target' : e z ∈ e.target := e.map_source hz_source
      change Φ z ∈ e.target at hz_target'
      simpa [Φ, hz_level.2] using hz_target'
    have hz_symm : e.symm (v, tPart hmn z) = z := by
      have hz_symm' : e.symm (e z) = z := e.left_inv hz_source
      change e.symm (Φ z) = z at hz_symm'
      simpa [Φ, hz_level.2] using hz_symm'
    have ht_mem : tPart hmn z ∈ T₀ := by
      change (v, tPart hmn z) ∈ e.target ∩ G ⁻¹' S
      refine ⟨hz_target, ?_⟩
      simpa [G, hz_symm] using hz_level.1
    have hx_mem : xPart hmn z = g (tPart hmn z) := by
      simp [g, G, hz_symm]
    exact ⟨ht_mem, hx_mem⟩
  · intro hz_graph
    rcases hz_graph with ⟨ht_mem, hx_mem⟩
    have hy : (v, tPart hmn z) ∈ e.target ∩ G ⁻¹' S := ht_mem
    have hy_target : (v, tPart hmn z) ∈ e.target := hy.1
    have hy_memS : G (v, tPart hmn z) ∈ S := hy.2
    have hG_eq : e (G (v, tPart hmn z)) = (v, tPart hmn z) := by
      simpa [G] using e.right_inv hy_target
    have ht_eq : tPart hmn (G (v, tPart hmn z)) = tPart hmn z := by
      simpa [e, Φ] using congrArg Prod.snd hG_eq
    have hx_eq : xPart hmn (G (v, tPart hmn z)) = xPart hmn z := by
      calc
        xPart hmn (G (v, tPart hmn z))
            = g (tPart hmn z) := by simp [g, G]
        _ = xPart hmn z := by simpa using hx_mem.symm
    have hz_eq : z = G (v, tPart hmn z) := by
      calc
        z = xtPair hmn (xPart hmn z) (tPart hmn z) := by
          symm
          exact xtPair_xPart_tPart (hmn := hmn) z
        _ = xtPair hmn (xPart hmn (G (v, tPart hmn z))) (tPart hmn (G (v, tPart hmn z))) := by
          rw [hx_eq, ht_eq]
        _ = G (v, tPart hmn z) := xtPair_xPart_tPart (hmn := hmn) (G (v, tPart hmn z))
    have hf_eq : f (G (v, tPart hmn z)) = v := by
      simpa [e, Φ] using congrArg Prod.fst hG_eq
    refine ⟨?_, ?_⟩
    · simpa [G, ← hz_eq] using hy_memS
    · simpa [G, ← hz_eq] using hf_eq


end ImplicitFunctionTheorem
