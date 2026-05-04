import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear

noncomputable section

set_option linter.unusedSectionVars false

open scoped Topology Set Filter

namespace EuclideanSplit

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {n m : ℕ}

/-- Canonical splitting `ℝ^(n+m) ≃L ℝ^n × ℝ^m`. -/
noncomputable abbrev splitEquiv (n m : ℕ) :
    Euc (n + m) ≃L[ℝ] Euc n × Euc m :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)

/-- First `n` coordinates of a vector in `ℝ^(n+m)`. -/
noncomputable def fstE (z : Euc (n + m)) : Euc n :=
  ((splitEquiv n m) z).1

/-- Last `m` coordinates of a vector in `ℝ^(n+m)`. -/
noncomputable def sndE (z : Euc (n + m)) : Euc m :=
  ((splitEquiv n m) z).2

/-- Reassemble a vector of `ℝ^n × ℝ^m` into `ℝ^(n+m)`. -/
noncomputable def pairE (x : Euc n) (y : Euc m) : Euc (n + m) :=
  (splitEquiv n m).symm (x, y)

@[simp] theorem fstE_pairE (x : Euc n) (y : Euc m) :
    fstE (n := n) (m := m) (pairE x y) = x := by
  simp [fstE, pairE, splitEquiv]
  rfl

@[simp] theorem sndE_pairE (x : Euc n) (y : Euc m) :
    sndE (n := n) (m := m) (pairE x y) = y := by
  simp [sndE, pairE, splitEquiv]
  rfl

@[simp] theorem pairE_fstE_sndE (z : Euc (n + m)) :
    pairE (n := n) (m := m)
      (fstE (n := n) (m := m) z)
      (sndE (n := n) (m := m) z) = z := by
  simpa [pairE, fstE, sndE, splitEquiv] using
    (splitEquiv n m).symm_apply_apply z

/-- First component of a map into `ℝ^(n+m)`. -/
noncomputable def front {X : Type*} (γ : X → Euc (n + m)) : X → Euc n :=
  fun t => fstE (n := n) (m := m) (γ t)

/-- Second component of a map into `ℝ^(n+m)`. -/
noncomputable def back {X : Type*} (γ : X → Euc (n + m)) : X → Euc m :=
  fun t => sndE (n := n) (m := m) (γ t)

/-- Reassemble two maps into a map into `ℝ^(n+m)`. -/
noncomputable def joinMap {X : Type*}
    (α : X → Euc n) (β : X → Euc m) : X → Euc (n + m) :=
  fun t => pairE (n := n) (m := m) (α t) (β t)

@[simp] theorem front_joinMap {X : Type*}
    (α : X → Euc n) (β : X → Euc m) :
    front (n := n) (m := m) (joinMap α β) = α := by
  funext t
  simp [front, joinMap]

@[simp] theorem back_joinMap {X : Type*}
    (α : X → Euc n) (β : X → Euc m) :
    back (n := n) (m := m) (joinMap α β) = β := by
  funext t
  simp [back, joinMap]

@[simp] theorem joinMap_front_back {X : Type*}
    (γ : X → Euc (n + m)) :
    joinMap (n := n) (m := m)
      (front (n := n) (m := m) γ)
      (back  (n := n) (m := m) γ) = γ := by
  funext t
  simp [joinMap, front, back]

/-! ## FDeriv API -/

/--
If `α` and `β` have Fréchet derivatives, then `joinMap α β`
has derivative obtained by first forming the product derivative,
then applying `(splitEquiv n m).symm`.
-/
theorem HasFDerivAt.join
    {α : X → Euc n} {β : X → Euc m}
    {α' : X →L[ℝ] Euc n} {β' : X →L[ℝ] Euc m}
    {x : X}
    (hα : HasFDerivAt α α' x)
    (hβ : HasFDerivAt β β' x) :
    HasFDerivAt
      (joinMap α β)
      (((splitEquiv n m).symm : Euc n × Euc m →L[ℝ] Euc (n + m)).comp
        (α'.prod β'))
      x := by
  -- Codex target:
  -- use `hα.prodMk hβ`, then compose with `(splitEquiv n m).symm.hasFDerivAt`.
  simpa [joinMap, splitEquiv] using
    ((splitEquiv n m).symm.hasFDerivAt.comp x (hα.prodMk hβ))

/--
`fderiv` version of the previous theorem.
This is the original-coordinate version of
`Dγ = (Dα, Dβ)`.
-/
theorem fderiv_join
    {α : X → Euc n} {β : X → Euc m} {x : X}
    (hα : DifferentiableAt ℝ α x)
    (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (joinMap α β) x =
      (((splitEquiv n m).symm : Euc n × Euc m →L[ℝ] Euc (n + m)).comp
        ((fderiv ℝ α x).prod (fderiv ℝ β x))) := by
  -- Codex target:
  -- apply `.fderiv` to `HasFDerivAt.join hα.hasFDerivAt hβ.hasFDerivAt`.
  simpa using
    (HasFDerivAt.join
      (n := n) (m := m)
      (α := α) (β := β)
      hα.hasFDerivAt hβ.hasFDerivAt).fderiv

/--
If `γ` is differentiable, then its front component is differentiable.
-/
theorem DifferentiableAt.front
    {γ : X → Euc (n + m)} {x : X}
    (hγ : DifferentiableAt ℝ γ x) :
    DifferentiableAt ℝ (front γ) x := by
  -- Codex target:
  -- compose `γ` with `splitEquiv n m`, then take `.fst`.
  simpa [front, splitEquiv] using
    (((splitEquiv n m).differentiableAt.comp x hγ).fst)

/--
If `γ` is differentiable, then its back component is differentiable.
-/
theorem DifferentiableAt.back
    {γ : X → Euc (n + m)} {x : X}
    (hγ : DifferentiableAt ℝ γ x) :
    DifferentiableAt ℝ (back γ) x := by
  simpa [back, splitEquiv] using
    (((splitEquiv n m).differentiableAt.comp x hγ).snd)

/--
Component derivative: front part.
-/
theorem HasFDerivAt.front
    {γ : X → Euc (n + m)}
    {γ' : X →L[ℝ] Euc (n + m)}
    {x : X}
    (hγ : HasFDerivAt γ γ' x) :
    HasFDerivAt
      (front γ)
      ((ContinuousLinearMap.fst ℝ (Euc n) (Euc m)).comp
        (((splitEquiv n m : Euc (n + m) ≃L[ℝ] Euc n × Euc m) : Euc (n + m) →L[ℝ] Euc n × Euc m).comp γ'))
      x := by
  -- Codex target:
  -- first compose by `splitEquiv n m`, then use `.fst`.
  simpa [front, splitEquiv] using
    (((splitEquiv n m).hasFDerivAt.comp x hγ).fst)

/--
Component derivative: back part.
-/
theorem HasFDerivAt.back
    {γ : X → Euc (n + m)}
    {γ' : X →L[ℝ] Euc (n + m)}
    {x : X}
    (hγ : HasFDerivAt γ γ' x) :
    HasFDerivAt
      (back γ)
      ((ContinuousLinearMap.snd ℝ (Euc n) (Euc m)).comp
        (((splitEquiv n m : Euc (n + m) ≃L[ℝ] Euc n × Euc m) : Euc (n + m) →L[ℝ] Euc n × Euc m).comp γ'))
      x := by
  simpa [back, splitEquiv] using
    (((splitEquiv n m).hasFDerivAt.comp x hγ).snd)

/-! ## One-dimensional `deriv` API -/

variable {α : ℝ → Euc n} {β : ℝ → Euc m} {t : ℝ}

/--
Derivative of the first component of a curve in `ℝ^(n+m)`.
-/
theorem HasDerivAt.front
    {γ : ℝ → Euc (n + m)} {γ' : Euc (n + m)} {t₀ : ℝ}
    (hγ : HasDerivAt γ γ' t₀) :
    HasDerivAt
      (front (n := n) (m := m) γ)
      (fstE (n := n) (m := m) γ')
      t₀ := by
  -- Codex target:
  -- 1. compose `γ` with `splitEquiv n m`
  -- 2. use `.fst`
  -- 3. simplify definitions of `front` and `fstE`
  have hs :
      HasDerivAt
        (fun t => (splitEquiv n m) (γ t))
        ((splitEquiv n m) γ')
        t₀ := by
    simpa using
      ((splitEquiv n m).hasFDerivAt.comp t₀ hγ)
  simpa [front, fstE] using hs.fst

/--
Derivative of the second component of a curve in `ℝ^(n+m)`.
-/
theorem HasDerivAt.back
    {γ : ℝ → Euc (n + m)} {γ' : Euc (n + m)} {t₀ : ℝ}
    (hγ : HasDerivAt γ γ' t₀) :
    HasDerivAt
      (back (n := n) (m := m) γ)
      (sndE (n := n) (m := m) γ')
      t₀ := by
  have hs :
      HasDerivAt
        (fun t => (splitEquiv n m) (γ t))
        ((splitEquiv n m) γ')
        t₀ := by
    simpa using
      ((splitEquiv n m).hasFDerivAt.comp t₀ hγ)
  simpa [back, sndE] using hs.snd

/--
One-dimensional derivative version:
`deriv (joinMap α β) t = join of deriv α and deriv β`.
-/
theorem deriv_join
    (hα : DifferentiableAt ℝ α t)
    (hβ : DifferentiableAt ℝ β t) :
    deriv (joinMap α β) t =
      (splitEquiv n m).symm (deriv α t, deriv β t) := by
  -- Codex target:
  -- either use `HasDerivAt.prodMk`, then compose by the continuous linear map,
  -- or derive it from `fderiv_join` and `deriv = fderiv ... 1`.
  have hF := fderiv_join (n := n) (m := m) (α := α) (β := β) hα hβ
  -- Usually `simp [deriv, hF]` is enough after unfolding `deriv`.
  simp only [deriv, hF]
  simp

variable {n m : ℕ}

end EuclideanSplit

namespace EuclideanSplit

variable {n m : ℕ}

/-- Graph of `f` over a base set `S`, living inside `ℝ^(n+m)`. -/
def graphSet (f : Euc n → Euc m) (S : Set (Euc n)) : Set (Euc (n + m)) :=
  {z : Euc (n + m) | fstE z ∈ S ∧
       sndE z = f (fstE z)}

@[simp] theorem pairE_mem_graphSet
    {f : Euc n → Euc m} {S : Set (Euc n)} {x : Euc n} :
    pairE (n := n) (m := m) x (f x) ∈ graphSet f S ↔ x ∈ S := by
  simp only [graphSet, Set.mem_setOf_eq, fstE_pairE, sndE_pairE, and_true]

/-- The linear map `u ↦ (u, L u)`. -/
noncomputable def graphCLM
    (L : Euc n →L[ℝ] Euc m) :
    Euc n →L[ℝ] Euc (n + m) :=
  ((splitEquiv n m).symm : Euc n × Euc m →L[ℝ] Euc (n + m)).comp
    ((ContinuousLinearMap.id ℝ (Euc n)).prod L)

@[simp] theorem graphCLM_apply
    (L : Euc n →L[ℝ] Euc m) (u : Euc n) :
    graphCLM L u = pairE u (L u) := by
  rfl

@[simp] theorem fstE_graphCLM
    (L : Euc n →L[ℝ] Euc m) (u : Euc n) :
    fstE (graphCLM L u) = u := by
  simp [graphCLM, fstE]; rfl

@[simp] theorem sndE_graphCLM
    (L : Euc n →L[ℝ] Euc m) (u : Euc n) :
    sndE (graphCLM L u) = L u := by
  simp [graphCLM, sndE]; rfl

noncomputable def graphCLMRangeEquiv
    (L : Euc n →L[ℝ] Euc m) :
    Euc n ≃ₗ[ℝ] ↥((EuclideanSplit.graphCLM L).range) :=
{ toFun := fun u => ⟨EuclideanSplit.graphCLM L u, ⟨u, rfl⟩⟩
  invFun := fun ξ => EuclideanSplit.fstE ξ.1
  left_inv := by
    intro u
    simp
  right_inv := by
    intro ξ
    rcases ξ with ⟨z, u, rfl⟩
    ext
    simp
  map_add' := by
    intro u v
    ext
    simp [map_add]
  map_smul' := by
    intro c u
    ext
    simp [map_smul] }

end EuclideanSplit
