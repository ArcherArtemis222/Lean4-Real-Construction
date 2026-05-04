import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear
import Lean4RealConstruction.LagrangeMultiplier.PairComponent

open EuclideanSplit

variable {n m : ℕ}

-- 第一組：核心 equivalence
-- 先加一個 cast，用來把 Euc n 改寫成 Euc (m + (n-m))

namespace EuclideanPrefixSplit

/-- Change the dimension index by a proof of equality. -/
noncomputable def eucCast {n n' : ℕ} (h : n = n') :
    Euc n ≃L[ℝ] Euc n' := by
  subst h
  exact ContinuousLinearEquiv.refl ℝ (Euc n)

/--
Split `ℝ^n` into the first `m` coordinates and the remaining `n-m` coordinates.

This is the main bridge:
`Euc n ≃L[ℝ] Euc m × Euc (n-m)`.
-/
noncomputable def splitPrefixEquiv
    (n m : ℕ) (hmn : m ≤ n) :
    Euc n ≃L[ℝ] Euc m × Euc (n - m) :=
  (eucCast (n := n) (n' := m + (n - m)) (by omega)).trans
    (EuclideanSplit.splitEquiv m (n - m))

end EuclideanPrefixSplit

-- 第二組：點／向量層 API
-- 這一組對應之前的 `fstE`/`sndE`/`pairE`，但現在是「從 Euc n 切前 m 維」

namespace EuclideanPrefixSplit

variable {n m : ℕ}

/-- The first `m` coordinates of a vector in `ℝ^n`. -/
noncomputable def xPart
    (hmn : m ≤ n) (z : Euc n) : Euc m :=
  ((splitPrefixEquiv n m hmn) z).1

/-- The remaining `n-m` coordinates of a vector in `ℝ^n`. -/
noncomputable def tPart
    (hmn : m ≤ n) (z : Euc n) : Euc (n - m) :=
  ((splitPrefixEquiv n m hmn) z).2

/-- Reassemble `(x,t)` as a vector in `ℝ^n`. -/
noncomputable def xtPair
    (hmn : m ≤ n) (x : Euc m) (t : Euc (n - m)) : Euc n :=
  (splitPrefixEquiv n m hmn).symm (x, t)

@[simp] theorem xPart_xtPair
    (hmn : m ≤ n) (x : Euc m) (t : Euc (n - m)) :
    xPart hmn (xtPair hmn x t) = x := by
  simp [xPart, xtPair, splitPrefixEquiv]
  rfl

@[simp] theorem tPart_xtPair
    (hmn : m ≤ n) (x : Euc m) (t : Euc (n - m)) :
    tPart hmn (xtPair hmn x t) = t := by
  simp [tPart, xtPair, splitPrefixEquiv]
  rfl

@[simp] theorem xtPair_xPart_tPart
    (hmn : m ≤ n) (z : Euc n) :
    xtPair hmn (xPart hmn z) (tPart hmn z) = z := by
  simpa [xPart, tPart, xtPair, splitPrefixEquiv] using
    (splitPrefixEquiv n m hmn).symm_apply_apply z

end EuclideanPrefixSplit

-- 第三組：函數／曲線層 API
-- 這一組對應之前的 `front`/`back`/`joinMap`

namespace EuclideanPrefixSplit

variable {n m : ℕ}

/-- First-coordinate part of a map into `ℝ^n`. -/
noncomputable def xMap {X : Type*}
    (hmn : m ≤ n) (γ : X → Euc n) : X → Euc m :=
  fun s => xPart hmn (γ s)

/-- Remaining-coordinate part of a map into `ℝ^n`. -/
noncomputable def tMap {X : Type*}
    (hmn : m ≤ n) (γ : X → Euc n) : X → Euc (n - m) :=
  fun s => tPart hmn (γ s)

/-- Reassemble two maps into a map into `ℝ^n`. -/
noncomputable def xtMap {X : Type*}
    (hmn : m ≤ n)
    (x : X → Euc m) (t : X → Euc (n - m)) : X → Euc n :=
  fun s => xtPair hmn (x s) (t s)

@[simp] theorem xMap_xtMap {X : Type*}
    (hmn : m ≤ n)
    (x : X → Euc m) (t : X → Euc (n - m)) :
    xMap hmn (xtMap hmn x t) = x := by
  funext s
  simp [xMap, xtMap]

@[simp] theorem tMap_xtMap {X : Type*}
    (hmn : m ≤ n)
    (x : X → Euc m) (t : X → Euc (n - m)) :
    tMap hmn (xtMap hmn x t) = t := by
  funext s
  simp [tMap, xtMap]

@[simp] theorem xtMap_xMap_tMap {X : Type*}
    (hmn : m ≤ n) (γ : X → Euc n) :
    xtMap hmn (xMap hmn γ) (tMap hmn γ) = γ := by
  funext s
  simp [xMap, tMap, xtMap]

end EuclideanPrefixSplit

-- 第四組：把函數拆成 sections

namespace EuclideanPrefixSplit

variable {n m : ℕ}

/-- View a function on `ℝ^n` as a function on `ℝ^m × ℝ^(n-m)`. -/
noncomputable def splitDomain
    (hmn : m ≤ n) {X : Type*}
    (g : Euc n → X) :
    Euc m × Euc (n - m) → X :=
  fun p => g (xtPair hmn p.1 p.2)

/-- Curried version of `splitDomain`. -/
noncomputable def splitDomain₂
    (hmn : m ≤ n) {X : Type*}
    (g : Euc n → X) :
    Euc m → Euc (n - m) → X :=
  fun x t => g (xtPair hmn x t)

/-- Fix `t`; view `g` as a function of the first `m` variables. -/
noncomputable def xSection
    (hmn : m ≤ n) {X : Type*}
    (g : Euc n → X) (t : Euc (n - m)) :
    Euc m → X :=
  fun x => g (xtPair hmn x t)

/-- Fix `x`; view `g` as a function of the remaining variables. -/
noncomputable def tSection
    (hmn : m ≤ n) {X : Type*}
    (g : Euc n → X) (x : Euc m) :
    Euc (n - m) → X :=
  fun t => g (xtPair hmn x t)

end EuclideanPrefixSplit

-- 第五組：線性投影與線性嵌入

namespace EuclideanPrefixSplit

variable {n m : ℕ}

/-- Linear projection onto the first `m` coordinates. -/
noncomputable def xProjCLM
    (hmn : m ≤ n) : Euc n →L[ℝ] Euc m :=
  (ContinuousLinearMap.fst ℝ (Euc m) (Euc (n - m))).comp
    ((splitPrefixEquiv n m hmn : Euc n ≃L[ℝ] Euc m × Euc (n - m))
      : Euc n →L[ℝ] Euc m × Euc (n - m))

/-- Linear projection onto the remaining `n-m` coordinates. -/
noncomputable def tProjCLM
    (hmn : m ≤ n) : Euc n →L[ℝ] Euc (n - m) :=
  (ContinuousLinearMap.snd ℝ (Euc m) (Euc (n - m))).comp
    ((splitPrefixEquiv n m hmn : Euc n ≃L[ℝ] Euc m × Euc (n - m))
      : Euc n →L[ℝ] Euc m × Euc (n - m))

/-- Linear inclusion of first-coordinate variations: `u ↦ (u, 0)`. -/
noncomputable def xInclCLM
    (hmn : m ≤ n) : Euc m →L[ℝ] Euc n :=
  ((splitPrefixEquiv n m hmn).symm
      : Euc m × Euc (n - m) →L[ℝ] Euc n).comp
    (ContinuousLinearMap.inl ℝ (Euc m) (Euc (n - m)))

/-- Linear inclusion of remaining-coordinate variations: `v ↦ (0, v)`. -/
noncomputable def tInclCLM
    (hmn : m ≤ n) : Euc (n - m) →L[ℝ] Euc n :=
  ((splitPrefixEquiv n m hmn).symm
      : Euc m × Euc (n - m) →L[ℝ] Euc n).comp
    (ContinuousLinearMap.inr ℝ (Euc m) (Euc (n - m)))

end EuclideanPrefixSplit

namespace EuclideanPrefixSplit

variable {n m : ℕ}

/-- The derivative block with respect to the first `m` variables. -/
noncomputable def DxBlock
    (hmn : m ≤ n)
    (g : Euc n → Euc m) (a : Euc n) :
    Euc m →L[ℝ] Euc m :=
  (fderiv ℝ g a).comp (xInclCLM hmn)

/-- The derivative block with respect to the remaining variables. -/
noncomputable def DtBlock
    (hmn : m ≤ n)
    (g : Euc n → Euc m) (a : Euc n) :
    Euc (n - m) →L[ℝ] Euc m :=
  (fderiv ℝ g a).comp (tInclCLM hmn)

end EuclideanPrefixSplit

--

namespace EuclideanPrefixSplit

open Set

variable {n m : ℕ}

/--
Graph of `h : Euc (n-m) → Euc m` inside `Euc n`,
using the splitting `z = (x,t)`.
-/
def graphOverT
    (hmn : m ≤ n)
    (h : Euc (n - m) → Euc m)
    (T : Set (Euc (n - m))) :
    Set (Euc n) :=
  {z | tPart hmn z ∈ T ∧
       xPart hmn z = h (tPart hmn z)}

@[simp] theorem xtPair_mem_graphOverT
    (hmn : m ≤ n)
    {h : Euc (n - m) → Euc m}
    {T : Set (Euc (n - m))}
    {t : Euc (n - m)} :
    xtPair hmn (h t) t ∈ graphOverT hmn h T ↔ t ∈ T := by
  simp [graphOverT]

end EuclideanPrefixSplit

namespace EuclideanPrefixSplit

open EuclideanSplit

variable {n m : ℕ}

/--
The equivalence sending the standard graph coordinate `(t, x)` in
`Euc ((n-m)+m)` to the prefix-split coordinate `(x, t)` in `Euc n`.
-/
noncomputable def graphOverTEquiv
    (hmn : m ≤ n) :
    Euc ((n - m) + m) ≃L[ℝ] Euc n :=
  ((EuclideanSplit.splitEquiv (n - m) m).trans
    (ContinuousLinearEquiv.prodComm ℝ (Euc (n - m)) (Euc m))).trans
    (splitPrefixEquiv n m hmn).symm

@[simp] theorem graphOverTEquiv_pairE
    (hmn : m ≤ n)
    (t : Euc (n - m)) (x : Euc m) :
    graphOverTEquiv hmn
      (EuclideanSplit.pairE (n := n - m) (m := m) t x)
      =
    xtPair hmn x t := by
  rw [xtPair, (splitPrefixEquiv n m hmn).eq_symm_apply, graphOverTEquiv]
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · change
      (((EuclideanSplit.splitEquiv (n - m) m)
        (EuclideanSplit.pairE (n := n - m) (m := m) t x)).2) = x
    simpa [EuclideanSplit.sndE] using
      (EuclideanSplit.sndE_pairE (n := n - m) (m := m) t x)
  · change
      (((EuclideanSplit.splitEquiv (n - m) m)
        (EuclideanSplit.pairE (n := n - m) (m := m) t x)).1) = t
    simpa [EuclideanSplit.fstE] using
      (EuclideanSplit.fstE_pairE (n := n - m) (m := m) t x)

@[simp] theorem graphOverTEquiv_symm_xtPair
    (hmn : m ≤ n)
    (x : Euc m) (t : Euc (n - m)) :
    (graphOverTEquiv hmn).symm
      (xtPair hmn x t)
      =
    EuclideanSplit.pairE (n := n - m) (m := m) t x := by
  apply (graphOverTEquiv hmn).injective
  simp [graphOverTEquiv_pairE]

end EuclideanPrefixSplit

namespace EuclideanPrefixSplit

open Set
open EuclideanSplit

variable {n m : ℕ}

theorem graphOverT_eq_image_graphSet
    (hmn : m ≤ n)
    (h : Euc (n - m) → Euc m)
    (T : Set (Euc (n - m))) :
    graphOverT hmn h T
      =
    graphOverTEquiv hmn ''
      (graphSet h T) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨ht, hx⟩

    refine ⟨pairE (n := n - m) (m := m)
        (tPart hmn z)
        (h (tPart hmn z)), ?_, ?_⟩

    · simp [graphSet, ht]

    · calc
        graphOverTEquiv hmn
          (pairE (n := n - m) (m := m)
            (tPart hmn z)
            (h (tPart hmn z)))
            =
          xtPair hmn (h (tPart hmn z)) (tPart hmn z) := by
            simp
        _ = xtPair hmn (xPart hmn z) (tPart hmn z) := by
            rw [← hx]
        _ = z := by
            exact xtPair_xPart_tPart (hmn := hmn) z

  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨ht, hx⟩
    have hz :
        graphOverTEquiv hmn w =
          xtPair hmn (h (fstE (n := n - m) (m := m) w))
            (fstE (n := n - m) (m := m) w) := by
      calc
        graphOverTEquiv hmn w
            =
          graphOverTEquiv hmn
            (pairE (n := n - m) (m := m)
              (fstE (n := n - m) (m := m) w)
              (sndE (n := n - m) (m := m) w)) := by
                rw [pairE_fstE_sndE (n := n - m) (m := m) w]
        _ =
          xtPair hmn
            (sndE (n := n - m) (m := m) w)
            (fstE (n := n - m) (m := m) w) :=
              graphOverTEquiv_pairE hmn
                (fstE (n := n - m) (m := m) w)
                (sndE (n := n - m) (m := m) w)
        _ =
          xtPair hmn
            (h (fstE (n := n - m) (m := m) w))
            (fstE (n := n - m) (m := m) w) := by
              rw [hx]
    rw [hz]
    simpa using ht

end EuclideanPrefixSplit
