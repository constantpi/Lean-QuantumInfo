import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

set_option diagnostics true
-- import Mathlib.Data.Matrix.Basic
-- import Mathlib.Algebra.Trace

-- import Mathlib.Analysis.NormedSpace.PiLp

-- open Complex

-- universe u

variable (d : Type ) [Fintype d] [DecidableEq d]

noncomputable instance : RCLike ℂ := inferInstance

-- noncomputable instance : SeminormedAddCommGroup (d → ℂ) :=
--   Pi.seminormedAddCommGroup

-- -- noncomputable instance : InnerProductSpace ℂ (PiLp 2 (fun _ : d => ℂ)) :=
-- --   PiLp.innerProductSpace ℂ (fun _ => ℂ)


-- -- 各成分が ℂ の PiLp 空間に対するインスタンスを定義
-- noncomputable instance : InnerProductSpace ℂ (PiLp 2 (fun _ : d => ℂ)) :=
--   -- @PiLp.innerProductSpace  (fun _ :d => ℂ)
--   sorry


-- noncomputable instance : CompleteSpace (PiLp 2 (fun _ : d => ℂ)) :=
--   -- PiLp.completeSpace ℂ (fun _ => ℂ)
--   sorry

noncomputable def ComplexHilbertSpace (d : Type) [Fintype d] [DecidableEq d] : Type  :=
  HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ))

-- 実際に2次元の複素ヒルベルト空間を定義する
-- ここでは、d を 2 として定義します。
-- ただしComplexHilbertSpaceを用いる
-- `ComplexHilbertSpace` を用いて複素二次元ヒルベルト空間を定義
noncomputable def TwoDimComplexHilbertSpace : Type :=
  ComplexHilbertSpace (Fin 2)



-- `ComplexHilbertSpace` を `HilbertSpace` にキャストする型クラスインスタンスを定義
noncomputable instance : Coe (ComplexHilbertSpace d) (HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ))) :=
  ⟨id⟩


-- `HilbertSpace` から `InnerProductSpace` へのキャストを定義
noncomputable instance  (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] : Coe (HilbertSpace 𝕜 E) (InnerProductSpace 𝕜 E) :=
  ⟨fun h => by
    letI : NormedAddCommGroup E := inferInstance
    letI : CompleteSpace E := inferInstance
    exact inferInstance⟩


noncomputable def inner_product_of_complex_hilbert_space
  {d : Type} [Fintype d] [DecidableEq d] (x y : ComplexHilbertSpace d) : ℂ :=
  -- まずx,yをinnerProductSpaceにキャスト
  let x' : InnerProductSpace ℂ (PiLp 2 (fun _ : d => ℂ)) := x
  let y' : InnerProductSpace ℂ (PiLp 2 (fun _ : d => ℂ)) := y
  -- その後、innerProductSpaceの内積を計算
  -- InnerProductSpace.inner x' y'

  sorry
  -- inner x' y'

-- 密度行列を定義する
-- def DensityMatrix (d : Type) [Fintype d] [DecidableEq d] : Type :=
--   { ρ : PiLp 2 (fun _ : d => ℂ) // 0 ≤ ρ }

-- スカラー積の型クラスインスタンスを提供
noncomputable instance : HSMul ℂ (ComplexHilbertSpace d) (ComplexHilbertSpace d) :=
  { hSMul := fun c x =>
    let x' : InnerProductSpace ℂ (PiLp 2 (fun _ : d => ℂ)) := x
    -- スカラー積を計算
    let result := c • x'
    -- InnerProductSpaceからComplexHilbertSpaceにキャスト
    result }


open Complex

-- `AddCommMonoid` のインスタンスを提供
noncomputable instance : AddCommMonoid (ComplexHilbertSpace d) :=
  sorry

-- `Module` の型クラスインスタンスを提供
noncomputable instance : Module ℂ (ComplexHilbertSpace d) :=
  sorry

-- 複素ヒルベルト空間上の線形作用素を定義
-- def LinearOperator (d : Type) [Fintype d] [DecidableEq d] : Type :=
--   { T : HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ)) → HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ)) //
--     ∀ x y : HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ)), ∀ a b : ℂ, T (a • x + b • y) = a • T x + b • T y }
def LinearOperator (d : Type) [Fintype d] [DecidableEq d] : Type :=
  {
    f : ComplexHilbertSpace d → ComplexHilbertSpace d //
    IsLinearMap ℂ f
    -- ∀ (x y : ComplexHilbertSpace d) (a b : ℂ), f (a • x + b • y) = a • f x + b • f y
  }

-- 今度は 正定値であることを要求する
-- def PositiveLinearOperator (d : Type) [Fintype d] [DecidableEq d] : Type :=
--   { T : LinearOperator d // ∀ v : ComplexHilbertSpace d, 0 ≤ dotProduct v (T v) ∧ Matrix.trace (T v) = 1 }

-- def LinearOperator2 (d : Type) [Fintype d] [DecidableEq d] : Type :=
--   LinearMap ℂ (ComplexHilbertSpace d) (ComplexHilbertSpace d)


-- 密度行列を定義する
-- def DensityMatrix (d : Type) [Fintype d] [DecidableEq d] : Type :=
--   { ρ : Matrix d d ℂ // ρ.isHermitian ∧ ∀ v : d → ℂ, 0 ≤ Matrix.dotProduct v (ρ.mulVec v) ∧ Matrix.trace ρ = 1 }


-- structure ComplexHilbertSpace (d : Type u) [Fintype d] [DecidableEq d] : Type (max u 1) where
--   space : HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ))

-- 密度行列を定義する

-- def DensityMatrix (d : Type u) [Fintype d] [DecidableEq d] : Type (max u 0) :=
--   {ρ : PiLp 2 (fun _ : d => ℂ) // 0 ≤ ρ}


-- import Mathlib.Analysis.InnerProductSpace.Defs
-- import Mathlib.Analysis.Complex.Basic
-- import Mathlib.Topology.Instances.Complex
-- import Mathlib.Analysis.InnerProductSpace.PiL2

-- -- `RCLike` のインスタンスを提供
-- noncomputable instance : RCLike ℂ := inferInstance

-- universe u

-- variable {d : Type u} [Fintype d] [DecidableEq d]

-- noncomputable instance : SeminormedAddCommGroup (d → ℂ) :=
--   Pi.seminormedAddCommGroup

-- -- /-- `ComplexHilbertSpace` は `d` 次元の複素線形空間を表します。 -/
-- -- structure ComplexHilbertSpace (d : Type*) [Fintype d] [DecidableEq d] : Type* :=
-- --   (space : HilbertSpace ℂ (d → ℂ))


-- noncomputable instance : InnerProductSpace ℂ (d → ℂ) :=
--   PiLp.innerProductSpace ℂ (fun _ => ℂ)

-- noncomputable instance : CompleteSpace (d → ℂ) :=
--   PiLp.completeSpace ℂ (fun _ => ℂ)

-- noncomputable def ComplexHilbertSpace : Type* :=
--   HilbertSpace ℂ (d → ℂ)
