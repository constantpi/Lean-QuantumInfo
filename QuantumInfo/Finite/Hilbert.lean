import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Bases
import Mathlib.LinearAlgebra.Trace

-- 2次元の複素ヒルベルト空間を具体的に定義
noncomputable def TwoDimComplexHilbertSpace : Type :=
  HilbertSpace ℂ (PiLp 2 (fun _ : Fin 2 => ℂ))

noncomputable instance : RCLike ℂ := inferInstance

-- 名前空間を定義
namespace HilbertSpaceOperations

-- 複素ヒルベルト空間を定義
variable {Qudit : Type} [NormedAddCommGroup Qudit]
  [InnerProductSpace ℂ Qudit] [CompleteSpace Qudit] [TopologicalSpace.SeparableSpace Qudit] [FiniteDimensional ℂ Qudit]

-- ベクトルの加算
def vector_addition (x y : Qudit) : Qudit := x + y

-- スカラー積
def scalar_multiplication (a : ℂ) (x : Qudit) : Qudit := a • x

-- 内積の略記
scoped notation "⟪" x ", " y "⟫" => inner ℂ x y

-- 内積計算
def inner_product (x y : Qudit) : ℂ := ⟪x, y⟫

-- ヒルベルト空間の次元を取得する関数
noncomputable def get_dimension : Nat :=
  Module.finrank ℂ Qudit

-- -- ヒルベルト空間が有限次元であることを表す命題
-- noncomputable def is_finite_dimensional : Prop :=
--   FiniteDimensional ℂ Qudit

-- 半正定値エルミート線形作用素の定義
-- 有界性はそのそも有限次元なので問題ない
def PosSemiDefiniteHermitOperator : Type :=
  { f : Qudit →ₗ[ℂ] Qudit // ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫ ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re }

-- 適当な基底を用いてトレースを定義する
def basis : Basis (Fin (Module.finrank ℂ Qudit)) ℂ Qudit :=
  sorry

-- トレースの定義
-- def trace (T : PosSemiDefiniteHermitOperator) : ℂ :=
--   let basis := Basis.ofFiniteDimensional ℂ Qudit
--   let dim := Module.finrank ℂ Qudit
--   let trace_value := (Finset.univ : Finset (Fin dim)).sum fun i => ⟪T.1 (basis i), basis i⟫
--   trace_value

-- 密度行列の定義
def DensityOperator : Type :=
  { f : Qudit →ₗ[ℂ] Qudit // Continuous f ∧ ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫ ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re
  ∧ LinearMap.trace ℂ Qudit f = 1 }

noncomputable instance : AddCommMonoid DensityOperator :=
  interInstance

-- 量子チャンネルの定義
def QuantumChannel : Type :=
  { f : DensityOperator →ₗ[ℂ] DensityOperator // Continuous f}

  -- TODO:測定とチャンネル(QuantumChannel)
  -- operatorをoperatorに移す線形写像
  -- DensityOperator(H): H:Qudit上のDensityOperatorの集合として定義したい
  -- H_in, H_out: Qubit
  -- QuantumChannel(H_in, H_out)
--   QuantumChannel(H_in, H_out):
-- CP completely positive map
-- TP trace preserving
-- Linear map
-- from LinearOperator(H_in) to LinearOperator(H_out)


end HilbertSpaceOperations
