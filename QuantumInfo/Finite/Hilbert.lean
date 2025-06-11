import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Bases
import Mathlib.LinearAlgebra.Trace

noncomputable instance : RCLike ℂ := inferInstance
-- 名前空間を定義
namespace HilbertSpaceOperations

-- 複素ヒルベルト空間を定義
-- variable {Qudit : Type} [NormedAddCommGroup Qudit]
--   [InnerProductSpace ℂ Qudit] [CompleteSpace Qudit] [TopologicalSpace.SeparableSpace Qudit] [FiniteDimensional ℂ Qudit]

-- QuditType を定義
class QuditType (a : Type) extends NormedAddCommGroup a, InnerProductSpace ℂ a, CompleteSpace a, TopologicalSpace.SeparableSpace a, FiniteDimensional ℂ a

-- ベクトルの加算
def vector_addition  (x y : Qudit) [QuditType Qudit]: Qudit := x + y

-- スカラー積
def scalar_multiplication  (a : ℂ) (x : Qudit) [QuditType Qudit]: Qudit := a • x

-- 内積の略記
scoped notation "⟪" x ", " y "⟫" => inner ℂ x y

-- 内積計算
def inner_product (x y : Qudit)  [QuditType Qudit]: ℂ := ⟪x, y⟫

-- ヒルベルト空間の次元を取得する関数
noncomputable def get_dimension (Qudit : Type) [QuditType Qudit] : Nat :=
  Module.finrank ℂ Qudit

-- -- ヒルベルト空間が有限次元であることを表す命題
-- noncomputable def is_finite_dimensional : Prop :=
--   FiniteDimensional ℂ Qudit

-- 半正定値エルミート線形作用素の定義
-- 有界性はそのそも有限次元なので問題ない
def PosSemiDefiniteHermitOperator (Qudit : Type) [QuditType Qudit] : Type :=
  { f : Qudit →ₗ[ℂ] Qudit // ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫ ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re }


-- 密度行列の定義
def DensityOperator (Qudit : Type) [QuditType Qudit] : Type :=
  { f : Qudit →ₗ[ℂ] Qudit // Continuous f ∧ ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫ ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re
  ∧ LinearMap.trace ℂ Qudit f = 1 }

-- QuditType クラスの型 Qudit を受け取り、Qudit から Qudit への線形写像の集合を返す関数
def LinearOperatorSet (Qudit : Type) [QuditType Qudit] : Type :=
  Qudit →ₗ[ℂ] Qudit



-- AddCommMonoid のインスタンスを定義
-- instance (Qudit : Type) [QuditType Qudit] : AddCommMonoid (LinearOperatorSet Qudit) where
--   add := sorry
--   zero := sorry

-- AddCommMonoid のインスタンスを定義
instance (Qudit : Type) [QuditType Qudit] : AddCommMonoid (LinearOperatorSet Qudit) :=
  LinearMap.addCommMonoid

-- module のインスタンスを定義
instance (Qudit : Type) [QuditType Qudit] : Module ℂ (LinearOperatorSet Qudit) :=
  LinearMap.module


def QuantumChannel (H_in H_out : Type) [QuditType H_in] [QuditType H_out] : Type :=
  { φ : LinearOperatorSet H_in →ₗ[ℂ] LinearOperatorSet H_out //
  -- トレースを保存する
  ∀ (f: LinearOperatorSet H_in), LinearMap.trace ℂ H_in f = LinearMap.trace ℂ H_out (φ f)
  -- 完全正定値写像
  }


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
