import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Bases
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
-- import Mathlib.Analysis.InnerProductSpace.TensorProduct

noncomputable instance : RCLike ℂ := inferInstance
-- 名前空間を定義
namespace HilbertSpaceOperations

-- 複素ヒルベルト空間を定義
-- variable {Qudit : Type} [NormedAddCommGroup Qudit]
--   [InnerProductSpace ℂ Qudit] [CompleteSpace Qudit] [TopologicalSpace.SeparableSpace Qudit] [FiniteDimensional ℂ Qudit]

-- QuditType を定義
class QuditType (a : Type) extends NormedAddCommGroup a, InnerProductSpace ℂ a,FiniteDimensional ℂ a

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

def tensor_product (Qudit1 Qudit2 : Type) [QuditType Qudit1] [QuditType Qudit2] : Type :=
  TensorProduct ℂ  Qudit1 Qudit2




-- tensor_product が QuditType であることを証明
noncomputable instance tensor_product_qudit_type (Qudit1 Qudit2 : Type) [QuditType Qudit1] [QuditType Qudit2] :
  QuditType (TensorProduct ℂ Qudit1 Qudit2) :=
{
  -- NormedAddCommGroup のインスタンス
  toAddCommGroup := TensorProduct.addCommGroup,

  -- InnerProductSpace のインスタンス
  toInnerProductSpace := sorry,
  norm := sorry,
  dist_self := sorry,
  dist_comm := sorry,
  dist_triangle := sorry,
  eq_of_dist_eq_zero := sorry,
  fg_top := sorry,

}


-- 半正定値エルミート線形作用素の定義
-- 有界性はそのそも有限次元なので問題ない
def PosSemiDefiniteHermitOperator (Qudit : Type) [QuditType Qudit] : Type :=
  { f : Qudit →ₗ[ℂ] Qudit // ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫ ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re }


-- 密度行列の定義
def DensityOperator (Qudit : Type) [QuditType Qudit] : Type :=
  { f : Qudit →ₗ[ℂ] Qudit //
   ∀ x y : Qudit, ⟪f.1 x, y⟫ = ⟪x, f.1 y⟫
   ∧ ∀ x: Qudit, 0 ≤  ⟪f.1 x, x⟫.re
   ∧ LinearMap.trace ℂ Qudit f = 1 }

-- QuditType クラスの型 Qudit を受け取り、Qudit から Qudit への線形写像の集合を返す関数
def LinearOperatorSet (Qudit : Type) [QuditType Qudit] : Type :=
  Qudit →ₗ[ℂ] Qudit

-- AddCommMonoid のインスタンスを定義
instance (Qudit : Type) [QuditType Qudit] : AddCommMonoid (LinearOperatorSet Qudit) :=
  LinearMap.addCommMonoid

-- module のインスタンスを定義
instance (Qudit : Type) [QuditType Qudit] : Module ℂ (LinearOperatorSet Qudit) :=
  LinearMap.module



-- Qudit1, Qudit2上の線形写像のテンソル積を定義
noncomputable def TensorProductMap [QuditType Qudit1] [QuditType Qudit2] [QuditType Qudit3] [QuditType Qudit4] (f1: LinearOperatorSet Qudit1 →ₗ[ℂ] LinearOperatorSet Qudit2) (f2: LinearOperatorSet Qudit3 →ₗ[ℂ] LinearOperatorSet Qudit4)  : LinearOperatorSet (TensorProduct ℂ Qudit1 Qudit3) →ₗ[ℂ] LinearOperatorSet (TensorProduct ℂ Qudit2 Qudit4) :=
  -- TensorProduct.map f1 f2
  sorry


def is_positive_map[QuditType H_in] [QuditType H_out] (φ : LinearOperatorSet H_in →ₗ[ℂ] LinearOperatorSet H_out)  : Prop :=
  --
  ∀ (f : LinearOperatorSet H_in),
    (∀ x : H_in, 0 ≤ ⟪f.1 x, x⟫.re) →
    (∀ y : H_out, 0 ≤ ⟪(φ f).1 y, y⟫.re)

instance (Qudit : Type) [QuditType Qudit] : AddCommMonoid (LinearOperatorSet Qudit) :=
  LinearMap.addCommMonoid


def QuantumChannel (H_in H_out : Type) [QuditType H_in] [QuditType H_out] : Type :=
  { φ : LinearOperatorSet H_in →ₗ[ℂ] LinearOperatorSet H_out //
  -- トレースを保存する
  ∀ (f: LinearOperatorSet H_in), LinearMap.trace ℂ H_in f = LinearMap.trace ℂ H_out (φ f)
  -- 完全正定値写像
  -- -- 任意の線形空間上の恒等写像とのテンソル積がis_positive_mapである
  ∧ ∀ (Z : Type) [QuditType Z],
    is_positive_map (TensorProductMap φ (LinearMap.id : LinearOperatorSet Z →ₗ[ℂ] LinearOperatorSet Z))
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

-- 測定を定義する
-- 測定とはPosSemiDefiniteHermitOperatorの有限個の集合であり、それらの和が恒等写像になるもの
def MeasurementOperator (Qudit : Type) [QuditType Qudit] : Type :=
  { M : Finset (PosSemiDefiniteHermitOperator Qudit) //
  -- 和が恒等写像になる
  Finset.sum M (fun f => f.1) = LinearMap.id
  }

end HilbertSpaceOperations
