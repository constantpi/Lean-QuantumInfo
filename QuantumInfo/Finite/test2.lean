import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

set_option diagnostics true

variable (d : Type ) [Fintype d] [DecidableEq d]

noncomputable instance : RCLike ℂ := inferInstance

noncomputable def ComplexHilbertSpace (d : Type) [Fintype d] [DecidableEq d] : Type  :=
  HilbertSpace ℂ (PiLp 2 (fun _ : d => ℂ))

-- 実際に2次元の複素ヒルベルト空間を定義する
noncomputable def TwoDimComplexHilbertSpace : Type :=
  ComplexHilbertSpace (Fin 2)


#check TwoDimComplexHilbertSpace

variable (v : TwoDimComplexHilbertSpace)

-- ベクトルの型を確認
#check v

-- noncomputable def example_vector : PiLp 2 (fun _ : Fin 2 => ℂ) :=
--   fun i => if i = 0 then (1 : ℂ) else (0 : ℂ)

noncomputable def example_vector : TwoDimComplexHilbertSpace :=
  ⟨fun i => if i = 0 then (1 : ℂ) else (0 : ℂ)⟩

#check example_vector
