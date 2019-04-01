import Width

data Selector =
  Body | Section | Par | H1 | H2 | Div | Nav | Span |
  Cl String |
  Id String

data CascadeSelect = Nil | (::) Selector CascadeSelect

cascadeSelectEx1 : CascadeSelect
cascadeSelectEx1 = [Cl "my-beautiful-button", Body, H1, Id "inputbox2"]

infixr 5 .|
data SelectGroup = HAS_STYLE | (.|) CascadeSelect SelectGroup

selectGroupEx1 : SelectGroup
selectGroupEx1 = [Body, H2, Nav] .| [Cl "design-header", Cl "nav-menu"] .| [Par] .| [Div] .| HAS_STYLE

data DeclSt : Type where
  St : (w, min, max : Width) -> DeclSt

emptySt : DeclSt
emptySt = St None None None

data PV : Type -> DeclSt -> DeclSt -> Type where
  Start     : PV () _ emptyState
  Width     : (w: Width)   -> {auto prf : WidthOrdered min w max} -> PV () (St None min max) (St w min max)
  MinWidth  : (min: Width) -> {auto prf : WidthOrdered min w max} -> PV () (St w None max)   (St w min max)
  MaxWidth  : (max: Width) -> {auto prf : WidthOrdered min w max} -> PV () (St w min None)   (St w min max)
  End       : PV () (St w min max) _
  (>>=)     : PV a s1 s2 -> (a -> PV b s2 s3) -> PV b s1 s3

cssSpec : PV () _ _
cssSpec = do Start
             MaxWidth (40 px)
             MinWidth (35 px)
             Width (35 px)
             End
