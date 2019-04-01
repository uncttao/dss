import Width

data DeclSt : Type where
  St : (w, min, max : Width) -> DeclSt

emptySt : DeclSt
emptySt = St None None None

data PV : Type -> DeclSt -> DeclSt -> Type where
  Start     : PV () emptySt emtpyState
  Width     : (w: Width)   -> {auto prf : WidthOrdered min w max} -> PV () (St None min max) (St w min max)
  MinWidth  : (min: Width) -> {auto prf : WidthOrdered min w max} -> PV () (St w None max)   (St w min max)
  MaxWidth  : (max: Width) -> {auto prf : WidthOrdered min w max} -> PV () (St w min None)   (St w min max)
  End       : PV () (St w min max) emtpyState
  (>>=)     : PV a s1 s2 -> (a -> PV b s2 s3) -> PV b s1 s3

cssSpec : PV () emptySt emptySt
cssSpec = do Start
             MaxWidth (40 px)
             MinWidth (35 px)
             Width (35 px)
             End
