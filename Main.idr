import Width

data Selector =
  P | Body | Div | Span | Nav | Button |
  Id String |
  Cl String

data CSSState : Type where
  St : (w, min, max : WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV)   -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St Undef min max) (St w min max)
  MinWidth  : (min: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w Undef max)   (St w min max)
  MaxWidth  : (max: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w min Undef)   (St w min max)
  End       : PVPair () (St w min max)     (St Undef Undef Undef)

  Pure      : ty -> PVPair ty s s
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Start
             MaxWidth (40 px)
             MinWidth (35 px)
             Width (35 px)
             End
