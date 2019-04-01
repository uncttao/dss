import Width

data CSSState : Type where
  St : (w, min, max : WidthV) -> CSSState

emptyState : CSSState
emptyState = St Undef Undef Undef

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     : PVPair () emptyState emtpyState
  Width     : (w: WidthV)   -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St Undef min max) (St w min max)
  MinWidth  : (min: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w Undef max)   (St w min max)
  MaxWidth  : (max: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w min Undef)   (St w min max)
  End       : PVPair () (St w min max) emtpyState
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

cssSpec : PVPair () emptyState emptyState
cssSpec = do Start
             MaxWidth (40 px)
             MinWidth (35 px)
             Width (35 px)
             End
