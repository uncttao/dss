data WidthV = Undef | Px Nat

data LTEWidthV : (w1, w2 : WidthV) -> Type where
  NoneCaseLeft 	  : LTEWidthV Undef _
  NoneCaseRight   : LTEWidthV _ Undef
  ValueLTE        : (LTE n m) -> LTEWidthV (Px n) (Px m)

data CSSState : Type where
  St  : (w: WidthV) -> (min: WidthV) -> (max: WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Begin     :                  PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV)   -> PVPair () (St Undef min max)     (St w min max)
  MinWidth  : (min: WidthV) -> PVPair () (St w Undef max)       (St w min max)
  MaxWidth  : (max: WidthV) -> PVPair () (St w min Undef)       (St w min max)
  End       :                  PVPair () (St w min max)         (St Undef Undef Undef)

  Pure: ty -> PVPair ty s s
  (>>=) : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Begin
             MaxWidth (Px 40)
             MinWidth (Px 10)
             Width (Px 30)
             End
