data WidthV = Undef | Px Nat

data LTEWidthV : (w1, w2 : WidthV) -> Type where
  NoneCaseLeft 	  : LTEWidthV Undef _
  NoneCaseRight   : LTEWidthV _ Undef
  ValueLTE        : (LTE n m) -> LTEWidthV (Px n) (Px m)

total
isLTEWidthV : (w1, w2: WidthV) -> Dec (w1 `LTEWidthV` w2)
isLTEWidthV Undef _ = Yes NoneCaseLeft
isLTEWidthV _ Undef = Yes NoneCaseRight
isLTEWidthV (Px m) (Px n) = case (isLTE m n) of
				 Yes mSmallerThanN => Yes (ValueLTE mSmallerThanN)
				 No notMAtMostN => No (\(ValueLTE mAtMostN) => notMAtMostN mAtMostN)

data CSSState : Type where
  St  : (w: WidthV) -> (min: WidthV) -> (max: WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     :                  PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV)   ->
              {auto p1 : isLTEWidthV min w = Yes _} ->
              {auto p2 : isLTEWidthV w max = Yes _} ->
                               PVPair () (St Undef min max)     (St w min max)
  MinWidth  : (min: WidthV) ->
              {auto p1 : isLTEWidthV min w = Yes _} ->
              {auto p3 : isLTEWidthV min max = Yes _} ->
                               PVPair () (St w Undef max)       (St w min max)
  MaxWidth  : (max: WidthV) ->
              {auto p2 : isLTEWidthV w max = Yes _} ->
              {auto p3 : isLTEWidthV min max = Yes _} ->
                               PVPair () (St w min Undef)       (St w min max)
  End       :                  PVPair () (St w min max)         (St Undef Undef Undef)

  Pure      : ty -> PVPair ty s s
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Start
             MaxWidth (Px 40)
             MinWidth (Px 39)
             Width (Px 39)
             End
