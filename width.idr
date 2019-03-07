%language ErrorReflection

data WidthV = Undef | Px Nat

data LTEWidthV  : (w1, w2 : WidthV) -> Type where
  NoneCaseLeft  : LTEWidthV Undef _
  NoneCaseRight : LTEWidthV _ Undef
  ValueLTE      : (LTE n m) -> LTEWidthV (Px n) (Px m)

total
isLTEWidthV : (w1, w2 : WidthV) -> Dec (LTEWidthV w1 w2)
isLTEWidthV Undef _ = Yes NoneCaseLeft
isLTEWidthV _ Undef = Yes NoneCaseRight
isLTEWidthV (Px m) (Px n) = case (isLTE m n) of
				 Yes mSmallerThanN => Yes (ValueLTE mSmallerThanN)
				 No notMAtMostN => No (\(ValueLTE mAtMostN) =>
							   notMAtMostN mAtMostN)

data CSSState : Type where
  St  : (w, min, max : WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV) ->
              {auto p1 : LTEWidthV min w} ->
              {auto p2 : LTEWidthV w max} ->
              PVPair () (St Undef min max) (St w min max)
  MinWidth  : (min: WidthV) ->
              {auto p1 : LTEWidthV min max} ->
              {auto p3 : LTEWidthV min w} ->
              PVPair () (St w Undef max)   (St w min max)
  MaxWidth  : (max: WidthV) ->
              {auto p3 : LTEWidthV min max} ->
              {auto p2 : LTEWidthV w max} ->
              PVPair () (St w min Undef)   (St w min max)
  End       : PVPair () (St w min max)     (St Undef Undef Undef)

  Pure      : ty -> PVPair ty s s
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

%error_handler
total
widthErr : Err -> Maybe (List ErrorReportPart)
widthErr (CantSolveGoal `(LTEWidthV ~w1 ~w2) _) =
  Just [ TextPart "Expect width ", TermPart w1,
         TextPart " to be smaller than or equal to ", TermPart w2,
         TextPart ". However, it seems that this is not true. " ]
widthErr _ = Nothing

cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Start
             MaxWidth (Px 40)
             MinWidth (Px 39)
             Width (Px 39)
             End

