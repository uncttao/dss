%language ErrorReflection

data WidthV = Undef | Px Nat

data LTEWidthV  : (w1, w2 : WidthV) -> Type where
  NoneCaseLeft  : LTEWidthV Undef _
  NoneCaseRight : LTEWidthV _ Undef
  ValueLTE      : (LTE n m) -> LTEWidthV (Px n) (Px m)

data LTEWidthVOrder : (w1, w2, w3: WidthV) -> Type where
  InOrder       : LTEWidthV w1 w2 -> LTEWidthV w2 w3 -> LTEWidthVOrder w1 w2 w3

total
isLTEWidthV : (w1, w2 : WidthV) -> Dec (LTEWidthV w1 w2)
isLTEWidthV Undef _ 	  = Yes NoneCaseLeft
isLTEWidthV _ Undef       = Yes NoneCaseRight
isLTEWidthV (Px m) (Px n) = case (isLTE m n) of
  Yes mSmallerThanN => Yes (ValueLTE mSmallerThanN)
  No notMAtMostN => No (\(ValueLTE mAtMostN) => notMAtMostN mAtMostN)

total isLTEWidthVOrder : (w1, w2, w3 : WidthV) -> Dec (LTEWidthVOrder w1 w2 w3)
isLTEWidthVOrder w1 w2 w3 = case (isLTEWidthV w1 w2) of
      Yes w1AtMostW2 => case (isLTEWidthV w2 w3) of
        Yes w2AtMostW3 => Yes (InOrder w1AtMostW2 w2AtMostW3)
        No w2GreaterW3 => No (\(InOrder _ w2AtMostW3) => w2GreaterW3 w2AtMostW3)
      No w1GreaterW2 => No (\(InOrder w1AtMostW2 _) => w1GreaterW2 w1AtMostW2)

data CSSState : Type where
  St  : (w, min, max : WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV)   -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St Undef min max) (St w min max)
  MinWidth  : (min: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w Undef max)   (St w min max)
  MaxWidth  : (max: WidthV) -> {auto p : LTEWidthVOrder min w max} -> PVPair () (St w min Undef)   (St w min max)
  End       : PVPair () (St w min max)     (St Undef Undef Undef)

  Pure      : ty -> PVPair ty s s
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

%error_handler
widthErr : Err -> Maybe (List ErrorReportPart)
widthErr (CantSolveGoal `(LTEWidthVOrder ~w1 ~w2 ~w3) _) =
  Just [TextPart "It must be true that ", TermPart w1, TextPart "(min-width) <= ", TermPart w2, TextPart "(width) <= ", TermPart w3, TextPart "(max-width)."]
widthErr _ = Nothing


cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Start
             MaxWidth (Px 40)
             MinWidth (Px 35)
             Width (Px 38)
             End
