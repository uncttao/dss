module Width

%language ErrorReflection

public export
data WidthV = Undef | Px Nat

public export
data LTEWidthV  : (w1, w2 : WidthV) -> Type where
  NoneCaseLeft  : LTEWidthV Undef _
  NoneCaseRight : LTEWidthV _ Undef
  ValueLTE      : (LTE n m) -> LTEWidthV (Px n) (Px m)

public export
data LTEWidthVOrder : (w1, w2, w3: WidthV) -> Type where
  InOrder       : LTEWidthV w1 w2 -> LTEWidthV w2 w3 -> LTEWidthVOrder w1 w2 w3

public export
total
isLTEWidthV : (w1, w2 : WidthV) -> Dec (LTEWidthV w1 w2)
isLTEWidthV Undef _ 	  = Yes NoneCaseLeft
isLTEWidthV _ Undef       = Yes NoneCaseRight
isLTEWidthV (Px m) (Px n) = case (isLTE m n) of
  Yes mSmallerThanN => Yes (ValueLTE mSmallerThanN)
  No notMAtMostN => No (\(ValueLTE mAtMostN) => notMAtMostN mAtMostN)

public export
total isLTEWidthVOrder : (w1, w2, w3 : WidthV) -> Dec (LTEWidthVOrder w1 w2 w3)
isLTEWidthVOrder w1 w2 w3 = case (isLTEWidthV w1 w2) of
      Yes w1AtMostW2 => case (isLTEWidthV w2 w3) of
        Yes w2AtMostW3 => Yes (InOrder w1AtMostW2 w2AtMostW3)
        No w2GreaterW3 => No (\(InOrder _ w2AtMostW3) => w2GreaterW3 w2AtMostW3)
      No w1GreaterW2 => No (\(InOrder w1AtMostW2 _) => w1GreaterW2 w1AtMostW2)

%error_handler
widthErr : Err -> Maybe (List ErrorReportPart)
widthErr (CantSolveGoal `(LTEWidthVOrder ~w1 ~w2 ~w3) _) =
  Just [TextPart "It must be true that ", TermPart w1, TextPart "(min-width) <= ", TermPart w2, TextPart "(width) <= ", TermPart w3, TextPart "(max-width)."]
widthErr _ = Nothing
