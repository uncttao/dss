module Width

%language ErrorReflection

public export
data Width = None | Px Nat

syntax [x] px = Px x

public export
data LTEWidth  : (w1, w2 : Width) -> Type where
  NoneCaseLeft  : LTEWidth None _
  NoneCaseRight : LTEWidth _ None
  ValueLTE      : (LTE n m) -> LTEWidth (Px n) (Px m)

public export
data WidthOrdered : (w1, w2, w3: Width) -> Type where
  InOrder       : LTEWidth w1 w2 -> LTEWidth w2 w3 -> WidthOrdered w1 w2 w3

public export
total
isLTEWidth : (w1, w2 : Width) -> Dec (LTEWidth w1 w2)
isLTEWidth None _ 	  = Yes NoneCaseLeft
isLTEWidth _ None       = Yes NoneCaseRight
isLTEWidth (Px m) (Px n) = case (isLTE m n) of
  Yes mSmallerThanN => Yes (ValueLTE mSmallerThanN)
  No notMAtMostN => No (\(ValueLTE mAtMostN) => notMAtMostN mAtMostN)

public export
total isWidthOrdered : (w1, w2, w3 : Width) -> Dec (WidthOrdered w1 w2 w3)
isWidthOrdered w1 w2 w3 = case (isLTEWidth w1 w2) of
      Yes w1AtMostW2 => case (isLTEWidth w2 w3) of
        Yes w2AtMostW3 => Yes (InOrder w1AtMostW2 w2AtMostW3)
        No w2GreaterW3 => No (\(InOrder _ w2AtMostW3) => w2GreaterW3 w2AtMostW3)
      No w1GreaterW2 => No (\(InOrder w1AtMostW2 _) => w1GreaterW2 w1AtMostW2)

%error_handler
public export
widthErr : Err -> Maybe (List ErrorReportPart)
widthErr (CantSolveGoal `(WidthOrdered ~w1 ~w2 ~w3) _) =
  Just [TextPart "It must be true that ", TermPart w1, TextPart "(min-width) <= ", TermPart w2, TextPart "(width) <= ", TermPart w3, TextPart "(max-width)."]
widthErr _ = Nothing
