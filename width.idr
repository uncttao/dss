%language ErrorReflection

data WidthV = Undef | Px Nat

data CheckWidthIntent = LeftBounded | RightBounded | RangeSound

data LTEWidthV  : (w1, w2 : WidthV) -> (intent: CheckWidthIntent) -> Type where
  NoneCaseLeft  : (intent: CheckWidthIntent) -> LTEWidthV Undef _ intent
  NoneCaseRight : (intent: CheckWidthIntent) -> LTEWidthV _ Undef intent
  ValueLTE      : (intent: CheckWidthIntent) -> (LTE n m) ->
						LTEWidthV (Px n) (Px m) intent

total
isLTEWidthV : (w1, w2 : WidthV) -> (intent: CheckWidthIntent) -> Dec (LTEWidthV w1 w2 intent)
isLTEWidthV Undef _ intent       = Yes (NoneCaseLeft intent)
isLTEWidthV _ Undef intent       = Yes (NoneCaseRight intent)
isLTEWidthV (Px m) (Px n) intent = case (isLTE m n) of
  Yes mSmallerThanN => Yes (ValueLTE intent mSmallerThanN)
  No notMAtMostN => No (\(ValueLTE intent mAtMostN) =>
                          notMAtMostN mAtMostN)

data CSSState : Type where
  St  : (w, min, max : WidthV) -> CSSState

data PVPair : Type -> CSSState -> CSSState -> Type where
  Start     : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
  Width     : (w: WidthV) ->
              {auto p1 : LTEWidthV min w LeftBounded} ->
              {auto p2 : LTEWidthV w max RightBounded} ->
              PVPair () (St Undef min max) (St w min max)
  MinWidth  : (min: WidthV) ->
              {auto p1 : LTEWidthV min max RangeSound} ->
              {auto p3 : LTEWidthV min w LeftBounded} ->
              PVPair () (St w Undef max)   (St w min max)
  MaxWidth  : (max: WidthV) ->
              {auto p3 : LTEWidthV min max RangeSound} ->
              {auto p2 : LTEWidthV w max RightBounded} ->
              PVPair () (St w min Undef)   (St w min max)
  End       : PVPair () (St w min max)     (St Undef Undef Undef)

  Pure      : ty -> PVPair ty s s
  (>>=)     : PVPair a s1 s2 -> (a -> PVPair b s2 s3) -> PVPair b s1 s3

%error_handler
widthErr : Err -> Maybe (List ErrorReportPart)
widthErr (CantSolveGoal `(LTEWidthV ~w1 ~w2 ~intent) _) = case intent of
  (P _ (NS (UN "LeftBounded") _) _)  => Just [TextPart "You either specified a width ", TermPart w2, TextPart " smaller than min-width ", TermPart w1, TextPart " or a min-width", TermPart w1, TextPart " greater than width ", TermPart w2, TextPart "!"]
  (P _ (NS (UN "RightBounded") _) _) => Just [TextPart "Hey, it doesn't make sense to say width is ", TermPart w1, TextPart " but having a max-width of ", TermPart w2, TextPart "!"]
  (P _ (NS (UN "RangeSound") _) _)   => Just [TextPart "Oops! min-width", TermPart w1, TextPart " cannot be greater than max-width ", TermPart w2, TextPart ". Please try again!"]
widthErr _ = Nothing

cssSpec : PVPair () (St Undef Undef Undef) (St Undef Undef Undef)
cssSpec = do Start
             MaxWidth (Px 40)
             MinWidth (Px 40)
             Width (Px 40)
             End

