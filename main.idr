import Width

%language ErrorReflection

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
