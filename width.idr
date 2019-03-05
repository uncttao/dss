data WidthSpec = None | Px Nat

data LTEWidthSpec : (w1, w2 : WidthSpec) -> Type where
  NoneCaseLeft 	  : LTEWidthSpec None _
  NoneCaseRight   : LTEWidthSpec _ None
  ValueLTE        : (LTE n m) -> LTEWidthSpec (Px n) (Px m)

-- (Width, MinWidth, MaxWidth)
data CSSState : WidthSpec -> WidthSpec -> WidthSpec -> Type where
  ValidState  : (width: WidthSpec) -> (minWidth: WidthSpec) -> (maxWidth: WidthSpec) ->
                (LTEWidthSpec minWidth width) ->
		(LTEWidthSpec width maxWidth) -> CSSState width minWidth maxWidth

data PVPair : Type -> Type where
  Width     : (w: WidthSpec) -> PVPair ()
  MinWidth  : PVPair ()
  MaxWidth  : PVPair ()

  Pure: ty -> PVPair ty
  (>>=) : PVPair a -> (a -> PVPair b) -> PVPair b

cssSpec : PVPair ()
cssSpec = do MaxWidth
             MinWidth
             Width (Px 3)
