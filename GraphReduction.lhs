> module GraphReduction where


> import Control.Exception (Exception(..), throwIO)
> import Data.IORef (IORef, newIORef, readIORef, writeIORef)
> import Data.Typeable (cast)
> import qualified LambdaPiCombinators as C

> data Node = NodePtr :@: NodePtr

> data NodePtr = S | K | I | B | C | P | T | S' | B' | C' | NodePtr (IORef Node)
>
> instance Show NodePtr where
>   show S = "S"
>   show K = "K"
>   show I = "I"
>   show B = "B"
>   show C = "C"
>   show P = "P"
>   show T = "T"
>   show S' = "S'"
>   show B' = "B"
>   show C' = "C"
>   show NodePtr{} = "<nodeptr>"

> newNodePtr :: Node -> IO NodePtr
> newNodePtr = fmap NodePtr . newIORef

Unwrap indirection when we access a field.

> indirection :: NodePtr -> IO (Maybe NodePtr)
> indirection x = do
>   case x of
>     NodePtr ref -> do
>       n <- readIORef ref
>       case n of
>         I :@: x -> do
>           pure (Just x)
>         _ ->
>           pure Nothing
>     _ ->
>       pure Nothing

> readLeft :: IORef Node -> IO NodePtr
> readLeft ref = do
>   l :@: r <- readIORef ref
>   indirection l >>= maybe (pure l) (\x -> writeIORef ref (x :@: r) >> pure x)

> readRight :: IORef Node -> IO NodePtr
> readRight ref = do
>   l :@: r <- readIORef ref
>   indirection r >>= maybe (pure r) (\x -> writeIORef ref (l :@: x) >> pure x)

> showNodePtr :: NodePtr -> IO String
> showNodePtr = go False
>   where
>     go _ S = pure "S"
>     go _ K = pure "K"
>     go _ I = pure "I"
>     go _ B = pure "B"
>     go _ C = pure "C"
>     go p (NodePtr x) = do
>       y :@: z <- readIORef x
>       y' <- go False y
>       z' <- go True  z
>       pure $
>         if p then "(" <> y' <> " " <> z' <> ")" else y' <> " " <> z'

To find the result, run |gs <- reduce g []; pure (last gs)|:

> reduce :: NodePtr -> [IORef Node] -> IO NodePtr
> reduce (NodePtr x) s = do
>   l <- readLeft x
>   reduce l (x:s)
> reduce K (x:y:s) = do
>   x' <- readRight x
>   writeIORef y (I :@: x')
>   reduce x' (y:s)
> reduce S (f:g:x:s) = do
>   f' <- readRight f
>   g' <- readRight g
>   x' <- readRight x
>   fx <- newNodePtr (f' :@: x')
>   gx <- newNodePtr (g' :@: x')
>   writeIORef x (fx :@: gx)
>   reduce fx (x:s)
> reduce B (f:g:x:s) = do
>   f' <- readRight f
>   g' <- readRight g
>   x' <- readRight x
>   fx <- newNodePtr (f' :@: x')
>   writeIORef x (fx :@: g')
>   reduce fx (x:s)
> reduce C (f:g:x:s) = do
>   f' <- readRight f
>   x' <- readRight x
>   g' <- readRight g
>   gx <- newNodePtr (g' :@: x')
>   writeIORef x (f' :@: gx)
>   reduce f' (x:s)
> reduce S' (k:f:g:x:s) = do
>   f' <- readRight f
>   x' <- readRight x
>   fx <- newNodePtr (f' :@: x')
>   g' <- readRight g
>   gx <- newNodePtr (g' :@: x')
>   k' <- readRight k
>   kfx <- newNodePtr (k' :@: fx)
>   writeIORef x (kfx :@: gx)
>   reduce kfx (x:s)
> reduce B' (k:f:g:x:s) = do
>   k' <- readRight k
>   f' <- readRight f
>   g' <- readRight g
>   x' <- readRight x
>   kf <- newNodePtr (k' :@: f')
>   gx <- newNodePtr (g' :@: x')
>   writeIORef x (kf :@: gx)
>   reduce kf (x:s)
> reduce C' (k:f:g:x:s) = do
>   k' <- readRight k
>   f' <- readRight f
>   g' <- readRight g
>   x' <- readRight x
>   fx <- newNodePtr (f' :@: x')
>   kfx <- newNodePtr (k' :@: fx)
>   writeIORef x (kfx :@: g')
>   reduce kfx (x:s)
> reduce P [x,y] = do
>   x'  <- readRight x
>   x'' <- reduce x' []
>   writeIORef x (P :@: x'')
>   y'  <- readRight y
>   y'' <- reduce y' []
>   writeIORef y (NodePtr x :@: y'')
>   pure (NodePtr x) -- reduce x and y recursively
> reduce T [] = pure T
> reduce a s = throwIO $ IncorrectNumberOfArguments a

There is no I rule, because the indirections should take care of that if
the application of I is reducible. Because this implements normal order
reduction, it's not quite suitable for comparing lambda-pi terms

> data SomeGraphReductionException
>   = forall e . Exception e => SomeGraphReductionException e
> instance Show SomeGraphReductionException where
>   show (SomeGraphReductionException e) = show e
> instance Exception SomeGraphReductionException where
>
> data IncorrectNumberOfArguments =
>   IncorrectNumberOfArguments NodePtr deriving (Show)
>
> instance Exception IncorrectNumberOfArguments where
>   toException = toException . SomeGraphReductionException
>   fromException x = do
>     SomeGraphReductionException e <- fromException x
>     cast x
>   displayException (IncorrectNumberOfArguments h) =
>     "Incorrect number of arguments for " <> show h

> i :: IO NodePtr -> IO NodePtr
> i mx = do
>   x <- mx
>   newNodePtr (I :@: x)

> k :: IO NodePtr -> IO NodePtr -> IO NodePtr
> k mx my = do
>  x <- mx
>  f <- newNodePtr (K :@: x)
>  y <- my
>  newNodePtr (f :@: y)

> s :: IO NodePtr -> IO NodePtr -> IO NodePtr -> IO NodePtr
> s mf mg mx = do
>   f <- mf
>   sf <- newNodePtr (S :@: f)
>   g <- mg
>   sfg <- newNodePtr (sf :@: g)
>   x <- mx
>   newNodePtr (sfg :@: x)

> toGraph :: C.Combinator -> IO NodePtr
> toGraph C.S = pure S
> toGraph C.K = pure K
> toGraph C.I = pure I
> toGraph C.B = pure B
> toGraph C.C = pure C
> toGraph C.T = pure T
> toGraph C.P = pure P
> toGraph C.S' = pure S'
> toGraph C.C' = pure C'
> toGraph C.B' = pure B'
> toGraph c | x C.:@: y <- C.wnf c = do
>   x' <- toGraph x
>   y' <- toGraph y
>   newNodePtr (x' :@: y')
