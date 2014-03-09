import Test.Quickcheck
import Test.Quickcheck.Monadic
import Language.Haskell.TH
import Control.Monad.Free.TH
import Quickcheck.GenT

toGenT :: (Monad m) => Gen (m a) -> GenT m a
toGenT = liftGen >=> lift

instance MonadReader m => MonadReader (GenT m) where
  ask     = lift ask
  local f = toGenT . liftM (local f) . runGenT

newtype VarName = VarName { varName :: Name }

newtype VarT = VarType { varT :: Type }

genType :: [VarT] -> Gen Type

genType vars = sized $ \n -> do
  frequency [(1,       ),
             (1, (vars !) <$> choose (0, length vars - 1),
             (1,       ),
             …]

genConstructor :: [VarT] -> Gen Con

newtype DataD = DataDec { dataD :: Dec }

instance VarName

instance Arbitrary DataD where
  arbitrary = do
    NonEmpty vars <- arbitrary
    
    let param = last vars
        
    let rest  = init vars
        
    DataName name <- arbitrary
    
    DataD [] name map vars (listOf1 genConstructor vars)

    let free =
      (do
          len <- choose (0, 2)
          genType )

newtype WithVars a = WithVars (ReaderT [VarName] Q a) deriving (Monad, MonadReader)


instance Arbitrary (WithVars Cons) where
  arbitrary = runGenT $ do
    argNodep <- local init       $ listOf1 toGenT arbitrary
    argFree  <- local (:[]).last $ flip vectorOf arbitrary <$> (choose (0,3))
    param <- asks $ VarT . (:[]).last
    argFree' <- take 2 $  atMost 1 (== param) argFree
    args <- shuffleM (argFree ++ argNodep)

    name <- mkName
    
    frequency [(1, do
                     name <- mkName "A"
                     return $ NormalC name args),
               (1, do
                     name <- mkName "A"
                     namedArgs <- mapM (\t -> do name <- mkName "f"
                                               (name, NotStrict, t)) args
                     return $ RecC name namedArgs),
               (1, do
                     name <- mkName ":"
                     case args of
                       x:y:[] ->
                        frequency 
                          [(2, return $ InfixC x name y),
                           (1, return $ NormalC name args)]
                       _      -> return NormalC name args
               (1, do
                   name <- mkName ":")

    where
      atMost :: Eq a => Integer -> (a -> Bool) -> [a] -> [a]
      atMost _ _ [] = []
      atMost 0 p xs               = filter (not p) xs
      atMost n p (x : xs) | n > 0 && p x = x : (atMost n p xs)
      atMost n p (x : xs) | n > 0        = x : (atMost n p xs)

numberOfDeclarations :: DataD -> PropertyM IO ()
numberOfDeclarations (DataDec dec) = monadicIO $ do
  decs <- runQ (liftDec dec)
  let DataD _ _ vars cons = dec
  assert $ length decs == length cons

main = do
  quickCheck numberOfDeclarations
  
  
  


