--------------------------------------------------------------------------------

module Copilot.Kind.IL.Translate ( translate ) where

import Copilot.Kind.IL.Spec
import Copilot.Kind.Misc.Cast
import Copilot.Kind.Misc.Utils

import qualified Copilot.Core as C
import Copilot.Kind.CoreUtils.Operators
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Writer
import Control.Monad.State

import Data.Char

--------------------------------------------------------------------------------

-- 'nc' stands for **naming conventions**
ncSeq :: C.Id -> SeqId
ncSeq = printf "s%d"

-- We assume all local variables have distinct names whatever their scopes are
ncLocal :: C.Name -> SeqId
ncLocal s = "l" ++ dropWhile (not . isNumber) s

ncExternVar :: C.Name -> SeqId
ncExternVar n = "ext_" ++ n

ncExternFun :: C.Name -> SeqId
ncExternFun n = "_" ++ n

ncUnhandledOp :: String -> FunName
ncUnhandledOp = id

--------------------------------------------------------------------------------

-- | Translates a Copilot specification to an IL specification

translate :: C.Spec -> Spec
translate cspec@(C.Spec {C.specStreams}) = runTrans $ do 

  let mainSeqs = map seqDescr specStreams
  let modelInit = concatMap streamInit specStreams
  
  mainConstraints <- mapM streamRec specStreams
  properties <- Map.fromList <$> do
    forM (C.specProperties cspec) $ 
      \(C.Property {C.propertyName, C.propertyExpr}) -> do
        e' <- expr Bool propertyExpr
        return $ (propertyName, e')
        
  localSeqs <- getLocalSeqs
  localConstraints <- getLocalVarsConstraints
  unintFuns <- getUnintFuns
  
  return $ Spec 
    { modelInit
    , modelRec = mainConstraints ++ localConstraints
    , properties
    , depth
    , sequences = mainSeqs ++ localSeqs
    , unintFuns }
    
  where
      
    depth = 
      let bufferSize (C.Stream { C.streamBuffer }) = length streamBuffer in
        if null specStreams 
          then 0
          else maximum . (map bufferSize) $ specStreams


seqDescr :: C.Stream -> SeqDescr
seqDescr (C.Stream { C.streamId, C.streamExprType }) = 
  casting streamExprType (\t' -> SeqDescr (ncSeq streamId) t')


streamInit :: C.Stream -> [Constraint]
streamInit (C.Stream { C.streamId       = id
                     , C.streamBuffer   = b :: [val]
                     , C.streamExprType = ty}) = 

  zipWith initConstraint [0,1..] b
  where
    initConstraint :: Integer -> val -> Constraint
    initConstraint p v = casting ty $ \ty' -> 
      Op2 Bool Eq 
        (SVal ty' (ncSeq id) (Fixed p)) 
        (Const ty' $ cast ty' $ toDyn ty v)
 
                
streamRec :: C.Stream -> Trans Constraint
streamRec (C.Stream { C.streamId       = id
                    , C.streamExpr     = e
                    , C.streamBuffer   = b
                    , C.streamExprType = ty})
                    
  = let depth = length b in casting ty $ \ty' -> 
    do
      e' <- expr ty' e
      return $ Op2 Bool Eq
         (SVal ty' (ncSeq id) (_n_plus depth)) e'    

--------------------------------------------------------------------------------

expr :: forall t a . Type t -> C.Expr a -> Trans (Expr t)

expr t (C.Const ct v) = return $ Const t (cast t $ toDyn ct v)

expr t (C.Drop _ k id) = return $
  SVal t (ncSeq id) (_n_plus k)
    
    
expr t (C.Local ta _ name ea eb) = casting ta $ \ta' -> do
  ea' <- expr ta' ea
  newLocalVar 
    (SeqDescr (ncLocal name) ta') 
    (Op2 Bool Eq (SVal ta' (ncLocal name) _n_) ea')
  expr t eb


expr t (C.Var _ name) = return $ SVal t (ncLocal name) _n_


expr t (C.ExternVar ta name _) = casting ta $ \ta' -> do
  newExternVar (SeqDescr (ncExternVar name) ta')
  return $ SVal t (ncExternVar name) _n_


expr t (C.ExternFun ta name args _ _) = do
  newAnonFun descr
  mapM trArg args >>= return . FunApp t (ncExternFun name)
  where 
    trArg (C.UExpr {C.uExprExpr, C.uExprType}) = casting uExprType $ \ta ->
      U <$> expr ta uExprExpr
    descr =  
      let argType (C.UExpr {C.uExprType}) = casting uExprType U
      in casting ta $ \ta' ->
        UnintFunDescr (ncExternFun name) ta' (map argType args)


-- Arrays and functions are treated the same way
expr t (C.ExternArray _ tb name _ ind _ _) = casting tb $ \tb' -> do
  newAnonFun $ UnintFunDescr (ncExternFun name) tb' [U Integer]
  ind' <- U <$> expr Integer ind
  return $ FunApp t (ncExternFun name) [ind']
  
  
expr t (C.Op1 op e) = handleOp1
  t (op, e) expr notHandled Op1
  
  where notHandled (UnhandledOp1 opName ta tb) = do
          e' <- U <$> expr ta e
          newAnonFun $ UnintFunDescr (ncUnhandledOp opName) tb [U ta]
          return $ FunApp t (ncUnhandledOp opName) [e']


expr t (C.Op2 op e1 e2) = handleOp2
  t (op, e1, e2) expr notHandled Op2 (Op1 Bool Not)
  
  where notHandled (UnhandledOp2 opName ta tb tc) = do
          e1' <- U <$> expr ta e1
          e2' <- U <$> expr tb e2
          newAnonFun $ UnintFunDescr (ncUnhandledOp opName) tc [U ta, U tb]
          return $ FunApp t (ncUnhandledOp opName) [e1', e2']


expr t (C.Op3 (C.Mux _) cond e1 e2) = do
  cond' <- expr Bool cond
  e1'   <- expr t    e1
  e2'   <- expr t    e2
  return $ Ite t cond' e1' e2'

--------------------------------------------------------------------------------

data TransST = TransST
  { _unintFuns  :: [UnintFunDescr]
  , _localSeqs :: [SeqDescr]
  , _localVarsConstraints :: [Constraint] }
  
type Trans a = State TransST a

newAnonFun :: UnintFunDescr -> Trans ()
newAnonFun f = modify $ \st -> st {_unintFuns = f : _unintFuns st}

newExternVar :: SeqDescr -> Trans ()
newExternVar d = modify $ \st -> st {_localSeqs = d : _localSeqs st}

newLocalVar :: SeqDescr -> Constraint -> Trans ()
newLocalVar d c = do 
  modify $ \st -> st {_localSeqs = d : _localSeqs st}
  modify $ \st -> st {_localVarsConstraints = c : _localVarsConstraints st}
  
getUnintFuns :: Trans ([UnintFunDescr])
getUnintFuns = nubBy' (compare `on` funName) . _unintFuns <$> get

getLocalVarsConstraints :: Trans ([Constraint])
getLocalVarsConstraints = _localVarsConstraints <$> get

getLocalSeqs :: Trans ([SeqDescr])
getLocalSeqs = nubBy' (compare `on` seqId) . _localSeqs <$> get

runTrans :: Trans a -> a
runTrans m = fst $ runState m $ TransST [] [] []

--------------------------------------------------------------------------------
