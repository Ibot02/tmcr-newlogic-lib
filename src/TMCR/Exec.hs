module TMCR.Exec {-(TransactionalShufflesProgress(), TransactionalShuffleProgress(), TReadEval(..), runAsyncsForever, runAsyncsLogicOnly, initialTShuffleProgress)-} where

{-
import TMCR.Exec.Internal
import TMCR.Logic.Shuffle (ShuffleName)

class (Monad m) => MonadExecShuffle m where
  shufflesToComplete :: m [([Thingy], ShuffleName, [Thingy])]

  shuffleSetFrom :: Thingy -> ShuffleName -> Maybe Thingy -> m ()
  shuffleSetTo :: Thingy -> ShuffleName -> Maybe Thingy -> m ()
-}