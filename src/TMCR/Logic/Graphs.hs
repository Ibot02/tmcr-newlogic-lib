module TMCR.Logic.Graphs where


--todo
data Bipartite a b
bipSetEdgesTo :: a -> [b] -> Bipartite b a -> Bipartite b a
bipSetEdgesTo = undefined
bipGetEdgesFrom :: a -> Bipartite a b -> [b]
bipGetEdgesFrom = undefined
data TaggedGraph t n
taggedGetEdgesTo :: (Ord n) => n -> TaggedGraph t n -> [(n, t)]
taggedGetEdgesTo = undefined
taggedGetEdgesFrom :: (Ord n) => n -> TaggedGraph t n -> [(t, n)]
taggedGetEdgesFrom = undefined

taggedEdge :: t -> n -> n -> TaggedGraph t n
taggedEdge = undefined

instance Semigroup (TaggedGraph t n) where
instance Monoid (TaggedGraph t n) where