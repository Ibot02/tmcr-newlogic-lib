module TMCR.Logic.Graphs (Bipartite, bipSetEdgesTo, bipGetEdgesFrom, TaggedGraph, taggedGetEdgesTo, taggedGetEdgesFrom, taggedEdge) where

import Algebra.Graph
import qualified Algebra.Graph.Bipartite.AdjacencyMap as Bip
import qualified Algebra.Graph.Labelled as Labelled
import Algebra.Graph.Labelled ((-<), (>-))

--todo
type Bipartite = Bip.AdjacencyMap
bipSetEdgesTo :: (Ord a, Ord b) => a -> [b] -> Bipartite b a -> Bipartite b a
bipSetEdgesTo dst src graph = foldl (\acc x -> acc `Bip.overlay` Bip.edge x dst) graph src
bipGetEdgesFrom :: (Eq a) => a -> Bipartite a b -> [b]
bipGetEdgesFrom src graph = concatMap snd $ filter ((==src) . fst) $ Bip.leftAdjacencyList graph

type TaggedGraph t = Labelled.Graph [t]
taggedGetEdgesTo :: (Eq t, Ord n) => n -> TaggedGraph t n -> [(n, t)]
taggedGetEdgesTo dst graph = flatten $ fmap Labelled.inputs $ Labelled.context (== dst) graph
taggedGetEdgesFrom :: (Eq t, Ord n) => n -> TaggedGraph t n -> [(t, n)]
taggedGetEdgesFrom src graph = fmap (\(x,y) -> (y,x)) $ flatten $ fmap Labelled.outputs $ Labelled.context (== src) graph

flatten :: Maybe [([t],n)] -> [(n,t)]
flatten Nothing = []
flatten (Just xs) = [(n,t) | (ts,n) <- xs, t <- ts]

taggedEdge :: t -> n -> n -> TaggedGraph t n
taggedEdge t src dst = src -< [t] >- dst