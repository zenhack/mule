include UnionFind.Make(UnionFind.StoreMap)

let modify f x = set x (f (get x))
