
let union_with ~f l r =
  if not (UnionFind.eq l r) then
    begin
      let value = f (UnionFind.get l) (UnionFind.get r) in
      let ret = UnionFind.union l r in
      UnionFind.set ret value
    end
