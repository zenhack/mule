
type 'a t = ('a * 'a list)

let cons a (b, cs) = (a, b::cs)
let singleton x = (x, [])
