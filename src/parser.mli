
type 'a parser_t  = ('a, unit) MParser.t

val expr : (Ast.Surface.Expr.t, unit) MParser.t
val expr_file : (Ast.Surface.Expr.t, unit) MParser.t
val typ : (Ast.Surface.Type.t, unit) MParser.t
val type_file : (Ast.Surface.Type.t, unit) MParser.t
val repl_line : (Ast.Surface.Expr.t option, unit) MParser.t

val located : 'a parser_t -> 'a Ast.Surface.Located.t parser_t
