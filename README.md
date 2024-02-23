# mini-frontend
A highly minimal compiler frontend, useful for experimentation

## Testing

1. Clone the Repository
2. Run the build script (It exists for windows, but not for linux. The code should work as-is though, there's just no buildscript for it)
3. Run the exe with your code file as the first argument

## Structure
Note: Important Declarations in Parens.\
\
Lexing: (lexer.h: TokenType, Token, Lexer)\
Pretty Basic, nothing to write home about.\
\
Parsing: (parser.h: NodeType, ASTNode, ConstantValue, Parser)\
Simple Pratt Parsing, Jai/Odin/Pascal like syntax.\
\
Checking: (check.h: ValueTypeKind, ValueType, Symbol, CheckingWork, Checker)\
Checking is done via a simple worklist algorithm.\
Two major functions are implemented: IsReady(Node) and Transfer(Node).\
IsReady: Thinking of an ASTNode as a node in a directed dependency graph instead of an AST, the IsReady function returns true if all the incoming dependency edges are resolved or ready to be resolved. Along with that, the node's status is also set appropriately.\
Transfer: Given that the node is ready to be resolved, the Transfer function does the actual resolving.

## TODOs
- Some code samples.
